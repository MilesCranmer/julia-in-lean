import JuliaLean.base.operators
import JuliaLean.base.number
import JuliaLean.base.tuple
import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.base.array
import JuliaLean.base.int
import JuliaLean.base.bitarray
import JuliaLean.base.checked
import JuliaLean.base.abstractarray
import JuliaLean.base.range
import JuliaLean.Proofs.base.range
import JuliaLean.base.indices
import JuliaLean.Proofs.base.array
import JuliaLean.Proofs.base.bitarray.common.count
import JuliaLean.Proofs.base.bitarray.common.reshape
import JuliaLean.Proofs.base.bitarray.common.shift

namespace JuliaLean.CompletionState3

@[simp] theorem runBind {E S A B : Type} (action : ExceptT E (StateM S) A)
    (next : A → ExceptT E (StateM S) B) (state : S) :
    ((action >>= next).run state) =
      match action.run state with
      | (.ok value, final) => (next value).run final
      | (.error error, final) => (.error error, final) := by
  simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind]
  cases action state with
  | mk result final => cases result <;> rfl

@[simp] theorem runMap {E S A B : Type} (action : ExceptT E (StateM S) A)
    (f : A → B) (state : S) :
    ((f <$> action).run state) =
      match action.run state with
      | (.ok value, final) => (.ok (f value), final)
      | (.error error, final) => (.error error, final) := by
  simp only [Functor.map, ExceptT.map, Bind.bind, ExceptT.run, ExceptT.mk, StateT.bind]
  cases action state with
  | mk result final => cases result <;> rfl

@[simp] theorem runCatch {E S A : Type} (action : ExceptT E (StateM S) A)
    (handler : E → ExceptT E (StateM S) A) (state : S) :
    (tryCatchThe E action handler).run state =
      match action.run state with
      | (.ok value, final) => (.ok value, final)
      | (.error error, final) => (handler error).run final := by
  simp only [tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch, Bind.bind,
    ExceptT.run, ExceptT.mk, StateT.bind]
  cases action state with
  | mk result final => cases result <;> rfl

@[simp] theorem runPure {E S A : Type} (value : A) (state : S) :
    ((pure value : ExceptT E (StateM S) A).run state) = (.ok value, state) := rfl

@[simp] theorem runThrow {E S A : Type} (error : E) (state : S) :
    ((throwThe E error : ExceptT E (StateM S) A).run state) = (.error error, state) := rfl

@[simp] theorem runGet {E S : Type} (state : S) :
    ((get : ExceptT E (StateM S) S).run state) = (.ok state, state) := rfl

@[simp] theorem byteToListLength (bytes : ByteArray) : bytes.toList.length = bytes.size := by
  have loop : ∀ (i : Nat) (r : List UInt8),
      (ByteArray.toList.loop bytes i r).length = bytes.size - i + r.length := by
    intro i r
    fun_induction ByteArray.toList.loop bytes i r with
    | case1 i r h ih => simp only [List.length_cons] at ih; omega
    | case2 i r h => simp only [List.length_reverse]; omega
  exact loop 0 []


end JuliaLean.CompletionState3

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group2

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Each input header uses its original independent storage handle. -/
theorem concat_vector_chunks (entry : List Bool × Nat) :
    (concat_vector entry).chunks = entry.2 := rfl

/-- The exact frozen vector concatenation observations hold throughout the supported total-size range 0–64. -/
theorem concat_frozen_vector_contract_small (vectors : List (List Bool))
    (hne : vectors ≠ []) (hcount : vectors.length ≤ 9223372036854775807)
    (hbound : vectors.flatten.length ≤ 64) :
    let handles : List BitVector := (vectors.zip (List.range vectors.length)).map fun entry =>
      ⟨entry.2, int entry.1.length, [int entry.1.length]⟩
    let state := concat_initial vectors
    let vertical := (bitArrayVcatVectors handles (fun n => Round5.Round2.allocateBitArrayModel [n])).run state
    match vertical.1 with
    | .ok v =>
      v.dims = [int vectors.flatten.length] ∧ bitValues vertical.2 v = vectors.flatten ∧
        Round5.Round2.PackedInvariant vertical.2 v ∧
        ((∀ xs ∈ vectors, xs.length = (vectors.headD []).length) →
          let horizontal := (bitArrayHcatVectors handles
            (fun rows cols => Round5.Round2.allocateBitArrayModel [rows, cols])).run state
          match horizontal.1 with
          | .ok h => h.dims = [int (vectors.headD []).length, int vectors.length] ∧
              bitValues horizontal.2 h = vectors.flatten ∧ Round5.Round2.PackedInvariant horizontal.2 h
          | .error _ => False)
    | .error _ => False := by
  dsimp only
  let horizontalCondition : Prop :=
    (∀ xs ∈ vectors, xs.length = (vectors.headD []).length) →
      let handles : List BitVector := (vectors.zip (List.range vectors.length)).map fun entry =>
        ⟨entry.2, int entry.1.length, [int entry.1.length]⟩
      let horizontal := (bitArrayHcatVectors handles
        (fun rows cols => Round5.Round2.allocateBitArrayModel [rows, cols])).run (concat_initial vectors)
      match horizontal.1 with
      | .ok h => h.dims = [int (vectors.headD []).length, int vectors.length] ∧
          bitValues horizontal.2 h = vectors.flatten ∧ Round5.Round2.PackedInvariant horizontal.2 h
      | .error _ => False
  have hhorizontal : horizontalCondition := by
    intro hall
    dsimp only
    obtain ⟨out, finished, hrun, hdims, hbits, hinv⟩ := concat_hcat_small_correct vectors hne hcount hbound hall
    rw [hrun]
    exact ⟨hdims, hbits, hinv⟩
  obtain ⟨out, finished, hrun, hdims, hbits, hinv⟩ := concat_vcat_small_correct vectors hbound
  rw [hrun]
  exact ⟨hdims, hbits, hinv, hhorizontal⟩
end JuliaLean.ChatGPT.Batch3.Group2
end JuliaLean.Proofs.base.bitarray

section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace JuliaLean.ChatGPT.Batch4.Group8
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.Archive20261102Round6

def aliasExtremaParent : BitMatrix := ⟨0, int 1, [int 1, int 1]⟩
def aliasExtremaState : State := MutableMemory.initial [some (u64 2)]

theorem aliasExtremaParent_valid :
    ValidExtremaStorage aliasExtremaState aliasExtremaParent := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (0 : Int) ≤ 1 ∧ 1 ≤ (1 : Int) ∧ (1 : Int) - 1 + 1 ≤ 33 ∧ (33 : Nat) < 2 ^ 63
    decide
  · decide
  · rfl
  · intro d hd
    change d ∈ [int 1, int 1] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hd
    subst d
    decide
  · decide
  · decide
  · intro cell hcell
    change cell ∈ [some (u64 2)] at hcell
    have heq := List.mem_singleton.mp hcell
    rw [heq]
    rfl
  · intro slots hslots
    change slots ∈ [[some (u64 2)] ++ List.replicate 32 none] at hslots
    have heq := List.mem_singleton.mp hslots
    rw [heq]
    decide

/-- Maximum reads the true padding bit introduced by growing a vector alias. -/
theorem BitarrayScalarExtremaValues_refuted : ¬ JuliaLean.Proofs.base.bitarray.Archive20261102Round6.ScalarExtremaValues := by
  intro h
  have hx := h aliasExtremaState aliasExtremaParent aliasExtremaParent_valid
  have hf : ((bitArrayMaximum bitArrayAny aliasExtremaParent).run aliasExtremaState).1 ≠ .ok false := by
    change (Except.ok true : Except Error Bool) ≠ .ok false
    intro bad
    cases bad
  exact hf hx.2.2.2
end JuliaLean.ChatGPT.Batch4.Group8
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true

/-- The exact frozen `findall` invocation, factored for per-input results. -/
@[irreducible] def scan_findAllAction (xs : List Bool) : BitMutationM Nat :=
  let B : BitArray 1 := ⟨0, int xs.length, [int xs.length]⟩
  let count : BitArray 1 → BitMutationM I64 := fun _ => pure (int (Int.ofNat (countTrue xs)))
  let allocate : I64 → BitMutationM Nat := fun n => mutableAllocate (some ⟨8, false, false⟩) 0 n
  let set : Nat → BitIndex → I64 → BitMutationM Unit := fun handle key index =>
    BitFindAllSpec.match_1 (fun _ => BitMutationM Unit) key
      (fun i => mutableSet handle (u64 i.val) index)
      (fun indices => mutableSet handle (u64 ((indices.headD (int 0)).val)) index)
  let allindices : Nat → BitArray 1 → BitMutationM Nat := fun handle array => do
    for i in intRange (int 1) array.len do mutableSet handle (u64 i.val) i
    pure handle
  bitArrayFindAll count allocate set allindices trailingZerosWord B

/-- The exact frozen output observation, applied to a separately checked execution result. -/
def scan_findAllOutcome (count : Nat) (result : Except Error Nat × State) : Prop :=
  BitFindAllSpec.match_3 (fun _ => Prop) result
    (fun output state' => (state'.contents output).length = count)
    (fun _ _ => False)

/-- Zero population count exits immediately after successful result allocation. -/
theorem scan_findAll_zero_run {N : Nat} {V : Type}
    (count : BitArray N → BitMutationM I64) (allocate : I64 → BitMutationM V)
    (set : V → BitIndex → I64 → BitMutationM Unit)
    (allindices : V → BitArray N → BitMutationM V)
    (trailingZeros : U64 → I64) (B : BitArray N) (s outState : State) (out : V)
    (hc : (count B).run s = (.ok (int 0), s))
    (ha : (allocate (int 0)).run s = (.ok out, outState)) :
    (bitArrayFindAll count allocate set allindices trailingZeros B).run s =
      (.ok out, outState) := by
  simp only [bitArrayFindAll, shape_run_bind, hc, ha, beq_self_eq_true,
    ite_true, shape_run_pure]

/-- The all-indices branch writes only within the freshly allocated vector. -/
theorem scan_allIndices_run (s : State) (n : Nat)
    (hn : n ≤ 9223372036854775807) :
    ((do
      for i in intRange (int 1) (int n) do
        mutableSet s.arrays.length (u64 i.val) i
      pure s.arrays.length) : BitMutationM Nat).run
        (shiftFreshHeap s (List.replicate n none)) =
      (.ok s.arrays.length, shiftFreshHeap s
        ((List.range n).map (fun i => some (u64 (int ((i + 1 : Nat) : Int)).val)))) := by
  rw [packedObserve_intRange n hn, List.forIn_map]
  have hr := shiftFreshWriteLoop s (List.range n) (List.replicate n none)
    (fun i => u64 (int ((i + 1 : Nat) : Int)).val)
    (by simpa only [List.length_replicate] using hn)
    (by intro i hi; simpa only [List.length_replicate] using List.mem_range.mp hi)
  have hf := shiftFreshFoldAll (List.replicate n (none : Option U64))
    (fun i => some (u64 (int ((i + 1 : Nat) : Int)).val))
  simp only [List.length_replicate] at hf
  rw [hf] at hr
  simp only [shape_run_bind, hr, shape_run_pure]

/-- A positive count equal to the logical length chooses the all-indices branch. -/
theorem scan_findAll_full_run {N : Nat} {V : Type}
    (count : BitArray N → BitMutationM I64) (allocate : I64 → BitMutationM V)
    (set : V → BitIndex → I64 → BitMutationM Unit)
    (allindices : V → BitArray N → BitMutationM V)
    (trailingZeros : U64 → I64) (B : BitArray N)
    (s allocated outState : State) (out result : V)
    (hn : B.len ≠ int 0)
    (hc : (count B).run s = (.ok B.len, s))
    (ha : (allocate B.len).run s = (.ok out, allocated))
    (hi : (allindices out B).run allocated = (.ok result, outState)) :
    (bitArrayFindAll count allocate set allindices trailingZeros B).run s =
      (.ok result, outState) := by
  have hzero : (B.len == int 0) = false := beq_eq_false_iff_ne.mpr hn
  simp only [bitArrayFindAll, shape_run_bind, hc, ha, hzero,
    Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true, hi]


/-- An output run and its visible length imply the exact findall observation. -/
theorem scan_findAll_observe_from (xs : List Bool) (output : Nat) (out : State)
    (hr : (scan_findAllAction xs).run (initWords (encodeBits xs)) = (.ok output, out))
    (hc : (out.contents output).length = countTrue xs) :
    scan_findAllOutcome (countTrue xs) ((scan_findAllAction xs).run (initWords (encodeBits xs))) := by
  exact Eq.mpr (congrArg (scan_findAllOutcome (countTrue xs)) hr) hc

/-- The zero-count frozen program allocates an empty result and then returns it. -/
theorem scan_findAll_zero_result (xs : List Bool) (hc : countTrue xs = 0) :
    (scan_findAllAction xs).run (initWords (encodeBits xs)) =
      (.ok 1, shiftFreshHeap (initWords (encodeBits xs)) []) := by
  have ha := shiftFreshAllocate (initWords (encodeBits xs)) 0 (by omega)
  unfold scan_findAllAction
  apply scan_findAll_zero_run
  · change (Except.ok (int (Int.ofNat (countTrue xs))), initWords (encodeBits xs)) = _
    rw [hc]
    rfl
  · exact ha

/-- Zero-count inputs satisfy the frozen length contract at every list length. -/
theorem scan_findAll_zero (xs : List Bool) (hc : countTrue xs = 0) :
    scan_findAllOutcome (countTrue xs) ((scan_findAllAction xs).run (initWords (encodeBits xs))) := by
  have hcontents := shiftFreshContents (initWords (encodeBits xs)) [] (by decide)
  change (shiftFreshHeap (initWords (encodeBits xs)) []).contents 1 = [] at hcontents
  apply scan_findAll_observe_from xs 1 _ (scan_findAll_zero_result xs hc)
  rw [hcontents, hc]
  rfl

/-- The positive all-true frozen program fills the complete fresh result. -/
theorem scan_findAll_full_result (xs : List Bool) (hc : countTrue xs = xs.length)
    (hn : xs.length ≤ 576460752303423488) (hp : 0 < xs.length) :
    (scan_findAllAction xs).run (initWords (encodeBits xs)) =
      (.ok 1, shiftFreshHeap (initWords (encodeBits xs))
        ((List.range xs.length).map (fun i => some (u64 (int ((i + 1 : Nat) : Int)).val)))) := by
  have hsize : xs.length ≤ 9223372036854775807 := by omega
  have hne : int xs.length ≠ int 0 := by
    intro he
    have hv := congrArg Subtype.val he
    rw [packedInt_val xs.length hsize] at hv
    change (xs.length : Int) = 0 at hv
    omega
  have ha := shiftFreshAllocate (initWords (encodeBits xs)) xs.length hn
  have hi := scan_allIndices_run (initWords (encodeBits xs)) xs.length hsize
  unfold scan_findAllAction
  apply scan_findAll_full_run
  · exact hne
  · change (Except.ok (int (Int.ofNat (countTrue xs))), initWords (encodeBits xs)) = _
    rw [hc]
    rfl
  · exact ha
  · exact hi

/-- All-true inputs satisfy the frozen length contract below the output allocation bound. -/
theorem scan_findAll_full (xs : List Bool) (hc : countTrue xs = xs.length)
    (hn : xs.length ≤ 576460752303423488) :
    scan_findAllOutcome (countTrue xs) ((scan_findAllAction xs).run (initWords (encodeBits xs))) := by
  by_cases hz : xs.length = 0
  · exact scan_findAll_zero xs (hc.trans hz)
  · have hp : 0 < xs.length := by omega
    have hsize : xs.length ≤ 9223372036854775807 := by omega
    have hs : ((List.range xs.length).map
        (fun i => some (u64 (int ((i + 1 : Nat) : Int)).val))).length ≤ 9223372036854775807 := by
      simpa only [List.length_map, List.length_range] using hsize
    have hcontents := shiftFreshContents (initWords (encodeBits xs))
      ((List.range xs.length).map (fun i => some (u64 (int ((i + 1 : Nat) : Int)).val))) hs
    change (shiftFreshHeap (initWords (encodeBits xs)) _).contents 1 = _ at hcontents
    apply scan_findAll_observe_from xs 1 _ (scan_findAll_full_result xs hc hn hp)
    rw [hcontents, List.length_map, List.length_range, hc]
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true


set_option backward.isDefEq.respectTransparency false

/-- The exact any/all observations under a representable logical-length bound. -/
theorem scan_vectorLoopObservations_bounded (xs : List Bool)
    (hbound : xs.length ≤ (IntTy.max .i64).toNat) :
    let B := vectorBits xs
    let state := initWords (encodeBits xs)
    ((bitArrayAny B).run state).1 = .ok (xs.any id) ∧
      ((bitArrayAll B).run state).1 = .ok (xs.all id) := by
  have hn : xs.length ≤ 9223372036854775807 := hbound
  have hv := packedObserve_intVal xs.length hn
  have hnonnegative : int 0 ≤ int xs.length := by
    change (int 0).val ≤ (int xs.length).val
    rw [hv]
    change (0 : Int) ≤ (xs.length : Int)
    omega
  have hmul : int 1 * int xs.length = int xs.length := by
    apply Subtype.ext
    change wrapInt .i64 ((int 1).val * (int xs.length).val) = (int xs.length).val
    rw [hv]
    change wrapInt .i64 (1 * (xs.length : Int)) = (xs.length : Int)
    have hv' : wrapInt .i64 (xs.length : Int) = (xs.length : Int) := hv
    simpa only [Int.one_mul] using hv'
  have hshape : [int xs.length].foldl (· * ·) (int 1) = int xs.length := by
    simpa only [List.foldl_cons, List.foldl_nil] using hmul
  have h := BitarraysCountAnyAll_proven (N := 1) [int xs.length] xs rfl
    (by
      intro d hd
      have heq : d = int xs.length := List.mem_singleton.mp hd
      rw [heq]
      exact hnonnegative)
    hshape hbound
  exact h.2
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

abbrev scan_FindSkipState := Option Nat × I64 × I64 × U64
abbrev scan_FindMainState := Option Nat × I64 × I64 × I64 × List I64 × U64

def scan_find_skipStep (chunks output : Nat) (_ : Unit)
    (registers : scan_FindSkipState) : BitMutationM (ForInStep scan_FindSkipState) := do
  let Bi := registers.2.1
  let i1 := registers.2.2.1
  let c := registers.2.2.2
  if c == u64 0 then
    let count ← mutableLength chunks
    if Bi == count then
      pure (.done (some output, Bi, i1, c))
    else
      let i1 := i1 + int 64
      let Bi := Bi + int 1
      let c ← mutableGet chunks Bi
      pure (.yield (none, Bi, i1, c))
  else
    pure (.done (none, Bi, i1, c))

def scan_find_skip (chunks output : Nat) (Bi i1 : I64) (c : U64) :
    BitMutationM scan_FindSkipState :=
  forIn ({} : Lean.Loop) (none, Bi, i1, c) (scan_find_skipStep chunks output)

def scan_find_mainStep (chunks output : Nat) (dims : List I64)
    (write : Nat → BitIndex → I64 → BitMutationM Unit) (trailingZeros : U64 → I64)
    (_ : Unit) (registers : scan_FindMainState) : BitMutationM (ForInStep scan_FindMainState) := do
  let Bi := registers.2.1
  let i1 := registers.2.2.1
  let i := registers.2.2.2.1
  let irest := registers.2.2.2.2.1
  let c := registers.2.2.2.2.2
  let skipped ← scan_find_skip chunks output Bi i1 c
  let Bi := skipped.2.1
  let i1 := skipped.2.2.1
  let c := skipped.2.2.2
  match skipped.1 with
  | some result => pure (.done (some result, Bi, i1, i, irest, c))
  | none =>
      let tz := trailingZeros c
      let nextWord := blsr c
      let (coord, rest) := overflowInd (i1 + tz) irest dims
      let key := if rest.isEmpty then toIndEmpty coord rest else toInd coord rest
      write output key i
      pure (.yield (none, Bi, i1 - tz, i + int 1, rest, nextWord))

def scan_find_main (chunks output : Nat) (dims : List I64)
    (write : Nat → BitIndex → I64 → BitMutationM Unit) (trailingZeros : U64 → I64)
    (Bi i1 i : I64) (irest : List I64) (c : U64) : BitMutationM scan_FindMainState :=
  forIn ({} : Lean.Loop) (none, Bi, i1, i, irest, c)
    (scan_find_mainStep chunks output dims write trailingZeros)

def scan_find_body {N : Nat} (B : BitArray N) (output : Nat)
    (write : Nat → BitIndex → I64 → BitMutationM Unit) (trailingZeros : U64 → I64) :
    BitMutationM Nat := do
  let c ← mutableGet B.chunks (int 1)
  let registers ← scan_find_main B.chunks output B.dims write trailingZeros
    (int 1) (int 1) (int 1) (List.replicate (N - 1) (int 1)) c
  match registers.1 with
  | some result => pure result
  | none => pure output

/-- Remaining output entries in the live word and the unread source suffix. -/
def scan_find_remaining (words : List U64) (k : Nat) (c : U64) : Nat :=
  popcountWord c + ((words.drop (k + 1)).map popcountWord).sum

theorem scan_find_remaining_next (words : List U64) (k : Nat)
    (hk : k + 1 < words.length) :
    scan_find_remaining words k (u64 0) =
      scan_find_remaining words (k + 1) (words.getD (k + 1) (u64 0)) := by
  have hd : words.drop (k + 1) = words.getD (k + 1) (u64 0) :: words.drop (k + 1 + 1) := by
    rw [← List.getElem_cons_drop (h := hk), List.getElem_eq_getD (u64 0)]
  unfold scan_find_remaining
  rw [hd]
  simp only [List.map_cons, List.sum_cons]
  have hz : popcountWord (u64 0) = 0 := by decide
  rw [hz, Nat.zero_add]

/-- A nonempty word exits the inner search without changing state. -/
theorem scan_find_skip_nonzero (chunks output : Nat) (Bi i1 : I64) (c : U64)
    (s : State) (hc : c ≠ u64 0) :
    (scan_find_skip chunks output Bi i1 c).run s =
      (.ok (none, Bi, i1, c), s) := by
  apply reverseLoopDone
  have hb : (c == u64 0) = false := beq_eq_false_iff_ne.mpr hc
  simp only [scan_find_skipStep, hb, Bool.false_eq_true, ite_false, shape_run_pure]

/-- The last empty source word terminates the inner search. -/
theorem scan_find_skip_last (words : List U64) (slots : List (Option U64))
    (k : Nat) (i1 : I64) (hk : k + 1 = words.length) :
    (scan_find_skip 0 1 (int ((k + 1 : Nat) : Int)) i1 (u64 0)).run
        (shiftFreshHeap (initWords words) slots) =
      (.ok (some 1, int ((k + 1 : Nat) : Int), i1, u64 0), shiftFreshHeap (initWords words) slots) := by
  apply reverseLoopDone
  have he : (int ((k + 1 : Nat) : Int) == int words.length) = true := by rw [hk]; exact beq_self_eq_true _
  simp only [scan_find_skipStep, beq_self_eq_true, ite_true, shape_run_bind,
    shiftFreshSourceLength, he, shape_run_pure]

/-- One empty-word iteration composes the source length and next-word reads. -/
theorem scan_find_skip_step_from (chunks output : Nat) (Bi i1 count : I64)
    (word : U64) (s : State)
    (hne : (Bi == count) = false)
    (hlen : (mutableLength chunks).run s = (.ok count, s))
    (hread : (mutableGet chunks (Bi + int 1)).run s = (.ok word, s)) :
    (scan_find_skipStep chunks output () (none, Bi, i1, u64 0)).run s =
      (.ok (.yield (none, Bi + int 1, i1 + int 64, word)), s) := by
  simp only [scan_find_skipStep, beq_self_eq_true, ite_true, shape_run_bind,
    hlen, hne, Bool.false_eq_true, ite_false, hread, shape_run_pure]

/-- Advancing to a following word leaves the source and destination heap intact. -/
theorem scan_find_skip_step (words : List U64) (slots : List (Option U64))
    (k : Nat) (i1 : I64) (hn : words.length ≤ 9223372036854775807)
    (hk : k + 1 < words.length) :
    (scan_find_skipStep 0 1 () (none, int ((k + 1 : Nat) : Int), i1, u64 0)).run
        (shiftFreshHeap (initWords words) slots) =
      (.ok (.yield (none, int ((k + 1 + 1 : Nat) : Int), i1 + int 64,
        words.getD (k + 1) (u64 0))), shiftFreshHeap (initWords words) slots) := by
  have he : (int ((k + 1 : Nat) : Int) == int words.length) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    have hv := congrArg Subtype.val he
    rw [packedInt_val (k + 1) (by omega), packedInt_val words.length hn] at hv
    omega
  have hi : int ((k + 1 : Nat) : Int) + int 1 = int ((k + 1 + 1 : Nat) : Int) := by
    rw [packedInt_add]
    congr 1
  have hread : (mutableGet 0 (int ((k + 1 : Nat) : Int) + int 1)).run
      (shiftFreshHeap (initWords words) slots) =
      (.ok (words.getD (k + 1) (u64 0)), shiftFreshHeap (initWords words) slots) := by
    rw [hi]
    exact shiftFreshSource words slots (k + 1) hn hk
  have h := scan_find_skip_step_from 0 1 (int ((k + 1 : Nat) : Int)) i1
    (int words.length) (words.getD (k + 1) (u64 0)) _ he
    (shiftFreshSourceLength words slots) hread
  exact h.trans (by rw [hi])

/-- The inner search either reaches the last empty word or finds a nonempty word,
preserving the number of still-unwritten entries and the entire heap. -/
theorem scan_find_skip_complete (words : List U64) (slots : List (Option U64))
    (k : Nat) (i1 : I64) (c : U64) (hn : words.length ≤ 9223372036854775807)
    (hk : k < words.length) :
    ∃ next : Nat, ∃ coord : I64, ∃ word : U64, ∃ found : Option Nat,
      next < words.length ∧
      (scan_find_skip 0 1 (int ((k + 1 : Nat) : Int)) i1 c).run
          (shiftFreshHeap (initWords words) slots) =
        (.ok (found, int ((next + 1 : Nat) : Int), coord, word),
          shiftFreshHeap (initWords words) slots) ∧
      scan_find_remaining words next word = scan_find_remaining words k c ∧
      ((found = some 1 ∧ word = u64 0 ∧ next + 1 = words.length) ∨
        (found = none ∧ word ≠ u64 0)) := by
  by_cases hc : c = u64 0
  · subst c
    by_cases he : k + 1 = words.length
    · exact ⟨k, i1, u64 0, some 1, hk,
        scan_find_skip_last words slots k i1 he, rfl, Or.inl ⟨rfl, rfl, he⟩⟩
    · have hk' : k + 1 < words.length := by omega
      obtain ⟨next, coord, word, found, hnext, hrun, hcount, hcase⟩ :=
        scan_find_skip_complete words slots (k + 1) (i1 + int 64)
          (words.getD (k + 1) (u64 0)) hn hk'
      refine ⟨next, coord, word, found, hnext, ?_, ?_, hcase⟩
      · exact reverseLoopYield (scan_find_skipStep 0 1)
          (none, int ((k + 1 : Nat) : Int), i1, u64 0)
          (none, int ((k + 1 + 1 : Nat) : Int), i1 + int 64, words.getD (k + 1) (u64 0))
          (found, int ((next + 1 : Nat) : Int), coord, word) _ _ _
          (scan_find_skip_step words slots k i1 hn hk') hrun
      · exact hcount.trans (scan_find_remaining_next words k hk').symm
  · exact ⟨k, i1, c, none, hk,
      scan_find_skip_nonzero 0 1 (int ((k + 1 : Nat) : Int)) i1 c _ hc,
      rfl, Or.inr ⟨rfl, hc⟩⟩
termination_by words.length - k
decreasing_by omega

/-- The frozen result callback writes the scalar coordinate as an unsigned word. -/
def scan_findWrite (handle : Nat) (key : BitIndex) (index : I64) : BitMutationM Unit :=
  BitFindAllSpec.match_1 (fun _ => BitMutationM Unit) key
    (fun i => mutableSet handle (u64 i.val) index)
    (fun indices => mutableSet handle (u64 ((indices.headD (int 0)).val)) index)

/-- A finished inner search terminates the outer scan. -/
theorem scan_find_mainStep_done (chunks output : Nat) (dims : List I64)
    (write : Nat → BitIndex → I64 → BitMutationM Unit) (tz : U64 → I64)
    (Bi i1 i nextBi nextCoord : I64) (c nextWord : U64) (s : State)
    (hskip : (scan_find_skip chunks output Bi i1 c).run s =
      (.ok (some output, nextBi, nextCoord, nextWord), s)) :
    (scan_find_mainStep chunks output dims write tz () (none, Bi, i1, i, [], c)).run s =
      (.ok (.done (some output, nextBi, nextCoord, i, [], nextWord)), s) := by
  simp only [scan_find_mainStep, shape_run_bind, hskip, shape_run_pure]

/-- A nonempty current word writes one result and clears exactly its lowest set bit. -/
theorem scan_find_mainStep_write (chunks output : Nat) (dims : List I64)
    (write : Nat → BitIndex → I64 → BitMutationM Unit) (tz : U64 → I64)
    (Bi i1 i nextBi nextCoord : I64) (c nextWord : U64) (s out : State)
    (hskip : (scan_find_skip chunks output Bi i1 c).run s =
      (.ok (none, nextBi, nextCoord, nextWord), s))
    (hwrite : (write output (.scalar (nextCoord + tz nextWord)) i).run s = (.ok (), out)) :
    (scan_find_mainStep chunks output dims write tz () (none, Bi, i1, i, [], c)).run s =
      (.ok (.yield (none, nextBi, nextCoord - tz nextWord, i + int 1, [], blsr nextWord)), out) := by
  simp only [scan_find_mainStep, shape_run_bind, hskip, overflowInd,
    List.isEmpty_nil, ite_true, toIndEmpty, hwrite, shape_run_pure]

/-- The mixed scan terminates after consuming its finite remaining population;
every callback write stays inside the original destination allocation. -/
theorem scan_find_main_complete (words : List U64) (slots : List (Option U64))
    (k done : Nat) (coord : I64) (c : U64) (dims : List I64) (tz : U64 → I64)
    (hn : words.length ≤ 9223372036854775807)
    (hm : slots.length ≤ 9223372036854775807) (hk : k < words.length)
    (hcapacity : done + scan_find_remaining words k c ≤ slots.length) :
    ∃ registers : scan_FindMainState, ∃ final : List (Option U64),
      (scan_find_main 0 1 dims scan_findWrite tz
        (int ((k + 1 : Nat) : Int)) coord (int ((done + 1 : Nat) : Int)) [] c).run
          (shiftFreshHeap (initWords words) slots) =
        (.ok registers, shiftFreshHeap (initWords words) final) ∧
      registers.1 = some 1 ∧ final.length = slots.length := by
  obtain ⟨next, nextCoord, word, found, hnext, hskip, hcount, hcase⟩ :=
    scan_find_skip_complete words slots k coord c hn hk
  rcases hcase with ⟨hfound, hword, hend⟩ | ⟨hfound, hword⟩
  · subst found
    refine ⟨(some 1, int ((next + 1 : Nat) : Int), nextCoord,
      int ((done + 1 : Nat) : Int), [], word), slots, ?_, rfl, rfl⟩
    exact reverseLoopDone (scan_find_mainStep 0 1 dims scan_findWrite tz) _ _ _ _
      (scan_find_mainStep_done 0 1 dims scan_findWrite tz
        (int ((k + 1 : Nat) : Int)) coord (int ((done + 1 : Nat) : Int))
        (int ((next + 1 : Nat) : Int)) nextCoord c word _ hskip)
  · subst found
    have hpop := scan_blsr_population word hword
    have hremaining : scan_find_remaining words next (blsr word) + 1 =
        scan_find_remaining words k c := by
      unfold scan_find_remaining at hcount ⊢
      omega
    have hdone : done < slots.length := by omega
    let finalSlots := slots.set done (some (u64 (nextCoord + tz word).val))
    have hf : finalSlots.length = slots.length := List.length_set
    have hwrite : (scan_findWrite 1 (.scalar (nextCoord + tz word))
        (int ((done + 1 : Nat) : Int))).run (shiftFreshHeap (initWords words) slots) =
        (.ok (), shiftFreshHeap (initWords words) finalSlots) :=
      shiftFreshSet (initWords words) slots done (u64 (nextCoord + tz word).val) hm hdone
    have hstep := scan_find_mainStep_write 0 1 dims scan_findWrite tz
      (int ((k + 1 : Nat) : Int)) coord (int ((done + 1 : Nat) : Int))
      (int ((next + 1 : Nat) : Int)) nextCoord c word _ _ hskip hwrite
    have hi : int ((done + 1 : Nat) : Int) + int 1 = int ((done + 1 + 1 : Nat) : Int) := by
      rw [packedInt_add]
      congr 1
    have hstep' : (scan_find_mainStep 0 1 dims scan_findWrite tz ()
        (none, int ((k + 1 : Nat) : Int), coord, int ((done + 1 : Nat) : Int), [], c)).run
          (shiftFreshHeap (initWords words) slots) =
        (.ok (.yield (none, int ((next + 1 : Nat) : Int), nextCoord - tz word,
          int ((done + 1 + 1 : Nat) : Int), [], blsr word)),
          shiftFreshHeap (initWords words) finalSlots) :=
      hstep.trans (by rw [hi])
    obtain ⟨registers, final, hrun, hresult, hlength⟩ :=
      scan_find_main_complete words finalSlots next (done + 1) (nextCoord - tz word)
        (blsr word) dims tz hn (by rw [hf]; exact hm) hnext (by rw [hf]; omega)
    refine ⟨registers, final, ?_, hresult, hlength.trans hf⟩
    exact reverseLoopYield (scan_find_mainStep 0 1 dims scan_findWrite tz)
      (none, int ((k + 1 : Nat) : Int), coord, int ((done + 1 : Nat) : Int), [], c)
      (none, int ((next + 1 : Nat) : Int), nextCoord - tz word,
        int ((done + 1 + 1 : Nat) : Int), [], blsr word)
      registers _ _ _ hstep' hrun
termination_by scan_find_remaining words k c
decreasing_by
  have hpop := scan_blsr_population word hword
  unfold scan_find_remaining at hcount ⊢
  omega

/-- Compose the initial chunk load and the completed nested scan. -/
theorem scan_find_body_from {N : Nat} (B : BitArray N) (output : Nat)
    (write : Nat → BitIndex → I64 → BitMutationM Unit) (tz : U64 → I64)
    (s out : State) (c : U64) (registers : scan_FindMainState)
    (hread : (mutableGet B.chunks (int 1)).run s = (.ok c, s))
    (hloop : (scan_find_main B.chunks output B.dims write tz
      (int 1) (int 1) (int 1) (List.replicate (N - 1) (int 1)) c).run s =
        (.ok registers, out))
    (hresult : registers.1 = some output) :
    (scan_find_body B output write tz).run s = (.ok output, out) := by
  unfold scan_find_body
  refine concat_bind_success _ _ s s out c output hread ?_
  refine concat_bind_success _ _ s out out registers output hloop ?_
  simp only [hresult, shape_run_pure]

/-- The mixed packed-word branch returns successfully and preserves the allocated
result length for any source whose total population fits the destination. -/
theorem scan_find_body_complete (words : List U64) (slots : List (Option U64))
    (len : I64) (dims : List I64) (tz : U64 → I64)
    (hn : words.length ≤ 9223372036854775807)
    (hm : slots.length ≤ 9223372036854775807) (hp : 0 < words.length)
    (hcapacity : (words.map popcountWord).sum ≤ slots.length) :
    ∃ final : List (Option U64),
      (scan_find_body (⟨0, len, dims⟩ : BitArray 1) 1 scan_findWrite tz).run
          (shiftFreshHeap (initWords words) slots) =
        (.ok 1, shiftFreshHeap (initWords words) final) ∧ final.length = slots.length := by
  have hd : words = words.getD 0 (u64 0) :: words.drop 1 := by
    have h := List.drop_eq_getElem_cons (l := words) (i := 0) hp
    simpa only [List.drop_zero, Nat.zero_add, List.getElem_eq_getD (u64 0)] using h
  have hremaining : scan_find_remaining words 0 (words.getD 0 (u64 0)) =
      (words.map popcountWord).sum := by
    unfold scan_find_remaining
    have hh := congrArg (fun ws : List U64 => (ws.map popcountWord).sum) hd
    simpa only [List.map_cons, List.sum_cons] using hh.symm
  obtain ⟨registers, final, hrun, hresult, hlength⟩ :=
    scan_find_main_complete words slots 0 0 (int 1) (words.getD 0 (u64 0)) dims tz
      hn hm hp (by rw [Nat.zero_add, hremaining]; exact hcapacity)
  refine ⟨final, ?_, hlength⟩
  exact scan_find_body_from (⟨0, len, dims⟩ : BitArray 1) 1 scan_findWrite tz _ _
    (words.getD 0 (u64 0)) registers (shiftFreshSource words slots 0 hn hp) hrun hresult
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- A packed chunk's population is exactly the number of true source bits assigned to it. -/
theorem ctor_find_word_population (xs : List Bool) (chunk : Nat) :
    popcountWord (packedPrefix xs chunk 64) =
      (List.range 64).countP (fun bit => xs.getD (chunk * 64 + bit) false) := by
  unfold popcountWord
  apply List.countP_congr
  intro bit hbit
  change (packedBit (packedPrefix xs chunk 64) bit = true) ↔ _
  rw [packedWord_bit xs chunk bit (List.mem_range.mp hbit)]

/-- Canonical packed storage contains one set bit for each true logical element. -/
theorem ctor_find_population_sum (xs : List Bool) :
    ((encodeBits xs).map popcountWord).sum = countTrue xs := by
  rw [packedPrefix_eq_encode, List.map_map]
  simp only [Function.comp_def, ctor_find_word_population]
  exact packedGrouping_count xs

/-- The logical population never exceeds the source length. -/
theorem ctor_find_count_bound (xs : List Bool) : countTrue xs ≤ xs.length := by
  exact List.count_le_length

/-- Every encoded population sum lies below the logical source length. -/
theorem ctor_find_population_bound (xs : List Bool) :
    ((encodeBits xs).map popcountWord).sum ≤ xs.length := by
  rw [ctor_find_population_sum]
  exact ctor_find_count_bound xs

/-- Loading the first chunk initializes the remaining-population invariant exactly. -/
theorem ctor_find_initial_population (xs : List Bool) (hp : 0 < xs.length) :
    popcountWord ((encodeBits xs).getD 0 (u64 0)) +
      (((encodeBits xs).drop 1).map popcountWord).sum = countTrue xs := by
  have hw : 0 < (encodeBits xs).length := by
    rw [packedEncoded_length]
    unfold wordCount
    omega
  have hd : encodeBits xs = (encodeBits xs).getD 0 (u64 0) :: (encodeBits xs).drop 1 := by
    have h := List.drop_eq_getElem_cons (l := encodeBits xs) (i := 0) hw
    simpa only [List.drop_zero, Nat.zero_add, List.getElem_eq_getD (fallback := u64 0)] using h
  have h := congrArg (fun words : List U64 => (words.map popcountWord).sum) hd
  simp only [List.map_cons, List.sum_cons] at h
  exact h.symm.trans (ctor_find_population_sum xs)
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The mixed branch is the original nested scan with its registers made explicit. -/
theorem scan_find_mixed_from_runs {N : Nat}
    (count : BitArray N → BitMutationM I64) (allocate : I64 → BitMutationM Nat)
    (write : Nat → BitIndex → I64 → BitMutationM Unit)
    (allindices : Nat → BitArray N → BitMutationM Nat)
    (trailingZeros : U64 → I64) (B : BitArray N)
    (nnz : I64) (output : Nat) (s allocated finished : State)
    (hc : (count B).run s = (.ok nnz, s))
    (ha : (allocate nnz).run s = (.ok output, allocated))
    (hz : nnz ≠ int 0) (hn : nnz ≠ B.len)
    (hb : (scan_find_body B output write trailingZeros).run allocated =
      (.ok output, finished)) :
    (bitArrayFindAll count allocate write allindices trailingZeros B).run s =
      (.ok output, finished) := by
  have hzero : (nnz == int 0) = false := beq_eq_false_iff_ne.mpr hz
  have hfull : (nnz == B.len) = false := beq_eq_false_iff_ne.mpr hn
  simp only [bitArrayFindAll, shape_run_bind, hc, ha, hzero, hfull,
    Bool.false_eq_true, ite_false, ite_true]
  unfold scan_find_body scan_find_main scan_find_mainStep scan_find_skip scan_find_skipStep at hb
  simp only [shape_run_bind] at hb
  unfold Break.runK.match_1 scan_find_mainStep.match_3 at *
  exact hb
end JuliaLean.ChatGPT.Batch5.Group2
end

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true

/-- The frozen mixed branch terminates with an output allocation of exactly the
logical population, for every native-sized source and allocatable result. -/
theorem scan_findAll_mixed_result (xs : List Bool)
    (hn : xs.length ≤ 9223372036854775807)
    (ha : countTrue xs ≤ 576460752303423488)
    (hp : 0 < countTrue xs) (hm : countTrue xs ≠ xs.length) :
    ∃ final : List (Option U64),
      (scan_findAllAction xs).run (initWords (encodeBits xs)) =
        (.ok 1, shiftFreshHeap (initWords (encodeBits xs)) final) ∧
      final.length = countTrue xs := by
  have hcount : countTrue xs ≤ 9223372036854775807 := by omega
  have hlen : 0 < xs.length := by have := ctor_find_count_bound xs; omega
  have hwords : 0 < (encodeBits xs).length := by
    rw [packedEncoded_length]
    unfold wordCount
    omega
  obtain ⟨final, hbody, hfinal⟩ := scan_find_body_complete (encodeBits xs)
    (List.replicate (countTrue xs) none) (int xs.length) [int xs.length] trailingZerosWord
    (packedEncoded_lengthBound xs hn)
    (by rw [List.length_replicate]; exact hcount) hwords
    (by rw [ctor_find_population_sum, List.length_replicate]; exact Nat.le_refl _)
  refine ⟨final, ?_, ?_⟩
  · have hzero : int (countTrue xs) ≠ int 0 := by
      intro he
      have hv := congrArg Subtype.val he
      rw [packedInt_val (countTrue xs) hcount] at hv
      change (countTrue xs : Int) = 0 at hv
      omega
    have hfull : int (countTrue xs) ≠ int xs.length := by
      intro he
      have hv := congrArg Subtype.val he
      rw [packedInt_val (countTrue xs) hcount, packedInt_val xs.length hn] at hv
      omega
    unfold scan_findAllAction
    exact scan_find_mixed_from_runs _ _ scan_findWrite _ trailingZerosWord
      (⟨0, int xs.length, [int xs.length]⟩ : BitArray 1) (int (countTrue xs)) 1
      (initWords (encodeBits xs))
      (shiftFreshHeap (initWords (encodeBits xs)) (List.replicate (countTrue xs) none))
      (shiftFreshHeap (initWords (encodeBits xs)) final) rfl
      (shiftFreshAllocate (initWords (encodeBits xs)) (countTrue xs) ha) hzero hfull hbody
  · simpa only [List.length_replicate] using hfinal

/-- The exact frozen observation holds for every native-sized source whose
result fits the model's word-allocation bound, including arbitrary mixed bits. -/
theorem scan_findAll_bounded (xs : List Bool)
    (hn : xs.length ≤ 9223372036854775807)
    (ha : countTrue xs ≤ 576460752303423488) :
    scan_findAllOutcome (countTrue xs)
      ((scan_findAllAction xs).run (initWords (encodeBits xs))) := by
  by_cases hz : countTrue xs = 0
  · exact scan_findAll_zero xs hz
  · by_cases hf : countTrue xs = xs.length
    · exact scan_findAll_full xs hf (by omega)
    · obtain ⟨final, hrun, hlength⟩ := scan_findAll_mixed_result xs hn ha (by omega) hf
      apply scan_findAll_observe_from xs 1 _ hrun
      have hc := shiftFreshContents (initWords (encodeBits xs)) final
        (by rw [hlength]; omega)
      change (shiftFreshHeap (initWords (encodeBits xs)) final).contents 1 = final at hc
      rw [hc, hlength]

/-- A single source-length bound is sufficient for all branches of frozen findall. -/
theorem scan_findAll_length_bounded (xs : List Bool)
    (hn : xs.length ≤ 576460752303423488) :
    scan_findAllOutcome (countTrue xs)
      ((scan_findAllAction xs).run (initWords (encodeBits xs))) :=
  scan_findAll_bounded xs (by omega) (Nat.le_trans (ctor_find_count_bound xs) hn)
end JuliaLean.ChatGPT.Batch5.Group2
end

section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace JuliaLean.ChatGPT.Batch5.Group1

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean.C JuliaLean.base.int

/-- Normalize the explicit constructor to the cast form recognized by arithmetic automation. -/
theorem b5CountConstructorToCast (n : Nat) : Int.ofNat n = (n : Int) := rfl

/-- A wrapping accumulation can be regrouped before its final conversion. -/
theorem b5CountWrapAdd (t : IntTy) (a b : Int) :
    JInt.wrap t ((JInt.wrap t a).val + b) = JInt.wrap t (a + b) := by
  apply Subtype.ext
  exact JuliaLean.Proofs.base.int.wrapInt_add_left t a b

/-- The explicit word population-count callback fits in the native integer. -/
theorem b5CountCallbackValue (word : U64) :
    (int (Int.ofNat (popcountWord word))).val = Int.ofNat (popcountWord word) := by
  change (int (popcountWord word : Int)).val = (popcountWord word : Int)
  apply packedInt_val
  have h : popcountWord word ≤ 64 :=
    Nat.le_trans List.countP_le_length (by simp only [List.length_range, Nat.le_refl])
  omega

/-- Each encoded chunk counts precisely the true bits that it represents. -/
theorem b5CountPackedWord (xs : List Bool) (chunk : Nat) :
    popcountWord (packedPrefix xs chunk 64) =
      (List.range 64).countP (fun bit => xs.getD (chunk * 64 + bit) false) := by
  unfold popcountWord
  apply List.countP_congr
  intro bit hbit
  have h := packedWord_bit xs chunk bit (List.mem_range.mp hbit)
  change (packedPrefix xs chunk 64).val.toNat.testBit bit =
    xs.getD (chunk * 64 + bit) false at h
  rw [h]

/-- The count accumulator covers every modeled signed and unsigned type. -/
theorem b5CountPackedFold (t : IntTy) (xs : List Bool) (indices : List Nat) (acc : Int) :
    indices.foldl (fun (n : JInt t) chunk =>
      JInt.wrap t (n.val + (int (Int.ofNat (popcountWord (packedPrefix xs chunk 64)))).val))
        (JInt.wrap t acc) =
      JInt.wrap t (acc + Int.ofNat ((indices.map (fun chunk =>
        (List.range 64).countP (fun bit => xs.getD (chunk * 64 + bit) false))).sum)) := by
  induction indices generalizing acc with
  | nil =>
      change JInt.wrap t acc = JInt.wrap t (acc + 0)
      rw [Int.add_zero]
  | cons chunk indices ih =>
      rw [List.foldl_cons, b5CountCallbackValue, b5CountPackedWord, b5CountWrapAdd, ih,
        List.map_cons, List.sum_cons]
      congr 1
      simp only [b5CountConstructorToCast]
      omega

/-- Exact count and complete state preservation when the physical chunk count fits. -/
theorem b5CountNativeChunks (t : IntTy) (xs : List Bool) (init : JInt t)
    (hchunks : (encodeBits xs).length ≤ (IntTy.max .i64).toNat) :
    (bitcount (fun n : JInt t => fun c : I64 => JInt.wrap t (n.val + c.val))
      id (fun word : U64 => int (Int.ofNat (popcountWord word))) init 0).run
        (initWords (encodeBits xs)) =
      (.ok (JInt.wrap t (init.val + Int.ofNat (countTrue xs))), initWords (encodeBits xs)) := by
  rw [bcLoop_bitcount_run _ _ _ _ _ hchunks]
  have hi : JInt.wrap t init.val = init := by
    apply Subtype.ext
    exact JuliaLean.Proofs.base.int.wrapInt_val init
  have hfold :
      (encodeBits xs).foldl (fun n : JInt t => fun word =>
        JInt.wrap t (n.val + (int (Int.ofNat (popcountWord word))).val)) init =
      JInt.wrap t (init.val + Int.ofNat (countTrue xs)) := by
    rw [packedPrefix_eq_encode, List.foldl_map]
    have hf := b5CountPackedFold t xs (List.range (wordCount xs.length)) init.val
    rw [hi] at hf
    have hc := packedGrouping_count xs
    change ((List.range (wordCount xs.length)).map (fun chunk =>
      (List.range 64).countP (fun bit => xs.getD (chunk * 64 + bit) false))).sum = countTrue xs at hc
    rw [hc] at hf
    exact hf
  change (Except.ok ((encodeBits xs).foldl (fun n : JInt t => fun word =>
    JInt.wrap t (n.val + (int (Int.ofNat (popcountWord word))).val)) init),
    initWords (encodeBits xs)) = _
  rw [hfold]

/-- Native-length inputs return the exact typed count and leave the complete state unchanged. -/
theorem b5CountNativeLength (t : IntTy) (xs : List Bool) (init : JInt t)
    (hn : xs.length ≤ (IntTy.max .i64).toNat) :
    (bitcount (fun n : JInt t => fun c : I64 => JInt.wrap t (n.val + c.val))
      id (fun word : U64 => int (Int.ofNat (popcountWord word))) init
      (vectorBits xs).chunks).run (initWords (encodeBits xs)) =
      (.ok (JInt.wrap t (init.val + Int.ofNat (countTrue xs))), initWords (encodeBits xs)) := by
  exact b5CountNativeChunks t xs init (packedEncoded_lengthBound xs hn)

/-- All four frozen search observations hold outside the logical range, in any state. -/
theorem b5FindBoundary (xs : List Bool) (start : I64) (s : State)
    (houtside : start ≤ int 0 ∨ start > int xs.length) :
    (bitArrayFindNext id (unsafeBitFindNext trailingZerosWord)
      (vectorBits xs) start).run s = (findForwardSpec xs start true, s) ∧
    (bitArrayFindNextNot trailingOnesWord (vectorBits xs) start).run s =
      (findForwardSpec xs start false, s) ∧
    (bitArrayFindPrev id (unsafeBitFindPrev topSetBitWord)
      (vectorBits xs) start).run s = (findBackwardSpec xs start true, s) ∧
    (bitArrayFindPrevNot leadingOnesWord (vectorBits xs) start).run s =
      (findBackwardSpec xs start false, s) := by
  by_cases hi : start ≤ int 0
  · simp only [bitArrayFindNext, bitArrayFindNextNot, bitArrayFindPrev,
      bitArrayFindPrevNot, findForwardSpec, findBackwardSpec, id_eq, hi, ite_true]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · have he := houtside.resolve_left hi
    simp only [bitArrayFindNext, bitArrayFindNextNot, bitArrayFindPrev,
      bitArrayFindPrevNot, findForwardSpec, findBackwardSpec, vectorBits,
      b5CountConstructorToCast, id_eq, hi, he, ite_false, ite_true]
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The full search contract on an empty input follows from its boundary checks. -/
theorem b5FindEmpty (start : I64) (s : State) :
    (bitArrayFindNext id (unsafeBitFindNext trailingZerosWord)
      (vectorBits []) start).run s = (findForwardSpec [] start true, s) ∧
    (bitArrayFindNextNot trailingOnesWord (vectorBits []) start).run s =
      (findForwardSpec [] start false, s) ∧
    (bitArrayFindPrev id (unsafeBitFindPrev topSetBitWord)
      (vectorBits []) start).run s = (findBackwardSpec [] start true, s) ∧
    (bitArrayFindPrevNot leadingOnesWord (vectorBits []) start).run s =
      (findBackwardSpec [] start false, s) := by
  apply b5FindBoundary
  change start.val ≤ 0 ∨ 0 < start.val
  omega
end JuliaLean.ChatGPT.Batch5.Group1
end



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch5.Group4

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2
open JuliaLean.Proofs.base.bitarray.Archive20261102Round6

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- Lifting a successful pure array result preserves the mutation heap. -/
theorem mtx_lift_pure {α : Type} (x : α) :
    liftArray (pure x) = (pure x : BitMutationM α) := rfl

/-- A successful result binds directly in the pure array error monad. -/
theorem mtx_result_ok_bind {α β : Type} (x : α)
    (next : α → JuliaLean.base.abstractarray.Result β) :
    ((Except.ok x : JuliaLean.base.abstractarray.Result α) >>= next) = next x := rfl

/-- Pure array computations use the ordinary successful-result constructor. -/
theorem mtx_result_pure {α : Type} (x : α) :
    (pure x : JuliaLean.base.abstractarray.Result α) = Except.ok x := rfl

/-- The installed native-axis length conversion preserves its endpoint. -/
theorem mtx_axis_length (n : I64) :
    axisLength (JuliaLean.base.range.unchecked_oneto n) = .ok n := by
  simp only [axisLength, JuliaLean.base.range.length_OneTo_smallints,
    JuliaLean.Proofs.base.range.ctor_iv]
  change rangeArray (JuliaLean.base.range.JConvert.convert n) = .ok n
  rw [JuliaLean.Proofs.base.range.convert_wide n ⟨Int.le_refl _, Int.le_refl _⟩]
  rfl

/-- Matrix Cartesian checks accept the two interior native coordinates. -/
theorem mtx_check_coordinates (s : State) (B : BitMatrix) (rows columns i j : I64)
    (hd : B.dims = [rows, columns])
    (hi : 1 ≤ i.val ∧ i.val ≤ rows.val)
    (hj : 1 ≤ j.val ∧ j.val ≤ columns.val) :
    (matrixCheck B [i, j]).run s = (.ok (), s) := by
  have hr : 0 ≤ rows.val := by omega
  have hc : 0 ≤ columns.val := by omega
  have hir : JuliaLean.base.abstractarray.checkindexOneTo rows i = true := by
    rw [JuliaLean.Proofs.base.range.checkindexOneTo_iff rows i hr]
    exact decide_eq_true hi
  have hjc : JuliaLean.base.abstractarray.checkindexOneTo columns j = true := by
    rw [JuliaLean.Proofs.base.range.checkindexOneTo_iff columns j hc]
    exact decide_eq_true hj
  simp only [matrixCheck, JuliaLean.base.abstractarray.checkboundsMany,
    matrixAxes, JuliaLean.base.abstractarray.axesDefault, bitArraySize, hd,
    pure_bind, List.map_cons, List.map_nil,
    checkCoordinates, JuliaLean.base.abstractarray.checkboundsIndicesCons,
    List.headD_cons, List.tail_cons, JuliaLean.base.range.unchecked_oneto,
    hir, hjc, ite_true, JuliaLean.base.abstractarray.checkboundsIndicesNil,
    JuliaLean.base.abstractarray.allTupleM, mtx_result_pure, mtx_result_ok_bind,
    liftArray, Bool.not_true, Bool.false_eq_true, ite_false,
    shape_run_bind, shape_run_pure]
  all_goals rfl

/-- The Cartesian-to-linear dispatch performs the source's native arithmetic. -/
theorem mtx_linear_coordinates (s : State) (B : BitMatrix) (rows columns i j : I64)
    (hd : B.dims = [rows, columns]) :
    (matrixLinear B [i, j]).run s =
      (.ok (add_int (add_int (int 1) (mul_int (sub_int i (int 1)) (int 1)))
        (mul_int (sub_int j (int 1)) (mul_int (int 1) rows))), s) := by
  have hhead (x : Axis) (xs : List Axis) :
      JuliaLean.base.abstractarray.tupleGet (x :: xs) (int 1) = .ok x := by
    rfl
  simp only [matrixLinear, JuliaLean.base.abstractarray.toLinearMany,
    JuliaLean.base.abstractarray.sub2indArray, matrixAxes,
    JuliaLean.base.abstractarray.axesDefault, bitArraySize, hd,
    pure_bind, List.map_cons, List.map_nil, JuliaLean.base.abstractarray.sub2indAxes,
    linearCoordinates, JuliaLean.base.abstractarray.sub2indRecurse,
    hhead, List.tail_cons,
    JuliaLean.base.abstractarray.nextLRange, mtx_axis_length,
    JuliaLean.base.abstractarray.offsetinRange, JuliaLean.base.range.first_OneTo,
    JuliaLean.base.abstractarray.sub2indRecurseDone,
    mtx_result_pure, mtx_result_ok_bind, liftArray, shape_run_pure]
  all_goals rfl

/-- Native multiplication of representable naturals retains modular arithmetic. -/
theorem mtx_mul_nat (a b : Nat) (ha : a ≤ 9223372036854775807)
    (hb : b ≤ 9223372036854775807) :
    mul_int (int a) (int b) = int ((a * b : Nat) : Int) := by
  apply Subtype.ext
  rw [JuliaLean.Proofs.base.int.mul_int_val, packedInt_val a ha, packedInt_val b hb]
  rfl

/-- Native addition of representable naturals retains modular arithmetic. -/
theorem mtx_add_nat (a b : Nat) (ha : a ≤ 9223372036854775807)
    (hb : b ≤ 9223372036854775807) :
    add_int (int a) (int b) = int ((a + b : Nat) : Int) := by
  apply Subtype.ext
  rw [JuliaLean.Proofs.base.int.add_int_val, packedInt_val a ha, packedInt_val b hb]
  rfl

/-- Subtracting one from an interior one-based coordinate gives its exact
zero-based natural coordinate. -/
theorem mtx_sub_one (k : Nat) (hk : k + 1 ≤ 9223372036854775807) :
    sub_int (int ((k + 1 : Nat) : Int)) (int 1) = int k := by
  apply Subtype.ext
  rw [JuliaLean.Proofs.base.int.sub_int_val, packedInt_val (k + 1) hk]
  change wrapInt .i64 ((k + 1 : Nat) - (1 : Int)) = wrapInt .i64 (k : Int)
  congr 1
  omega

/-- A diagonal's zero-based linear coordinate lies inside the square. -/
theorem mtx_diagonal_bound (n k : Nat) (hk : k < n) : k * n + k < n * n := by
  have hmul := Nat.mul_le_mul_right n (by omega : k + 1 ≤ n)
  rw [Nat.add_mul, Nat.one_mul] at hmul
  omega

/-- The complete coordinate dispatch addresses the expected diagonal bit. -/
theorem mtx_linear_diagonal (s : State) (B : BitMatrix) (n k : Nat)
    (hn : n ≤ 9223372036854775807) (hp : n * n ≤ 9223372036854775807)
    (hk : k < n) (hd : B.dims = [int n, int n]) :
    (matrixLinear B [int ((k + 1 : Nat) : Int), int ((k + 1 : Nat) : Int)]).run s =
      (.ok (int ((k * n + k + 1 : Nat) : Int)), s) := by
  have hb := mtx_diagonal_bound n k hk
  have hmulright : mul_int (int k) (int 1) = int k := by
    simpa only [Int.natCast_one, Nat.mul_one] using
      mtx_mul_nat k 1 (by omega) (by decide)
  have hmulleft : mul_int (int 1) (int n) = int n := by
    simpa only [Int.natCast_one, Nat.one_mul] using
      mtx_mul_nat 1 n (by decide) hn
  have haddone : add_int (int 1) (int k) = int ((1 + k : Nat) : Int) := by
    simpa only [Int.natCast_one] using mtx_add_nat 1 k (by decide) (by omega)
  rw [mtx_linear_coordinates s B (int n) (int n) _ _ hd,
    mtx_sub_one k (by omega), hmulright, hmulleft, haddone,
    mtx_mul_nat k n (by omega) hn,
    mtx_add_nat (1 + k) (k * n) (by omega) (by omega)]
  congr 3
  omega

/-- The actual public scalar check accepts every interior linear coordinate. -/
theorem mtx_scalar_bounds (s : State) (B : BitMatrix) (i : I64)
    (hi : 1 ≤ i.val ∧ i.val ≤ B.len.val) :
    (scalarBounds B i).run s = (.ok (), s) := by
  have hn : 0 ≤ B.len.val := by omega
  have ho : JuliaLean.base.range.oneto B.len =
      .ok (JuliaLean.base.range.unchecked_oneto B.len) := by
    change JuliaLean.base.range.JOneTo1.oneTo B.len = _
    rw [JuliaLean.Proofs.base.range.oneTo_ok]
    simp only [JuliaLean.Proofs.base.range.oneToStop, show ¬ B.len.val < 0 by omega, ite_false]
    rfl
  have hc : JuliaLean.base.abstractarray.checkindexOneTo B.len i = true := by
    rw [JuliaLean.Proofs.base.range.checkindexOneTo_iff B.len i hn]
    exact decide_eq_true hi
  simp only [scalarBounds, JuliaLean.base.abstractarray.checkboundsOne,
    JuliaLean.base.abstractarray.eachindexLinear, bitArrayLength, pure_bind,
    ho, rangeArray, Except.mapError, JuliaLean.base.range.unchecked_oneto,
    hc, mtx_result_pure, mtx_result_ok_bind, liftArray, Bool.not_true,
    Bool.false_eq_true, ite_false, shape_run_bind, shape_run_pure]
  all_goals rfl

/-- The public Cartesian setter composes its checks and its single packed write. -/
theorem mtx_set_from (s out : State) (B : BitMatrix) (value : Bool)
    (is : List I64) (index : I64)
    (hcheck : (matrixCheck B is).run s = (.ok (), s))
    (hlinear : (matrixLinear B is).run s = (.ok index, s))
    (hscalar : (scalarBounds B index).run s = (.ok (), s))
    (hwrite : (unsafeBitSetIndex B.chunks value index).run s = (.ok (), out)) :
    (matrixSet B value is).run s = (.ok B, out) := by
  simp only [matrixSet, JuliaLean.base.abstractarray.setindexArray,
    JuliaLean.base.abstractarray.errorCanonicalSetindexOther, mtx_lift_pure,
    JuliaLean.base.indices.to_indices_A_Ints, pure_bind,
    JuliaLean.base.abstractarray.setindexLinear]
  erw [mtx_run_bind_ok hcheck, mtx_run_bind_ok hlinear]
  simp only [bitArraySetIndex, JuliaLean.base.number.convertSame, pure_bind]
  erw [mtx_run_bind_ok hscalar, mtx_run_bind_ok hwrite]
  rfl

/-- Writing an encoded logical bit in newly allocated storage changes just the
corresponding encoded list element and preserves the complete earlier heap. -/
theorem mtx_write_fresh (s : State) (xs : List Bool) (i : Nat) (value : Bool)
    (hn : xs.length ≤ 9223372036854775807) (hi : i < xs.length) :
    (unsafeBitSetIndex s.arrays.length value (int ((i + 1 : Nat) : Int))).run
      (shiftFreshHeap s ((encodeBits xs).map some)) =
        (.ok (), shiftFreshHeap s ((encodeBits (xs.set i value)).map some)) := by
  have hw : (encodeBits xs).length ≤ 9223372036854775807 :=
    packedEncoded_lengthBound xs hn
  have hc : i / 64 < (encodeBits xs).length := by
    rw [packedEncoded_length]
    unfold wordCount
    omega
  have hm : ((encodeBits xs).map some)[i / 64]? = some (some (encodeBits xs)[i / 64]) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hc]
    rfl
  have hread := shiftFreshRead s ((encodeBits xs).map some) (i / 64) (encodeBits xs)[i / 64]
    (by simpa only [List.length_map] using hw) (by simpa only [List.length_map] using hc) hm
  apply scalar_internal_write_run _ _ s.arrays.length
    (int ((i + 1 : Nat) : Int)) (int ((i / 64 + 1 : Nat) : Int))
    (int ((i % 64 : Nat) : Int)) (encodeBits xs)[i / 64] value
    (scalar_chunks_nat i (by omega)) hread
  rw [shiftFreshSet s ((encodeBits xs).map some) (i / 64) _
    (by simpa only [List.length_map] using hw) (by simpa only [List.length_map] using hc)]
  rw [← List.map_set, scalar_encode_set xs i value hi]
  simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range,
    scalar_set_word]

/-- One complete public diagonal assignment updates the expected logical bit. -/
theorem mtx_set_diagonal (s : State) (xs : List Bool) (B : BitMatrix) (n k : Nat)
    (hn : n ≤ 9223372036854775807) (hp : n * n ≤ 9223372036854775807)
    (hk : k < n) (hlen : xs.length = n * n)
    (hb : B.chunks = s.arrays.length)
    (hd : B.dims = [int n, int n]) (hl : B.len = int ((n * n : Nat) : Int)) :
    (matrixSet B true [int ((k + 1 : Nat) : Int), int ((k + 1 : Nat) : Int)]).run
      (shiftFreshHeap s ((encodeBits xs).map some)) =
        (.ok B, shiftFreshHeap s ((encodeBits (xs.set (k * n + k) true)).map some)) := by
  have hbound := mtx_diagonal_bound n k hk
  have hcoord : 1 ≤ (int ((k + 1 : Nat) : Int)).val ∧
      (int ((k + 1 : Nat) : Int)).val ≤ (int n).val := by
    rw [packedInt_val (k + 1) (by omega), packedInt_val n hn]
    omega
  apply mtx_set_from _ _ B true _ (int ((k * n + k + 1 : Nat) : Int))
  · exact mtx_check_coordinates _ B (int n) (int n) _ _ hd hcoord hcoord
  · exact mtx_linear_diagonal _ B n k hn hp hk hd
  · apply mtx_scalar_bounds
    rw [hl, packedInt_val (n * n) hp, packedInt_val (k * n + k + 1) (by omega)]
    omega
  · rw [hb]
    exact mtx_write_fresh s xs (k * n + k) true (by rw [hlen]; exact hp) (by rw [hlen]; exact hbound)

/-- The fresh matrix header used throughout the diagonal loop. -/
def mtx_matrix (s : State) (n : Nat) : BitMatrix :=
  ⟨s.arrays.length, int ((n * n : Nat) : Int), [int n, int n]⟩

/-- The diagonal coordinate occurs exactly when row and column agree. -/
theorem mtx_mem_diagonal (n j : Nat) (hj : j < n * n) :
    j ∈ (List.range n).map (fun k => k * n + k) ↔ j % n = j / n := by
  have hn : 0 < n := by
    by_cases h : n = 0
    · subst n; omega
    · omega
  constructor
  · intro hm
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
    have hkn := List.mem_range.mp hk
    have hmod : (k * n + k) % n = k := Nat.mul_add_mod_of_lt hkn
    have hdiv : (k * n + k) / n = k := by
      rw [Nat.mul_comm k n, Nat.mul_add_div hn, Nat.div_eq_of_lt hkn, Nat.add_zero]
    rw [hmod, hdiv]
  · intro hd
    have hq : j / n < n := (Nat.div_lt_iff_lt_mul hn).mpr hj
    refine List.mem_map.mpr ⟨j / n, List.mem_range.mpr hq, ?_⟩
    have he := Nat.div_add_mod' j n
    rw [hd] at he
    exact he

/-- The diagonal write fold produces the independent row/column specification. -/
theorem mtx_diagonal_fold (n : Nat) :
    (List.range n).foldl (fun xs k => xs.set (k * n + k) true)
      (List.replicate (n * n) false) =
        (List.range (n * n)).map (fun j => j % n == j / n) := by
  have hfold :
      (List.range n).foldl (fun xs k => xs.set (k * n + k) true)
        (List.replicate (n * n) false) =
      ((List.range n).map (fun k => k * n + k)).foldl (fun xs k => xs.set k true)
        (List.replicate (n * n) false) := by rw [List.foldl_map]
  rw [hfold]
  apply List.ext_getElem
  · rw [mtx_fillfold_length]
    simp only [List.length_replicate, List.length_map, List.length_range]
  · intro j hj hj'
    have hjn : j < n * n := by
      rw [mtx_fillfold_length, List.length_replicate] at hj
      exact hj
    rw [List.getElem_eq_getD (fallback := false),
      mtx_fillfold_get ((List.range n).map (fun k => k * n + k)) true false
        (List.replicate (n * n) false) (by
          intro k hk
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
          rw [List.length_replicate]
          exact mtx_diagonal_bound n i (List.mem_range.mp hi)) j,
      List.getElem_map, List.getElem_range, fillReplicateGet, if_pos hjn]
    by_cases hd : j % n = j / n
    · rw [if_pos ((mtx_mem_diagonal n j hjn).mpr hd)]
      exact (beq_iff_eq.mpr hd).symm
    · rw [if_neg (fun hm => hd ((mtx_mem_diagonal n j hjn).mp hm))]
      exact (beq_eq_false_iff_ne.mpr hd).symm

/-- Transport a sequence of successful assignments to its logical state fold. -/
theorem mtx_forIn_results {ι σ α : Type} (action : ι → BitMutationM α) (value : α)
    (step : σ → ι → σ) (store : σ → State) (P : σ → Prop) (indices : List ι)
    (hrun : ∀ w, P w → ∀ i ∈ indices,
      (action i).run (store w) = (.ok value, store (step w i)))
    (hpres : ∀ w, P w → ∀ i ∈ indices, P (step w i)) (w : σ) (hw : P w) :
    (forIn indices PUnit.unit (fun i _ => do
      let _ ← action i
      pure (ForInStep.yield PUnit.unit))).run (store w) =
        (.ok PUnit.unit, store (indices.foldl step w)) := by
  have hf := dequeForInFold (fun i => do let _ ← action i; pure ()) step store P indices
    (by
      intro w hw i hi
      rw [mtx_run_bind_ok (hrun w hw i hi)]
      rfl) hpres w hw
  simpa only [bind_assoc, pure_bind] using hf

/-- Execute every public Cartesian diagonal assignment on the fresh square. -/
theorem mtx_diagonal_loop (s : State) (n : Nat)
    (hn : n ≤ 9223372036854775807) (hp : n * n ≤ 9223372036854775807) :
    (forIn (intRange (int 1) (int n)) PUnit.unit (fun i _ => do
      let _ ← matrixSet (mtx_matrix s n) true [i, i]
      pure (ForInStep.yield PUnit.unit))).run
      (shiftFreshHeap s ((encodeBits (List.replicate (n * n) false)).map some)) =
        (.ok PUnit.unit, shiftFreshHeap s
          ((encodeBits ((List.range (n * n)).map (fun j => j % n == j / n))).map some)) := by
  have hf := mtx_forIn_results
    (fun k => matrixSet (mtx_matrix s n) true
      [int ((k + 1 : Nat) : Int), int ((k + 1 : Nat) : Int)]) (mtx_matrix s n)
    (fun xs k => xs.set (k * n + k) true)
    (fun xs => shiftFreshHeap s ((encodeBits xs).map some))
    (fun xs => xs.length = n * n) (List.range n)
    (by
      intro xs hx k hk
      exact mtx_set_diagonal s xs (mtx_matrix s n) n k hn hp
        (List.mem_range.mp hk) hx rfl rfl rfl)
    (by intro xs hx k hk; rw [List.length_set]; exact hx)
    (List.replicate (n * n) false) (List.length_replicate ..)
  rw [packedObserve_intRange n hn, List.forIn_map]
  rw [mtx_diagonal_fold n] at hf
  exact hf
end JuliaLean.ChatGPT.Batch5.Group4



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray
namespace Models1Group16

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray

/-- Counting with a machine-integer init adds the number of logical true bits
modulo that type's bit width. Inputs include every width and every initializer,
all ranks, and readable alias states; the chunk heap is unchanged.
Julia source: base/bitarray.jl:1448-1456.
Documentation: base/reduce.jl:1067-1090; bit-array logical-element invariant.
Only the explicitly represented BitInteger init specialization is claimed. -/
def CountMachineResidue : Prop :=
  ∀ (N : Nat) (t : IntTy) (s : Heap) (B : BitArray N) (init : JInt t),
    Readable s B →
    let result := (JuliaLean.base.bitarray.Models1Group16.countMachine B init).run s
    result.2 = s ∧
    match result.1 with
    | .ok n =>
        (n.val - init.val - ((bits s B).count true : Int)) % (2 : Int)^t.bits = 0
    | .error _ => False


/-- Mathematical ordered matching positions, independent of the chunk scans. -/
def matchingPositions {N : Nat} (s : Heap) (B : BitArray N) (wanted : Bool) : List Nat :=
  ((List.range B.len.val.toNat).filter fun i => bitAt s B i == wanted).map (· + 1)

def nextPosition {N : Nat} (s : Heap) (B : BitArray N) (start : Int) (wanted : Bool) :
    Option I64 :=
  ((matchingPositions s B wanted).find? fun (i : Nat) => decide (start ≤ (i : Int))).map
    (fun i => int (i : Int))

def prevPosition {N : Nat} (s : Heap) (B : BitArray N) (start : Int) (wanted : Bool) :
    Option I64 :=
  ((matchingPositions s B wanted).reverse.find? fun (i : Nat) => decide ((i : Int) ≤ start)).map
    (fun i => int (i : Int))

/-- Forward search includes its start, returns the first true position, and has
the documented directional bounds behavior. All machine widths and values are
included; conversion failure precedes bounds checking. Readable alias states
are included, so tail bits outside the logical array cannot be silently assumed
away. Julia source: base/bitarray.jl:1478-1483.
Documentation: base/array.jl:2368-2376. -/
def FindNextMachineContract : Prop :=
  ∀ (N : Nat) (t : IntTy) (s : Heap) (B : BitArray N) (start : JInt t),
    Readable s B →
    let result := (JuliaLean.base.bitarray.Models1Group16.findNextMachine B start).run s
    result.2 = s ∧
    if ¬ FitsNative start.val then result.1 = .error .inexact
    else if start.val ≤ 0 then result.1 = .error .bounds
    else result.1 = .ok (nextPosition s B start.val true)

/-- == and isequal Fix2 with a Bool payload search for that logical value,
including false. All machine-Integer starts and their failures are included.
Julia source: base/bitarray.jl:1520-1526.
Documentation: base/array.jl:2368-2376 and the predicate search docstrings. -/
def FindNextFixedMachineContract : Prop :=
  ∀ (N : Nat) (t : IntTy) (s : Heap) (B : BitArray N) (start : JInt t) (wanted : Bool),
    Readable s B →
    let result := (JuliaLean.base.bitarray.Models1Group16.findNextFixedMachine wanted B start).run s
    result.2 = s ∧
    if ¬ FitsNative start.val then result.1 = .error .inexact
    else if start.val ≤ 0 then result.1 = .error .bounds
    else result.1 = .ok (nextPosition s B start.val wanted)

/-- Backward search returns the last true position no greater than start.
Nonpositive native starts return nothing; an upper out-of-bounds native start
throws. Julia source: base/bitarray.jl:1563-1568.
Documentation: base/array.jl:2553-2563. -/
def FindPrevMachineContract : Prop :=
  ∀ (N : Nat) (t : IntTy) (s : Heap) (B : BitArray N) (start : JInt t),
    Readable s B →
    let result := (JuliaLean.base.bitarray.Models1Group16.findPrevMachine B start).run s
    result.2 = s ∧
    if ¬ FitsNative start.val then result.1 = .error .inexact
    else if B.len.val < start.val then result.1 = .error .bounds
    else result.1 = .ok (prevPosition s B start.val true)

/-- Backward Bool Fix2 search has the same full machine-start domain and preserves
the entire heap. Julia source: base/bitarray.jl:1596-1602.
Documentation: base/array.jl:2553-2563 and predicate search docstrings. -/
def FindPrevFixedMachineContract : Prop :=
  ∀ (N : Nat) (t : IntTy) (s : Heap) (B : BitArray N) (start : JInt t) (wanted : Bool),
    Readable s B →
    let result := (JuliaLean.base.bitarray.Models1Group16.findPrevFixedMachine wanted B start).run s
    result.2 = s ∧
    if ¬ FitsNative start.val then result.1 = .error .inexact
    else if B.len.val < start.val then result.1 = .error .bounds
    else result.1 = .ok (prevPosition s B start.val wanted)


/-- Independent first-extremum relation over logical values, not a scan or
comparison with another model. `greatest=true` selects the maximum relation. -/
def FirstVectorExtreme (s : Heap) (A : BitVector) (greatest : Bool)
    (value : Bool) (index : I64) : Prop :=
  1 ≤ index.val ∧ index.val ≤ A.len.val ∧
  bitAt s A (index.val - 1).toNat = value ∧
  (∀ j : Nat, j < A.len.val.toNat →
    if greatest then
      (if bitAt s A j then 1 else 0 : Nat) ≤ (if value then 1 else 0)
    else
      (if value then 1 else 0 : Nat) ≤ (if bitAt s A j then 1 else 0)) ∧
  (∀ j : Nat, j < (index.val - 1).toNat → bitAt s A j ≠ value)

/-- findmax on a BitVector returns its largest Boolean and the first native
index attaining it, rejects empty input with ArgumentError, and leaves all
memory and aliases unchanged. Native lengths and physical sizes are enforced by
Readable; dirty padding and extra aliased chunks are not discarded.
Julia source: base/bitarray.jl:1620-1631.
Documentation: base/reduce.jl:859-881; base/abstractarray.jl:145-170.
Only the explicitly represented BitVector specialization is claimed. -/
def FindMaxVectorContract : Prop :=
  ∀ (s : Heap) (A : BitVector), Readable s A →
    let result := (JuliaLean.base.bitarray.Models1Group16.findMaxVector A).run s
    result.2 = s ∧
    if A.len.val = 0 then
      result.1 = .error (.argument "BitArray must be non-empty")
    else match result.1 with
      | .ok (value, index) => FirstVectorExtreme s A true value index
      | .error _ => False

/-- findmin on a BitVector returns its smallest Boolean and its first native
index, with the same full represented input domain and empty-array error.
Julia source: base/bitarray.jl:1633-1648.
Documentation: base/reduce.jl:925-948; base/abstractarray.jl:145-170. -/
def FindMinVectorContract : Prop :=
  ∀ (s : Heap) (A : BitVector), Readable s A →
    let result := (JuliaLean.base.bitarray.Models1Group16.findMinVector A).run s
    result.2 = s ∧
    if A.len.val = 0 then
      result.1 = .error (.argument "BitArray must be non-empty")
    else match result.1 with
      | .ok (value, index) => FirstVectorExtreme s A false value index
      | .error _ => False
end Models1Group16
end JuliaLean.Proofs.base.bitarray



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group10

open JuliaLean

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def searchLastMatch (p : Nat → Bool) (n : Nat) : Option Nat :=
  (List.range n).reverse.find? p

theorem searchLastMatchSucc (p : Nat → Bool) (n : Nat) :
    searchLastMatch p (n + 1) = if p n then some n else searchLastMatch p n := by
  simp only [searchLastMatch, List.range_succ, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.find?_cons]
  cases p n <;> rfl

theorem searchLastMatchSome (p : Nat → Bool) (n i : Nat) (hi : i < n)
    (hp : p i = true) (hn : ∀ j, i < j → j < n → p j = false) :
    searchLastMatch p n = some i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [searchLastMatchSucc]
    by_cases he : i = n
    · subst i
      simp only [hp, ite_true]
    · have hni : i < n := by omega
      have hz : p n = false := hn n (by omega) (by omega)
      simp only [hz, Bool.false_eq_true, ite_false]
      exact ih hni (fun j hij hjn => hn j hij (by omega))

theorem searchLastMatchCongr (p q : Nat → Bool) (n : Nat)
    (h : ∀ i, i < n → p i = q i) : searchLastMatch p n = searchLastMatch q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [searchLastMatchSucc, searchLastMatchSucc, h n (by omega),
      ih (fun i hi => h i (by omega))]

theorem searchLastMatchAddFalse (p : Nat → Bool) (n m : Nat)
    (h : ∀ i, n ≤ i → i < n + m → p i = false) :
    searchLastMatch p (n + m) = searchLastMatch p n := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.add_succ, searchLastMatchSucc]
    have hz : p (n + m) = false := h (n + m) (by omega) (by omega)
    simp only [hz, Bool.false_eq_true, ite_false]
    exact ih (fun i hi hib => h i hi (by omega))

theorem searchLastMatchTruncate (p : Nat → Bool) (n m : Nat) (hn : n ≤ m) :
    searchLastMatch (fun i => p i && decide (i < n)) m = searchLastMatch p n := by
  have he : m = n + (m - n) := by omega
  rw [he]
  rw [searchLastMatchAddFalse _ n (m - n) (by
    intro i hi _
    have hz : ¬ i < n := by omega
    simp only [decide_eq_false hz, Bool.and_false])]
  apply searchLastMatchCongr
  intro i hi
  simp only [decide_eq_true hi, Bool.and_true]
end JuliaLean.ChatGPT.Batch9.Group10



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group10

open JuliaLean

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

open JuliaLean.base.int JuliaLean.Proofs.base.int

theorem searchTopSetBitSpec (word : JInt .u64) :
    let r := (top_set_bit word).val.toNat
    r ≤ 64 ∧
    (word ≠ JInt.lit .u64 0 → 0 < r) ∧
    (0 < r → bitOf word (r - 1) = true) ∧
    (∀ j, r ≤ j → bitOf word j = false) := by
  obtain ⟨hn, hu, hp, hl⟩ := topSetBit_proven .u64 word
  change 0 ≤ (top_set_bit word).val at hn
  change (top_set_bit word).val ≤ 64 at hu
  dsimp only
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro hword
    by_cases hz : 0 < (top_set_bit word).val.toNat
    · exact hz
    exfalso
    have hr : (top_set_bit word).val.toNat = 0 := by omega
    rw [hr] at hp
    have hpattern : pattern word = 0 := by omega
    have hpat := pattern_of_unsigned (u := .u64) rfl word
    have hw := word.property.1
    change 0 ≤ word.val at hw
    apply hword
    apply Subtype.ext
    change word.val = 0
    omega
  · intro hr
    rw [bitOf_eq]
    apply Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt
    · exact hl (by omega)
    · have he : (top_set_bit word).val.toNat - 1 + 1 = (top_set_bit word).val.toNat := by omega
      rw [he]
      exact hp
  · intro j hj
    rw [bitOf_eq]
    apply Nat.testBit_lt_two_pow
    exact Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by decide) hj)
end JuliaLean.ChatGPT.Batch9.Group10



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group10

open JuliaLean

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

open JuliaLean.base.int JuliaLean.Proofs.base.int

open JuliaLean.base.array JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray.Models1Group16

theorem searchPrevPositionAsLast {N : Nat} (s : MutableMemory U64) (B : BitArray N)
    (start : Int) (wanted : Bool) (hstart : 0 ≤ start) (hbound : start ≤ B.len.val) :
    prevPosition s B start wanted =
      (searchLastMatch (fun i => bitAt s B i == wanted) start.toNat).map
        (fun i => int ((i + 1 : Nat) : Int)) := by
  unfold prevPosition matchingPositions
  have hcast (position : Option Nat) :
      Option.map (fun i : Int => int i) (do
        let i ← position
        pure (i : Int)) =
      position.map (fun i : Nat => int (i : Int)) := by
    cases position <;> rfl
  rw [hcast]
  rw [← List.map_reverse, List.find?_map, Option.map_map, ← List.filter_reverse,
    List.find?_filter]
  have hpred (i : Nat) : decide (((i + 1 : Nat) : Int) ≤ start) =
      decide (i < start.toNat) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  simp only [Function.comp_def, Bool.decide_and, Bool.decide_coe, hpred]
  change (searchLastMatch (fun i => (bitAt s B i == wanted) && decide (i < start.toNat))
      B.len.val.toNat).map (fun i => int ((i + 1 : Nat) : Int)) = _
  rw [searchLastMatchTruncate _ start.toNat B.len.val.toNat (by omega)]
end JuliaLean.ChatGPT.Batch9.Group10



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group10

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray
open JuliaLean.base.bitarray.Models1Group16
open JuliaLean.Proofs.base.bitarray.Models1Group16

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem searchRunBind {α β : Type} (act : BitMutationM α) (next : α → BitMutationM β)
    (s : MutableMemory U64) :
    ((act >>= next).run s) =
      match act.run s with
      | (.ok value, after) => (next value).run after
      | (.error error, after) => (.error error, after) := by
  simp only [ExceptT.run, ExceptT.bind, ExceptT.mk, StateT.bind, Bind.bind]
  cases h : act s with
  | mk result after => cases result <;> rfl

theorem searchRunPure {α : Type} (value : α) (s : MutableMemory U64) :
    ((pure value : BitMutationM α).run s) = (.ok value, s) := by rfl

theorem searchNativeIntValue (n : Int) (h : FitsNative n) : (int n).val = n := by
  change wrapInt .i64 n = n
  apply wrapInt_of_inRange
  change -(2 : Int)^63 ≤ n ∧ n ≤ (2 : Int)^63 - 1
  rcases h with ⟨hl, hu⟩
  exact ⟨hl, by omega⟩

theorem searchNativeInteger {t : IntTy} (start : JInt t) (s : MutableMemory U64) :
    (nativeInteger start).run s =
      if FitsNative start.val then (.ok (int start.val), s) else (.error .inexact, s) := by
  by_cases hf : FitsNative start.val
  · rw [if_pos hf]
    have hr : IntTy.i64.min ≤ start.val ∧ start.val ≤ IntTy.i64.max := by
      change -(2 : Int)^63 ≤ start.val ∧ start.val ≤ (2 : Int)^63 - 1
      rcases hf with ⟨hl, hu⟩
      exact ⟨hl, by omega⟩
    unfold nativeInteger JuliaLean.base.int.convert JInt.convert
    rw [dif_pos hr]
    change (Except.ok ⟨start.val, hr⟩, s) = (Except.ok (int start.val), s)
    have he : (⟨start.val, hr⟩ : I64) = int start.val := by
      apply Subtype.ext
      exact (searchNativeIntValue start.val hf).symm
    rw [he]
  · rw [if_neg hf]
    have hr : ¬ (IntTy.i64.min ≤ start.val ∧ start.val ≤ IntTy.i64.max) := by
      intro h
      apply hf
      change -(2 : Int)^63 ≤ start.val ∧ start.val < (2 : Int)^63
      change -(2 : Int)^63 ≤ start.val ∧ start.val ≤ (2 : Int)^63 - 1 at h
      exact ⟨h.1, by omega⟩
    unfold nativeInteger JuliaLean.base.int.convert JInt.convert
    rw [dif_neg hr]
    rfl

theorem searchPrevPositionNonpositive {N : Nat} (s : MutableMemory U64)
    (B : BitArray N) (start : Int) (wanted : Bool) (hstart : start ≤ 0) :
    prevPosition s B start wanted = none := by
  unfold prevPosition
  have hnone : ((matchingPositions s B wanted).reverse.find?
      fun (i : Nat) => decide ((i : Int) ≤ start)) = none := by
    apply List.find?_eq_none.mpr
    intro i hi
    have hm := List.mem_reverse.mp hi
    obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
    change j + 1 = i at he
    intro hb
    have hb := of_decide_eq_true hb
    omega
  rw [hnone]
  rfl

theorem searchPrevConversionError {N : Nat} {t : IntTy}
    (s : MutableMemory U64) (B : BitArray N) (start : JInt t)
    (hstart : ¬ FitsNative start.val) :
    (findPrevMachine B start).run s = (.error .inexact, s) := by
  unfold findPrevMachine
  rw [searchRunBind, searchNativeInteger, if_neg hstart]

theorem searchPrevNonpositive {N : Nat} {t : IntTy}
    (s : MutableMemory U64) (B : BitArray N) (start : JInt t)
    (hf : FitsNative start.val) (hstart : start.val ≤ 0) :
    (findPrevMachine B start).run s = (.ok none, s) := by
  have hn : int start.val ≤ int 0 := by
    change (int start.val).val ≤ (int 0).val
    rw [searchNativeIntValue _ hf]
    exact hstart
  unfold findPrevMachine
  rw [searchRunBind, searchNativeInteger, if_pos hf]
  simp only [bitArrayFindPrev, hn, ite_true]
  rfl

theorem searchPrevAboveLength {N : Nat} {t : IntTy}
    (s : MutableMemory U64) (B : BitArray N) (start : JInt t)
    (hf : FitsNative start.val) (hlen : 0 ≤ B.len.val) (hstart : B.len.val < start.val) :
    (findPrevMachine B start).run s = (.error .bounds, s) := by
  have hn : ¬ int start.val ≤ int 0 := by
    change ¬ (int start.val).val ≤ (int 0).val
    rw [searchNativeIntValue _ hf]
    change ¬ start.val ≤ 0
    omega
  have ha : int start.val > B.len := by
    change B.len.val < (int start.val).val
    rw [searchNativeIntValue _ hf]
    exact hstart
  unfold findPrevMachine
  rw [searchRunBind, searchNativeInteger, if_pos hf]
  simp only [bitArrayFindPrev, hn, ha, ite_false, ite_true]
  rfl
end JuliaLean.ChatGPT.Batch9.Group10



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group10

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.int
open JuliaLean.Proofs.base.bitarray.Models1Group16
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.ChatGPT.Batch4.Group8

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def searchPrevLoop (read : I64 → BitMutationM U64) (start : I64) :
    BitMutationM (Option I64) := do
  let mut i := start
  while i ≥ int 1 do
    let word ← read i
    if word != u64 0 then
      return some (shl_int (i - int 1) (int 6) + top_set_bit word)
    i := i - int 1
  return none

def searchPrevLoopStep (read : I64 → BitMutationM U64) (_ : Unit)
    (r : Option (Option I64) × I64) : BitMutationM (ForInStep (Option (Option I64) × I64)) := do
  if r.2 ≥ int 1 then
    let word ← read r.2
    if word != u64 0 then
      return .done (some (some (shl_int (r.2 - int 1) (int 6) + top_set_bit word)), r.2)
    return .yield (none, r.2 - int 1)
  else return .done (none, r.2)

set_option backward.isDefEq.respectTransparency false in
theorem searchPrevLoopFactor (read : I64 → BitMutationM U64) (start : I64) :
    searchPrevLoop read start = (do
      let r ← Lean.Loop.forIn ({} : Lean.Loop) (none, start) (searchPrevLoopStep read)
      match r.1 with
      | some value => pure value
      | none => pure none) := by
  unfold searchPrevLoop searchPrevLoopStep
  simp only [ForIn.forIn]
  congr 1
  funext r
  cases r.1 <;> rfl

theorem searchPrevLoopStop (read : I64 → BitMutationM U64) (start : I64)
    (s : MutableMemory U64) (hstart : ¬ start ≥ int 1) :
    (searchPrevLoop read start).run s = (.ok none, s) := by
  rw [searchPrevLoopFactor, searchRunBind]
  have hl : (Lean.Loop.forIn ({} : Lean.Loop) (none, start) (searchPrevLoopStep read)).run s =
      (.ok (none, start), s) := by
    apply reverseLoopDone
    simp only [searchPrevLoopStep, hstart, ite_false, searchRunPure]
  rw [hl]
  rfl

theorem searchPrevLoopHit (read : I64 → BitMutationM U64) (start : I64)
    (s : MutableMemory U64) (word : U64) (hstart : start ≥ int 1)
    (hread : (read start).run s = (.ok word, s)) (hword : word ≠ u64 0) :
    (searchPrevLoop read start).run s =
      (.ok (some (shl_int (start - int 1) (int 6) + top_set_bit word)), s) := by
  rw [searchPrevLoopFactor, searchRunBind]
  have hl : (Lean.Loop.forIn ({} : Lean.Loop) (none, start) (searchPrevLoopStep read)).run s =
      (.ok (some (some (shl_int (start - int 1) (int 6) + top_set_bit word)), start), s) := by
    apply reverseLoopDone
    simp only [searchPrevLoopStep, hstart, ite_true, searchRunBind, hread,
      bne_iff_ne.mpr hword, searchRunPure]
  rw [hl]
  rfl

theorem searchPrevLoopMiss (read : I64 → BitMutationM U64) (start : I64)
    (s : MutableMemory U64) (hstart : start ≥ int 1)
    (hread : (read start).run s = (.ok (u64 0), s)) :
    (searchPrevLoop read start).run s = (searchPrevLoop read (start - int 1)).run s := by
  rw [searchPrevLoopFactor, Lean.Loop.forIn_eq_of_monadTail]
  simp only [searchRunBind, searchPrevLoopStep, hstart, ite_true, hread,
    bne_self_eq_false, Bool.false_eq_true, ite_false, searchRunPure]
  rw [searchPrevLoopFactor]
  simp only [searchRunBind]

theorem searchNativeIntSelf (index : I64) : int index.val = index := by
  apply Subtype.ext
  change wrapInt .i64 index.val = index.val
  exact wrapInt_val index

theorem searchIntSubOne (k : Nat) (hk : k + 1 ≤ 9223372036854775807) :
    int ((k + 1 : Nat) : Int) - int 1 = int (k : Int) := by
  apply Subtype.ext
  change wrapInt .i64 ((int ((k + 1 : Nat) : Int)).val - 1) = (int (k : Int)).val
  rw [packedInt_val (k + 1) hk, packedInt_val k (by omega)]
  have he : ((k + 1 : Nat) : Int) - 1 = (k : Int) := by omega
  rw [he]
  apply wrapInt_of_inRange
  change -(2 : Int)^63 ≤ (k : Int) ∧ (k : Int) ≤ (2 : Int)^63 - 1
  omega

theorem searchChunkShift (k : Nat) (hk : k * 64 ≤ 9223372036854775807) :
    shl_int (int (k : Int)) (int 6) = int ((k * 64 : Nat) : Int) := by
  apply Subtype.ext
  rw [shl_int_val, packedInt_val k (by omega)]
  have hp : pattern (int 6) = 6 := by decide
  rw [hp, packedInt_val (k * 64) hk]
  change wrapInt .i64 ((k : Int) * 64) = ((k * 64 : Nat) : Int)
  rw [wrapInt_of_inRange]
  · omega
  · change -(2 : Int)^63 ≤ (k : Int) * 64 ∧ (k : Int) * 64 ≤ (2 : Int)^63 - 1
    omega

theorem searchPrevLoopCorrect (read : I64 → BitMutationM U64) (s : MutableMemory U64)
    (words : Nat → U64) (p : Nat → Bool) (k : Nat)
    (hk : k * 64 ≤ 9223372036854775807)
    (hread : ∀ j, j < k → (read (int ((j + 1 : Nat) : Int))).run s = (.ok (words j), s))
    (hbits : ∀ j, j < k → ∀ b, b < 64 → p (j * 64 + b) = bitOf (words j) b) :
    (searchPrevLoop read (int (k : Int))).run s =
      (.ok ((searchLastMatch p (k * 64)).map (fun i => int ((i + 1 : Nat) : Int))), s) := by
  induction k with
  | zero =>
    change (searchPrevLoop read (int 0)).run s = (.ok none, s)
    exact searchPrevLoopStop read (int 0) s (by decide)
  | succ k ih =>
    have hsmall : k + 1 ≤ 9223372036854775807 := by omega
    have hpositive : int ((k + 1 : Nat) : Int) ≥ int 1 := by
      change (int 1).val ≤ (int ((k + 1 : Nat) : Int)).val
      rw [packedInt_val (k + 1) hsmall]
      change (1 : Int) ≤ ((k + 1 : Nat) : Int)
      omega
    have hr := hread k (by omega)
    by_cases hword : words k = u64 0
    · have hreadZero : (read (int ((k + 1 : Nat) : Int))).run s = (.ok (u64 0), s) := by
        rw [hr, hword]
      rw [searchPrevLoopMiss read (int ((k + 1 : Nat) : Int)) s hpositive hreadZero,
        searchIntSubOne k hsmall]
      rw [ih (by omega) (fun j hj => hread j (by omega))
        (fun j hj b hb => hbits j (by omega) b hb)]
      have he : (k + 1) * 64 = k * 64 + 64 := by omega
      rw [he]
      have htail : ∀ i, k * 64 ≤ i → i < k * 64 + 64 → p i = false := by
        intro i hlo hhi
        have he : k * 64 + (i - k * 64) = i := by omega
        rw [← he, hbits k (by omega) (i - k * 64) (by omega), hword]
        change Nat.testBit 0 (i - k * 64) = false
        exact Nat.zero_testBit _
      rw [searchLastMatchAddFalse p (k * 64) 64 htail]
    · rw [searchPrevLoopHit read (int ((k + 1 : Nat) : Int)) s (words k) hpositive hr hword]
      obtain ⟨htopBound, htopPositive, htopBit, htopAbove⟩ := searchTopSetBitSpec (words k)
      have htopPos := htopPositive hword
      let r := (top_set_bit (words k)).val.toNat
      have hlast : searchLastMatch p ((k + 1) * 64) = some (k * 64 + (r - 1)) := by
        apply searchLastMatchSome
        · dsimp only [r]
          omega
        · rw [hbits k (by omega) (r - 1) (by dsimp only [r]; omega)]
          exact htopBit htopPos
        · intro j hj hbound
          have he : k * 64 + (j - k * 64) = j := by omega
          rw [← he, hbits k (by omega) (j - k * 64) (by omega)]
          exact htopAbove (j - k * 64) (by dsimp only [r] at hj; omega)
      rw [hlast]
      have ht : top_set_bit (words k) = int (r : Int) := by
        have hn := (topSetBit_proven .u64 (words k)).1
        have he : (r : Int) = (top_set_bit (words k)).val := Int.toNat_of_nonneg hn
        rw [he]
        exact (searchNativeIntSelf _).symm
      have hout : shl_int (int ((k + 1 : Nat) : Int) - int 1) (int 6) +
          top_set_bit (words k) = int ((k * 64 + (r - 1) + 1 : Nat) : Int) := by
        rw [searchIntSubOne k hsmall, searchChunkShift k (by omega), ht, packedInt_add]
        apply congrArg int
        dsimp only [r]
        omega
      rw [hout]
      rfl

def searchStoredWord {N : Nat} (s : MutableMemory U64) (B : BitArray N) (chunk : Nat) : U64 :=
  ((s.contents B.chunks)[chunk]?.getD none).getD (u64 0)

theorem searchObserveStored {N : Nat} (s : MutableMemory U64) (B : BitArray N)
    (chunk bit : Nat) (hbit : bit < 64) :
    bitAt s B (chunk * 64 + bit) = bitOf (searchStoredWord s B chunk) bit := by
  have hdiv : (chunk * 64 + bit) / 64 = chunk := by omega
  have hmod : (chunk * 64 + bit) % 64 = bit := by omega
  simp only [bitAt, hdiv, hmod, searchStoredWord]
  rw [bitOf_eq, pattern_of_unsigned (u := .u64) rfl,
    Nat.testBit_eq_decide_div_mod_eq]

theorem searchReadStored {N : Nat} (s : MutableMemory U64) (B : BitArray N)
    (hvalid : s.validVector B.chunks)
    (hassigned : ∀ cell ∈ s.contents B.chunks, cell.isSome = true)
    (chunk : Nat) (hchunk : chunk < (s.contents B.chunks).length) :
    (mutableGet B.chunks (int ((chunk + 1 : Nat) : Int))).run s =
      (.ok (searchStoredWord s B chunk), s) := by
  obtain ⟨word, hword⟩ := iteration_assigned_word (s.contents B.chunks) chunk hchunk hassigned
  have he : searchStoredWord s B chunk = word := by
    simp only [searchStoredWord, hword, Option.getD_some]
  rw [he]
  exact group8_mutableGet_of_contents s B.chunks chunk word hvalid hword

theorem searchBitOfPacked (word : U64) (bit : Nat) : bitOf word bit = packedBit word bit := by
  rw [bitOf_eq, pattern_of_unsigned (u := .u64) rfl]
  rfl

theorem searchChunkStart (start : I64) (hstart : 0 < start.val) :
    div64 (start - int 1) + int 1 =
      int (((start.val.toNat - 1) / 64 + 1 : Nat) : Int) := by
  have hb := start.property
  change -(2 : Int)^63 ≤ start.val ∧ start.val ≤ (2 : Int)^63 - 1 at hb
  have ha := (scalar_chunks_id start (by change (1 : Int) ≤ start.val; omega)).1
  apply Subtype.ext
  change (getChunksId start).1.val = _
  rw [ha, packedInt_val _ (by omega)]
  omega

theorem searchMaskBit (start : I64) (hstart : 0 < start.val) (bit : Nat) :
    bitOf (maskEnd start) bit =
      decide (((start.val.toNat - 1) / 64) * 64 + bit < start.val.toNat) := by
  have hb := start.property
  change -(2 : Int)^63 ≤ start.val ∧ start.val ≤ (2 : Int)^63 - 1 at hb
  have hn : start.val.toNat ≤ 9223372036854775807 := by omega
  have he : int (start.val.toNat : Int) = start := by
    apply Subtype.ext
    rw [packedInt_val _ hn]
    omega
  have hm := packedMask_last_bit start.val.toNat bit (by omega) hn
  rw [he] at hm
  rw [searchBitOfPacked, hm]
  have hc : JuliaLean.Proofs.base.bitarray.wordCount start.val.toNat - 1 =
      (start.val.toNat - 1) / 64 := by
    unfold JuliaLean.Proofs.base.bitarray.wordCount
    omega
  rw [hc]

theorem searchMaskedBit {N : Nat} (s : MutableMemory U64) (B : BitArray N)
    (start : I64) (hstart : 0 < start.val) (bit : Nat) (hbit : bit < 64) :
    bitOf (and_int (searchStoredWord s B ((start.val.toNat - 1) / 64)) (maskEnd start)) bit =
      (bitAt s B (((start.val.toNat - 1) / 64) * 64 + bit) &&
        decide (((start.val.toNat - 1) / 64) * 64 + bit < start.val.toNat)) := by
  change bitOf (band (searchStoredWord s B ((start.val.toNat - 1) / 64)) (maskEnd start)) bit = _
  rw [bitOf_band, searchMaskBit start hstart bit,
    ← searchObserveStored s B ((start.val.toNat - 1) / 64) bit hbit]

theorem searchPrevRawFactor (chunks : Nat) (start : I64) :
    unsafeBitFindPrev top_set_bit chunks start = (do
      let chunkStart := div64 (start - int 1) + int 1
      let mask := maskEnd start
      let word ← mutableGet chunks chunkStart
      if and_int word mask != u64 0 then
        return some (shl_int (chunkStart - int 1) (int 6) + top_set_bit (and_int word mask))
      searchPrevLoop (mutableGet chunks) (chunkStart - int 1)) := by rfl

theorem searchPrevRawCorrect {N : Nat} (s : MutableMemory U64) (B : BitArray N)
    (start : I64) (hreadable : Readable s B) (hstart : 0 < start.val)
    (hend : start.val ≤ B.len.val) :
    (unsafeBitFindPrev top_set_bit B.chunks start).run s =
      (.ok ((searchLastMatch (bitAt s B) start.val.toNat).map
        (fun i => int ((i + 1 : Nat) : Int))), s) := by
  rcases hreadable with ⟨hvalid, hlength, _, _, _, _, _, hcover, hassigned, _⟩
  let n := start.val.toNat
  let k := (n - 1) / 64
  let word := searchStoredWord s B k
  let masked := and_int word (maskEnd start)
  have hsbound := start.property.2
  change start.val ≤ (2 : Int)^63 - 1 at hsbound
  have hn : n ≤ 9223372036854775807 := by dsimp only [n]; omega
  have hnp : 0 < n := by dsimp only [n]; omega
  have hnl : n ≤ B.len.val.toNat := by dsimp only [n]; omega
  have hklo : k * 64 < n := by dsimp only [k]; omega
  have hkhi : n ≤ k * 64 + 64 := by dsimp only [k]; omega
  have hksmall : k + 1 ≤ 9223372036854775807 := by omega
  have hkcontents : k < (s.contents B.chunks).length := by dsimp only [k]; omega
  have hget : (mutableGet B.chunks (int ((k + 1 : Nat) : Int))).run s = (.ok word, s) :=
    searchReadStored s B hvalid hassigned k hkcontents
  have hchunk : div64 (start - int 1) + int 1 = int ((k + 1 : Nat) : Int) :=
    searchChunkStart start hstart
  rw [searchPrevRawFactor]
  simp only [hchunk, searchRunBind, hget]
  change ((if masked != u64 0 then
      pure (some (shl_int (int ((k + 1 : Nat) : Int) - int 1) (int 6) + top_set_bit masked))
    else searchPrevLoop (mutableGet B.chunks) (int ((k + 1 : Nat) : Int) - int 1)).run s) =
      (.ok ((searchLastMatch (bitAt s B) n).map (fun i => int ((i + 1 : Nat) : Int))), s)
  by_cases hz : masked = u64 0
  · have hb : (masked != u64 0) = false := by rw [hz]; rfl
    simp only [hb, Bool.false_eq_true, ite_false]
    rw [searchIntSubOne k hksmall]
    have hloop := searchPrevLoopCorrect (mutableGet B.chunks) s (searchStoredWord s B)
      (bitAt s B) k (by omega)
      (fun j hj => searchReadStored s B hvalid hassigned j (by omega))
      (fun j _ b hb => searchObserveStored s B j b hb)
    rw [hloop]
    have htail : ∀ i, k * 64 ≤ i → i < n → bitAt s B i = false := by
      intro i hlo hhi
      let b := i - k * 64
      have hb : b < 64 := by dsimp only [b]; omega
      have hm := searchMaskedBit s B start hstart b hb
      change bitOf masked b = (bitAt s B (k * 64 + b) && decide (k * 64 + b < n)) at hm
      rw [hz] at hm
      have hzbit : bitOf (u64 0) b = false := by
        change Nat.testBit 0 b = false
        exact Nat.zero_testBit _
      have he : k * 64 + b = i := by dsimp only [b]; omega
      rw [hzbit, he, decide_eq_true hhi, Bool.and_true] at hm
      exact hm.symm
    have ht := searchLastMatchAddFalse (bitAt s B) (k * 64) (n - k * 64)
      (fun i hlo hhi => htail i hlo (by omega))
    have hnEq : k * 64 + (n - k * 64) = n := by omega
    rw [hnEq] at ht
    rw [ht]
  · have hb : (masked != u64 0) = true := bne_iff_ne.mpr hz
    simp only [hb, ite_true, searchRunPure]
    obtain ⟨hrbound, hrpositive, hrbit, hrabove⟩ := searchTopSetBitSpec masked
    have hrpos := hrpositive hz
    let r := (top_set_bit masked).val.toNat
    have hselected := searchMaskedBit s B start hstart (r - 1) (by dsimp only [r]; omega)
    change bitOf masked (r - 1) =
      (bitAt s B (k * 64 + (r - 1)) && decide (k * 64 + (r - 1) < n)) at hselected
    rw [hrbit hrpos] at hselected
    have hselectedBoth := Bool.and_eq_true_iff.mp hselected.symm
    have hindexBound : k * 64 + (r - 1) < n := of_decide_eq_true hselectedBoth.2
    have hlast : searchLastMatch (bitAt s B) n = some (k * 64 + (r - 1)) := by
      apply searchLastMatchSome _ n _ hindexBound hselectedBoth.1
      intro i hlo hhi
      let b := i - k * 64
      have hb : b < 64 := by dsimp only [b]; omega
      have hbr : (top_set_bit masked).val.toNat ≤ b := by dsimp only [b, r] at *; omega
      have hm := searchMaskedBit s B start hstart b hb
      change bitOf masked b = (bitAt s B (k * 64 + b) && decide (k * 64 + b < n)) at hm
      have he : k * 64 + b = i := by dsimp only [b]; omega
      rw [hrabove b hbr, he, decide_eq_true hhi, Bool.and_true] at hm
      exact hm.symm
    rw [hlast]
    have ht : top_set_bit masked = int (r : Int) := by
      have hn := (topSetBit_proven .u64 masked).1
      have he : (r : Int) = (top_set_bit masked).val := Int.toNat_of_nonneg hn
      rw [he]
      exact (searchNativeIntSelf _).symm
    have hout : shl_int (int ((k + 1 : Nat) : Int) - int 1) (int 6) + top_set_bit masked =
        int ((k * 64 + (r - 1) + 1 : Nat) : Int) := by
      rw [searchIntSubOne k hksmall, searchChunkShift k (by omega), ht, packedInt_add]
      apply congrArg int
      dsimp only [r]
      omega
    rw [hout]
    rfl

theorem Models1G16FindprevMachine_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group16.FindPrevMachineContract := by
  intro N t s B start hreadable
  dsimp only
  by_cases hfit : FitsNative start.val
  · by_cases hnonpositive : start.val ≤ 0
    · rw [searchPrevNonpositive s B start hfit hnonpositive]
      refine ⟨rfl, ?_⟩
      rw [if_neg (not_not_intro hfit)]
      have hupper : ¬ B.len.val < start.val := by
        have hn := hreadable.2.1
        omega
      rw [if_neg hupper, searchPrevPositionNonpositive s B start.val true hnonpositive]
    · by_cases hupper : B.len.val < start.val
      · rw [searchPrevAboveLength s B start hfit hreadable.2.1 hupper]
        refine ⟨rfl, ?_⟩
        rw [if_neg (not_not_intro hfit), if_pos hupper]
      · have hpositive : 0 < start.val := by omega
        have hnval : (int start.val).val = start.val := searchNativeIntValue _ hfit
        have hnpositive : ¬ int start.val ≤ int 0 := by
          change ¬ (int start.val).val ≤ 0
          rw [hnval]
          omega
        have hnupper : ¬ int start.val > B.len := by
          change ¬ B.len.val < (int start.val).val
          rw [hnval]
          exact hupper
        have hraw := searchPrevRawCorrect s B (int start.val) hreadable
          (by rw [hnval]; exact hpositive) (by rw [hnval]; omega)
        have hrun : (JuliaLean.base.bitarray.Models1Group16.findPrevMachine B start).run s =
            (.ok (prevPosition s B start.val true), s) := by
          unfold JuliaLean.base.bitarray.Models1Group16.findPrevMachine
          rw [searchRunBind, searchNativeInteger, if_pos hfit]
          simp only [bitArrayFindPrev, hnpositive, hnupper, ite_false]
          rw [hraw, hnval]
          rw [searchPrevPositionAsLast s B start.val true (by omega) (by omega)]
          have hp : (fun i => bitAt s B i == true) = bitAt s B := by
            funext i
            cases bitAt s B i <;> rfl
          rw [hp]
        rw [hrun]
        refine ⟨rfl, ?_⟩
        rw [if_neg (not_not_intro hfit), if_neg hupper]
  · rw [searchPrevConversionError s B start hfit]
    refine ⟨rfl, ?_⟩
    rw [if_pos hfit]
end JuliaLean.ChatGPT.Batch9.Group10



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group10

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.int
open JuliaLean.Proofs.base.bitarray.Models1Group16
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem searchNotNot (word : U64) : not_int (not_int word) = word := by
  apply packedBit_ext
  intro bit hbit
  simp only [← searchBitOfPacked]
  change bitOf (bnot (bnot word)) bit = bitOf word bit
  rw [bitOf_bnot _ hbit, bitOf_bnot _ hbit, Bool.not_not]

theorem searchNotZeroIffMax (word : U64) : not_int word = u64 0 ↔ word = u64Max := by
  constructor
  · intro he
    have h := congrArg (fun value : U64 => not_int value) he
    simpa only [searchNotNot, show not_int (u64 0) = u64Max from rfl] using h
  · intro he
    rw [he]
    rfl

theorem searchNotNonzero (word : U64) :
    (not_int word != u64 0) = (word != u64Max) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne]
  exact not_congr (searchNotZeroIffMax word)

theorem searchNotOrNot (word mask : U64) :
    not_int (or_int word (not_int mask)) = and_int (not_int word) mask := by
  apply packedBit_ext
  intro bit hbit
  simp only [← searchBitOfPacked]
  change bitOf (bnot (bor word (bnot mask))) bit = bitOf (band (bnot word) mask) bit
  rw [bitOf_bnot _ hbit, bitOf_bor, bitOf_bnot _ hbit, bitOf_band, bitOf_bnot _ hbit]
  cases bitOf word bit <;> cases bitOf mask bit <;> rfl

theorem searchTopNot (word : U64) :
    top_set_bit (not_int word) =
      int 64 - leading_ones_Integer leading_zeros not_int word := by
  apply Subtype.ext
  rw [top_set_bit, sub, sub_int_val]
  have hm : (mul (lit .i64 8) (sizeof (not_int word))).val = 64 := by
    change (mul (lit .i64 8) (lit .i64 8)).val = 64
    decide
  rw [hm]
  rfl

def searchPrevNotLoop (read : I64 → BitMutationM U64) (start : I64) :
    BitMutationM (Option I64) := do
  let mut i := start
  while i ≥ int 1 do
    let word ← read i
    if word != u64Max then
      return some (shl_int (i - int 1) (int 6) +
        (int 64 - leading_ones_Integer leading_zeros not_int word))
    i := i - int 1
  return none

theorem searchPrevNotLoopAsSearch (read : I64 → BitMutationM U64) (start : I64) :
    searchPrevNotLoop read start =
      searchPrevLoop (fun i => do return not_int (← read i)) start := by
  simp only [searchPrevNotLoop, searchPrevLoop, bind_assoc, pure_bind,
    searchNotNonzero, searchTopNot]

def searchPrevAt (read : I64 → BitMutationM U64) (start : I64) :
    BitMutationM (Option I64) := do
  let chunkStart := div64 (start - int 1) + int 1
  let mask := maskEnd start
  let word ← read chunkStart
  if and_int word mask != u64 0 then
    return some (shl_int (chunkStart - int 1) (int 6) + top_set_bit (and_int word mask))
  searchPrevLoop read (chunkStart - int 1)

theorem searchPrevNotOriginalFactor {N : Nat} (B : BitArray N) (start : I64) :
    bitArrayFindPrevNot (leading_ones_Integer leading_zeros not_int) B start = (do
      if start ≤ int 0 then return none
      if start > B.len then throw Error.bounds
      let chunkStart := div64 (start - int 1) + int 1
      let mask := not_int (maskEnd start)
      let word ← mutableGet B.chunks chunkStart
      if or_int word mask != u64Max then
        return some (shl_int (chunkStart - int 1) (int 6) +
          (int 64 - leading_ones_Integer leading_zeros not_int (or_int word mask)))
      searchPrevNotLoop (mutableGet B.chunks) (chunkStart - int 1)) := by rfl

theorem searchPrevNotFactor {N : Nat} (B : BitArray N) (start : I64) :
    bitArrayFindPrevNot (leading_ones_Integer leading_zeros not_int) B start = (do
      if start ≤ int 0 then return none
      if start > B.len then throw Error.bounds
      searchPrevAt (fun i => do return not_int (← mutableGet B.chunks i)) start) := by
  rw [searchPrevNotOriginalFactor]
  simp only [searchPrevAt, bind_assoc, pure_bind, ← searchNotNonzero,
    ← searchTopNot, searchNotOrNot, searchPrevNotLoopAsSearch]

theorem searchReadComplement {N : Nat} (s : MutableMemory U64) (B : BitArray N)
    (hvalid : s.validVector B.chunks)
    (hassigned : ∀ cell ∈ s.contents B.chunks, cell.isSome = true)
    (chunk : Nat) (hchunk : chunk < (s.contents B.chunks).length) :
    ((do return not_int (← mutableGet B.chunks (int ((chunk + 1 : Nat) : Int))))
        : BitMutationM U64).run s = (.ok (not_int (searchStoredWord s B chunk)), s) := by
  rw [searchRunBind, searchReadStored s B hvalid hassigned chunk hchunk]
  rfl

theorem searchObserveComplement {N : Nat} (s : MutableMemory U64) (B : BitArray N)
    (chunk bit : Nat) (hbit : bit < 64) :
    (!bitAt s B (chunk * 64 + bit)) = bitOf (not_int (searchStoredWord s B chunk)) bit := by
  rw [searchObserveStored s B chunk bit hbit]
  exact (bitOf_bnot (searchStoredWord s B chunk) hbit).symm

theorem searchPrevAtCorrect (read : I64 → BitMutationM U64) (s : MutableMemory U64)
    (words : Nat → U64) (p : Nat → Bool) (start : I64) (hstart : 0 < start.val)
    (hread : ∀ j, j ≤ (start.val.toNat - 1) / 64 →
      (read (int ((j + 1 : Nat) : Int))).run s = (.ok (words j), s))
    (hbits : ∀ j, j ≤ (start.val.toNat - 1) / 64 → ∀ b, b < 64 →
      p (j * 64 + b) = bitOf (words j) b) :
    (searchPrevAt read start).run s =
      (.ok ((searchLastMatch p start.val.toNat).map (fun i => int ((i + 1 : Nat) : Int))), s) := by
  let n := start.val.toNat
  let k := (n - 1) / 64
  let word := words k
  let masked := and_int word (maskEnd start)
  have hsbound := start.property.2
  change start.val ≤ (2 : Int)^63 - 1 at hsbound
  have hn : n ≤ 9223372036854775807 := by dsimp only [n]; omega
  have hnp : 0 < n := by dsimp only [n]; omega
  have hklo : k * 64 < n := by dsimp only [k]; omega
  have hkhi : n ≤ k * 64 + 64 := by dsimp only [k]; omega
  have hksmall : k + 1 ≤ 9223372036854775807 := by omega
  have hget : (read (int ((k + 1 : Nat) : Int))).run s = (.ok word, s) :=
    hread k (Nat.le_refl _)
  have hchunk : div64 (start - int 1) + int 1 = int ((k + 1 : Nat) : Int) :=
    searchChunkStart start hstart
  have hmaskbit : ∀ b, b < 64 → bitOf masked b =
      (p (k * 64 + b) && decide (k * 64 + b < n)) := by
    intro b hb
    change bitOf (band (words k) (maskEnd start)) b = _
    rw [bitOf_band, searchMaskBit start hstart b, ← hbits k (Nat.le_refl _) b hb]
  unfold searchPrevAt
  simp only [hchunk, searchRunBind, hget]
  change ((if masked != u64 0 then
      pure (some (shl_int (int ((k + 1 : Nat) : Int) - int 1) (int 6) + top_set_bit masked))
    else searchPrevLoop read (int ((k + 1 : Nat) : Int) - int 1)).run s) =
      (.ok ((searchLastMatch p n).map (fun i => int ((i + 1 : Nat) : Int))), s)
  by_cases hz : masked = u64 0
  · have hb : (masked != u64 0) = false := by rw [hz]; rfl
    simp only [hb, Bool.false_eq_true, ite_false]
    rw [searchIntSubOne k hksmall]
    have hloop := searchPrevLoopCorrect read s words p k (by omega)
      (fun j hj => hread j (by change j ≤ k; omega))
      (fun j hj b hb => hbits j (by change j ≤ k; omega) b hb)
    rw [hloop]
    have htail : ∀ i, k * 64 ≤ i → i < n → p i = false := by
      intro i hlo hhi
      let b := i - k * 64
      have hb : b < 64 := by dsimp only [b]; omega
      have hm := hmaskbit b hb
      rw [hz] at hm
      have hzbit : bitOf (u64 0) b = false := by
        change Nat.testBit 0 b = false
        exact Nat.zero_testBit _
      have he : k * 64 + b = i := by dsimp only [b]; omega
      rw [hzbit, he, decide_eq_true hhi, Bool.and_true] at hm
      exact hm.symm
    have ht := searchLastMatchAddFalse p (k * 64) (n - k * 64)
      (fun i hlo hhi => htail i hlo (by omega))
    have hnEq : k * 64 + (n - k * 64) = n := by omega
    rw [hnEq] at ht
    rw [ht]
  · have hb : (masked != u64 0) = true := bne_iff_ne.mpr hz
    simp only [hb, ite_true, searchRunPure]
    obtain ⟨hrbound, hrpositive, hrbit, hrabove⟩ := searchTopSetBitSpec masked
    have hrpos := hrpositive hz
    let r := (top_set_bit masked).val.toNat
    have hselected := hmaskbit (r - 1) (by dsimp only [r]; omega)
    rw [hrbit hrpos] at hselected
    have hselectedBoth := Bool.and_eq_true_iff.mp hselected.symm
    have hindexBound : k * 64 + (r - 1) < n := of_decide_eq_true hselectedBoth.2
    have hlast : searchLastMatch p n = some (k * 64 + (r - 1)) := by
      apply searchLastMatchSome _ n _ hindexBound hselectedBoth.1
      intro i hlo hhi
      let b := i - k * 64
      have hb : b < 64 := by dsimp only [b]; omega
      have hbr : (top_set_bit masked).val.toNat ≤ b := by dsimp only [b, r] at *; omega
      have hm := hmaskbit b hb
      have he : k * 64 + b = i := by dsimp only [b]; omega
      rw [hrabove b hbr, he, decide_eq_true hhi, Bool.and_true] at hm
      exact hm.symm
    rw [hlast]
    have ht : top_set_bit masked = int (r : Int) := by
      have hn := (topSetBit_proven .u64 masked).1
      have he : (r : Int) = (top_set_bit masked).val := Int.toNat_of_nonneg hn
      rw [he]
      exact (searchNativeIntSelf _).symm
    have hout : shl_int (int ((k + 1 : Nat) : Int) - int 1) (int 6) + top_set_bit masked =
        int ((k * 64 + (r - 1) + 1 : Nat) : Int) := by
      rw [searchIntSubOne k hksmall, searchChunkShift k (by omega), ht, packedInt_add]
      apply congrArg int
      dsimp only [r]
      omega
    rw [hout]
    rfl

theorem searchPrevNotInside {N : Nat} (s : MutableMemory U64) (B : BitArray N)
    (start : I64) (hreadable : Readable s B) (hstart : 0 < start.val)
    (hend : start.val ≤ B.len.val) :
    (bitArrayFindPrevNot (leading_ones_Integer leading_zeros not_int) B start).run s =
      (.ok (prevPosition s B start.val false), s) := by
  have hnonpositive : ¬ start ≤ int 0 := by change ¬ start.val ≤ 0; omega
  have hupper : ¬ start > B.len := by change ¬ B.len.val < start.val; omega
  rw [searchPrevNotFactor]
  simp only [hnonpositive, hupper, ite_false]
  have hcorrect := searchPrevAtCorrect
    (fun i => do return not_int (← mutableGet B.chunks i)) s
    (fun j => not_int (searchStoredWord s B j)) (fun i => !bitAt s B i) start hstart
    (by
      intro j hj
      apply searchReadComplement s B hreadable.1 hreadable.2.2.2.2.2.2.2.2.1 j
      have cover := hreadable.2.2.2.2.2.2.2.1
      omega)
    (fun j _ b hb => searchObserveComplement s B j b hb)
  rw [hcorrect, searchPrevPositionAsLast s B start.val false (by omega) hend]
  have hp : (fun i => bitAt s B i == false) = (fun i => !bitAt s B i) := by
    funext i
    cases bitAt s B i <;> rfl
  rw [hp]

theorem searchFixedFalse {N : Nat} {t : IntTy} (B : BitArray N) (start : JInt t) :
    JuliaLean.base.bitarray.Models1Group16.findPrevFixedMachine false B start = (do
      let native ← JuliaLean.base.bitarray.Models1Group16.nativeInteger start
      bitArrayFindPrevNot (leading_ones_Integer leading_zeros not_int) B native) := by
  simp only [JuliaLean.base.bitarray.Models1Group16.findPrevFixedMachine,
    show (false == false) = true from rfl, ite_true, bind_pure]

theorem searchFixedTrue {N : Nat} {t : IntTy} (B : BitArray N) (start : JInt t) :
    JuliaLean.base.bitarray.Models1Group16.findPrevFixedMachine true B start =
      JuliaLean.base.bitarray.Models1Group16.findPrevMachine B start := by
  simp only [JuliaLean.base.bitarray.Models1Group16.findPrevFixedMachine,
    show (true == false) = false from rfl, show (true == true) = true from rfl,
    Bool.false_eq_true, ite_false, ite_true, bind_pure]

theorem Models1G16FindprevFixedMachine_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group16.FindPrevFixedMachineContract := by
  intro N t s B start wanted hreadable
  cases wanted with
  | true =>
    dsimp only
    rw [searchFixedTrue]
    exact Models1G16FindprevMachine_proven N t s B start hreadable
  | false =>
    dsimp only
    rw [searchFixedFalse, searchRunBind, searchNativeInteger]
    by_cases hfit : FitsNative start.val
    · rw [if_pos hfit]
      dsimp only
      have hnval : (int start.val).val = start.val := searchNativeIntValue _ hfit
      by_cases hnonpositive : start.val ≤ 0
      · have hp : int start.val ≤ int 0 := by
          change (int start.val).val ≤ 0
          rw [hnval]
          exact hnonpositive
        simp only [bitArrayFindPrevNot, hp, ite_true, searchRunPure]
        refine ⟨by trivial, ?_⟩
        rw [if_neg (not_not_intro hfit)]
        have hu : ¬ B.len.val < start.val := by
          have hlen := hreadable.2.1
          omega
        rw [if_neg hu, searchPrevPositionNonpositive s B start.val false hnonpositive]
      · have hp : ¬ int start.val ≤ int 0 := by
          change ¬ (int start.val).val ≤ 0
          rw [hnval]
          exact hnonpositive
        by_cases hupper : B.len.val < start.val
        · have hu : int start.val > B.len := by
            change B.len.val < (int start.val).val
            rw [hnval]
            exact hupper
          simp only [bitArrayFindPrevNot, hp, hu, ite_false, ite_true]
          refine ⟨rfl, ?_⟩
          rw [if_neg (not_not_intro hfit), if_pos hupper]
          rfl
        · rw [searchPrevNotInside s B (int start.val) hreadable
            (by rw [hnval]; omega) (by rw [hnval]; omega), hnval]
          refine ⟨rfl, ?_⟩
          rw [if_neg (not_not_intro hfit), if_neg hupper]
    · rw [if_neg hfit]
      refine ⟨rfl, ?_⟩
      rw [if_pos hfit]
end JuliaLean.ChatGPT.Batch9.Group10



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group10

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def searchTinyVector : BitVector := ⟨0, int 1, [int 1]⟩
def searchPaddingHeap : MutableMemory U64 := MutableMemory.initial [some (u64 2)]
def searchExtraHeap : MutableMemory U64 := MutableMemory.initial [some (u64 1), some (u64 0)]

theorem searchPaddingReadable :
    JuliaLean.Proofs.base.bitarray.Models1Group16.Readable searchPaddingHeap searchTinyVector := by
  unfold JuliaLean.Proofs.base.bitarray.Models1Group16.Readable
  decide

theorem searchExtraReadable :
    JuliaLean.Proofs.base.bitarray.Models1Group16.Readable searchExtraHeap searchTinyVector := by
  unfold JuliaLean.Proofs.base.bitarray.Models1Group16.Readable
  decide


theorem Models1G16FindnextMachine_refuted :
    ¬ JuliaLean.Proofs.base.bitarray.Models1Group16.FindNextMachineContract := by
  intro h
  have hx := (h 1 .i64 searchPaddingHeap searchTinyVector (int 1) searchPaddingReadable).2
  have hf : JuliaLean.Proofs.base.bitarray.Models1Group16.FitsNative (int 1).val := by decide
  have hp : ¬ (int 1).val ≤ 0 := by decide
  rw [if_neg (not_not_intro hf), if_neg hp] at hx
  have hn : ((JuliaLean.base.bitarray.Models1Group16.findNextMachine searchTinyVector (int 1)).run
      searchPaddingHeap).1 ≠ .ok
      (JuliaLean.Proofs.base.bitarray.Models1Group16.nextPosition searchPaddingHeap searchTinyVector
        (int 1).val true) := by decide
  exact hn hx


theorem Models1G16FindnextFixedMachine_refuted :
    ¬ JuliaLean.Proofs.base.bitarray.Models1Group16.FindNextFixedMachineContract := by
  intro h
  have hx := (h 1 .i64 searchPaddingHeap searchTinyVector (int 1) true searchPaddingReadable).2
  have hf : JuliaLean.Proofs.base.bitarray.Models1Group16.FitsNative (int 1).val := by decide
  have hp : ¬ (int 1).val ≤ 0 := by decide
  rw [if_neg (not_not_intro hf), if_neg hp] at hx
  have hn : ((JuliaLean.base.bitarray.Models1Group16.findNextFixedMachine true searchTinyVector (int 1)).run
      searchPaddingHeap).1 ≠ .ok
      (JuliaLean.Proofs.base.bitarray.Models1Group16.nextPosition searchPaddingHeap searchTinyVector
        (int 1).val true) := by decide
  exact hn hx


theorem Models1G16FindmaxVector_refuted :
    ¬ JuliaLean.Proofs.base.bitarray.Models1Group16.FindMaxVectorContract := by
  intro h
  have hx := (h searchPaddingHeap searchTinyVector searchPaddingReadable).2
  have hp : ¬ searchTinyVector.len.val = 0 := by decide
  rw [if_neg hp] at hx
  have hr : ((JuliaLean.base.bitarray.Models1Group16.findMaxVector searchTinyVector).run
      searchPaddingHeap).1 = .ok (true, int 2) := by decide
  rw [hr] at hx
  have hn : ¬ JuliaLean.Proofs.base.bitarray.Models1Group16.FirstVectorExtreme
      searchPaddingHeap searchTinyVector true true (int 2) := by
    intro hbad
    have hbound := hbad.2.1
    change (2 : Int) ≤ 1 at hbound
    omega
  exact hn hx


theorem Models1G16FindminVector_refuted :
    ¬ JuliaLean.Proofs.base.bitarray.Models1Group16.FindMinVectorContract := by
  intro h
  have hx := (h searchExtraHeap searchTinyVector searchExtraReadable).2
  have hp : ¬ searchTinyVector.len.val = 0 := by decide
  rw [if_neg hp] at hx
  have hr : ((JuliaLean.base.bitarray.Models1Group16.findMinVector searchTinyVector).run
      searchExtraHeap).1 = .ok (false, int 2) := by decide
  rw [hr] at hx
  have hn : ¬ JuliaLean.Proofs.base.bitarray.Models1Group16.FirstVectorExtreme
      searchExtraHeap searchTinyVector false false (int 2) := by
    intro hbad
    have hbound := hbad.2.1
    change (2 : Int) ≤ 1 at hbound
    omega
  exact hn hx
end JuliaLean.ChatGPT.Batch9.Group10



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group10

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray.Models1Group16

theorem Models1G16CountMachineResidue_refuted :
    ¬ JuliaLean.Proofs.base.bitarray.Models1Group16.CountMachineResidue := by
  intro h
  have hv := (h 2 .u8 countAliasHeap countAliasArray (JInt.wrap .u8 0)
    countAliasReadable).2
  change (1 : Int) = 0 at hv
  exact (by decide : (1 : Int) ≠ 0) hv
end JuliaLean.ChatGPT.Batch9.Group10



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray

open JuliaLean.Registry
def entriesFindnext1 : List JuliaLean.Registry.Entry := [
  { id := "bitarrays-count-init-wrap", juliaFile := "base/bitarray.jl", juliaFns := ["count(::BitArray; init)", "bitcount"],
    statement := "count(B; init) returns the same value as count(v; init) on Vector{Bool}, init plus the number of true elements, for every BitInteger type of init.", source := "count docstring (base/reduce.jl:1067-1090); invariant: BitArray behaves as Array{Bool}",
    status := .todo, prop := ``CountAgrees, thm := none, notes := "Statement defect: with init Int64(0) and xs = true :: replicate (2^69 - 1) false, the 2^63-word chunk count wraps negative so bitcount returns zero although the specified count is one; Julia cannot construct this input; require xs.length \u2264 typemax(Int)." },
  { id := "bitarrays-count-any-all", juliaFile := "base/bitarray.jl", juliaFns := ["count(::BitArray)", "any(::BitArray)", "all(::BitArray)"],
    statement := "For valid BitArrays with length less than typemax(Int)/2, count, any, and all agree with the logical bits.", source := "base/bitarray.jl:1439-1447,1715-1745",
    status := .proven, prop := ``Round2.CountAnyAllAgrees, thm := some ``Round2.CountAnyAllAgrees_proven },
  { id := "bitarrays-find", juliaFile := "base/bitarray.jl", juliaFns := ["findnext(::BitArray, ::Integer)", "findprev(::BitArray, ::Integer)", "findnextnot", "findprevnot", "findnext(!, ::BitArray, i)", "findprev(!, ::BitArray, i)"],
    statement := "findnext and findprev (for true, and through findnextnot/findprevnot for false) agree with the generic methods on Vector{Bool} for every Int start, including the BoundsError cases.", source := "findnext/findprev docstrings (base/array.jl); invariant: BitVector behaves as Vector{Bool}",
    status := .todo, prop := ``FindAgrees, thm := none, notes := "Statement defect: with xs = true :: replicate (2^69) false and start = Int64(1), the logical length wraps to one but the 2^63+1-word chunk-header length wraps negative, so the model read throws bounds while findForwardSpec returns some 1; Julia cannot construct this input; require xs.length \u2264 typemax(Int)." }
]
def entriesFindnext2 : List JuliaLean.Registry.Entry := [
  { id := "memsafety-bitarray-vector-loops", juliaFile := "base/bitarray.jl", juliaFns := ["bitcount", "findall", "all", "any", "reverse!", "map!"],
    statement := "Loops derived from a chunk vector's own length access only indices one through that length.", source := "invariant: each loop is over 1:length(B.chunks), base/bitarray.jl:1263-1305,1439-1444,1611-1735",
    status := .todo, prop := ``BitVectorLoopInBounds, thm := none }
]
def entriesFindnext3 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-find-extrema-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["findmax@1620", "findmin@1633", "minimum@1747", "maximum@1748"],
    statement := "findmin and findmax return the correct Boolean extreme and its first index.", source := "obvious invariant; base/bitarray.jl:1620",
    status := .todo, prop := ``FindExtremaAgrees, thm := none, notes := "Statement defect: false for List.replicate (2^64) false, whose modeled native length wraps to zero so findmin/findmax throw before scanning; Julia cannot construct this input, and the statement needs xs.length \u2264 2^63-1." }
]
def entriesFindnext4 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-scalar-extrema-values", juliaFile := "base/bitarray.jl",
    juliaFns := ["minimum(::BitArray)", "maximum(::BitArray)"],
    statement := "Minimum and maximum return the Boolean extrema of all logical elements, reject empty arrays with ArgumentError, and leave packed source storage unchanged.",
    source := "base/bitarray.jl:1724-1748", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64147; see bugs/bitarray-scalar-extrema-values.yaml",
    prop := ``Archive20261102Round6.ScalarExtremaValues, thm := some ``JuliaLean.ChatGPT.Batch4.Group8.BitarrayScalarExtremaValues_refuted }
]
namespace Completion
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

theorem bitcountInitialTypeError : BitcountInitialTypeError := by
  intro N T A R C init B convertInit add remainder convertResult asT initial s final h htype
  simp [bitcountDispatch, bitArrayCountDispatch, h, htype]

end Completion

def entriesFindnext5 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-count-machine-residue", juliaFile := "base/bitarray.jl",
    juliaFns := ["bitcount(::Vector{UInt64}; init::BitInteger)", "_count(identity, ::BitArray, ::Colon, init::BitInteger)"],
    statement := "Counting adds the number of logical true bits to every machine-integer initializer modulo its type width, without mutating storage.",
    source := "base/bitarray.jl:1448-1456", issue := "Searched JuliaLang/julia issues and PRs; matches #64147; see bugs/bitarrays-vec-resize-alias.yaml", status := .refuted,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.CountMachineResidue, thm := some ``JuliaLean.ChatGPT.Batch9.Group10.Models1G16CountMachineResidue_refuted,
    notes := "Counterexample confirmed on Julia 1.13.2 and pinned master. Shared root cause and runtime evidence: bugs/bitarrays-vec-resize-alias.yaml." },
  { id := "bitarray-findnext-machine", juliaFile := "base/bitarray.jl",
    juliaFns := ["findnext(::BitArray, ::BitInteger)"],
    statement := "Forward search over every machine Integer start returns the first logical true position, includes start, preserves the heap, and retains conversion and bounds errors.",
    source := "base/bitarray.jl:1478-1483", issue := "Searched JuliaLang/julia issues and PRs; matches #64147; see bugs/bitarrays-vec-resize-alias.yaml", status := .refuted,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.FindNextMachineContract, thm := some ``JuliaLean.ChatGPT.Batch9.Group10.Models1G16FindnextMachine_refuted,
    notes := "Counterexample confirmed on Julia 1.13.2 and pinned master. Shared root cause and runtime evidence: bugs/bitarrays-vec-resize-alias.yaml." },
  { id := "bitarray-findnext-fixed-machine", juliaFile := "base/bitarray.jl",
    juliaFns := ["findnext(::Fix2{isequal/==,Bool}, ::BitArray, ::BitInteger)"],
    statement := "Bool Fix2 forward search returns the first requested logical value for every machine Integer start and leaves all storage unchanged.",
    source := "base/bitarray.jl:1520-1526", issue := "Searched JuliaLang/julia issues and PRs; matches #64147; see bugs/bitarrays-vec-resize-alias.yaml", status := .refuted,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.FindNextFixedMachineContract, thm := some ``JuliaLean.ChatGPT.Batch9.Group10.Models1G16FindnextFixedMachine_refuted,
    notes := "Counterexample confirmed on Julia 1.13.2 and pinned master. Shared root cause and runtime evidence: bugs/bitarrays-vec-resize-alias.yaml." },
  { id := "bitarray-findprev-machine", juliaFile := "base/bitarray.jl",
    juliaFns := ["findprev(::BitArray, ::BitInteger)"],
    statement := "Backward search includes its start, returns the last true position, and preserves native conversion, nonpositive-start and upper-bounds behavior.",
    source := "base/bitarray.jl:1563-1568", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.FindPrevMachineContract, thm := some ``JuliaLean.ChatGPT.Batch9.Group10.Models1G16FindprevMachine_proven,
    notes := "Machine-type specialization only; full generic row remains blocked. Contracts include readable alias states; map! snapshot semantics are conditional only where documentation warns about shifted overlap." },
  { id := "bitarray-findprev-fixed-machine", juliaFile := "base/bitarray.jl",
    juliaFns := ["findprev(::Fix2{isequal/==,Bool}, ::BitArray, ::BitInteger)"],
    statement := "Bool Fix2 backward search returns the last requested value for every machine start, with exact conversion and bounds error classes.",
    source := "base/bitarray.jl:1596-1602", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.FindPrevFixedMachineContract, thm := some ``JuliaLean.ChatGPT.Batch9.Group10.Models1G16FindprevFixedMachine_proven,
    notes := "Machine-type specialization only; full generic row remains blocked. Contracts include readable alias states; map! snapshot semantics are conditional only where documentation warns about shifted overlap." },
  { id := "bitarray-findmax-vector", juliaFile := "base/bitarray.jl",
    juliaFns := ["findmax(::BitVector)"],
    statement := "Vector maximum returns the largest logical Boolean and its first one-based native index, rejects an empty input with ArgumentError, and leaves the entire heap unchanged.",
    source := "base/bitarray.jl:1620-1631; base/reduce.jl:859-881", issue := "Searched JuliaLang/julia issues and PRs; matches #64147; see bugs/bitarrays-vec-resize-alias.yaml", status := .refuted,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.FindMaxVectorContract, thm := some ``JuliaLean.ChatGPT.Batch9.Group10.Models1G16FindmaxVector_refuted,
    notes := "Counterexample confirmed on Julia 1.13.2 and pinned master. Shared root cause and runtime evidence: bugs/bitarrays-vec-resize-alias.yaml." },
  { id := "bitarray-findmin-vector", juliaFile := "base/bitarray.jl",
    juliaFns := ["findmin(::BitVector)"],
    statement := "Vector minimum returns the smallest logical Boolean and its first one-based native index, preserves every memory/alias, and retains the empty-array ArgumentError.",
    source := "base/bitarray.jl:1633-1648; base/reduce.jl:925-948", issue := "Searched JuliaLang/julia issues and PRs; matches #64147; see bugs/bitarrays-vec-resize-alias.yaml", status := .refuted,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group16.FindMinVectorContract, thm := some ``JuliaLean.ChatGPT.Batch9.Group10.Models1G16FindminVector_refuted,
    notes := "Counterexample confirmed on Julia 1.13.2 and pinned master. Shared root cause and runtime evidence: bugs/bitarrays-vec-resize-alias.yaml." },
  { id := "bitarray-count-initial-type-error", juliaFile := "base/bitarray.jl",
    juliaFns := ["bitcount(Bc::Vector{UInt64}; init::T=0) where T",
      "_count(::typeof(identity), B::BitArray, ::Colon, init)"],
    statement := "Counting reports TypeError when the initializer conversion fails the explicitly typed accumulator check, preserves the conversion's prior effects, and performs no packed-array traversal afterward.",
    source := "base/bitarray.jl:1448-1456", status := .proven,
    prop := ``BitcountInitialTypeError, thm := some ``Completion.bitcountInitialTypeError }
]
end JuliaLean.Proofs.base.bitarray


namespace JuliaLean.Proofs.base.bitarray.Dispatch

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray
namespace Model
export JuliaLean.base.bitarray.Dispatch
  (findNext findPrev findNextFixed findPrevFixed findNextFunction findPrevFunction
    findNextInt findPrevInt)
end Model

/-- Errors raised by an Integer's native conversion remain visible to callers
of every public search overload, including effects performed before the error. -/
def SearchConversionErrors : Prop :=
  ∀ (N : Nat) (I F V : Type) (B : BitArray N) (start : I)
    (toInt : I → BitMutationM I64) (test : F → Bool → BitMutationM V)
    (convertBool : V → BitMutationM Bool) (testf : F)
    (s final : MutableMemory U64) (error : JuliaLean.base.array.Error),
    (toInt start).run s = (.error error, final) →
    (Model.findNext toInt B start).run s = (.error error, final) ∧
    (Model.findPrev toInt B start).run s = (.error error, final) ∧
    (∀ value, (Model.findNextFixed toInt value B start).run s = (.error error, final) ∧
      (Model.findPrevFixed toInt value B start).run s = (.error error, final)) ∧
    (Model.findNextFunction toInt test convertBool testf B start).run s =
      (.error error, final) ∧
    (Model.findPrevFunction toInt test convertBool testf B start).run s =
      (.error error, final)

/-- A failed predicate call at false must be observable even for an invalid
start, since the documented function is evaluated before start validation. -/
def SearchPredicateErrors : Prop :=
  ∀ (N : Nat) (F V : Type) (B : BitArray N) (start : I64)
    (test : F → Bool → BitMutationM V) (convertBool : V → BitMutationM Bool)
    (testf : F) (s final : MutableMemory U64) (error : JuliaLean.base.array.Error),
    (test testf false).run s = (.error error, final) →
    (Model.findNextInt test convertBool testf B start).run s = (.error error, final) ∧
    (Model.findPrevInt test convertBool testf B start).run s = (.error error, final)

theorem SearchConversionErrors_proven : SearchConversionErrors := by
  intro N I F V B start toInt test convertBool testf s final error h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Model.findNext, h]
  · simp [Model.findPrev, h]
  · intro value
    cases value <;> simp [Model.findNextFixed, Model.findPrevFixed,
      Model.findNext, Model.findPrev, h]
  · simp [Model.findNextFunction, h]
  · simp [Model.findPrevFunction, h]

theorem SearchPredicateErrors_proven : SearchPredicateErrors := by
  intro N F V B start test convertBool testf s final error h
  constructor <;>
    simp [Model.findNextInt, Model.findPrevInt,
      JuliaLean.base.bitarray.Dispatch.findNextIntChecked,
      JuliaLean.base.bitarray.Dispatch.findPrevIntChecked,
      bitArrayFindNextInt, bitArrayFindPrevInt,
      JuliaLean.base.bitarray.Dispatch.checkedPredicateBool, h]

def SearchPredicateConversionErrors : Prop :=
  ∀ (N : Nat) (F V : Type) (B : BitArray N) (start : I64)
    (test : F → Bool → BitMutationM V) (convertBool : V → BitMutationM Bool)
    (testf : F) (first : V) (initial tested final : MutableMemory U64)
    (error : JuliaLean.base.array.Error),
    (test testf false).run initial = (.ok first, tested) →
    (convertBool first).run tested = (.error error, final) →
    (Model.findNextFunction pure test convertBool testf B start).run initial =
      (.error error, final) ∧
    (Model.findPrevFunction pure test convertBool testf B start).run initial =
      (.error error, final)

theorem SearchPredicateConversionErrors_proven : SearchPredicateConversionErrors := by
  intro N F V B start test convertBool testf first initial tested final error htest hconvert
  constructor <;>
    simp [Model.findNextFunction, Model.findPrevFunction, Model.findNextInt, Model.findPrevInt,
      JuliaLean.base.bitarray.Dispatch.findNextIntChecked,
      JuliaLean.base.bitarray.Dispatch.findPrevIntChecked,
      bitArrayFindNextInt, bitArrayFindPrevInt,
      JuliaLean.base.bitarray.Dispatch.checkedPredicateBool, htest, hconvert]

def SearchTruePredicateErrors : Prop :=
  ∀ (N : Nat) (F V : Type) (B : BitArray N) (start : I64)
    (test : F → Bool → BitMutationM V) (convertBool : V → BitMutationM Bool)
    (testf : F) (first : V) (firstBool : Bool)
    (initial tested converted final : MutableMemory U64)
    (error : JuliaLean.base.array.Error),
    (test testf false).run initial = (.ok first, tested) →
    (convertBool first).run tested = (.ok firstBool, converted) →
    (test testf true).run converted = (.error error, final) →
    (Model.findNextFunction pure test convertBool testf B start).run initial =
      (.error error, final) ∧
    (Model.findPrevFunction pure test convertBool testf B start).run initial =
      (.error error, final)

theorem SearchTruePredicateErrors_proven : SearchTruePredicateErrors := by
  intro N F V B start test convertBool testf first firstBool initial tested converted final
    error htest hconvert htrue
  constructor <;>
    simp [Model.findNextFunction, Model.findPrevFunction, Model.findNextInt, Model.findPrevInt,
      JuliaLean.base.bitarray.Dispatch.findNextIntChecked,
      JuliaLean.base.bitarray.Dispatch.findPrevIntChecked,
      bitArrayFindNextInt, bitArrayFindPrevInt,
      JuliaLean.base.bitarray.Dispatch.checkedPredicateBool, htest, hconvert, htrue]

def SearchTrueConversionErrors : Prop :=
  ∀ (N : Nat) (F V : Type) (B : BitArray N) (start : I64)
    (test : F → Bool → BitMutationM V) (convertBool : V → BitMutationM Bool)
    (testf : F) (first second : V) (firstBool : Bool)
    (initial tested converted testedTrue final : MutableMemory U64)
    (error : JuliaLean.base.array.Error),
    (test testf false).run initial = (.ok first, tested) →
    (convertBool first).run tested = (.ok firstBool, converted) →
    (test testf true).run converted = (.ok second, testedTrue) →
    (convertBool second).run testedTrue = (.error error, final) →
    (Model.findNextFunction pure test convertBool testf B start).run initial =
      (.error error, final) ∧
    (Model.findPrevFunction pure test convertBool testf B start).run initial =
      (.error error, final)

theorem SearchTrueConversionErrors_proven : SearchTrueConversionErrors := by
  intro N F V B start test convertBool testf first second firstBool initial tested converted
    testedTrue final error htest hconvert htrue hconvertTrue
  constructor <;>
    simp [Model.findNextFunction, Model.findPrevFunction, Model.findNextInt, Model.findPrevInt,
      JuliaLean.base.bitarray.Dispatch.findNextIntChecked,
      JuliaLean.base.bitarray.Dispatch.findPrevIntChecked,
      bitArrayFindNextInt, bitArrayFindPrevInt,
      JuliaLean.base.bitarray.Dispatch.checkedPredicateBool, htest, hconvert, htrue, hconvertTrue]

def SearchLaterPredicateErrors : Prop :=
  SearchPredicateConversionErrors ∧ SearchTruePredicateErrors ∧ SearchTrueConversionErrors

theorem SearchLaterPredicateErrors_proven : SearchLaterPredicateErrors :=
  ⟨SearchPredicateConversionErrors_proven, SearchTruePredicateErrors_proven,
    SearchTrueConversionErrors_proven⟩

/-- If both typed predicate results agree, search uses only the logical extent
after the two calls and conversions. Their effects survive even an invalid start.
Source: base/bitarray.jl:1530-1541,1606-1617
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def SearchConstantPredicateOutcomes : Prop :=
  ∀ (N : Nat) (F V : Type) (B : BitArray N) (start : I64)
    (test : F → Bool → BitMutationM V) (convertBool : V → BitMutationM Bool)
    (testf : F) (first second : V) (matched : Bool)
    (initial testedFalse convertedFalse testedTrue final : MutableMemory U64),
    (test testf false).run initial = (.ok first, testedFalse) →
    (convertBool first).run testedFalse = (.ok matched, convertedFalse) →
    (test testf true).run convertedFalse = (.ok second, testedTrue) →
    (convertBool second).run testedTrue = (.ok matched, final) →
    (Model.findNextFunction pure test convertBool testf B start).run initial =
      ((if start.val ≤ 0 then .error JuliaLean.base.array.Error.bounds
        else if B.len.val < start.val then .ok none
        else .ok (if matched then some start else none)), final) ∧
    (Model.findPrevFunction pure test convertBool testf B start).run initial =
      ((if start.val ≤ 0 then .ok none
        else if B.len.val < start.val then .error JuliaLean.base.array.Error.bounds
        else .ok (if matched then some start else none)), final)

theorem SearchConstantPredicateOutcomes_proven : SearchConstantPredicateOutcomes := by
  intro N F V B start test convertBool testf first second matched
    initial testedFalse convertedFalse testedTrue final hfalse hconvertFalse htrue hconvertTrue
  have hlow : (start ≤ int 0) ↔ start.val ≤ 0 := Iff.rfl
  have hhigh : (B.len < start) ↔ B.len.val < start.val := Iff.rfl
  by_cases hlo : start.val ≤ 0 <;>
    by_cases hhi : B.len.val < start.val <;> cases matched <;>
    simp [Model.findNextFunction, Model.findPrevFunction, Model.findNextInt, Model.findPrevInt,
      JuliaLean.base.bitarray.Dispatch.findNextIntChecked,
      JuliaLean.base.bitarray.Dispatch.findPrevIntChecked,
      bitArrayFindNextInt, bitArrayFindPrevInt,
      JuliaLean.base.bitarray.Dispatch.checkedPredicateBool,
      hfalse, hconvertFalse, htrue, hconvertTrue, hlow, hhigh, hlo, hhi]

end JuliaLean.Proofs.base.bitarray.Dispatch

namespace JuliaLean.Proofs.base.bitarray

def entriesFindnext6 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-search-conversion-errors", juliaFile := "base/bitarray.jl",
    juliaFns := ["findnext(B::BitArray, start::Integer)", "findprev(B::BitArray, start::Integer)",
      "findnext(::Fix2{isequal/==,Bool}, ::BitArray, ::Integer)",
      "findprev(::Fix2{isequal/==,Bool}, ::BitArray, ::Integer)",
      "findnext(::Function, ::BitArray, ::Integer)", "findprev(::Function, ::BitArray, ::Integer)"],
    statement := "Every public packed-array search preserves the exception and prior effects of a failed conversion of its Integer start, independently of array contents and predicate behavior.",
    source := "base/bitarray.jl:1478-1483,1520-1541,1563-1568,1596-1617",
    status := .proven, prop := ``Dispatch.SearchConversionErrors,
    thm := some ``Dispatch.SearchConversionErrors_proven },
  { id := "bitarray-search-predicate-errors", juliaFile := "base/bitarray.jl",
    juliaFns := ["_findnext_int", "_findprev_int"],
    statement := "A failing predicate on false propagates its exception and prior effects for every native start, including starts outside the logical array.",
    source := "base/bitarray.jl:1531-1541,1607-1617",
    status := .proven, prop := ``Dispatch.SearchPredicateErrors,
    thm := some ``Dispatch.SearchPredicateErrors_proven },
  { id := "bitarray-search-later-predicate-errors", juliaFile := "base/bitarray.jl",
    juliaFns := ["findnext(::Function, ::BitArray, ::Integer)",
      "findprev(::Function, ::BitArray, ::Integer)"],
    statement := "For every native start, failure while converting the false predicate result, calling the predicate on true, or converting its true result preserves the exact error and all prior effects in both search directions, before any bounds check.",
    source := "base/bitarray.jl:1530-1541,1606-1617", status := .proven,
    prop := ``Dispatch.SearchLaterPredicateErrors,
    thm := some ``Dispatch.SearchLaterPredicateErrors_proven },
  { id := "bitarray-search-constant-predicate-outcomes", juliaFile := "base/bitarray.jl",
    juliaFns := ["findnext(::Function, ::BitArray, ::Integer)",
      "findprev(::Function, ::BitArray, ::Integer)"],
    statement := "When the predicate's typed results on false and true agree, both search directions preserve all effects of those calls and conversions, return the start exactly when it is in the logical extent and matches, and otherwise return nothing or BoundsError according to their documented start rules without accessing packed storage.",
    source := "base/bitarray.jl:1530-1541,1606-1617", status := .proven,
    prop := ``Dispatch.SearchConstantPredicateOutcomes,
    thm := some ``Dispatch.SearchConstantPredicateOutcomes_proven }
]

end JuliaLean.Proofs.base.bitarray
