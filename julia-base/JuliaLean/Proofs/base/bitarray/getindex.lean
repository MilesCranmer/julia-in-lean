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

namespace JuliaLean.CompletionState4

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


end JuliaLean.CompletionState4

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

/-- An invalid scalar index fails before reading or mutating storage. -/
theorem scalar_invalid_read_write {N : Nat} {X : Type}
    (convert : X → BitMutationM Bool) (B : BitArray N) (x : X) (i : I64)
    (s : State) (hn : 0 ≤ B.len.val) (hi : ¬ (int 1 ≤ i ∧ i ≤ B.len)) :
    (bitArrayGetIndex Round5.Round2.checkBitArrayBounds B i).run s =
      (.error .bounds, s) ∧
    (bitArraySetIndex Round5.Round2.checkBitArrayBounds convert B x i).run s =
      (.error .bounds, s) := by
  constructor <;>
    simp only [bitArrayGetIndex, bitArraySetIndex, shape_run_bind,
      scalar_bounds_run B i s hn, hi, ite_false]

/-- At a valid index, failed conversion is reported before the write. -/
theorem scalar_valid_conversion_error {N : Nat} {X : Type}
    [JuliaLean.base.range.JConvert Bool X] (B : BitArray N) (x : X) (i : I64)
    (e : JuliaLean.base.range.Exc) (s : State)
    (hn : 0 ≤ B.len.val) (hi : int 1 ≤ i ∧ i ≤ B.len)
    (he : JuliaLean.base.range.JConvert.convert (T := Bool) x = .error e) :
    (bitArraySetIndex Round5.Round2.checkBitArrayBounds
      Round5.Round2.convertBoolMutation B x i).run s =
      (.error (Round5.Round2.mutationErrorOfRange e), s) := by
  simp only [bitArraySetIndex, shape_run_bind, scalar_bounds_run B i s hn,
    hi, and_self, ite_true, scalar_conversion_error x e s he]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def scalarObservation {N : Nat} (B : BitArray N) (s : State) (i : I64)
    (converted : JuliaLean.base.range.JlX Bool)
    (rd : Id (Except Error Bool × MutableMemory U64)) (wr : Id (Except Error (BitArray N) × MutableMemory U64)) : Prop :=
  if int 1 ≤ i ∧ i ≤ B.len then
    rd.1 = .ok (bitAt s B (i.val.toNat - 1)) ∧
    (Round5.Round2.ScalarIndexAgrees.match_1 (fun _ _ => Prop) converted wr.1
      (fun value _ =>
        bitValues wr.2 B = (bitValues s B).set (i.val.toNat - 1) value ∧
        Round5.Round2.PackedInvariant wr.2 B)
      (fun _ _ => wr.2 = s)
      (fun _ _ => False))
  else rd.1 = .error .bounds ∧ wr.1 = .error .bounds ∧ wr.2 = s

theorem scalarObservation_invalid {N : Nat} (B : BitArray N) (s : State) (i : I64)
    (converted : JuliaLean.base.range.JlX Bool)
    (rd : Id (Except Error Bool × MutableMemory U64)) (wr : Id (Except Error (BitArray N) × MutableMemory U64))
    (hi : ¬ (int 1 ≤ i ∧ i ≤ B.len))
    (hr : rd = (.error .bounds, s)) (hw : wr = (.error .bounds, s)) :
    scalarObservation B s i converted rd wr := by
  simp only [scalarObservation, hi, ite_false, hr, hw]
  exact ⟨True.intro, True.intro, True.intro⟩

theorem scalarObservation_error {N : Nat} (B : BitArray N) (s : State) (i : I64)
    (rd : Id (Except Error Bool × MutableMemory U64)) (wr : Id (Except Error (BitArray N) × MutableMemory U64))
    (e : JuliaLean.base.range.Exc) (e' : Error)
    (hi : int 1 ≤ i ∧ i ≤ B.len)
    (hr : rd = (.ok (bitAt s B (i.val.toNat - 1)), s)) (hw : wr = (.error e', s)) :
    scalarObservation B s i (.error e) rd wr := by
  simp only [scalarObservation, hi, ite_true, hr, hw]
  exact ⟨True.intro, True.intro⟩

theorem scalarObservation_ok {N : Nat} (B : BitArray N) (s : State) (i : I64)
    (rd : Id (Except Error Bool × MutableMemory U64)) (wr : Id (Except Error (BitArray N) × MutableMemory U64))
    (value : Bool) (B' : BitArray N) (s' : State)
    (hi : int 1 ≤ i ∧ i ≤ B.len)
    (hr : rd = (.ok (bitAt s B (i.val.toNat - 1)), s)) (hw : wr = (.ok B', s'))
    (hb : bitValues s' B = (bitValues s B).set (i.val.toNat - 1) value)
    (hp : Round5.Round2.PackedInvariant s' B) :
    scalarObservation B s i (.ok value) rd wr := by
  simp only [scalarObservation, hi, ite_true, hr, hw]
  exact ⟨True.intro, hb, hp⟩

theorem scalarObservation_valid {N : Nat} (B : BitArray N) (s : State) (i : I64)
    (converted : JuliaLean.base.range.JlX Bool)
    (rd : Id (Except Error Bool × MutableMemory U64)) (wr : Id (Except Error (BitArray N) × MutableMemory U64))
    (hi : int 1 ≤ i ∧ i ≤ B.len)
    (hr : rd = (.ok (bitAt s B (i.val.toNat - 1)), s))
    (he : ∀ e, converted = .error e → ∃ e', wr = (.error e', s))
    (hv : ∀ value, converted = .ok value → ∃ B' s', wr = (.ok B', s') ∧
      bitValues s' B = (bitValues s B).set (i.val.toNat - 1) value ∧
      Round5.Round2.PackedInvariant s' B) :
    scalarObservation B s i converted rd wr := by
  cases hc : converted with
  | error e =>
    obtain ⟨e', hw⟩ := he e hc
    exact scalarObservation_error B s i rd wr e e' hi hr hw
  | ok value =>
    obtain ⟨B', s', hw, hb, hp⟩ := hv value hc
    exact scalarObservation_ok B s i rd wr value B' s' hi hr hw hb hp

theorem scalar_public_read_initial_at {N : Nat} (xs : List Bool) (dims : List I64) (i : I64)
    (hn : xs.length ≤ 9223372036854775807)
    (hi : int 1 ≤ i ∧ i ≤ int xs.length) :
    let B : BitArray N := ⟨0, int xs.length, dims⟩
    let s := initWords (encodeBits xs)
    (bitArrayGetIndex Round5.Round2.checkBitArrayBounds B i).run s =
      (.ok (bitAt s B (i.val.toNat - 1)), s) := by
  let B : BitArray N := ⟨0, int xs.length, dims⟩
  let s := initWords (encodeBits xs)
  have hnonneg : 0 ≤ (int xs.length).val := by
    rw [packedInt_val xs.length hn]
    omega
  obtain ⟨hj, hei⟩ := scalar_valid_index_coordinates xs i hn hi
  have hraw := scalar_read_initial xs (i.val.toNat - 1) hn hj
  have hraw' := (congrArg (fun k : I64 => (unsafeBitGetIndex 0 k).run s) hei).trans hraw
  have hbit := scalar_bitAt_initial (N := N) xs dims (i.val.toNat - 1) hn hj
  exact (scalar_public_read_valid B i s hnonneg hi).trans
    (hraw'.trans (congrArg (fun b : Bool => ((.ok b : Except Error Bool), s)) hbit.symm))

theorem scalar_public_write_initial_at {N : Nat} (xs : List Bool) (dims : List I64) (i : I64)
    {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X) (value : Bool)
    (hn : xs.length ≤ 9223372036854775807)
    (hi : int 1 ≤ i ∧ i ≤ int xs.length)
    (he : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok value) :
    let B : BitArray N := ⟨0, int xs.length, dims⟩
    let s := initWords (encodeBits xs)
    (bitArraySetIndex Round5.Round2.checkBitArrayBounds
      Round5.Round2.convertBoolMutation B x i).run s =
        (.ok B, initWords (encodeBits (xs.set (i.val.toNat - 1) value))) := by
  let B : BitArray N := ⟨0, int xs.length, dims⟩
  let s := initWords (encodeBits xs)
  have hnonneg : 0 ≤ (int xs.length).val := by
    rw [packedInt_val xs.length hn]
    omega
  obtain ⟨hj, hei⟩ := scalar_valid_index_coordinates xs i hn hi
  have hraw := scalar_write_initial xs (i.val.toNat - 1) value hn hj
  have hraw' := (congrArg (fun k : I64 => (unsafeBitSetIndex 0 value k).run s) hei).trans hraw
  exact scalar_public_write_valid B x i value s _ hnonneg hi he hraw'

theorem scalar_set_initial_bits {N : Nat} (xs : List Bool) (dims : List I64)
    (i : Nat) (value : Bool) (hn : xs.length ≤ 9223372036854775807) :
    let B : BitArray N := ⟨0, int xs.length, dims⟩
    bitValues (initWords (encodeBits (xs.set i value))) B =
      (bitValues (initWords (encodeBits xs)) B).set i value := by
  have hp := scalar_bits_initial (N := N) (xs.set i value) dims
    (by simpa only [List.length_set] using hn)
  simp only [List.length_set] at hp
  dsimp only
  rw [hp, scalar_bits_initial xs dims hn]

theorem scalar_set_initial_invariant {N : Nat} (xs : List Bool) (dims : List I64)
    (i : Nat) (value : Bool) (hn : xs.length ≤ 9223372036854775807) :
    Round5.Round2.PackedInvariant (initWords (encodeBits (xs.set i value)))
      (⟨0, int xs.length, dims⟩ : BitArray N) := by
  have hp := scalar_initial_invariant (N := N) (xs.set i value) dims
    (by simpa only [List.length_set] using hn)
  simpa only [List.length_set] using hp
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096

theorem scalarFrozenFromObservation {N : Nat} (xs : List Bool) (dims : List I64) (i : I64)
    {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X)
    (hr : dims.length = N) (hs : dims.foldl (· * ·) (int 1) = int xs.length) :
    let B : BitArray N := ⟨0, int xs.length, dims⟩
    let s := initWords (encodeBits xs)
    scalarObservation B s i (JuliaLean.base.range.JConvert.convert (T := Bool) x)
      ((bitArrayGetIndex Round5.Round2.checkBitArrayBounds B i).run s)
      ((bitArraySetIndex Round5.Round2.checkBitArrayBounds
        Round5.Round2.convertBoolMutation B x i).run s) →
      Round5.Round2.ScalarIndexAgrees xs dims i x hr hs := by
  exact fun h => h
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Scalar access and conversion obey the frozen contract at every rank. -/
theorem BitarraysScalarIndex_proven :
    JuliaLean.Proofs.base.bitarray.Round5.ScalarIndexAgrees := by
  intro N xs dims i X _ x hRank _ hSize _ hbound
  have hn : xs.length ≤ 9223372036854775807 := by
    change xs.length < 4611686018427387903 at hbound
    omega
  have hnonneg : 0 ≤ (int xs.length).val := by
    rw [packedInt_val xs.length hn]
    omega
  let B : BitArray N := ⟨0, int xs.length, dims⟩
  let s := initWords (encodeBits xs)
  let rd := (bitArrayGetIndex Round5.Round2.checkBitArrayBounds B i).run s
  let wr := (bitArraySetIndex Round5.Round2.checkBitArrayBounds
    Round5.Round2.convertBoolMutation B x i).run s
  apply scalarFrozenFromObservation xs dims i x hRank hSize
  change scalarObservation B s i (JuliaLean.base.range.JConvert.convert (T := Bool) x) rd wr
  by_cases hi : int 1 ≤ i ∧ i ≤ B.len
  · apply scalarObservation_valid B s i _ rd wr hi
    · exact scalar_public_read_initial_at xs dims i hn hi
    · intro e he
      exact ⟨Round5.Round2.mutationErrorOfRange e,
        scalar_valid_conversion_error B x i e s hnonneg hi he⟩
    · intro value he
      refine ⟨B, initWords (encodeBits (xs.set (i.val.toNat - 1) value)), ?_, ?_, ?_⟩
      · exact scalar_public_write_initial_at xs dims i x value hn hi he
      · exact scalar_set_initial_bits xs dims (i.val.toNat - 1) value hn
      · exact scalar_set_initial_invariant xs dims (i.val.toNat - 1) value hn
  · have h := scalar_invalid_read_write Round5.Round2.convertBoolMutation
      B x i s hnonneg hi
    exact scalarObservation_invalid B s i _ rd wr hi h.1 h.2
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace JuliaLean.ChatGPT.Batch4.Group8

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4

set_option maxHeartbeats 1000000

/-- Every nonpositive scalar read fails with a bounds error and preserves storage. -/
theorem group8_mutableGet_nonpositive {α : Type} (s : MutableMemory α)
    (handle : Nat) (index : I64) (hi : index.val ≤ 0) :
    (mutableGet handle index).run s = (.error .bounds, s) := by
  cases ha : s.arrays[handle]? with
  | none =>
    simp only [mutableGet, shape_run_bind, shape_vector_run, ha]
  | some a =>
    have hbad : ¬ (1 ≤ index.val ∧ index ≤ a.size) := by omega
    simp only [mutableGet, shape_run_bind, shape_vector_run, ha, hbad,
      decide_false, Bool.not_false, ite_true]
    rfl
end JuliaLean.ChatGPT.Batch4.Group8
end

section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace JuliaLean.ChatGPT.Batch4.Group8

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.Archive20261102Round6

/-- Advancing the chunk quotient by one never wraps a native integer. -/
theorem iteration_chunk_address_value (i : I64) :
    (div64 i + int 1).val = i.val / 64 + 1 := by
  change wrapInt .i64 ((div64 i).val + 1) = _
  rw [scalar_div64_val]
  apply wrapInt_of_inRange
  have hb := i.property
  change -9223372036854775808 ≤ i.val ∧ i.val ≤ 9223372036854775807 at hb
  change -9223372036854775808 ≤ i.val / 64 + 1 ∧
    i.val / 64 + 1 ≤ 9223372036854775807
  omega

/-- A nonnegative iteration state names its one-based physical chunk. -/
theorem iteration_chunk_address (i : I64) (hi : 0 ≤ i.val) :
    div64 i + int 1 = int ((i.val.toNat / 64 + 1 : Nat) : Int) := by
  have hb := i.property
  change -9223372036854775808 ≤ i.val ∧ i.val ≤ 9223372036854775807 at hb
  have hfit : i.val.toNat / 64 + 1 ≤ 9223372036854775807 := by omega
  apply Subtype.ext
  rw [iteration_chunk_address_value, packedInt_val _ hfit]
  omega

/-- The low six native bits agree with the natural remainder. -/
theorem iteration_bit_address (i : I64) (hi : 0 ≤ i.val) :
    mod64 i = int ((i.val.toNat % 64 : Nat) : Int) := by
  apply Subtype.ext
  rw [scalar_mod64_val, packedInt_val _ (by omega)]
  omega

/-- A successful primitive read exposes the independent division/parity bit value. -/
theorem iteration_observe_word {N : Nat} (s : State) (b : BitArray N)
    (i : I64) (word : U64) (hi : 0 ≤ i.val)
    (hw : (s.contents b.chunks)[i.val.toNat / 64]? = some (some word)) :
    (and_int word (shl_int (u64 1) (mod64 i)) != u64 0) = storedBit s b i.val.toNat := by
  rw [iteration_bit_address i hi]
  apply (scalar_mask_test_ofNat word (i.val.toNat % 64) (Nat.mod_lt _ (by decide))).trans
  simp only [storedBit, hw, Option.getD_some, packedBit]
  exact Nat.testBit_eq_decide_div_mod_eq

/-- Negative states reject before any successful physical read. -/
theorem iteration_negative {N : Nat} (s : State) (b : BitArray N) (i : I64)
    (hb : 0 ≤ b.len.val) (hi : i.val < 0) :
    (bitArrayIterate b i).run s = (.error .bounds, s) := by
  have hbefore : ¬ i ≥ b.len := by
    change ¬ b.len.val ≤ i.val
    omega
  have hnonpos : (div64 i + int 1).val ≤ 0 := by
    rw [iteration_chunk_address_value]
    omega
  have hr := group8_mutableGet_nonpositive s b.chunks (div64 i + int 1) hnonpos
  simp only [bitArrayIterate, hbefore, ite_false, shape_run_bind, hr]

/-- Iteration at or beyond the logical end terminates without touching storage. -/
theorem iteration_ended {N : Nat} (s : State) (b : BitArray N) (i : I64)
    (hi : b.len.val ≤ i.val) :
    (bitArrayIterate b i).run s = (.ok none, s) := by
  have hge : i ≥ b.len := hi
  simp only [bitArrayIterate, hge, ite_true, shape_run_pure]

/-- A valid intermediate state reads exactly one logical bit and advances once. -/
theorem iteration_inside {N : Nat} (s : State) (b : BitArray N) (i : I64)
    (hv : s.validVector b.chunks) (hlen : 0 ≤ b.len.val)
    (hcover : (b.len.val.toNat + 63) / 64 ≤ (s.contents b.chunks).length)
    (hassigned : ∀ cell ∈ s.contents b.chunks, cell.isSome = true)
    (hi : 0 ≤ i.val) (hbefore : i.val < b.len.val) :
    (bitArrayIterate b i).run s =
      (.ok (some (storedBit s b i.val.toNat, int (i.val + 1))), s) := by
  have hk : i.val.toNat / 64 < (s.contents b.chunks).length := by omega
  obtain ⟨word, hw⟩ := iteration_assigned_word (s.contents b.chunks) (i.val.toNat / 64) hk hassigned
  have hr := group8_mutableGet_of_contents s b.chunks (i.val.toNat / 64) word hv hw
  rw [← iteration_chunk_address i hi] at hr
  have hm := iteration_observe_word s b i word hi hw
  have hnot : ¬ i ≥ b.len := by
    change ¬ b.len.val ≤ i.val
    omega
  simp only [bitArrayIterate, hnot, ite_false, shape_run_bind, hr, shape_run_pure, hm]
  rfl

/-- Full native-state iteration, including aliases, unread tail bits, and negative states. -/
theorem BitarrayBitArrayIteratorYields_proven : JuliaLean.Proofs.base.bitarray.Archive20261102Round6.BitArrayIterationFull := by
  intro N s b i hv
  rcases hv with ⟨hvalid, hlen, _hrank, _hdims, _hshape, hcover, hassigned, _hmem⟩
  dsimp only
  by_cases hi : i.val < 0
  · rw [iteration_negative s b i hlen hi]
    simp only [hi, ite_true, and_self]
  · by_cases hb : i.val < b.len.val
    · rw [iteration_inside s b i hvalid hlen hcover hassigned (by omega) hb]
      simp only [hi, hb, ite_false, ite_true, and_self]
    · rw [iteration_ended s b i (by omega)]
      simp only [hi, hb, ite_false, and_self]
end JuliaLean.ChatGPT.Batch4.Group8
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

/-- The stored input length supplies the needed native square-product bound. -/
theorem mtx_square_bounds (B : BitMatrix) (n : Nat) (hinput : MatrixInput B n n) :
    n < 9223372036854775807 ∧ n * n ≤ 9223372036854775807 := by
  have hb := B.len.property
  change -9223372036854775808 ≤ B.len.val ∧ B.len.val ≤ 9223372036854775807 at hb
  rw [hinput.2.2.2] at hb
  have hn : n ≤ 9223372036854775807 := by
    have h := hinput.1
    change (n : Int) ≤ 9223372036854775807 at h
    omega
  have hp : n * n ≤ 9223372036854775807 := by omega
  refine ⟨?_, hp⟩
  by_cases h : n < 9223372036854775807
  · exact h
  · have he : n = 9223372036854775807 := by omega
    rw [he] at hp
    omega
end JuliaLean.ChatGPT.Batch5.Group4



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch5.Group4

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2
open JuliaLean.Proofs.base.bitarray.Archive20261102Round6

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Every bounded removed slice still has a native length. -/
theorem spc_slice_length (xs : List Bool) (r : BitRange) :
    (spliceSliceList xs r).length ≤ xs.length := by
  unfold spliceSliceList
  split
  · simp only [List.length_nil, Nat.zero_le]
  · simp only [List.length_take, List.length_drop]
    omega

/-- The slice callback is exact before the mutation suffix of splice begins. -/
theorem spc_slice_callback (xs : List Bool) (r : BitRange) (s : State)
    (hn : xs.length ≤ 9223372036854775807) :
    ((do
      let values := spliceSliceList (bitValues (initWords (encodeBits xs)) (vectorBits xs)) r
      makeBitVector values) : BitMutationM BitVector).run s =
      (.ok (⟨s.arrays.length, int (spliceSliceList xs r).length,
        [int (spliceSliceList xs r).length]⟩ : BitVector),
      shiftFreshHeap s ((encodeBits (spliceSliceList xs r)).map some)) := by
  have hvalues := scalar_bits_initial (N := 1) xs [int xs.length] hn
  change bitValues (initWords (encodeBits xs)) (vectorBits xs) = xs at hvalues
  rw [hvalues]
  exact spc_makeBitVector_run s _ (Nat.le_trans (spc_slice_length xs r) hn)
end JuliaLean.ChatGPT.Batch5.Group4



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch5.Group4

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2
open JuliaLean.Proofs.base.bitarray.Archive20261102Round6

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- A valid vector's visible cell count equals its nonnegative native header. -/
theorem spc_valid_length (s : State) (handle : Nat) (hv : s.validVector handle) :
    (s.contents handle).length ≤ 9223372036854775807 ∧
      (mutableLength handle).run s = (.ok (int (s.contents handle).length), s) := by
  cases ha : s.arrays[handle]? with
  | none => simp only [MutableMemory.validVector, ha] at hv
  | some a =>
    cases hm : s.memories[a.reference.1]? with
    | none => simp only [MutableMemory.validVector, ha, hm] at hv
    | some slots =>
      have hv' : 0 ≤ a.size.val ∧ 1 ≤ a.reference.2.val ∧
          a.reference.2.val - 1 + a.size.val ≤ (slots.length : Int) ∧
          slots.length < 2 ^ 63 := by
        simpa only [MutableMemory.validVector, ha, hm] using hv
      have hb := a.size.property
      change -9223372036854775808 ≤ a.size.val ∧ a.size.val ≤ 9223372036854775807 at hb
      have hcontents : (s.contents handle).length = a.size.val.toNat := by
        simp only [MutableMemory.contents, ha, hm, Option.getD_some,
          List.length_take, List.length_drop]
        omega
      have he : int (s.contents handle).length = a.size := by
        apply Subtype.ext
        rw [packedInt_val _ (by rw [hcontents]; omega), hcontents]
        omega
      refine ⟨by rw [hcontents]; omega, ?_⟩
      simp only [mutableLength, shape_run_bind, shape_vector_run, ha, shape_run_pure, he]

/-- The exact physical word selected by a one-based chunk index. -/
def spc_visible_word (s : State) (handle : Nat) (i : I64) : U64 :=
  ((s.contents handle)[i.val.toNat - 1]?.getD none).getD (u64 0)

/-- Every enumerated initialized chunk of a valid vector is a successful pure read. -/
theorem spc_valid_read (s : State) (handle : Nat) (hv : s.validVector handle)
    (assigned : ∀ cell ∈ s.contents handle, cell.isSome = true)
    (i : I64) (hi : i ∈ intRange (int 1) (int (s.contents handle).length)) :
    (mutableGet handle i).run s = (.ok (spc_visible_word s handle i), s) := by
  have hlen := (spc_valid_length s handle hv).1
  rw [packedObserve_intRange _ hlen] at hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  have hbound := List.mem_range.mp hj
  obtain ⟨word, hw⟩ := JuliaLean.ChatGPT.Batch4.Group8.iteration_assigned_word
    (s.contents handle) j hbound assigned
  have hind : (int ((j + 1 : Nat) : Int)).val.toNat - 1 = j := by
    rw [packedInt_val _ (by omega), Int.toNat_natCast]
    omega
  have hword : spc_visible_word s handle (int ((j + 1 : Nat) : Int)) = word := by
    simp only [spc_visible_word, hind, hw, Option.getD_some]
  rw [hword]
  exact JuliaLean.ChatGPT.Batch4.Group8.group8_mutableGet_of_contents s handle j word hv hw

/-- A finite Boolean observation agrees with its stream inside the logical
    extent and uses false outside it. -/
theorem spc_observed_getD (f : Nat → Bool) (n i : Nat) :
    ((List.range n).map f).getD i false = if i < n then f i else false := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hi : i < n
  · rw [List.getElem?_eq_getElem (by simpa only [List.length_map, List.length_range] using hi),
      Option.getD_some, List.getElem_map, List.getElem_range, if_pos hi]
  · rw [List.getElem?_eq_none (by simp only [List.length_map, List.length_range]; omega),
      Option.getD_none, if_neg hi]

/-- Canonical padding identifies each physical word with the packer of the
    logical observation, including any extra all-zero chunks. -/
theorem spc_padded_word (s : State) (a : BitVector) (ha : ValidIterationStorage s a)
    (hpad : ∀ i : Nat, a.len.val.toNat ≤ i → i < (s.contents a.chunks).length*64 →
      storedBit s a i = false)
    (j : Nat) (hj : j < (s.contents a.chunks).length) :
    spc_visible_word s a.chunks (int ((j+1 : Nat) : Int)) =
      packedPrefix ((List.range a.len.val.toNat).map (storedBit s a)) j 64 := by
  have hlen := (spc_valid_length s a.chunks ha.1).1
  have hindex : (int ((j+1 : Nat) : Int)).val.toNat-1 = j := by
    rw [packedInt_val _ (by omega), Int.toNat_natCast]
    omega
  simp only [spc_visible_word, hindex]
  apply packedBit_ext
  intro k hk
  rw [packedWord_bit _ j k hk]
  have hdiv : (j*64+k)/64 = j := by omega
  have hmod : (j*64+k)%64 = k := by omega
  have hbit : packedBit (((s.contents a.chunks)[j]?.getD none).getD (u64 0)) k =
      storedBit s a (j*64+k) := by
    simp only [storedBit, hdiv, hmod, packedBit]
    exact Nat.testBit_eq_decide_div_mod_eq
  rw [hbit, spc_observed_getD]
  by_cases hi : j*64+k < a.len.val.toNat
  · rw [if_pos hi]
  · rw [if_neg hi]
    exact hpad _ (by omega) (by omega)
end JuliaLean.ChatGPT.Batch5.Group4



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray.Models1Group15

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.base.bitarray.Models1Group15

/-- Scalar reading is read-only on every heap. Both native public bounds
checks reject indices before accessing chunk storage, even if the chunk
handle is absent. Negative rank-one lengths, including push overflow states,
retain the native unsigned-axis behavior instead of an invented signed check.
Bool setter failures are nonmutating and successful setters return the same
BitArray header. The raw-store frame is retained on every setter run; no exact
chunk-count premise is used.
Julia source: base/bitarray.jl:668-671,688-692 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/abstractarray.jl:1306-1310,1442-1446;
source bounds-order and mutation invariants. The setter claim is Bool-only. -/
def ScalarBoundsAndState : Prop :=
  ∀ (N : Nat) (B : BitArray N) (i : I64) (x : Bool) (s : MutableMemory U64),
    let read := (JuliaLean.base.bitarray.Models1Group15.getIndex B i).run s
    let write := (JuliaLean.base.bitarray.Models1Group15.setIndexBool B x i).run s
    read.2 = s ∧
    (ScalarIndexAccepted B i = false →
      read.1 = .error .bounds ∧ write.1 = .error .bounds ∧ write.2 = s) ∧
    (match write.1 with | .ok returned => returned = B | .error _ => write.2 = s) ∧
    DestinationFrame s write.2 B.chunks

/-- Every signed scalar index receives the native bounds outcome or the actual
stored bit at the machine-wrapped address. The physical chunk vector is
machine-bounded, but its length may be smaller or larger than the logical
BitArray length after alias resizing. Negative stored lengths are included:
rank-one unchecked axes may accept indices which higher ranks reject. Accepted
indices whose backing chunk has disappeared give the model's explicit bounds
obligation error. An unassigned raw-store marker gives the existing boundary's
undefinedReference outcome; this is not a claim that initialized Julia UInt64
storage can contain a Julia reference error. All reads preserve every alias.
Julia source: base/bitarray.jl:122,661-671 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/abstractarray.jl:1306-1310; doc/src/manual/arrays.md:1236-1238. -/
def ScalarGetIndexValues : Prop :=
  ∀ (N : Nat) (B : BitArray N) (i : I64) (s : MutableMemory U64),
    s.validVector B.chunks →
    let result := (JuliaLean.base.bitarray.Models1Group15.getIndex B i).run s
    let address := WrappedZeroBasedScalar i
    let chunk := address / 64 + 1
    result.2 = s ∧
    if ScalarIndexAccepted B i = false then result.1 = .error .bounds
    else if chunk < 1 then result.1 = .error .bounds
    else match (s.contents B.chunks)[(chunk - 1).toNat]? with
      | none => result.1 = .error .bounds
      | some none => result.1 = .error .undefinedReference
      | some (some word) => result.1 = .ok
          (decide ((word.val / (2 : Int) ^ (address % 64).toNat) % 2 = 1))

/-- A successful Bool scalar assignment changes exactly the requested stored
bit, returns the input BitArray, preserves all other physical bits/cells and
headers, and is visible through every overlapping physical alias. Native
bounds are checked before storage access, including unchecked negative
rank-one axes. Missing backing chunks or unassigned raw-store cells fail
without mutation. All Int indices, wrapped negative lengths and chunk-count
mismatches after alias shrinkage/growth are included; unused dimensions are free.
Julia source: base/bitarray.jl:122,675-692 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/abstractarray.jl:1442-1446;
doc/src/manual/arrays.md:1236-1238. Useful partial Bool specialization only. -/
def ScalarSetIndexBoolValues : Prop :=
  ∀ (N : Nat) (B : BitArray N) (i : I64) (x : Bool) (s : MutableMemory U64),
    s.validVector B.chunks →
    let result := (JuliaLean.base.bitarray.Models1Group15.setIndexBool B x i).run s
    let address := WrappedZeroBasedScalar i
    let chunk := address / 64 + 1
    if ScalarIndexAccepted B i = false then result.1 = .error .bounds ∧ result.2 = s
    else if chunk < 1 then result.1 = .error .bounds ∧ result.2 = s
    else match (s.contents B.chunks)[(chunk - 1).toNat]? with
      | none => result.1 = .error .bounds ∧ result.2 = s
      | some none => result.1 = .error .undefinedReference ∧ result.2 = s
      | some (some _) => result.1 = .ok B ∧
          ∃ (header : MutableVector) (word : U64), s.arrays[B.chunks]? = some header ∧
            SingleStoredBitWrite s result.2 header.reference.1
              ((header.reference.2.val - 1).toNat + (chunk - 1).toNat)
              (address % 64) x word

/-- Return-valued native chunk setter: every signed chunk index and shift count
is included. An invalid chunk index or unreadable raw cell stops before writes;
a successful call returns precisely the updated stored UInt64. Negative or
at-least-64 shift counts set no bit of the UInt64(1) mask and leave the word
unchanged. The guarantee is expressed by mathematical bit observations, not
by copying the implementation's OR/AND/shift expression.
Julia source: base/bitarray.jl:680-686 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Internal return-value and physical-write invariant. -/
def UnsafeSetIndexAtReturnsWord : Prop :=
  ∀ (chunks : Nat) (x : Bool) (wordIndex bitIndex : I64) (s : MutableMemory U64)
    (header : MutableVector), s.validVector chunks →
    s.arrays[chunks]? = some header →
    let result := (JuliaLean.base.bitarray.Models1Group15.unsafeSetIndexAt
      chunks x wordIndex bitIndex).run s
    if wordIndex.val < 1 ∨ header.size.val < wordIndex.val then
      result.1 = .error .bounds ∧ result.2 = s
    else match (s.contents chunks)[(wordIndex.val - 1).toNat]? with
      | none => result.1 = .error .bounds ∧ result.2 = s
      | some none => result.1 = .error .undefinedReference ∧ result.2 = s
      | some (some _) => ∃ word : U64, result.1 = .ok word ∧
          SingleStoredBitWrite s result.2 header.reference.1
            ((header.reference.2.val - 1).toNat + (wordIndex.val - 1).toNat)
            bitIndex.val x word

/-- The scalar unsafe setter forwards its helper's actual UInt64 return, and
changes only the addressed bit at the machine-wrapped one-based location.
The whole signed-index domain is included: invalid physical chunk addresses
report explicit boundary errors, while typemin's wrapped predecessor is not
silently replaced by an unbounded negative index.
Julia source: base/bitarray.jl:122,675-686 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Internal return-value, machine-address and physical-write invariant. -/
def UnsafeSetIndexReturnsWord : Prop :=
  ∀ (chunks : Nat) (x : Bool) (i : I64) (s : MutableMemory U64)
    (header : MutableVector), s.validVector chunks →
    s.arrays[chunks]? = some header →
    let address := WrappedZeroBasedScalar i
    let chunk := address / 64 + 1
    let result := (JuliaLean.base.bitarray.Models1Group15.unsafeSetIndex chunks x i).run s
    if chunk < 1 ∨ header.size.val < chunk then
      result.1 = .error .bounds ∧ result.2 = s
    else match (s.contents chunks)[(chunk - 1).toNat]? with
      | none => result.1 = .error .bounds ∧ result.2 = s
      | some none => result.1 = .error .undefinedReference ∧ result.2 = s
      | some (some _) => ∃ word : U64, result.1 = .ok word ∧
          SingleStoredBitWrite s result.2 header.reference.1
            ((header.reference.2.val - 1).toNat + (chunk - 1).toNat)
            (address % 64) x word
end JuliaLean.Proofs.base.bitarray.Models1Group15



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.Models1Group15

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem sp_mutableSet_failure (s : MutableMemory U64) (a : Nat) (word : U64) (i : I64) :
    match ((mutableSet a word i).run s).1 with
    | .ok _ => True
    | .error _ => ((mutableSet a word i).run s).2 = s := by
  cases ha : s.arrays[a]? with
  | none => simp only [sp_mutableSet_run, ha]
  | some header =>
      by_cases hb : 1 ≤ i.val ∧ i.val ≤ header.size.val
      · simp only [sp_mutableSet_run, ha, hb, and_self, ite_true]
        cases hm : s.memories[header.reference.1]? with
        | none => rfl
        | some slots =>
            by_cases hp : 1 ≤ (header.reference.2 + i - one).val ∧
                (header.reference.2 + i - one).val ≤ (slots.length : Int)
            · simp only [hp, and_self, ite_true]
            · simp only [hp, and_self, ite_false]
      · simp only [sp_mutableSet_run, ha, hb, ite_false]

theorem sp_internalRead_readonly (s : MutableMemory U64) (a : Nat) (i : I64) :
    ((unsafeBitGetIndex a i).run s).2 = s := by
  have hr := sp_mutableGet_readonly s a (getChunksId i).1
  rcases hg : (mutableGet a (getChunksId i).1).run s with ⟨res, after⟩
  rw [hg] at hr
  dsimp only at hr
  subst after
  simp only [unsafeBitGetIndex, stateExcept_bind, hg]
  cases res <;> rfl

theorem sp_internalWrite_frame (s : MutableMemory U64) (a : Nat) (x : Bool) (i : I64) :
    DestinationFrame s ((unsafeBitSetIndex a x i).run s).2 a ∧
    (match ((unsafeBitSetIndex a x i).run s).1 with
     | .ok _ => True
     | .error _ => ((unsafeBitSetIndex a x i).run s).2 = s) := by
  have hr := sp_mutableGet_readonly s a (getChunksId i).1
  rcases hg : (mutableGet a (getChunksId i).1).run s with ⟨res, after⟩
  rw [hg] at hr
  dsimp only at hr
  subst after
  simp only [unsafeBitSetIndex, unsafeBitSetIndexAt, stateExcept_bind, hg]
  cases res with
  | error e => exact ⟨sp_frame_refl s a, rfl⟩
  | ok word => exact ⟨sp_mutableSet_frame s a _ _, sp_mutableSet_failure s a _ _⟩

theorem Models1G15ScalarBoundsState_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group15.ScalarBoundsAndState := by
  intro N B i x s
  dsimp only
  have hr := sp_internalRead_readonly s B.chunks i
  have hw := sp_internalWrite_frame s B.chunks x i
  simp only [JuliaLean.base.bitarray.Models1Group15.getIndex,
    JuliaLean.base.bitarray.Models1Group15.setIndexBool, bitArrayGetIndex,
    bitArraySetIndex, stateExcept_bind, sp_nativeBounds_run]
  cases hc : ScalarIndexAccepted B i
  · simp only [Bool.false_eq_true, ite_false, implies_true, and_self, true_and]
    exact sp_frame_refl s B.chunks
  · simp only [ite_true, stateExcept_pure, JuliaLean.base.number.convertSame]
    rcases hs : (unsafeBitSetIndex B.chunks x i).run s with ⟨res, after⟩
    have hw' := hw
    rw [hs] at hw'
    cases res with
    | error e =>
        simp only [Bool.true_eq_false, false_implies, true_and]
        exact ⟨hr, hw'.2, hw'.1⟩
    | ok unit =>
        simp only [stateExcept_pure, Bool.true_eq_false, false_implies, true_and]
        exact ⟨hr, hw'.1⟩

theorem sp_bit_address (i : I64) :
    (getChunksId i).2 = int ((WrappedZeroBasedScalar i % 64).toNat : Int) := by
  apply Subtype.ext
  rw [(bh_address i).2, JuliaLean.ChatGPT.Batch2.Group4.packedInt_val]
  · have h0 := Int.emod_nonneg (WrappedZeroBasedScalar i) (by decide : (64 : Int) ≠ 0)
    omega
  · have h1 := Int.emod_lt_of_pos (WrappedZeroBasedScalar i) (by decide : (0 : Int) < 64)
    omega

theorem sp_internalRead_valid (s : MutableMemory U64) (a : Nat) (i : I64)
    (hv : s.validVector a) :
    (unsafeBitGetIndex a i).run s =
      ((if WrappedZeroBasedScalar i / 64 + 1 < 1 then .error .bounds
        else match (s.contents a)[(WrappedZeroBasedScalar i / 64 + 1 - 1).toNat]? with
          | none => .error .bounds
          | some none => .error .undefinedReference
          | some (some word) => .ok
              (decide ((word.val / (2 : Int) ^ (WrappedZeroBasedScalar i % 64).toNat) % 2 = 1))), s) := by
  simp only [unsafeBitGetIndex, stateExcept_bind, sp_mutableGet_valid s a _ hv,
    (bh_address i).1]
  by_cases hlow : WrappedZeroBasedScalar i / 64 + 1 < 1
  · simp only [hlow, ite_true]
  · simp only [hlow, ite_false]
    cases hget : (s.contents a)[(WrappedZeroBasedScalar i / 64 + 1 - 1).toNat]? with
    | none => rfl
    | some cell =>
        cases cell with
        | none => rfl
        | some word =>
            simp only [stateExcept_pure, sp_bit_address]
            have hb : (WrappedZeroBasedScalar i % 64).toNat < 64 := by
              have hmod := Int.emod_lt_of_pos (WrappedZeroBasedScalar i) (by decide : (0 : Int) < 64)
              omega
            rw [JuliaLean.ChatGPT.Batch3.Group1.scalar_mask_test word _ hb, sp_bit_math]

theorem Models1G15GetindexValues_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group15.ScalarGetIndexValues := by
  intro N B i s hv
  dsimp only
  simp only [JuliaLean.base.bitarray.Models1Group15.getIndex,
    bitArrayGetIndex, stateExcept_bind, sp_nativeBounds_run]
  cases hc : ScalarIndexAccepted B i
  · simp only [Bool.false_eq_true, ite_false, ite_true, and_self]
  · simp only [ite_true, Bool.true_eq_false, ite_false,
      sp_internalRead_valid s B.chunks i hv]
    by_cases hlow : WrappedZeroBasedScalar i / 64 + 1 < 1
    · simp only [hlow, ite_true, and_self]
    · simp only [hlow, ite_false]
      cases hget : (s.contents B.chunks)[(WrappedZeroBasedScalar i / 64 + 1 - 1).toNat]? with
      | none => exact ⟨True.intro, rfl⟩
      | some cell => cases cell <;> exact ⟨True.intro, rfl⟩

theorem sp_internalWrite_success (s : MutableMemory U64) (a : Nat) (x : Bool)
    (i : I64) (old : U64) (hv : s.validVector a)
    (hchunk : 1 ≤ (getChunksId i).1.val)
    (hread : (s.contents a)[((getChunksId i).1.val - 1).toNat]? = some (some old)) :
    ((unsafeBitSetIndex a x i).run s).1 = .ok () ∧
    ∃ (header : MutableVector) (word : U64), s.arrays[a]? = some header ∧
      SingleStoredBitWrite s ((unsafeBitSetIndex a x i).run s).2 header.reference.1
        ((header.reference.2.val - 1).toNat + ((getChunksId i).1.val - 1).toNat)
        (getChunksId i).2.val x word := by
  obtain ⟨mem, off, n, slots, h⟩ := validVector_vecAt hv
  have hlen : (s.contents a).length = n.val.toNat := by
    rw [h.contents]
    exact vwWindow_length h
  have hcell : ((getChunksId i).1.val - 1).toNat < (s.contents a).length :=
    (List.getElem?_eq_some_iff.mp hread).choose
  have hi : 1 ≤ (getChunksId i).1.val ∧ (getChunksId i).1.val ≤ n.val := by
    rw [hlen] at hcell
    have hn := h.2.2.2.1
    omega
  let bit := (WrappedZeroBasedScalar i % 64).toNat
  have hb : bit < 64 := by
    have hmod := Int.emod_lt_of_pos (WrappedZeroBasedScalar i) (by decide : (0 : Int) < 64)
    dsimp only [bit]
    omega
  let word := if x then or_int old (shl_int (u64 1) (int bit))
    else and_int old (not_int (shl_int (u64 1) (int bit)))
  let p := (off.val - 1).toNat + ((getChunksId i).1.val - 1).toNat
  let after : MutableMemory U64 :=
    {s with memories := s.memories.set mem (slots.set p (some word))}
  have hp : (off.val - 1 + (getChunksId i).1.val - 1).toNat = p := by
    have ho := h.2.2.1
    dsimp only [p]
    omega
  have hget : (mutableGet a (getChunksId i).1).run s = (.ok old, s) := by
    rw [sp_mutableGet_valid s a _ hv, if_neg (by omega), hread]
  have hset : (mutableSet a word (getChunksId i).1).run s = (.ok (), after) := by
    simpa only [hp, after] using vwSet_run s a mem off n slots h (getChunksId i).1 hi word
  have hw : (unsafeBitSetIndex a x i).run s = (.ok (), after) := by
    simp only [unsafeBitSetIndex, unsafeBitSetIndexAt, stateExcept_bind, hget,
      sp_bit_address]
    exact hset
  rw [hw]
  refine ⟨rfl, ⟨(mem, off), n⟩, word, h.1, ?_⟩
  have hraw : slots[p]? = some (some old) := by
    have hr := hread
    rw [h.contents] at hr
    simp only [vwWindow, List.getElem?_take, List.getElem?_drop] at hr
    rw [if_pos (by omega : ((getChunksId i).1.val - 1).toNat < n.val.toNat)] at hr
    exact hr
  have hbit : (getChunksId i).2.val = (bit : Int) := by
    rw [(bh_address i).2]
    have hm := Int.emod_nonneg (WrappedZeroBasedScalar i) (by decide : (64 : Int) ≠ 0)
    dsimp only [bit]
    omega
  rw [hbit]
  exact sp_singleBitUpdate s mem p slots old bit x h.2.1 hraw hb

theorem Models1G15SetindexBoolValues_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group15.ScalarSetIndexBoolValues := by
  intro N B i x s hv
  dsimp only
  rw [sp_publicWrite_run]
  cases hc : ScalarIndexAccepted B i
  · simp only [Bool.false_eq_true, ite_false, ite_true, and_self]
  · simp only [ite_true, Bool.true_eq_false, ite_false]
    by_cases hlow : WrappedZeroBasedScalar i / 64 + 1 < 1
    · simp only [hlow, ite_true, unsafeBitSetIndex, unsafeBitSetIndexAt,
        stateExcept_bind, sp_mutableGet_valid s B.chunks _ hv, (bh_address i).1, and_self]
    · simp only [hlow, ite_false]
      cases hget : (s.contents B.chunks)[(WrappedZeroBasedScalar i / 64 + 1 - 1).toNat]? with
      | none =>
          simp only [unsafeBitSetIndex, unsafeBitSetIndexAt, stateExcept_bind,
            sp_mutableGet_valid s B.chunks _ hv, (bh_address i).1, hlow,
            ite_false, hget, and_self]
      | some cell =>
          cases cell with
          | none =>
              simp only [unsafeBitSetIndex, unsafeBitSetIndexAt, stateExcept_bind,
                sp_mutableGet_valid s B.chunks _ hv, (bh_address i).1, hlow,
                ite_false, hget, and_self]
          | some old =>
              have hs := sp_internalWrite_success s B.chunks x i old hv
                (by rw [(bh_address i).1]; omega)
                (by simpa only [(bh_address i).1] using hget)
              rcases hr : (unsafeBitSetIndex B.chunks x i).run s with ⟨res, after⟩
              rw [hr] at hs
              cases res with
              | error e => cases hs.1
              | ok u =>
                  refine ⟨rfl, ?_⟩
                  simpa only [(bh_address i).1, (bh_address i).2] using hs.2
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray.Models1Group15

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

/-- Unsafe packed reads preserve every heap cell and header, including on
instrumented invalid-access errors. Julia source: base/bitarray.jl:661-666. -/
def ReusedUnsafeReadState : Prop :=
  ∀ (chunks : Nat) (index : I64) (before : MutableMemory U64),
    ((unsafeBitGetIndex chunks index).run before).2 = before

open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4 in
theorem ReusedUnsafeReadState_proven : ReusedUnsafeReadState := by
  intro chunks index before
  have hr : ((mutableGet chunks (getChunksId index).1).run before).2 = before := by
    simp only [mutableGet, shape_run_bind, shape_vector_run]
    cases ha : before.arrays[chunks]? with
    | none => rfl
    | some a =>
      simp only []
      by_cases hb : (!decide (1 ≤ (getChunksId index).1.val ∧
          (getChunksId index).1 ≤ a.size)) = true
      · simp only [hb, ite_true, shape_run_bind]
        rfl
      · simp only [hb, Bool.false_eq_true, ite_false, shape_run_bind, memoryRead, shape_run_get]
        cases hm : before.memories[a.reference.1]? with
        | none => rfl
        | some slots =>
          simp only [shape_run_pure]
          split <;> rfl
  simp only [unsafeBitGetIndex, shape_run_bind]
  cases hread : (mutableGet chunks (getChunksId index).1).run before with
  | mk result after =>
    simp only [hread] at hr
    subst after
    cases result <;> rfl
end JuliaLean.Proofs.base.bitarray.Models1Group15



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray

open JuliaLean.Registry
open JuliaLean JuliaLean.base.bitarray

def RangeAssignmentIndexErrors : Prop :=
  ∀ (World B X J K R : Type)
    (setindex : JuliaLean.base.indices.IndexStyle → B → X → K →
      ExceptT JuliaLean.base.array.Error (StateM World) R)
    (toIndices : B → (J × Unit) → ExceptT JuliaLean.base.array.Error (StateM World) (K × Unit))
    (array : B) (values : X) (j0 : J) (s final : World) (error : JuliaLean.base.array.Error),
    (toIndices array (j0, ())).run s = (.error error, final) →
    (bitArraySetIndexRangeDispatch setindex toIndices array values j0).run s =
      (.error error, final)

namespace Completion
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

theorem rangeAssignmentIndexErrors : RangeAssignmentIndexErrors := by
  intro World B X J K R setindex toIndices array values j0 s final error h
  simp [bitArraySetIndexRangeDispatch, h]

end Completion

def entriesGetindex1 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-range-assignment-index-errors", juliaFile := "base/bitarray.jl",
    juliaFns := ["setindex!(B::BitArray, X::AbstractArray, J0::Union{Colon,AbstractUnitRange{Int}})"],
    statement := "Range assignment propagates the index object's conversion exception and prior effects before assigning any values from the source array.",
    source := "base/bitarray.jl:697-699", status := .proven,
    prop := ``RangeAssignmentIndexErrors, thm := some ``Completion.rangeAssignmentIndexErrors },
  { id := "bitarrays-scalar-index", juliaFile := "base/bitarray.jl", juliaFns := ["getindex(::BitArray, ::Int)", "setindex!(::BitArray, x, ::Int)"],
    statement := "Scalar reads and writes match the logical bits for valid indexes and every installed Bool conversion; invalid indexes and failed conversions leave memory unchanged, and successful writes preserve zero padding.", source := "base/bitarray.jl:668-692; unused bits are zero (base/bitarray.jl:5-6)",
    status := .proven, prop := ``Round5.ScalarIndexAgrees, thm := some ``JuliaLean.ChatGPT.Batch3.Group1.BitarraysScalarIndex_proven }
]
def entriesGetindex2 : List JuliaLean.Registry.Entry := [
  { id := "bitarrays-setindex-mask-partial", juliaFile := "base/bitarray.jl", juliaFns := ["setindex!(::BitArray, X::AbstractArray, I::BitArray)", "_unsafe_setindex!(::BitArray, X, ::BitArray)"],
    statement := "B[I] = X with a logical BitVector mask agrees with v[I] = X on Vector{Bool}, including leaving the array unchanged when it throws DimensionMismatch for length(X) != count(I).", source := "invariant: BitVector behaves as Vector{Bool}; Array setindex! checks the shape before writing (setindex_shape_check, base/indices.jl)",
    status := .todo, prop := ``SetindexMaskAgrees, thm := none, notes := "Statement defect: take xs = mask = replicate (2^63) false and values = []; the length premises hold, but every successful result has at most typemax(Int) logical bits and cannot equal the required unchanged xs; Julia cannot construct this input; require xs.length \u2264 typemax(Int)." }
]
def entriesGetindex3 : List JuliaLean.Registry.Entry := [
  { id := "memsafety-bitarray-valid-chunk-index", juliaFile := "base/bitarray.jl", juliaFns := ["unsafe_bitgetindex", "unsafe_bitsetindex!", "findnext", "findprev", "findnextnot", "findprevnot"],
    statement := "After the public scalar/start check, get_chunks_id computes an in-bounds chunk for every valid BitArray.", source := "BitArray chunk-count invariant at base/bitarray.jl:5-6; checks at base/bitarray.jl:668-690,1469-1481,1553-1564",
    status := .todo, prop := ``BitArrayChunkInBounds, thm := none }
]
def entriesGetindex4 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-bit-array-iterator-yields", juliaFile := "base/bitarray.jl",
    juliaFns := ["iterate(::BitArray, ::Int)"],
    statement := "Iteration returns each logical bit in column-major order, advances exactly one position, stops at the logical length, and never mutates the array or its aliases. All native states are included: negative states reject with BoundsError and states at or beyond length terminate. The default call is the included state zero.",
    source := "base/bitarray.jl:352-355", status := .proven,
    prop := ``Archive20261102Round6.BitArrayIterationFull, thm := some ``JuliaLean.ChatGPT.Batch4.Group8.BitarrayBitArrayIteratorYields_proven }
]
def entriesGetindex5 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-scalar-bounds-state", juliaFile := "base/bitarray.jl",
    juliaFns := ["getindex(B::BitArray, i::Int)", "setindex!(B::BitArray, x, i::Int) (Bool-valued specialization)"],
    statement := "Scalar reads preserve the entire heap; indices rejected by the native rank-dependent bounds check raise BoundsError before chunk access for both reads and Bool writes, even with missing handles. Failed Bool writes are nonmutating, successful writes return the input header, and all runs preserve the physical destination frame.",
    source := "base/bitarray.jl:668-671,688-692; base/abstractarray.jl:1306-1310,1442-1446", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.ScalarBoundsAndState, thm := some ``JuliaLean.ChatGPT.Batch9.Group5.Models1G15ScalarBoundsState_proven,
    notes := "All heaps, all I64 indices and negative wrapped lengths are included. Rank-one unchecked axes use unsigned bounds, while higher-rank oneto axes clamp negative lengths to zero. The setter is a useful Bool-only partial result; arbitrary convert(Bool,x) remains blocked." },
  { id := "bitarray-getindex-values", juliaFile := "base/bitarray.jl",
    juliaFns := ["getindex(B::BitArray, i::Int)"],
    statement := "Every native scalar index returns the mathematically addressed stored bit after Int predecessor wrapping or the appropriate native-axis/physical bounds failure, without changing any heap state. Alias-induced backing growth or shrinkage is included; an exact logical-to-physical chunk count is not assumed.",
    source := "base/bitarray.jl:661-671; base/abstractarray.jl:1306-1310; doc/src/manual/arrays.md:1236-1238", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.ScalarGetIndexValues, thm := some ``JuliaLean.ChatGPT.Batch9.Group5.Models1G15GetindexValues_proven,
    notes := "The physical chunk vector must be a valid machine-bounded window. Negative rank-one lengths retain unchecked unsigned-axis semantics; higher ranks clamp their axes. Unassigned Option cells report the installed raw-store boundary's undefinedReference outcome; this is not a claim about native Julia UInt64 initialization." },
  { id := "bitarray-setindex-bool-values", juliaFile := "base/bitarray.jl",
    juliaFns := ["setindex!(B::BitArray, x, i::Int) (Bool-valued specialization)"],
    statement := "A successful Bool scalar assignment returns the same BitArray and changes exactly its addressed bit in shared physical memory, preserving all other bits, cells and headers; native bounds or underlying-storage errors leave the heap unchanged.",
    source := "base/bitarray.jl:675-692; base/abstractarray.jl:1442-1446; doc/src/manual/arrays.md:1236-1238", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.ScalarSetIndexBoolValues, thm := some ``JuliaLean.ChatGPT.Batch9.Group5.Models1G15SetindexBoolValues_proven,
    notes := "Useful Bool-only partial result. All signed Int indices, negative wrapped lengths and valid physical backing windows are included, with rank-dependent unsigned-axis behavior, alias growth/shrinkage and no exact chunk-count restriction. Physical-cell postconditions preserve visibility through every alias." },
  { id := "bitarray-unsafe-set-word-return", juliaFile := "base/bitarray.jl",
    juliaFns := ["_unsafe_bitsetindex!(Bc::Array{UInt64}, x::Bool, i1::Int, i2::Int)"],
    statement := "The internal word setter changes only the selected UInt64 bit and returns exactly the assigned stored word. All signed chunk indices and shift counts are included; invalid chunk accesses fail without mutation and out-of-range shifts leave the word unchanged.",
    source := "base/bitarray.jl:680-686 (internal return-value and shared-memory invariant)", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.UnsafeSetIndexAtReturnsWord, thm := none,
    notes := "Independent mathematical bit observations check the returned word and every other physical cell. Errors for invalid unsafe accesses are explicit obligations at the existing checked-memory boundary." },
  { id := "bitarray-unsafe-set-scalar-return", juliaFile := "base/bitarray.jl",
    juliaFns := ["unsafe_bitsetindex!(Bc::Array{UInt64}, x::Bool, i::Int)"],
    statement := "The internal scalar setter preserves the helper's UInt64 return and changes exactly the bit addressed after Int predecessor wrapping, preserving every other bit, cell and header; invalid physical addresses fail without mutation.",
    source := "base/bitarray.jl:122,675-686 (internal machine-address and return-value invariant)", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.UnsafeSetIndexReturnsWord, thm := none,
    notes := "Covers the entire signed Int index domain, including typemin(Int)'s wrapped predecessor, without substituting unbounded integer arithmetic in the model. Expected addressing is independently mathematical." }
]
def entriesGetindex6 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-reused-unsafe-read-state", juliaFile := "base/bitarray.jl",
    juliaFns := ["unsafe_bitgetindex(Bc::Vector{UInt64}, i::Int)"],
    statement := "Unsafe packed scalar reads never modify storage, for every native index and every instrumented heap, including errors.",
    source := "base/bitarray.jl:661-666", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.ReusedUnsafeReadState,
    thm := some ``JuliaLean.Proofs.base.bitarray.Models1Group15.ReusedUnsafeReadState_proven }
]
end JuliaLean.Proofs.base.bitarray


namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

def SetIndexConversionErrors : Prop :=
  ∀ (X : Type) (B : BitVector) (x : X) (i : I64)
    (convertBool : X → BitMutationM Bool) (s final : MutableMemory U64)
    (error : JuliaLean.base.array.Error),
    1 ≤ i.val → i.val ≤ B.len.val →
    (convertBool x).run s = (.error error, final) →
    (JuliaLean.base.bitarray.Dispatch.setIndex convertBool B x i).run s =
      (.error error, final)

theorem SetIndexConversionErrors_proven : SetIndexConversionErrors := by
  intro X B x i convertBool s final error hlo hhi hconvert
  change BitArray 1 at B
  have hi : Models1Group15.ScalarIndexAccepted B i = true := by
    have ilimits := i.property
    have blimits := B.len.property
    change -9223372036854775808 ≤ i.val ∧ i.val ≤ 9223372036854775807 at ilimits
    change -9223372036854775808 ≤ B.len.val ∧ B.len.val ≤ 9223372036854775807 at blimits
    have hm : (i.val - 1) % (2 : Int) ^ 64 = i.val - 1 :=
      Int.emod_eq_of_lt (by omega) (by change _ < 18446744073709551616; omega)
    have hb : B.len.val % (2 : Int) ^ 64 = B.len.val :=
      Int.emod_eq_of_lt (by omega) (by change _ < 18446744073709551616; omega)
    simp only [Models1Group15.ScalarIndexAccepted, if_pos rfl, hm, hb, decide_eq_true_eq]
    omega
  simp only [JuliaLean.base.bitarray.Dispatch.setIndex,
    JuliaLean.CompletionState4.runBind,
    JuliaLean.ChatGPT.Batch9.Group5.sp_nativeBounds_run, hi, ite_true, hconvert]

def entriesGetindex7 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-setindex-conversion-errors", juliaFile := "base/bitarray.jl",
    juliaFns := ["setindex!(B::BitArray, x, i::Int)"],
    statement := "At every valid BitVector position, scalar assignment propagates the exception and prior effects of a failed element conversion without a subsequent packed-storage write.",
    source := "base/bitarray.jl:688-692",
    status := .proven, prop := ``SetIndexConversionErrors,
    thm := some ``SetIndexConversionErrors_proven }
]

end JuliaLean.Proofs.base.bitarray
