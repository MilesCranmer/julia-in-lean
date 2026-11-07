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

namespace JuliaLean.CompletionState2

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


end JuliaLean.CompletionState2

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

set_option maxRecDepth 4096

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

/-- Rejected fill conversions leave every part of the state unchanged. -/
theorem fillConversionError {N : Nat} {X : Type}
    [JuliaLean.base.range.JConvert Bool X] (B : BitArray N) (x : X)
    (e : JuliaLean.base.range.Exc) (s : State)
    (hx : JuliaLean.base.range.JConvert.convert (T := Bool) x = .error e) :
    (fillBitArray Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel B x).run s =
      (.error (Round5.Round2.mutationErrorOfRange e), s) := by
  simp only [fillBitArray, Round5.Round2.convertBoolMutation, hx,
    Round5.Round2.liftRangeResult, shape_run_bind]
  rfl
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- A fold of point updates preserves the visible chunk count. -/
theorem fillFoldLength (indices : List Nat) (words : List U64) (value : U64) :
    (indices.foldl (fun ws j => ws.set j value) words).length = words.length := by
  induction indices generalizing words with
  | nil => rfl
  | cons i indices ih =>
    rw [List.foldl_cons, ih, List.length_set]

/-- A constant-write fold changes exactly the visited word positions. -/
theorem fillFoldGet (indices : List Nat) (value : U64) :
    ∀ (words : List U64), (∀ i ∈ indices, i < words.length) → ∀ j : Nat,
    (indices.foldl (fun ws i => ws.set i value) words).getD j (u64 0) =
      if j ∈ indices then value else words.getD j (u64 0) := by
  induction indices with
  | nil =>
    intro words _ j
    simp only [List.foldl_nil, List.not_mem_nil, ite_false]
  | cons i indices ih =>
    intro words hi j
    have hib := hi i List.mem_cons_self
    have hr := ih (words.set i value)
      (by intro k hk; rw [List.length_set]; exact hi k (List.mem_cons_of_mem i hk)) j
    rw [List.foldl_cons, hr]
    by_cases hj : j ∈ indices
    · rw [if_pos hj, if_pos (List.mem_cons_of_mem i hj)]
    · rw [if_neg hj, dequeWordGetSet words i j value hib]
      by_cases he : i = j
      · subst j
        rw [if_pos rfl, if_pos List.mem_cons_self]
      · have hnot : ¬ j ∈ i :: indices := by
          intro hmem
          rcases List.mem_cons.mp hmem with hmem | hmem
          · exact he hmem.symm
          · exact hj hmem
        rw [if_neg he, if_neg hnot]

/-- Visiting every visible word once produces a constant word list. -/
theorem fillFoldAll (words : List U64) (value : U64) :
    (List.range words.length).foldl (fun ws i => ws.set i value) words =
      List.replicate words.length value := by
  apply List.ext_getElem
  · rw [fillFoldLength, List.length_replicate]
  · intro j hj hj'
    have hbound : j < words.length := by rw [fillFoldLength] at hj; exact hj
    rw [List.getElem_eq_getD (fallback := u64 0),
      fillFoldGet (List.range words.length) value words
        (by intro i hi; exact List.mem_range.mp hi) j,
      if_pos (List.mem_range.mpr hbound), List.getElem_replicate]

/-- Every complete all-true chunk is the full one-bit mask. -/
theorem fillTrueFullWord (n chunk : Nat) (hc : chunk < wordCount n) (hm : n % 64 = 0) :
    packedPrefix (List.replicate n true) chunk 64 = u64Max := by
  apply packedBit_ext
  intro k hk
  have hi : chunk * 64 + k < n := by unfold wordCount at hc; omega
  rw [packedWord_bit _ _ _ hk, fillReplicateGet, if_pos hi, packedBit_max]
  exact (decide_eq_true hk).symm

/-- An all-true sequence occupying complete words has a constant full-mask encoding. -/
theorem fillTrueFullEncoding (n : Nat) (hm : n % 64 = 0) :
    encodeBits (List.replicate n true) = List.replicate (wordCount n) u64Max := by
  apply List.ext_getElem
  · rw [packedEncoded_length, List.length_replicate, List.length_replicate]
  · intro j hj hj'
    have hc : j < wordCount n := by simpa only [List.length_replicate] using hj'
    simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
    rw [fillTrueFullWord n j hc hm, List.getElem_replicate]

/-- The end mask is a full word when the logical length is a multiple of sixty-four. -/
theorem fillFullMask (n : Nat) (hn : n ≤ 9223372036854775807) (hm : n % 64 = 0) :
    maskEnd (int (n : Int)) = u64Max := by
  apply packedBit_ext
  intro k hk
  rw [packedMask_bit n k hn, packedBit_max]
  have hz : (-(n : Int)) % 64 = 0 := by omega
  rw [hz]
  rfl

/-- Intersecting the full mask with a word preserves that word. -/
theorem fillAndMax (word : U64) : and_int u64Max word = word := by
  apply packedBit_ext
  intro k hk
  rw [scalar_packedBit_and, packedBit_max, decide_eq_true hk, Bool.true_and]

/-- A nonempty all-true sequence contained in one word encodes as its end mask. -/
theorem fillTrueSingleEncoding (n : Nat) (hp : 0 < n) (hn : n ≤ 64) :
    encodeBits (List.replicate n true) = [maskEnd (int (n : Int))] := by
  have hw : wordCount n = 1 := by unfold wordCount; omega
  apply List.ext_getElem
  · rw [packedEncoded_length, List.length_replicate, hw]
    rfl
  · intro j hj hj'
    have hj0 : j = 0 := by simp only [List.length_cons, List.length_nil] at hj'; omega
    subst j
    simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range, List.getElem_cons_zero]
    apply packedBit_ext
    intro k hk
    rw [packedWord_bit _ _ _ hk, packedMask_last_bit n k hp (by omega), fillReplicateGet, hw]
    simp only [Nat.sub_self, Nat.zero_mul, Nat.zero_add]
    by_cases hi : k < n <;> simp only [hi, ite_true, ite_false, decide_true, decide_false]

/-- The natural-index action used by the installed chunk-vector fill loop. -/
def fillWordAction (value : U64) (i : Nat) : BitMutationM Unit :=
  mutableSet 0 value (int ((i + 1 : Nat) : Int))

/-- A concrete chunk-fill loop realizes the point-update fold without changing capacity. -/
theorem fillWordLoopRun (indices : List Nat) (words : List U64) (value : U64) (spare : Nat)
    (hn : words.length ≤ 9223372036854775807)
    (hi : ∀ i ∈ indices, i < words.length) :
    (forIn (indices.map (fun i => int ((i + 1 : Nat) : Int))) PUnit.unit
      (fun i _ => do
        mutableSet 0 value i
        pure (ForInStep.yield PUnit.unit))).run (dequeWordStore words spare) =
          (.ok PUnit.unit, dequeWordStore
            (indices.foldl (fun ws i => ws.set i value) words) spare) := by
  have hf := dequeForInFold (fillWordAction value) (fun ws i => ws.set i value)
    (fun ws => dequeWordStore ws spare) (fun ws => ws.length = words.length) indices
    (by
      intro ws hw i hi'
      exact dequeWordSet ws spare i value (by rw [hw]; exact hn) (by rw [hw]; exact hi i hi'))
    (by intro ws hw i _; rw [List.length_set]; exact hw) words rfl
  rw [List.forIn_map]
  simpa only [fillWordAction] using hf

/-- Filling a canonical chunk vector produces the exact constant-word store. -/
theorem fillChunkVectorRun (words : List U64) (word : U64) (spare : Nat)
    (hn : words.length ≤ 9223372036854775807) :
    (Round5.Round2.fillChunkVectorModel 0 word).run (dequeWordStore words spare) =
      (.ok (), dequeWordStore (List.replicate words.length word) spare) := by
  have hlo := fillWordLoopRun (List.range words.length) words word spare hn
    (by intro i hi; exact List.mem_range.mp hi)
  have hl : (forIn (intRange (int 1) (int words.length)) PUnit.unit (fun i _ => do
      mutableSet 0 word i
      pure (ForInStep.yield PUnit.unit))).run (dequeWordStore words spare) =
        (.ok PUnit.unit, dequeWordStore (List.replicate words.length word) spare) := by
    rw [packedObserve_intRange words.length hn]
    exact hlo.trans (congrArg (fun ws : List U64 =>
      ((.ok PUnit.unit : Except Error PUnit), dequeWordStore ws spare)) (fillFoldAll words word))
  exact fillChunkVectorFrom 0 word (int words.length) _ _ (dequeWordLength words spare) hl

/-- The frozen true branch fills every word and then writes the masked final word into chunk one. -/
theorem fillTrueFrom {N : Nat} {X : Type} (convert : X → BitMutationM Bool)
    (fill : Nat → U64 → BitMutationM Unit) (B : BitArray N) (x : X)
    (s full out : State) (nc : I64) (word : U64)
    (hc : (convert x).run s = (.ok true, s)) (hz : (B.len == int 0) = false)
    (hf : (fill B.chunks u64Max).run s = (.ok (), full))
    (hl : (mutableLength B.chunks).run full = (.ok nc, full))
    (hr : (mutableGet B.chunks nc).run full = (.ok word, full))
    (hw : (mutableSet B.chunks (and_int word (maskEndArray B)) (int 1)).run full = (.ok (), out)) :
    (fillBitArray convert fill B x).run s = (.ok B, out) := by
  simp only [fillBitArray, shape_run_bind, hc, hz, Bool.false_eq_true, ite_false,
    Bool.not_true, hf, hl, hr, hw, shape_run_pure]

/-- The exact word list produced by the frozen true-fill branch, which masks its first word. -/
def fillTrueModelWords (n : Nat) : List U64 :=
  (List.replicate (wordCount n) u64Max).set 0 (maskEnd (int (n : Int)))

/-- Converted false fills are correct for every native-sized logical sequence and rank. -/
theorem fillFalseRun {N : Nat} (xs : List Bool) (dims : List I64)
    {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X)
    (hn : xs.length ≤ 9223372036854775807)
    (he : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok false) :
    let B : BitArray N := ⟨0, int xs.length, dims⟩
    (fillBitArray Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel B x).run
      (initWords (encodeBits xs)) =
        (.ok B, initWords (encodeBits (List.replicate xs.length false))) := by
  let B : BitArray N := ⟨0, int xs.length, dims⟩
  by_cases hp : 0 < xs.length
  · let words := encodeBits xs
    have hw : words.length ≤ 9223372036854775807 := packedEncoded_lengthBound xs hn
    have hfill := fillChunkVectorRun words (u64 0) 32 hw
    have hr := fillFalseFrom Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel
      B x (dequeWordStore words 32) _ (scalar_conversion_ok x false _ he)
      (fillPositiveLength xs.length hp hn) hfill
    have hinit := congrArg (fun st : State =>
      (fillBitArray Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel B x).run st)
      (dequeWordStoreInitial words).symm
    exact hinit.trans (hr.trans (by
      rw [dequeWordStoreInitial, packedEncoded_length, ← fillFalseEncoding]))
  · have hz : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    exact fillEmptyFrom Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel
      B x false _ (scalar_conversion_ok x false _ he) rfl

/-- For every nonempty native-sized input, true fill has this exact first-masked-word result. -/
theorem fillTrueModelRun {N : Nat} (xs : List Bool) (dims : List I64)
    {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X)
    (hp : 0 < xs.length) (hn : xs.length ≤ 9223372036854775807)
    (he : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok true) :
    let B : BitArray N := ⟨0, int xs.length, dims⟩
    (fillBitArray Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel B x).run
      (initWords (encodeBits xs)) = (.ok B, initWords (fillTrueModelWords xs.length)) := by
  let B : BitArray N := ⟨0, int xs.length, dims⟩
  let words := encodeBits xs
  let full := List.replicate words.length u64Max
  have hcount : words.length = wordCount xs.length := packedEncoded_length xs
  have hw : words.length ≤ 9223372036854775807 := packedEncoded_lengthBound xs hn
  have hpos : 0 < words.length := by rw [hcount]; unfold wordCount; omega
  have hflen : full.length = words.length := List.length_replicate
  have hfill := fillChunkVectorRun words u64Max 32 hw
  have hl := dequeWordLength full 32
  rw [hflen] at hl
  have hg := dequeWordRead full 32 (words.length - 1)
    (by rw [hflen]; exact hw) (by rw [hflen]; omega)
  have hget : full.getD (words.length - 1) (u64 0) = u64Max := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos (by omega), Option.getD_some]
  rw [show words.length - 1 + 1 = words.length by omega, hget] at hg
  have hset := dequeWordSet full 32 0 (and_int u64Max (maskEndArray B))
    (by rw [hflen]; exact hw) (by rw [hflen]; omega)
  have hset' : (mutableSet 0 (and_int u64Max (maskEndArray B)) (int 1)).run
      (dequeWordStore full 32) =
        (.ok (), dequeWordStore (fillTrueModelWords xs.length) 32) := by
    exact hset.trans (by
      rw [fillAndMax]
      simp only [fillTrueModelWords, full, hcount, maskEndArray, bitArrayLength]
      rfl)
  have hr := fillTrueFrom Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel
    B x (dequeWordStore words 32) (dequeWordStore full 32) _ (int words.length) u64Max
    (scalar_conversion_ok x true _ he) (fillPositiveLength xs.length hp hn) hfill hl hg hset'
  have hinit := congrArg (fun st : State =>
    (fillBitArray Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel B x).run st)
    (dequeWordStoreInitial words).symm
  exact hinit.trans (hr.trans (by rw [dequeWordStoreInitial]))

/-- Complete-word true fills coincide with the documented Boolean encoding. -/
theorem fillTrueModelFull (n : Nat) (hn : n ≤ 9223372036854775807) (hm : n % 64 = 0) :
    fillTrueModelWords n = encodeBits (List.replicate n true) := by
  rw [fillTrueModelWords, fillFullMask n hn hm, List.set_replicate_self]
  exact (fillTrueFullEncoding n hm).symm

/-- A nonempty single-word true fill masks the same word that was filled. -/
theorem fillTrueModelSingle (n : Nat) (hp : 0 < n) (hn : n ≤ 64) :
    fillTrueModelWords n = encodeBits (List.replicate n true) := by
  have hw : wordCount n = 1 := by unfold wordCount; omega
  rw [fillTrueModelWords, hw, fillTrueSingleEncoding n hp hn]
  rfl

/-- Any converted Boolean is filled correctly in an empty logical array. -/
theorem fillEmptyRun {N : Nat} (dims : List I64)
    {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X) (value : Bool)
    (he : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok value) :
    let B : BitArray N := ⟨0, int 0, dims⟩
    (fillBitArray Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel B x).run
      (initWords (encodeBits [])) = (.ok B, initWords (encodeBits [])) := by
  exact fillEmptyFrom Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel
    _ x value _ (scalar_conversion_ok x value _ he) rfl

/-- True fills are correct for one-word arrays and lengths that occupy complete words. -/
theorem fillTrueRestrictedRun {N : Nat} (xs : List Bool) (dims : List I64)
    {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X)
    (hn : xs.length ≤ 9223372036854775807)
    (hscope : xs.length ≤ 64 ∨ xs.length % 64 = 0)
    (he : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok true) :
    let B : BitArray N := ⟨0, int xs.length, dims⟩
    (fillBitArray Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel B x).run
      (initWords (encodeBits xs)) =
        (.ok B, initWords (encodeBits (List.replicate xs.length true))) := by
  by_cases hp : 0 < xs.length
  · have hr := fillTrueModelRun (N := N) xs dims x hp hn he
    exact hr.trans (by
      rcases hscope with hsmall | hfull
      · rw [fillTrueModelSingle xs.length hp hsmall]
      · rw [fillTrueModelFull xs.length hn hfull])
  · have hz : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    exact fillEmptyRun dims x true he

/-- All-false fills return exactly the expected logical sequence with valid packed padding. -/
theorem fillFalseCorrect {N : Nat} (xs : List Bool) (dims : List I64)
    {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X)
    (hn : xs.length ≤ 9223372036854775807)
    (he : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok false) :
    let B : BitArray N := ⟨0, int xs.length, dims⟩
    ∃ (out : State),
      (fillBitArray Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel B x).run
        (initWords (encodeBits xs)) = (.ok B, out) ∧
      bitValues out B = List.replicate xs.length false ∧ Round5.Round2.PackedInvariant out B := by
  refine ⟨initWords (encodeBits (List.replicate xs.length false)), fillFalseRun xs dims x hn he, ?_, ?_⟩
  · have hp := scalar_bits_initial (N := N) (List.replicate xs.length false) dims
      (by simpa only [List.length_replicate] using hn)
    simpa only [List.length_replicate] using hp
  · have hp := scalar_initial_invariant (N := N) (List.replicate xs.length false) dims
      (by simpa only [List.length_replicate] using hn)
    simpa only [List.length_replicate] using hp

/-- The correct true-fill scopes also preserve all logical bits and the packed invariant. -/
theorem fillTrueRestrictedCorrect {N : Nat} (xs : List Bool) (dims : List I64)
    {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X)
    (hn : xs.length ≤ 9223372036854775807)
    (hscope : xs.length ≤ 64 ∨ xs.length % 64 = 0)
    (he : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok true) :
    let B : BitArray N := ⟨0, int xs.length, dims⟩
    ∃ (out : State),
      (fillBitArray Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel B x).run
        (initWords (encodeBits xs)) = (.ok B, out) ∧
      bitValues out B = List.replicate xs.length true ∧ Round5.Round2.PackedInvariant out B := by
  refine ⟨initWords (encodeBits (List.replicate xs.length true)),
    fillTrueRestrictedRun xs dims x hn hscope he, ?_, ?_⟩
  · have hp := scalar_bits_initial (N := N) (List.replicate xs.length true) dims
      (by simpa only [List.length_replicate] using hn)
    simpa only [List.length_replicate] using hp
  · have hp := scalar_initial_invariant (N := N) (List.replicate xs.length true) dims
      (by simpa only [List.length_replicate] using hn)
    simpa only [List.length_replicate] using hp
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The frozen true-fill result always has the requested number of visible chunks. -/
theorem fillTrueModelLength (n : Nat) : (fillTrueModelWords n).length = wordCount n := by
  simp only [fillTrueModelWords, List.length_set, List.length_replicate]

/-- In a partial final word, the first bit outside its low-bit mask is clear. -/
theorem fillPartialMaskBit (n : Nat) (hp : 0 < n) (hn : n ≤ 9223372036854775807)
    (hr : n % 64 ≠ 0) :
    packedBit (maskEnd (int n)) (n % 64) = false := by
  rw [packedMask_last_bit n (n % 64) hp hn]
  have hi : (wordCount n - 1) * 64 + n % 64 = n := by unfold wordCount; omega
  rw [hi, decide_eq_false (Nat.lt_irrefl n)]

/-- The first chunk is exactly the mask, independently of the input words. -/
theorem fillTrueModelFirst (n : Nat) (hp : 0 < n) :
    (fillTrueModelWords n).getD 0 (u64 0) = maskEnd (int n) := by
  have hw : 0 < wordCount n := by unfold wordCount; omega
  unfold fillTrueModelWords
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_set_self (by rw [List.length_replicate]; exact hw), Option.getD_some]

/-- Logical output inspection returns the selected visible bit within the logical length. -/
theorem fillLogicalGet {N : Nat} (s : State) (B : BitArray N) (n i : Nat)
    (hn : n ≤ 9223372036854775807) (hl : B.len = int n) (hi : i < n) :
    (bitValues s B).getD i false = bitAt s B i := by
  unfold bitValues
  rw [hl, packedInt_val n hn, Int.toNat_natCast]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by rw [List.length_range]; exact hi)]
  simp only [Option.map_some, Option.getD_some, List.getElem_range]

/-- Every multiword partial true-fill has a concrete false logical bit in its first word. -/
theorem fillTruePartialLogicalBit {N : Nat} (n : Nat) (dims : List I64)
    (hn : n ≤ 9223372036854775807) (hlarge : 64 < n) (hpartial : n % 64 ≠ 0) :
    (bitValues (initWords (fillTrueModelWords n))
      (⟨0, int n, dims⟩ : BitArray N)).getD (n % 64) false = false := by
  have hr : n % 64 < 64 := Nat.mod_lt _ (by decide)
  have hwords : (fillTrueModelWords n).length ≤ 9223372036854775807 := by
    rw [fillTrueModelLength]
    unfold wordCount
    omega
  have hc : (n % 64) / 64 < (fillTrueModelWords n).length := by
    rw [fillTrueModelLength]
    unfold wordCount
    omega
  have hcontents := scalar_initial_contents (fillTrueModelWords n) hwords
  have hb := scalar_bitAt_contents (initWords (fillTrueModelWords n))
    (⟨0, int n, dims⟩ : BitArray N) (fillTrueModelWords n) (n % 64) hcontents hc
  rw [List.getElem_eq_getD (fallback := u64 0)] at hb
  rw [Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr,
    fillTrueModelFirst n (by omega), fillPartialMaskBit n (by omega) hn hpartial] at hb
  exact (fillLogicalGet _ (⟨0, int n, dims⟩ : BitArray N) n (n % 64) hn rfl (by omega)).trans hb

/-- The defective multiword partial result cannot equal the requested all-true logical sequence. -/
theorem fillTruePartialLogicalMismatch {N : Nat} (n : Nat) (dims : List I64)
    (hn : n ≤ 9223372036854775807) (hlarge : 64 < n) (hpartial : n % 64 ≠ 0) :
    bitValues (initWords (fillTrueModelWords n)) (⟨0, int n, dims⟩ : BitArray N) ≠
      List.replicate n true := by
  intro heq
  have hget := congrArg (fun bits : List Bool => bits.getD (n % 64) false) heq
  rw [fillTruePartialLogicalBit n dims hn hlarge hpartial, fillReplicateGet,
    if_pos (by have := Nat.mod_lt n (by decide : 0 < 64); omega)] at hget
  cases hget

/-- Exact classification of logical correctness for the frozen true-fill model. -/
theorem fillTrueLogicalClassification {N : Nat} (n : Nat) (dims : List I64)
    (hn : n ≤ 9223372036854775807) :
    bitValues (initWords (fillTrueModelWords n)) (⟨0, int n, dims⟩ : BitArray N) =
      List.replicate n true ↔ n ≤ 64 ∨ n % 64 = 0 := by
  constructor
  · intro heq
    by_cases hsmall : n ≤ 64
    · exact Or.inl hsmall
    · by_cases hfull : n % 64 = 0
      · exact Or.inr hfull
      · exact False.elim (fillTruePartialLogicalMismatch n dims hn (by omega) hfull heq)
  · intro hscope
    have hencoding : fillTrueModelWords n = encodeBits (List.replicate n true) := by
      rcases hscope with hsmall | hfull
      · by_cases hp : 0 < n
        · exact fillTrueModelSingle n hp hsmall
        · have hz : n = 0 := by omega
          subst n
          exact fillTrueModelFull 0 (by decide) (by decide)
      · exact fillTrueModelFull n hn hfull
    rw [hencoding]
    have hbits := scalar_bits_initial (N := N) (List.replicate n true) dims
      (by simpa only [List.length_replicate] using hn)
    simpa only [List.length_replicate] using hbits

/-- Correct true-fill scopes satisfy both logical correctness and the packed invariant. -/
theorem fillTrueModelCorrectClassification {N : Nat} (n : Nat) (dims : List I64)
    (hn : n ≤ 9223372036854775807) :
    (bitValues (initWords (fillTrueModelWords n)) (⟨0, int n, dims⟩ : BitArray N) =
        List.replicate n true ∧
      Round5.Round2.PackedInvariant (initWords (fillTrueModelWords n))
        (⟨0, int n, dims⟩ : BitArray N)) ↔ n ≤ 64 ∨ n % 64 = 0 := by
  constructor
  · intro h
    exact (fillTrueLogicalClassification n dims hn).mp h.1
  · intro hscope
    refine ⟨(fillTrueLogicalClassification n dims hn).mpr hscope, ?_⟩
    have hencoding : fillTrueModelWords n = encodeBits (List.replicate n true) := by
      rcases hscope with hsmall | hfull
      · by_cases hp : 0 < n
        · exact fillTrueModelSingle n hp hsmall
        · have hz : n = 0 := by omega
          subst n
          exact fillTrueModelFull 0 (by decide) (by decide)
      · exact fillTrueModelFull n hn hfull
    rw [hencoding]
    have hi := scalar_initial_invariant (N := N) (List.replicate n true) dims
      (by simpa only [List.length_replicate] using hn)
    simpa only [List.length_replicate] using hi
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The exact first-masked-word true-fill result also covers the empty input. -/
theorem fillTrueModelRunAll {N : Nat} (xs : List Bool) (dims : List I64)
    {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X)
    (hn : xs.length ≤ 9223372036854775807)
    (he : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok true) :
    let B : BitArray N := ⟨0, int xs.length, dims⟩
    (fillBitArray Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel B x).run
      (initWords (encodeBits xs)) = (.ok B, initWords (fillTrueModelWords xs.length)) := by
  cases xs with
  | nil => exact fillEmptyRun dims x true he
  | cons b xs => exact fillTrueModelRun (b :: xs) dims x (by simp only [List.length_cons]; omega) hn he

/-- A failed fill conversion leaves every store unchanged and reports its translated error. -/
theorem fillConversionErrorRun {N : Nat} (B : BitArray N) (s : State)
    {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X)
    (e : JuliaLean.base.range.Exc)
    (he : JuliaLean.base.range.JConvert.convert (T := Bool) x = .error e) :
    (fillBitArray Round5.Round2.convertBoolMutation Round5.Round2.fillChunkVectorModel B x).run s =
      (.error (Round5.Round2.mutationErrorOfRange e), s) := by
  simp only [fillBitArray, shape_run_bind, scalar_conversion_error x e s he]

/-- The exact frozen per-input fill statement holds on true conversion precisely at the correct length boundary. -/
theorem fillPublicTrueClassification {N : Nat} (dims : List I64) (xs : List Bool)
    {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X)
    (hRank : dims.length = N) (hDims : ∀ d ∈ dims, int 0 ≤ d)
    (hSize : dims.foldl (· * ·) (int 1) = int xs.length)
    (hn : xs.length ≤ 9223372036854775807)
    (he : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok true) :
    Round5.Round2.FillAgrees dims xs x hRank hDims hSize ↔
      xs.length ≤ 64 ∨ xs.length % 64 = 0 := by
  have hr := fillTrueModelRunAll (N := N) xs dims x hn he
  unfold Round5.Round2.FillAgrees
  dsimp only
  rw [he, hr]
  exact fillTrueModelCorrectClassification xs.length dims hn

/-- Every successful false conversion satisfies the exact frozen per-input fill statement. -/
theorem fillPublicFalseCorrect {N : Nat} (dims : List I64) (xs : List Bool)
    {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X)
    (hRank : dims.length = N) (hDims : ∀ d ∈ dims, int 0 ≤ d)
    (hSize : dims.foldl (· * ·) (int 1) = int xs.length)
    (hn : xs.length ≤ 9223372036854775807)
    (he : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok false) :
    Round5.Round2.FillAgrees dims xs x hRank hDims hSize := by
  obtain ⟨out, hr, hb, hi⟩ := fillFalseCorrect (N := N) xs dims x hn he
  unfold Round5.Round2.FillAgrees
  dsimp only
  rw [he, hr]
  exact ⟨hb, hi⟩

/-- Every failed conversion satisfies the exact frozen error-preservation requirement. -/
theorem fillPublicErrorCorrect {N : Nat} (dims : List I64) (xs : List Bool)
    {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X)
    (hRank : dims.length = N) (hDims : ∀ d ∈ dims, int 0 ≤ d)
    (hSize : dims.foldl (· * ·) (int 1) = int xs.length)
    (e : JuliaLean.base.range.Exc)
    (he : JuliaLean.base.range.JConvert.convert (T := Bool) x = .error e) :
    Round5.Round2.FillAgrees dims xs x hRank hDims hSize := by
  have hr := fillConversionErrorRun (⟨0, int xs.length, dims⟩ : BitArray N)
    (initWords (encodeBits xs)) x e he
  unfold Round5.Round2.FillAgrees
  dsimp only
  rw [he, hr]

/-- Complete per-input classification of the frozen fill statement, including every conversion outcome. -/
theorem fillPublicClassification {N : Nat} (dims : List I64) (xs : List Bool)
    {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X)
    (hRank : dims.length = N) (hDims : ∀ d ∈ dims, int 0 ≤ d)
    (hSize : dims.foldl (· * ·) (int 1) = int xs.length)
    (hn : xs.length ≤ 9223372036854775807) :
    Round5.Round2.FillAgrees dims xs x hRank hDims hSize ↔
      match JuliaLean.base.range.JConvert.convert (T := Bool) x with
      | .ok true => xs.length ≤ 64 ∨ xs.length % 64 = 0
      | _ => True := by
  cases he : JuliaLean.base.range.JConvert.convert (T := Bool) x with
  | error e =>
    exact iff_of_true (fillPublicErrorCorrect dims xs x hRank hDims hSize e he) trivial
  | ok value =>
    cases value with
    | false => exact iff_of_true (fillPublicFalseCorrect dims xs x hRank hDims hSize hn he) trivial
    | true => exact fillPublicTrueClassification dims xs x hRank hDims hSize hn he
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

section
namespace JuliaLean.ChatGPT.Batch5.Group2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch2.Group4
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean.Proofs.base.bitarray.JuliaLean.ChatGPT.Batch3.Group2

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Negative dimensions are rejected before either allocation or filling occurs. -/
theorem ctor_fill_negative_dimension {N : Nat}
    (checked : List I64 → BitMutationM I64) (allocate : Nat → BitMutationM Nat)
    (fill : BitArray N → Bool → BitMutationM (BitArray N))
    (dim : I64) (rest : List I64) (s : State) (hdim : dim.val < 0) :
    (falsesIntegerDims (BitArrayUndef checked allocate) fill (dim :: rest)).run s =
      (.error (.argument s!"dimension size must be ≥ 0, got {dim.val} for dimension {1}"), s) ∧
    (truesIntegerDims (BitArrayUndef checked allocate) fill (dim :: rest)).run s =
      (.error (.argument s!"dimension size must be ≥ 0, got {dim.val} for dimension {1}"), s) := by
  constructor <;>
    simp only [falsesIntegerDims, truesIntegerDims, BitArrayUndef,
      List.forIn_cons, hdim, ite_true, shape_run_bind] <;> rfl

/-- True fill has the exact first-masked-word result of the unchanged model. -/
theorem ctor_fill_true_positive {N : Nat} (s : State) (n : Nat) (dims : List I64)
    (hp : 0 < n) (hn : n ≤ 9223372036854775807) :
    (fillBitArray (fun b => pure b) fillVectorChunks
      (⟨s.arrays.length, int n, dims⟩ : BitArray N) true).run
      (shiftFreshHeap s (shiftFreshInitial n)) =
      (.ok ⟨s.arrays.length, int n, dims⟩,
        shiftFreshHeap s ((fillTrueModelWords n).map some)) := by
  let count := wordCount n
  let full := List.replicate count (some u64Max)
  have hc : count ≤ 9223372036854775807 := by dsimp only [count]; unfold wordCount; omega
  have hcpos : 0 < count := by dsimp only [count]; unfold wordCount; omega
  have hflen : full.length = count := List.length_replicate
  have hf := ctor_fill_fresh s (shiftFreshInitial n) u64Max
    (by rw [shiftFreshInitialLength]; exact hc)
  rw [shiftFreshInitialLength] at hf
  have hl := shiftFreshLength s full
  rw [hflen] at hl
  have hr := shiftFreshRead s full (count - 1) u64Max
    (by rw [hflen]; exact hc) (by rw [hflen]; omega)
    (by simp only [full, List.getElem?_replicate, show count - 1 < count by omega, ite_true])
  rw [show count - 1 + 1 = count by omega] at hr
  have hw := shiftFreshSet s full 0 (and_int u64Max (maskEnd (int n)))
    (by rw [hflen]; exact hc) (by rw [hflen]; omega)
  rw [fillAndMax] at hw
  have hout : full.set 0 (some (maskEnd (int n))) = (fillTrueModelWords n).map some := by
    simp only [full, fillTrueModelWords, List.map_set, List.map_replicate]
    rfl
  rw [hout] at hw
  refine fillTrueFrom (fun b => pure b) fillVectorChunks
    (⟨s.arrays.length, int n, dims⟩ : BitArray N) true
    (shiftFreshHeap s (shiftFreshInitial n)) (shiftFreshHeap s full)
    (shiftFreshHeap s ((fillTrueModelWords n).map some)) (int count) u64Max
    rfl (fillPositiveLength n hp hn) hf hl hr ?_
  simpa only [maskEndArray, bitArrayLength, fillAndMax, Nat.zero_add, Int.natCast_one] using hw

/-- The frozen true-fill word list is correct on its complete supported length classes. -/
theorem ctor_true_encoding (n : Nat) (hn : n ≤ 9223372036854775807)
    (hscope : n ≤ 64 ∨ n % 64 = 0) :
    fillTrueModelWords n = encodeBits (List.replicate n true) := by
  rcases hscope with hsmall | hfull
  · by_cases hp : 0 < n
    · exact fillTrueModelSingle n hp hsmall
    · have hz : n = 0 := by omega
      subst n
      exact fillTrueModelFull 0 (by decide) (by decide)
  · exact fillTrueModelFull n hn hfull

/-- Both public fill constructors factor through their successful allocation and fill phases. -/
theorem ctor_fill_pair_from {N : Nat}
    (undef : List I64 → BitMutationM (BitArray N))
    (fill : BitArray N → Bool → BitMutationM (BitArray N))
    (dims : List I64) (B : BitArray N) (s allocated falseState trueState : State)
    (ha : (undef dims).run s = (.ok B, allocated))
    (hf : (fill B false).run allocated = (.ok B, falseState))
    (ht : (fill B true).run allocated = (.ok B, trueState)) :
    (falsesIntegerDims undef fill dims).run s = (.ok B, falseState) ∧
    (truesIntegerDims undef fill dims).run s = (.ok B, trueState) := by
  constructor <;>
    simp only [falsesIntegerDims, truesIntegerDims, shape_run_bind, ha, hf, ht]

/-- Validated fill constructors have exact encodings on the frozen true-fill model's valid scope. -/
theorem ctor_fill_constructors_run {N : Nat} (s : State) (dims : List I64) (n : Nat)
    (hdims : ∀ d ∈ dims, int 0 ≤ d)
    (hproduct : dims.foldl (· * ·) (int 1) = int n)
    (hn : n ≤ 9223372036854775807) (hscope : n ≤ 64 ∨ n % 64 = 0) :
    let undef : List I64 → BitMutationM (BitArray N) :=
      BitArrayUndef (fun ds => pure (ds.foldl (· * ·) (int 1))) allocateChunkVectorModel
    let fill : BitArray N → Bool → BitMutationM (BitArray N) :=
      fillBitArray (fun b => pure b) fillVectorChunks
    (falsesIntegerDims undef fill dims).run s =
      (.ok ⟨s.arrays.length, int n, dims⟩,
        shiftFreshHeap s ((encodeBits (List.replicate n false)).map some)) ∧
    (truesIntegerDims undef fill dims).run s =
      (.ok ⟨s.arrays.length, int n, dims⟩,
        shiftFreshHeap s ((encodeBits (List.replicate n true)).map some)) := by
  dsimp only
  by_cases hp : 0 < n
  · have ha := ctor_native_undef_positive (N := N) dims n s hdims hproduct hp hn
    have hf := ctor_fill_false_positive (N := N) s n dims hp hn
    have ht := ctor_fill_true_positive (N := N) s n dims hp hn
    rw [ctor_true_encoding n hn hscope] at ht
    exact ctor_fill_pair_from _ _ dims _ s _ _ _ ha hf ht
  · have hz : n = 0 := by omega
    subst n
    have ha := ctor_native_undef_zero (N := N) dims s hdims hproduct
    have hf := fillEmptyFrom (fun b => pure b) fillVectorChunks
      (⟨s.arrays.length, int 0, dims⟩ : BitArray N) false false (shiftFreshHeap s []) rfl rfl
    have ht := fillEmptyFrom (fun b => pure b) fillVectorChunks
      (⟨s.arrays.length, int 0, dims⟩ : BitArray N) true true (shiftFreshHeap s []) rfl rfl
    exact ctor_fill_pair_from _ _ dims _ s _ _ _ ha hf ht

/-- A checked pair of constructor executions supplies its original logical observations. -/
theorem ctor_fill_observation_from (dims : List I64) (B : BitArray 2)
    (falseResult trueResult : Except Error (BitArray 2) × State)
    (falseState trueState : State)
    (hf : falseResult = (.ok B, falseState)) (ht : trueResult = (.ok B, trueState))
    (hdims : B.dims = dims)
    (hfalse : bitValues falseState B = List.replicate B.len.val.toNat false)
    (htrue : bitValues trueState B = List.replicate B.len.val.toNat true) :
    (match falseResult.1, trueResult.1 with
    | .ok f, .ok t =>
      f.dims = dims ∧ t.dims = dims ∧
      bitValues falseResult.2 f = List.replicate f.len.val.toNat false ∧
      bitValues trueResult.2 t = List.replicate t.len.val.toNat true
    | _, _ => False) := by
  rw [hf, ht]
  exact ⟨hdims, hdims, hfalse, htrue⟩

/-- The original per-input fill observation holds with explicit size and valid true-fill guards. -/
theorem ctor_fill_constructors_bounded (dims : List I64) (n : Nat)
    (hdims : ∀ d ∈ dims, int 0 ≤ d)
    (hproduct : dims.foldl (· * ·) (int 1) = int n)
    (hn : n ≤ 9223372036854775807) (hscope : n ≤ 64 ∨ n % 64 = 0) :
    let checked : List I64 → BitMutationM I64 := fun ds => pure (ds.foldl (· * ·) (int 1))
    let allocate : Nat → BitMutationM Nat := fun n =>
      mutableAllocate (some ⟨8, false, false⟩) 0 (int (Int.ofNat n))
    let undef : List I64 → BitMutationM (BitArray 2) := BitArrayUndef checked allocate
    let fill : BitArray 2 → Bool → BitMutationM (BitArray 2) :=
      fun B value => fillBitArray (fun x => pure x) fillVectorChunks B value
    let falseResult := (falsesIntegerDims undef fill dims).run (MutableMemory.initial [])
    let trueResult := (truesIntegerDims undef fill dims).run (MutableMemory.initial [])
    match falseResult.1, trueResult.1 with
    | .ok f, .ok t =>
      f.dims = dims ∧ t.dims = dims ∧
      bitValues falseResult.2 f = List.replicate f.len.val.toNat false ∧
      bitValues trueResult.2 t = List.replicate t.len.val.toNat true
    | _, _ => False := by
  have hr := ctor_fill_constructors_run (N := 2) (MutableMemory.initial []) dims n
    hdims hproduct hn hscope
  dsimp only at hr ⊢
  refine ctor_fill_observation_from dims _ _ _ _ _ hr.1 hr.2 rfl ?_ ?_
  all_goals simp only [packedInt_val n hn, Int.toNat_natCast]
  · have h := ctor_fresh_bits (N := 2) (MutableMemory.initial [])
      (List.replicate n false) dims (by simpa only [List.length_replicate] using hn)
    simpa only [List.length_replicate] using h
  · have h := ctor_fresh_bits (N := 2) (MutableMemory.initial [])
      (List.replicate n true) dims (by simpa only [List.length_replicate] using hn)
    simpa only [List.length_replicate] using h
end JuliaLean.ChatGPT.Batch5.Group2
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

/-- Writing every slot once creates the corresponding constant slot list. -/
theorem mtx_fillfold_all {α : Type} (slots : List α) (value : α) :
    (List.range slots.length).foldl (fun ws i => ws.set i value) slots =
      List.replicate slots.length value := by
  apply List.ext_getElem
  · rw [mtx_fillfold_length, List.length_replicate]
  · intro j hj hj'
    have hbound : j < slots.length := by rw [mtx_fillfold_length] at hj; exact hj
    rw [List.getElem_eq_getD (fallback := value),
      mtx_fillfold_get (List.range slots.length) value value slots
        (by intro i hi; exact List.mem_range.mp hi) j,
      if_pos (List.mem_range.mpr hbound), List.getElem_replicate]

/-- The public fill loop initializes every fresh chunk while preserving the
complete earlier heap. -/
theorem mtx_fill_fresh_loop (s : State) (slots : List (Option U64))
    (hn : slots.length ≤ 9223372036854775807) :
    (forIn (intRange (int 1) (int slots.length)) PUnit.unit (fun i _ => do
      mutableSet s.arrays.length (u64 0) i
      pure (ForInStep.yield PUnit.unit))).run (shiftFreshHeap s slots) =
        (.ok PUnit.unit, shiftFreshHeap s (List.replicate slots.length (some (u64 0)))) := by
  have hf := dequeForInFold
    (fun i : Nat => mutableSet s.arrays.length (u64 0) (int ((i + 1 : Nat) : Int)))
    (fun ws i => ws.set i (some (u64 0))) (shiftFreshHeap s)
    (fun ws => ws.length = slots.length) (List.range slots.length)
    (by
      intro ws hw i hi
      exact shiftFreshSet s ws i (u64 0) (by rw [hw]; exact hn)
        (by rw [hw]; exact List.mem_range.mp hi))
    (by intro ws hw i hi; rw [List.length_set]; exact hw) slots rfl
  rw [packedObserve_intRange slots.length hn, List.forIn_map]
  exact hf.trans (congrArg (fun ws => ((.ok PUnit.unit : Except Error PUnit), shiftFreshHeap s ws))
    (mtx_fillfold_all slots (some (u64 0))))

/-- The public typed-fill dispatcher composes its index collection and write loop. -/
theorem mtx_fill_typed_from (handle : Nat) (indices : List I64) (s out : State)
    (hindices : (chunkIndices handle).run s = (.ok indices, s))
    (hloop : (forIn indices PUnit.unit (fun i _ => do
      mutableSet handle (u64 0) i
      pure (ForInStep.yield PUnit.unit))).run s = (.ok PUnit.unit, out)) :
    (fillTyped chunkIndices mutableSet handle (u64 0)).run s = (.ok handle, out) := by
  unfold fillTyped
  rw [mtx_run_bind_ok hindices, mtx_run_bind_ok hloop]
  rfl

/-- The source-selected native Int-to-UInt64 fill dispatch uses its typed loop. -/
theorem mtx_fill_native_from (handle : Nat) (s out : State)
    (hfill : (fillTyped chunkIndices mutableSet handle (u64 0)).run s = (.ok handle, out)) :
    (fillChunksNative handle (u64 0)).run s = (.ok (), out) := by
  have hconvert :
      (liftArray (JuliaLean.base.abstractarray.liftJulia
        (JuliaLean.base.int.convert .u64 (int 0))) : BitMutationM U64).run s =
          (.ok (u64 0), s) := rfl
  have hbang : (fillBang
      (fun (_ : I64) => false) (fun (_ : I64) => u64 0)
      (fun x => liftArray (JuliaLean.base.abstractarray.liftJulia
        (JuliaLean.base.int.convert .u64 x)))
      (fillTyped chunkIndices mutableSet) handle (int 0)).run s = (.ok handle, out) := by
    unfold fillBang
    simp only [Bool.false_eq_true, ite_false]
    rw [mtx_run_bind_ok hconvert]
    exact hfill
  unfold fillChunksNative
  simp only [beq_self_eq_true, ite_true]
  rw [mtx_run_bind_ok hbang]
  rfl
end JuliaLean.ChatGPT.Batch5.Group4



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray.Models1Group15

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.base.bitarray.Models1Group15

/-- Logical capacity of the partial final chunk, in ordinary arithmetic. -/
def FinalChunkBitCount (len : I64) : Nat :=
  if len.val % 64 = 0 then 64 else (len.val % 64).toNat

/-- Physical mutation invariant for a packed fill. Headers, allocation counts,
all memory sizes, and all cells outside the destination chunk window remain
unchanged. The retained physical final chunk has zero padding; every earlier
chunk is uniformly filled. This describes the actual shared chunk window even
when another alias has changed its length since B's header was created. -/
def FilledChunkWindow {N : Nat} (B : BitArray N) (x : Bool)
    (header : MutableVector) (before after : MutableMemory U64) : Prop :=
  after.arrays = before.arrays ∧ after.memories.length = before.memories.length ∧
  (∀ memory : Nat,
    (after.memories[memory]?).map List.length = (before.memories[memory]?).map List.length) ∧
  (∀ (memory position : Nat),
    (memory ≠ header.reference.1 ∨
      (position : Int) + 1 < header.reference.2.val ∨
      header.reference.2.val + header.size.val ≤ (position : Int) + 1) →
    StoredCell after memory position = StoredCell before memory position) ∧
  (after.contents B.chunks).length = header.size.val.toNat ∧
  (∀ wordIndex : Nat, wordIndex < header.size.val.toNat →
    ∃ word : U64, (after.contents B.chunks)[wordIndex]? = some (some word) ∧
      ∀ bit : Nat, bit < 64 →
        (word.val / (2 : Int) ^ bit) % 2 =
          (if x ∧ (wordIndex + 1 < header.size.val.toNat ∨ bit < FinalChunkBitCount B.len)
           then 1 else 0)) ∧
  (B.len.val ≤ 64 * header.size.val → LogicalBitsEqual after B x)

/-- Bool-valued fill! preserves B's identity and metadata, fills all logical
values when the shared chunk vector still covers them, and records exact
physical writes and padding even after alias growth or shrinkage. Empty B
returns without accessing chunks. For a nonempty B whose shared chunk vector
has been shrunk to zero, false succeeds without writes, while true raises
BoundsError at the final-chunk read after the empty fill. Valid physical vectors
may start with unassigned raw cells because fill overwrites them before reading.
The property does not require chunk count = ceil(length(B)/64), equal ranks,
nonaliasing, or valid unused dims.
Julia source: base/bitarray.jl:368-379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/array.jl:336-366; doc/src/manual/arrays.md:72.
This property covers the full Bool specialization; the Any-valued method remains
blocked on extensible convert(Bool,x). -/
def FillBoolValuesAndSharedStorage : Prop :=
  ∀ (N : Nat) (B : BitArray N) (x : Bool) (s : MutableMemory U64),
    0 ≤ B.len.val → (B.len.val = 0 ∨ s.validVector B.chunks) →
    let result := (JuliaLean.base.bitarray.Models1Group15.fillBool B x).run s
    if B.len.val = 0 then result.1 = .ok B ∧ result.2 = s
    else ∃ header : MutableVector, s.arrays[B.chunks]? = some header ∧
      if x = true ∧ header.size.val = 0 then
        result.1 = .error .bounds ∧ result.2 = s
      else result.1 = .ok B ∧ FilledChunkWindow B x header s result.2
end JuliaLean.Proofs.base.bitarray.Models1Group15



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.bitarray.Models1Group15

def bh_shape_action {α : Type} (action : BitMutationM α) : Prop :=
  ∀ s, FixedHeapShape s (action.run s).2

theorem bh_shape_refl (s : MutableMemory U64) : FixedHeapShape s s :=
  ⟨rfl, rfl, fun _ => rfl⟩

theorem bh_shape_pure {α : Type} (x : α) :
    bh_shape_action (pure x : BitMutationM α) := fun s => bh_shape_refl s

theorem bh_shape_bind {α β : Type} (action : BitMutationM α)
    (next : α → BitMutationM β) (ha : bh_shape_action action)
    (hn : ∀ x, bh_shape_action (next x)) :
    bh_shape_action (action >>= next) := by
  intro s
  simp only [stateExcept_bind]
  rcases he : action.run s with ⟨res, middle⟩
  have hs := ha s
  rw [he] at hs
  cases res with
  | error e => exact hs
  | ok x => exact bh_shape_trans hs (hn x middle)

theorem bh_shape_forIn {α β : Type} (indices : List α)
    (body : α → β → BitMutationM (ForInStep β))
    (hbody : ∀ i b, bh_shape_action (body i b)) (initial : β) :
    bh_shape_action (forIn indices initial body) := by
  induction indices generalizing initial with
  | nil => exact bh_shape_pure initial
  | cons i indices ih =>
    rw [List.forIn_cons]
    apply bh_shape_bind _ _ (hbody i initial)
    intro step
    cases step with
    | done b => exact bh_shape_pure b
    | yield b => exact ih b

theorem bh_shape_read (chunks : Nat) (index : I64) :
    bh_shape_action (mutableGet chunks index : BitMutationM U64) := by
  intro s
  rw [sp_mutableGet_readonly]
  exact bh_shape_refl s

theorem bh_shape_write (chunks : Nat) (word : U64) (index : I64) :
    bh_shape_action (mutableSet chunks word index) :=
  fun s => (sp_mutableSet_frame s chunks word index).1



theorem bh_fill_branch (chunks : Nat) (first last : I64)
    (f g : U64 → U64) (middle : U64) :
    bh_shape_action (do
      let c0 ← mutableGet chunks first
      mutableSet chunks (f c0) first
      forIn (intRange (first + int 1) (last - int 1)) PUnit.unit (fun k _ => do
        mutableSet chunks middle k
        pure (ForInStep.yield PUnit.unit))
      if last > first then
        let c1 ← mutableGet chunks last
        let word := g c1
        mutableSet chunks word last
        pure (some (Sum.inr word))
      else pure (some (Sum.inl false)) :
      BitMutationM JuliaLean.base.bitarray.Models1Group15.FillChunkResult) := by
  apply bh_shape_bind _ _ (bh_shape_read chunks first)
  intro c0
  apply bh_shape_bind _ _ (bh_shape_write chunks (f c0) first)
  intro unit
  apply bh_shape_bind
  · apply bh_shape_forIn
    intro k unit
    apply bh_shape_bind _ _ (bh_shape_write chunks middle k)
    intro unit
    exact bh_shape_pure _
  · intro unit
    split
    · apply bh_shape_bind _ _ (bh_shape_read chunks last)
      intro c1
      apply bh_shape_bind _ _ (bh_shape_write chunks (g c1) last)
      intro unit
      exact bh_shape_pure _
    · exact bh_shape_pure _

theorem bh_fill_shape (chunks : Nat) (value : Bool) (position count : I64) :
    bh_shape_action (JuliaLean.base.bitarray.Models1Group15.fillChunks
      chunks value position count) := by
  unfold JuliaLean.base.bitarray.Models1Group15.fillChunks
  split
  · exact bh_shape_pure _
  · cases getChunksId position with
    | mk k0 l0 =>
      cases getChunksId (position + count - int 1) with
      | mk k1 l1 =>
        dsimp only
        split <;> cases value <;>
          simp only [Bool.false_eq_true, ite_false, ite_true]
        all_goals exact bh_fill_branch chunks k0 k1 _ _ _
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray.Models1Group15

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

/-- Full-domain storage-accounting invariant for base/bitarray.jl:235-259.
Nonpositive counts perform no access. Every other outcome, including a partial
write followed by an instrumented unsafe-access error, preserves array headers,
memory-object count and every memory object's size. -/
def FillChunksStorageAccounting : Prop :=
  ∀ (chunks : Nat) (value : Bool) (position count : I64) (before : MutableMemory U64),
    let result := (JuliaLean.base.bitarray.Models1Group15.fillChunks
      chunks value position count).run before
    result.2.arrays = before.arrays ∧
    result.2.memories.length = before.memories.length ∧
    (∀ memory : Nat,
      (result.2.memories[memory]?).map List.length =
        (before.memories[memory]?).map List.length) ∧
    (count.val ≤ 0 → result.1 = .ok none ∧ result.2 = before)
end JuliaLean.Proofs.base.bitarray.Models1Group15



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.ChatGPT.Batch9.Group5
open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.bitarray.Models1Group15

theorem Models1G15FillChunksStorageAccounting_proven :
    JuliaLean.Proofs.base.bitarray.Models1Group15.FillChunksStorageAccounting := by
  intro chunks value position count before
  have hshape := bh_fill_shape chunks value position count before
  refine ⟨hshape.1, hshape.2.1, hshape.2.2, ?_⟩
  intro hcount
  have hle : count ≤ int 0 := hcount
  simp only [JuliaLean.base.bitarray.Models1Group15.fillChunks, hle,
    ite_true, stateExcept_pure, and_self]
end JuliaLean.ChatGPT.Batch9.Group5



set_option Elab.async false



set_option Elab.async false
namespace JuliaLean.Proofs.base.bitarray

open JuliaLean.Registry
open JuliaLean JuliaLean.base.bitarray

def BooleanVarargsErrors : Prop :=
  ∀ (World D R : Type) (dims : List D)
    (dispatch : List D → ExceptT JuliaLean.base.array.Error (StateM World) R)
    (s final : World) (error : JuliaLean.base.array.Error),
    (dispatch dims).run s = (.error error, final) →
    (falsesVarargsDispatch dispatch dims).run s = (.error error, final) ∧
    (truesVarargsDispatch dispatch dims).run s = (.error error, final)

def BooleanAxesAllocationErrors : Prop :=
  ∀ (World D A R : Type) (dims : D)
    (similar : D → ExceptT JuliaLean.base.array.Error (StateM World) A)
    (fill : A → Bool → ExceptT JuliaLean.base.array.Error (StateM World) R)
    (s final : World) (error : JuliaLean.base.array.Error),
    (similar dims).run s = (.error error, final) →
    (falsesAxesDispatch similar fill dims).run s = (.error error, final) ∧
    (truesAxesDispatch similar fill dims).run s = (.error error, final)

namespace Completion
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

theorem booleanVarargsErrors : BooleanVarargsErrors := by
  intro World D R dims dispatch s final error h
  exact ⟨h, h⟩

end Completion

namespace Completion
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

theorem booleanAxesAllocationErrors : BooleanAxesAllocationErrors := by
  intro World D A R dims similar fill s final error h
  simp [falsesAxesDispatch, truesAxesDispatch, h]

end Completion

def entriesFill1 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-boolean-varargs-errors", juliaFile := "base/bitarray.jl",
    juliaFns := ["falses(dims::DimOrInd...)", "trues(dims::DimOrInd...)"],
    statement := "Variadic Boolean array construction preserves every requested axis or dimension and propagates the selected tuple constructor's exception and prior effects.",
    source := "base/bitarray.jl:394,413", status := .proven,
    prop := ``BooleanVarargsErrors, thm := some ``Completion.booleanVarargsErrors },
  { id := "bitarray-boolean-axes-allocation-errors", juliaFile := "base/bitarray.jl",
    juliaFns := ["falses(dims::NTuple{N,DimOrInd}) where N",
      "trues(dims::NTuple{N,DimOrInd}) where N"],
    statement := "Axis-aware Boolean construction propagates allocation exceptions and prior effects before any attempt to fill the resulting array.",
    source := "base/bitarray.jl:398,417", status := .proven,
    prop := ``BooleanAxesAllocationErrors, thm := some ``Completion.booleanAxesAllocationErrors },
  { id := "bitarrays-fill", juliaFile := "base/bitarray.jl", juliaFns := ["fill!(::BitArray, x)"],
    statement := "For every valid rank and shape within the size bound, fill! converts x to Bool and fills every logical bit while preserving packed padding; failed conversions leave state unchanged.", source := "base/bitarray.jl:368-379; unused bits are zero (base/bitarray.jl:5-6)",
    status := .todo, prop := ``Round5.FillAgrees, thm := none, notes := "No complete exact proof returned. the full target is blocked at fill!(falses(65), true), where the model writes its final mask to chunk 1 although the quoted Julia source writes Bc[end]." }
]
def entriesFill2 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-fill-bool-storage", juliaFile := "base/bitarray.jl",
    juliaFns := ["fill!(B::BitArray, x) (Bool-valued specialization)"],
    statement := "Bool-valued fill! preserves B's header and all cells outside its shared chunk window, fills logical values when sufficient chunks remain, and preserves final physical-chunk padding. It also models alias growth/shrinkage: an empty logical array performs no access, and a nonempty array with zero remaining chunks throws BoundsError only for true.",
    source := "base/bitarray.jl:368-379; base/array.jl:336-366; doc/src/manual/arrays.md:72", status := .todo,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.FillBoolValuesAndSharedStorage, thm := none,
    notes := "No complete exact proof returned. The general shared-window frame, offsets and alias-resizing partition remain open." }
]
def entriesFill3 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-fill-chunks-storage-accounting",
    juliaFile := "base/bitarray.jl",
    juliaFns := ["fill_chunks!(Bc::Array{UInt64}, x::Bool, pos::Int, numbits::Int)"],
    statement := "Chunk fill preserves all array headers, memory-object counts and memory sizes on every result, including partial failures. Nonpositive counts return nothing without accessing storage.",
    source := "base/bitarray.jl:235-259",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Models1Group15.FillChunksStorageAccounting,
    thm := some ``JuliaLean.ChatGPT.Batch9.Group5.Models1G15FillChunksStorageAccounting_proven,
    notes := "Full signed position/count and arbitrary instrumented heap domain. Invalid unchecked accesses remain obligations at the existing memory boundary." }
]
end JuliaLean.Proofs.base.bitarray


namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

def FillConversionErrors : Prop :=
  ∀ (N : Nat) (X : Type) (B : BitArray N) (x : X)
    (convertBool : X → BitMutationM Bool) (s final : MutableMemory U64)
    (error : JuliaLean.base.array.Error),
    (convertBool x).run s = (.error error, final) →
    (JuliaLean.base.bitarray.Models1Group15.fillConvert convertBool B x).run s =
      (.error error, final)

namespace Completion
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

theorem fillConversionErrors : FillConversionErrors := by
  intro N X B x convertBool s final error h
  simp [Models1Group15.fillConvert, h]

end Completion

def entriesFill4 : List JuliaLean.Registry.Entry := [
  { id := "bitarray-fill-conversion-errors", juliaFile := "base/bitarray.jl",
    juliaFns := ["fill!(B::BitArray, x)"],
    statement := "Filling propagates the exception and prior effects of a failed element conversion, even for an empty BitArray, without performing any subsequent packed-storage writes.",
    source := "base/bitarray.jl:368-379",
    status := .proven, prop := ``FillConversionErrors, thm := some ``Completion.fillConversionErrors }
]

end JuliaLean.Proofs.base.bitarray
