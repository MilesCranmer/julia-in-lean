import JuliaLean.base.array
import JuliaLean.src.genericmemory_c
import JuliaLean.Proofs.base.dict
import JuliaLean.base.operators
import JuliaLean.base.int
import JuliaLean.base.number
import JuliaLean.base.abstractarray
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.range
import JuliaLean.Proofs.base.int
import JuliaLean.base.float
import JuliaLean.base.cmem
import JuliaLean.Proofs.base.cmem
import JuliaLean.base.pointer
import JuliaLean.base.set
import JuliaLean.Proofs.base.set
import JuliaLean.base.multidimensional
import JuliaLean.base.indices
import JuliaLean.base.essentials
import JuliaLean.Proofs.base.array.common.convert
import JuliaLean.Proofs.base.array.common.copy
import JuliaLean.Proofs.base.array.common.grow

attribute [local instance] JuliaLean.Proofs.base.array.layoutAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.nativeAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.layoutFunctionAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.nativeFunctionAllocationProjection

open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def BitIntegerEqualitySpec : Prop :=
  (∀ (t : IntTy) (A : Type) (values : A → List (JInt t))
      (dims : A → List Nat) (elementSize : I)
      (memcmp : A → A → I → I),
    (∀ a b, dims a = dims b → (values a).length = (values b).length) →
    (∀ a b, (values a).length = (values b).length →
      ((memcmp a b (elementSize * JInt.wrap .i64 ((values a).length : Int))).val = 0 ↔
        values a = values b)) →
    ∀ a b, equalBitInteger2171 (m := Id) dims (fun x y => decide (x = y))
      id (fun _ => ()) id (fun a => JInt.wrap .i64 ((values a).length : Int))
      elementSize memcmp (fun _ => ()) a b = true ↔
      dims a = dims b ∧ values a = values b) ∧
  (∀ (t : IntTy) (A : Type) (values : A → List (JInt t))
      (elementSize : I) (memcmp : A → A → I → I),
    (∀ a, (values a).length < 2 ^ 63) →
    (∀ a b, (values a).length = (values b).length →
      ((memcmp a b (elementSize * JInt.wrap .i64 ((values a).length : Int))).val = 0 ↔
        values a = values b)) →
    ∀ a b, equalBitIntegerVector (m := Id) id (fun _ => ()) id
      (fun a => JInt.wrap .i64 ((values a).length : Int)) elementSize
      memcmp (fun _ => ()) a b = true ↔ values a = values b)

private def byteLexCompare : List (JInt .u8) → List (JInt .u8) → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | x :: xs, y :: ys =>
    if x.val < y.val then -1 else if y.val < x.val then 1 else byteLexCompare xs ys

private def bytePrefixCompare : List (JInt .u8) → List (JInt .u8) → Int
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys =>
    if x.val < y.val then -1 else if y.val < x.val then 1 else bytePrefixCompare xs ys

private def byteLengthCompare (xs ys : List (JInt .u8)) : Int :=
  if xs.length < ys.length then -1 else if ys.length < xs.length then 1 else 0

private theorem bytePrefixCompare_cases (xs ys : List (JInt .u8)) :
    bytePrefixCompare xs ys = -1 ∨ bytePrefixCompare xs ys = 0 ∨ bytePrefixCompare xs ys = 1 := by
  induction xs generalizing ys with
  | nil => simp [bytePrefixCompare]
  | cons x xs ih =>
    cases ys with
    | nil => simp [bytePrefixCompare]
    | cons y ys =>
      simp only [bytePrefixCompare]
      split
      · exact Or.inl rfl
      · split
        · exact Or.inr (Or.inr rfl)
        · exact ih ys

private theorem byte_compare_decompose (xs ys : List (JInt .u8)) :
    (if bytePrefixCompare xs ys < 0 then -1 else
      if bytePrefixCompare xs ys > 0 then 1 else byteLengthCompare xs ys) = byteLexCompare xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [bytePrefixCompare, byteLexCompare, byteLengthCompare]
  | cons x xs ih =>
    cases ys with
    | nil => simp [bytePrefixCompare, byteLexCompare, byteLengthCompare]
    | cons y ys =>
      by_cases hxy : x.val < y.val
      · simp [bytePrefixCompare, byteLexCompare, hxy]
      · by_cases hyx : y.val < x.val
        · simp [bytePrefixCompare, byteLexCompare, hxy, hyx]
        · simpa [bytePrefixCompare, byteLexCompare, byteLengthCompare, hxy, hyx] using ih ys

/-- Byte-array comparison follows lexicographic byte order, with a shorter equal-prefix array first. -/
def ByteArrayComparisonSpec : Prop :=
  ∀ (memcmp : List (JInt .u8) → List (JInt .u8) → I → I),
    (∀ xs ys, xs.length < 2 ^ 63 → ys.length < 2 ^ 63 →
      ((memcmp xs ys (min (JInt.wrap .i64 xs.length) (JInt.wrap .i64 ys.length))).val < 0 ↔
        bytePrefixCompare xs ys = -1) ∧
      ((memcmp xs ys (min (JInt.wrap .i64 xs.length) (JInt.wrap .i64 ys.length))).val > 0 ↔
        bytePrefixCompare xs ys = 1)) →
    ∀ xs ys : List (JInt .u8), xs.length < 2 ^ 63 → ys.length < 2 ^ 63 →
      cmpBytes (m := Id) id (fun _ => ()) id
        (fun a => JInt.wrap .i64 a.length) memcmp (fun _ => ())
        (fun a b => JInt.wrap .i64 (JuliaLean.base.operators.cmpInteger
          (fun x y : I => decide (x.val < y.val))
          (fun x y : I => decide (x.val < y.val)) a b)) xs ys =
        JInt.wrap .i64 (byteLexCompare xs ys)
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round4
open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- `div(x, y)` for `Int` (int.jl `checked_sdiv_int`), with the divide error of this model. -/
def overallocationDivide (a b : I) : Except Error I :=
  match JuliaLean.base.int.checked_sdiv_int a b with
  | .ok v => .ok v
  | .error _ => .error .divide

/-- `overallocation(maxsize)` (array.jl:1102) with the `ctlz_int`, `div` and `<<` of int.jl. -/
def overallocationInt (n : I) : Except Error I :=
  overallocation (m := Except Error) JuliaLean.base.int.ctlz_int overallocationDivide
    JuliaLean.base.int.shl_Int n
private def byteLexCompare : List (JInt .u8) → List (JInt .u8) → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | x :: xs, y :: ys =>
    if x.val < y.val then -1 else if y.val < x.val then 1 else byteLexCompare xs ys

def byteMemcmp (p q : JuliaLean.base.pointer.Ptr Unit) (n : I) : ByteM I :=
  byteCall (fun heap => (JuliaLean.base.cmem.memcmp cLibrary
    (fun n : I => JuliaLean.base.cmem.remCsizeInt n.val) heap p q n).map (fun r => (heap, r)))

/-- `cmp(a::Vector{UInt8}, b::Vector{UInt8})` (array.jl:2156; `cmp` docstring in operators.jl:
"Return -1, 0, or 1 depending on whether `x` is less than, equal to, or greater than `y`") for byte
vectors of lengths `a.2`, `b.2` whose data start at bytes `a.1`, `b.1`: the result is the
lexicographic comparison of the two byte sequences, a proper prefix ordering first, through
cmem.jl's `memcmp` over cmem.lean's C library and operators.jl's `cmp` of the lengths; the heap is
unchanged. -/
def ByteArrayComparisonSpec : Prop :=
  ∀ (heap : JuliaLean.base.pointer.ByteHeap) (a b : Nat × Nat),
    a.2 < 2 ^ 63 → b.2 < 2 ^ 63 →
    JuliaLean.base.cmem.validRange heap (bytePtr a.1) (JInt.wrap .u64 a.2) →
    JuliaLean.base.cmem.validRange heap (bytePtr b.1) (JInt.wrap .u64 b.2) →
    (cmpBytes (m := ByteM) (fun a : Nat × Nat => pure a) (fun _ => pure ())
      (fun ref => pure (bytePtr ref.1)) (fun a => pure (JInt.wrap .i64 a.2)) byteMemcmp
      (fun _ => pure ())
      (fun x y => pure (JInt.wrap .i64 (JuliaLean.base.operators.cmpInteger
        (fun x y : I => decide (x.val < y.val)) (fun x y : I => decide (x.val < y.val)) x y)))
      a b).run heap =
      .ok (JInt.wrap .i64 (byteLexCompare (heap.readBytes a.1 a.2) (heap.readBytes b.1 b.2)), heap)

def StoresValues {T : Type} (codec : JuliaLean.base.pointer.ByteCodec T)
    (heap : JuliaLean.base.pointer.ByteHeap) (address : Nat) (values : List T) : Prop :=
  heap.readBytes address (values.length * codec.elementSize.val.toNat) =
    values.flatMap codec.encode

/-- `==(a::Arr, b::Arr) where {Arr <: BitIntegerArray}` and its one-dimensional method
(array.jl:2171, 2188; "use memcmp for == on bit integer types"), against the documented array
equality (`==` docstring in operators.jl and abstractarray.jl: arrays are equal when they have the
same shape and equal elements). For arrays of any BitInteger width whose elements are stored in the
byte heap through the type's byte representation (`ByteCodec`, the runtime layout, which has no
Lean model; its own laws say the encoding has exactly `sizeof(T)` bytes and is invertible), with
cmem.jl's `memcmp` over cmem.lean's C library: the result is `true` exactly when the shapes (for
the vector method, lengths) agree and the element values agree. -/
def BitIntegerEqualitySpec : Prop :=
  ∀ (t : IntTy) (codec : JuliaLean.base.pointer.ByteCodec (JInt t))
    (heap : JuliaLean.base.pointer.ByteHeap)
    (pa pb : Nat) (da db : List Nat) (xs ys : List (JInt t)),
    xs.length = da.prod → ys.length = db.prod →
    xs.length * codec.elementSize.val.toNat < 2 ^ 63 →
    ys.length * codec.elementSize.val.toNat < 2 ^ 63 →
    StoresValues codec heap pa xs → StoresValues codec heap pb ys →
    JuliaLean.base.cmem.validRange heap (bytePtr pa)
      (JInt.wrap .u64 (xs.length * codec.elementSize.val.toNat)) →
    JuliaLean.base.cmem.validRange heap (bytePtr pb)
      (JInt.wrap .u64 (ys.length * codec.elementSize.val.toNat)) →
    (equalBitInteger2171 (m := ByteM) (fun a : Nat × List Nat => pure a.2)
      (fun d e => decide (d = e)) (fun a => pure a) (fun _ => pure ())
      (fun ref => pure (bytePtr ref.1)) (fun a => pure (JInt.wrap .i64 a.2.prod))
      codec.elementSize byteMemcmp (fun _ => pure ()) (pa, da) (pb, db)).run heap =
      .ok (decide (da = db ∧ xs = ys), heap) ∧
    (da.length = 1 → db.length = 1 →
      (equalBitIntegerVector (m := ByteM) (fun a : Nat × List Nat => pure a) (fun _ => pure ())
        (fun ref => pure (bytePtr ref.1)) (fun a => pure (JInt.wrap .i64 a.2.prod))
        codec.elementSize byteMemcmp (fun _ => pure ()) (pa, da) (pb, db)).run heap =
        .ok (decide (xs = ys), heap))
end round4
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace opusGrowth
open JuliaLean JuliaLean.base.array
section
variable {α : Type}

theorem imin_val' (a b : I) : (@min I Subtype.instMin a b).val = min a.val b.val := rfl
end
end opusGrowth
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayGrow
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.array.round4
open JuliaLean.Proofs.base.array.opusGrowth
set_option maxHeartbeats 1000000
attribute [local irreducible] JInt.wrap

theorem vecAt_fresh (s : MutableMemory α) (n : I) (hn : 0 ≤ n.val) :
    VecAt { memories := s.memories ++ [List.replicate n.val.toNat none],
            arrays := s.arrays ++ [⟨(s.memories.length,one),n⟩] }
      s.arrays.length s.memories.length one n (List.replicate n.val.toNat none) := by
  have hb := ival_bounds n
  refine ⟨?_,?_,?_,hn,?_,?_⟩
  · simp
  · simp
  · rw [ival_one]; decide
  · simp only [ival_one,List.length_replicate]
    omega
  · simp only [List.length_replicate]
    omega
end solArrayGrow
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace ChatGPTBatch1.ArrayBytes
open JuliaLean JuliaLean.base.pointer JuliaLean.base.cmem

/-- Lexicographic comparison of bytes, including the proper-prefix case. -/
def batch1_byteLex : List Byte → List Byte → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | x :: xs, y :: ys =>
      if x.val < y.val then -1 else if y.val < x.val then 1 else batch1_byteLex xs ys

/-- Comparison of the common-length byte prefix. -/
def batch1_bytePrefix : List Byte → List Byte → Int
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys =>
      if x.val < y.val then -1 else if y.val < x.val then 1 else batch1_bytePrefix xs ys

def batch1_lengthCmp (xs ys : List Byte) : Int :=
  if xs.length < ys.length then -1 else if ys.length < xs.length then 1 else 0

theorem batch1_bytePrefix_cases (xs ys : List Byte) :
    batch1_bytePrefix xs ys = -1 ∨ batch1_bytePrefix xs ys = 0 ∨
      batch1_bytePrefix xs ys = 1 := by
  induction xs generalizing ys with
  | nil => exact Or.inr (Or.inl rfl)
  | cons x xs ih =>
    cases ys with
    | nil => exact Or.inr (Or.inl rfl)
    | cons y ys =>
      unfold batch1_bytePrefix
      split
      · exact Or.inl rfl
      · split
        · exact Or.inr (Or.inr rfl)
        · exact ih ys

theorem batch1_byte_compare_decompose (xs ys : List Byte) :
    (if batch1_bytePrefix xs ys < 0 then -1 else
      if batch1_bytePrefix xs ys > 0 then 1 else batch1_lengthCmp xs ys) =
      batch1_byteLex xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp only [batch1_bytePrefix, batch1_byteLex, batch1_lengthCmp,
      List.length_nil, List.length_cons, Int.lt_irrefl, Nat.lt_irrefl, ite_false, Nat.zero_lt_succ, ite_true]
  | cons x xs ih =>
    cases ys with
    | nil => simp only [batch1_bytePrefix, batch1_byteLex, batch1_lengthCmp,
        List.length_nil, List.length_cons, Int.lt_irrefl, ite_false, Nat.not_lt_zero,
        Nat.zero_lt_succ, ite_true]
    | cons y ys =>
      by_cases hxy : x.val < y.val
      · simp only [batch1_bytePrefix, batch1_byteLex, hxy, ite_true, show (-1 : Int) < 0 from by decide]
      · by_cases hyx : y.val < x.val
        · simp only [batch1_bytePrefix, batch1_byteLex, hxy, hyx, ite_false, ite_true,
            show ¬ (1 : Int) < 0 from by decide, show (1 : Int) > 0 from by decide]
        · simpa only [batch1_bytePrefix, batch1_byteLex, batch1_lengthCmp, hxy, hyx,
            ite_false, List.length_cons, Nat.add_lt_add_iff_right] using ih ys

theorem batch1_readBytes_length (heap : ByteHeap) (address size : Nat) :
    (heap.readBytes address size).length = size := by
  induction size generalizing address with
  | zero => rfl
  | succ size ih =>
    simp only [ByteHeap.readBytes, List.length_cons, ih]

theorem batch1_readBytes_mod (heap : ByteHeap) (size : Nat) :
    ∀ a b, a % 2 ^ 64 = b % 2 ^ 64 → heap.readBytes a size = heap.readBytes b size := by
  induction size with
  | zero => intros; rfl
  | succ size ih =>
    intro a b h
    simp only [ByteHeap.readBytes]
    congr 1
    · exact congrArg heap.byteAt h
    · exact ih (a + 1) (b + 1) (by
        rw [Nat.add_mod a 1, Nat.add_mod b 1, h])

theorem batch1_cMemcmp_prefix (heap : ByteHeap) (na nb : Nat) :
    ∀ a b, (StandardC.cMemcmp heap a b (min na nb)).val =
      batch1_bytePrefix (heap.readBytes a na) (heap.readBytes b nb) := by
  induction na generalizing nb with
  | zero => intros; rfl
  | succ na ih =>
    intro a b
    cases nb with
    | zero => rfl
    | succ nb =>
      rw [show min (na + 1) (nb + 1) = min na nb + 1 from by omega]
      simp only [ByteHeap.readBytes, batch1_bytePrefix, StandardC.cMemcmp]
      by_cases heq : heap.readByte a = heap.readByte b
      · have hv : (heap.readByte a).val = (heap.readByte b).val := congrArg Subtype.val heq
        simp only [heq, Int.lt_irrefl, ite_false, ite_true]
        exact ih nb (a + 1) (b + 1)
      · have hv : (heap.readByte a).val ≠ (heap.readByte b).val :=
          fun h => heq (Subtype.ext h)
        rw [if_neg heq]
        by_cases hlt : (heap.readByte a).val < (heap.readByte b).val
        · simp only [hlt, ite_true, StandardC.i32Lit]
        · have hgt : (heap.readByte b).val < (heap.readByte a).val := by omega
          simp only [hlt, hgt, ite_false, ite_true, StandardC.i32Lit]

theorem batch1_u64_nat_mod (n : Nat) :
    (JInt.wrap .u64 (n : Int)).val.toNat = n % 2 ^ 64 := by
  change ((n : Int) % (18446744073709551616 : Int)).toNat = n % 18446744073709551616
  omega


/-- A zero comparison of equally long byte sequences characterizes equality. -/
theorem batch1_bytePrefix_zero_iff (xs ys : List Byte) (hl : xs.length = ys.length) :
    batch1_bytePrefix xs ys = 0 ↔ xs = ys := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp hl.symm
    subst ys
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.length_cons, List.length_nil] at hl; omega
    | cons y ys =>
      have hl' : xs.length = ys.length := by
        simp only [List.length_cons] at hl
        omega
      by_cases hxy : x.val < y.val
      · simp only [batch1_bytePrefix, hxy, ite_true]
        constructor
        · intro h; omega
        · intro h
          have he := congrArg (fun z : List Byte => (z.headD x).val) h
          change x.val = y.val at he
          omega
      · by_cases hyx : y.val < x.val
        · simp only [batch1_bytePrefix, hxy, hyx, ite_false, ite_true]
          constructor
          · intro h; omega
          · intro h
            have he := congrArg (fun z : List Byte => (z.headD x).val) h
            change x.val = y.val at he
            omega
        · have he : x = y := Subtype.ext (by omega)
          subst y
          simp only [batch1_bytePrefix, Int.lt_irrefl, ite_false, List.cons.injEq,
            true_and, ih ys hl']

/-- Every codec for a nontrivial machine-integer type has positive byte width. -/
theorem batch1_codec_size_pos (t : IntTy) (codec : ByteCodec (JInt t)) :
    0 < codec.elementSize.val.toNat := by
  by_cases h : 0 < codec.elementSize.val.toNat
  · exact h
  have hz : codec.elementSize.val.toNat = 0 := by omega
  have h0 : codec.encode (JInt.wrap t 0) = [] :=
    List.length_eq_zero_iff.mp ((codec.encode_length _).trans hz)
  have h1 : codec.encode (JInt.wrap t 1) = [] :=
    List.length_eq_zero_iff.mp ((codec.encode_length _).trans hz)
  have he : JInt.wrap t 0 = JInt.wrap t 1 := by
    rw [← codec.decode_encode (JInt.wrap t 0), h0, ← h1, codec.decode_encode]
  have hn : JInt.wrap t 0 ≠ JInt.wrap t 1 := by cases t <;> decide
  exact False.elim (hn he)

/-- A fixed-width invertible encoding is injective on equally long element lists. -/
theorem batch1_codec_lists_injective {T : Type} (codec : ByteCodec T)
    (xs ys : List T) (hl : xs.length = ys.length)
    (he : xs.flatMap codec.encode = ys.flatMap codec.encode) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    exact (List.length_eq_zero_iff.mp hl.symm).symm
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.length_cons, List.length_nil] at hl; omega
    | cons y ys =>
      have hl' : xs.length = ys.length := by
        simp only [List.length_cons] at hl
        omega
      change codec.encode x ++ xs.flatMap codec.encode =
        codec.encode y ++ ys.flatMap codec.encode at he
      have ht := congrArg (List.take codec.elementSize.val.toNat) he
      have hx : (codec.encode x ++ xs.flatMap codec.encode).take codec.elementSize.val.toNat =
          codec.encode x := by rw [← codec.encode_length x, List.take_append_length]
      have hy : (codec.encode y ++ ys.flatMap codec.encode).take codec.elementSize.val.toNat =
          codec.encode y := by rw [← codec.encode_length y, List.take_append_length]
      rw [hx, hy] at ht
      have hxy : x = y := by
        rw [← codec.decode_encode x, ht, codec.decode_encode]
      subst y
      have htail := List.append_cancel_left he
      exact congrArg (List.cons x) (ih ys hl' htail)
end ChatGPTBatch1.ArrayBytes
end
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace ChatGPTBatch1.Array
open _root_.JuliaLean.Proofs.base.array.ChatGPTBatch1.ArrayBytes
open _root_.JuliaLean.Proofs.base.array.ChatGPTBatch1.ArrayFilter
open _root_.JuliaLean.Proofs.base.array.ChatGPTBatch1.ArrayRange




open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

open JuliaLean.Proofs.base.array.round6b (IntegerArgument bytePointer)

attribute [local irreducible] JInt.wrap wrapInt

theorem batch1_iMin_val (a b : I) : (min a b).val = min a.val b.val := by
  change (if a.val ≤ b.val then a else b).val = _
  by_cases h : a.val ≤ b.val
  · rw [if_pos h, Int.min_eq_left h]
  · rw [if_neg h, Int.min_eq_right (by omega)]

theorem batch1_iMin_subtype (a b : I) : @min I Subtype.instMin a b = min a b := by
  apply Subtype.ext
  rw [opusGrowth.imin_val', batch1_iMin_val]
end ChatGPTBatch1.Array
end
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace ChatGPTBatch1.Array
open _root_.JuliaLean.Proofs.base.array.ChatGPTBatch1.ArrayBytes
open _root_.JuliaLean.Proofs.base.array.ChatGPTBatch1.ArrayFilter
open _root_.JuliaLean.Proofs.base.array.ChatGPTBatch1.ArrayRange




open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

open JuliaLean.Proofs.base.array.round6b (IntegerArgument bytePointer)

attribute [local irreducible] JInt.wrap wrapInt


open JuliaLean.base.pointer JuliaLean.base.cmem

/-- Reading through a wrapped pointer is the same modular byte sequence. -/
theorem batch1_readBytes_bytePtr (heap : ByteHeap) (a n : Nat) :
    heap.readBytes (pointerAddress (round4.bytePtr a)) n = heap.readBytes a n := by
  apply batch1_readBytes_mod
  change (JInt.wrap .u64 (a : Int)).val.toNat % 2 ^ 64 = a % 2 ^ 64
  rw [batch1_u64_nat_mod, Nat.mod_mod]

/-- The concrete memcmp wrapper compares precisely the common prefix. -/
theorem batch1_byteMemcmp_run (heap : ByteHeap) (a b : Nat × Nat)
    (ha : a.2 < 2 ^ 63) (hb : b.2 < 2 ^ 63) :
    (round4.byteMemcmp (round4.bytePtr a.1) (round4.bytePtr b.1)
      (min (JInt.wrap .i64 a.2) (JInt.wrap .i64 b.2))).run heap =
      .ok (JInt.wrap .i64 (batch1_bytePrefix (heap.readBytes a.1 a.2)
        (heap.readBytes b.1 b.2)), heap) := by
  have hva : (JInt.wrap .i64 (a.2 : Int)).val = a.2 := ival_wrap _ (by omega)
  have hvb : (JInt.wrap .i64 (b.2 : Int)).val = b.2 := ival_wrap _ (by omega)
  have hvmin : (min (JInt.wrap .i64 (a.2 : Int)) (JInt.wrap .i64 (b.2 : Int))).val =
      (min a.2 b.2 : Nat) := by
    rw [batch1_iMin_val, hva, hvb]
    omega
  have hsize : (JInt.wrap .u64
      (min (JInt.wrap .i64 (a.2 : Int)) (JInt.wrap .i64 (b.2 : Int))).val).val.toNat =
      min a.2 b.2 := by
    rw [hvmin, batch1_u64_nat_mod]
    exact Nat.mod_eq_of_lt (by omega)
  change Except.ok (JInt.wrap .i64
    (StandardC.cMemcmp heap (pointerAddress (round4.bytePtr a.1))
      (pointerAddress (round4.bytePtr b.1))
      (JInt.wrap .u64
        (min (JInt.wrap .i64 (a.2 : Int)) (JInt.wrap .i64 (b.2 : Int))).val).val.toNat).val,
    heap) = _
  rw [hsize, batch1_cMemcmp_prefix, batch1_readBytes_bytePtr, batch1_readBytes_bytePtr]

/-- The C byte comparison and the length comparison compose to lexicographic order. -/
theorem MultidimcovArrayV2CmpBytes_proven :
    JuliaLean.Proofs.base.array.round4.ByteArrayComparisonSpec := by
  intro heap a b ha hb _ _
  have hva : (JInt.wrap .i64 (a.2 : Int)).val = a.2 := ival_wrap _ (by omega)
  have hvb : (JInt.wrap .i64 (b.2 : Int)).val = b.2 := ival_wrap _ (by omega)
  have hmem := batch1_byteMemcmp_run heap a b ha hb
  have hprefix := batch1_bytePrefix_cases (heap.readBytes a.1 a.2) (heap.readBytes b.1 b.2)
  have hpval : (JInt.wrap .i64 (batch1_bytePrefix (heap.readBytes a.1 a.2)
      (heap.readBytes b.1 b.2))).val =
      batch1_bytePrefix (heap.readBytes a.1 a.2) (heap.readBytes b.1 b.2) :=
    ival_wrap _ (by rcases hprefix with h | h | h <;> rw [h] <;> omega)
  have hcmpLength : JuliaLean.base.operators.cmpInteger
      (fun x y : I => decide (x.val < y.val))
      (fun x y : I => decide (x.val < y.val))
      (JInt.wrap .i64 a.2) (JInt.wrap .i64 b.2) =
      batch1_lengthCmp (heap.readBytes a.1 a.2) (heap.readBytes b.1 b.2) := by
    simp only [JuliaLean.base.operators.cmpInteger, hva, hvb,
      batch1_lengthCmp, batch1_readBytes_length, Int.ofNat_lt]
    by_cases hab : a.2 < b.2
    · simp only [hab, decide_true, ite_true, JuliaLean.base.operators.ifelseValue]
    · by_cases hba : b.2 < a.2
      · simp only [hab, hba, decide_false, decide_true, ite_false, ite_true,
          JuliaLean.base.operators.ifelseValue]
      · simp only [hab, hba, decide_false, ite_false, JuliaLean.base.operators.ifelseValue]
  refine Eq.trans (b := Except.ok (JInt.wrap .i64 (batch1_byteLex (heap.readBytes a.1 a.2)
    (heap.readBytes b.1 b.2)), heap)) ?_ ?_
  · simp only [cmpBytes, pure_bind, batch1_stateBind_run, batch1_iMin_subtype,
      hmem, hpval, hcmpLength]
    have hdecomp := batch1_byte_compare_decompose
      (heap.readBytes a.1 a.2) (heap.readBytes b.1 b.2)
    split
    · rw [if_pos ‹_›] at hdecomp
      rw [← hdecomp]
      rfl
    · split
      · rw [if_neg ‹_›, if_pos ‹_›] at hdecomp
        rw [← hdecomp]
        rfl
      · rw [if_neg ‹_›, if_neg ‹_›] at hdecomp
        rw [hdecomp]
        rfl
  · clear hmem hprefix hpval hcmpLength
    apply congrArg (fun z => Except.ok (JInt.wrap .i64 z, heap))
    generalize heap.readBytes a.1 a.2 = xs
    generalize heap.readBytes b.1 b.2 = ys
    induction xs generalizing ys with
    | nil => cases ys <;> rfl
    | cons x xs ih =>
      cases ys with
      | nil => rfl
      | cons y ys =>
        change (if x.val < y.val then (-1 : Int) else
            if y.val < x.val then 1 else batch1_byteLex xs ys) =
          (if x.val < y.val then (-1 : Int) else if y.val < x.val then 1 else _)
        by_cases hxy : x.val < y.val
        · simp only [hxy, ite_true]
        · by_cases hyx : y.val < x.val
          · simp only [hxy, hyx, ite_false, ite_true]
          · simp only [hxy, hyx, ite_false]
            exact ih ys


/-- The byte count of a valid typed array agrees with exact natural multiplication. -/
theorem batch1_codec_byte_count (t : IntTy) (codec : ByteCodec (JInt t))
    (xs : List (JInt t)) (hn : xs.length * codec.elementSize.val.toNat < 2 ^ 63) :
    codec.elementSize * JInt.wrap .i64 (xs.length : Int) =
      JInt.wrap .i64 (xs.length * codec.elementSize.val.toNat : Nat) := by
  have hpos := batch1_codec_size_pos t codec
  have hle := Nat.le_mul_of_pos_right xs.length hpos
  have hlen : (JInt.wrap .i64 (xs.length : Int)).val = xs.length := ival_wrap _ (by omega)
  change JInt.wrap .i64 (codec.elementSize.val * (JInt.wrap .i64 (xs.length : Int)).val) =
    JInt.wrap .i64 (xs.length * codec.elementSize.val.toNat : Nat)
  apply congrArg (JInt.wrap .i64)
  rw [hlen, Int.natCast_mul, Int.toNat_of_nonneg codec.size_nonnegative, Int.mul_comm]

/-- With equal element counts, memcmp is zero exactly for equal values. -/
theorem batch1_bit_compare_run (t : IntTy) (codec : ByteCodec (JInt t))
    (heap : ByteHeap) (pa pb : Nat) (xs ys : List (JInt t))
    (hl : xs.length = ys.length)
    (hn : xs.length * codec.elementSize.val.toNat < 2 ^ 63)
    (hx : round4.StoresValues codec heap pa xs)
    (hy : round4.StoresValues codec heap pb ys) :
    (do let c ← round4.byteMemcmp (round4.bytePtr pa) (round4.bytePtr pb)
          (codec.elementSize * JInt.wrap .i64 (xs.length : Int))
        pure (c.val == 0) : round4.ByteM Bool).run heap = .ok (decide (xs = ys), heap) := by
  let n := xs.length * codec.elementSize.val.toNat
  let as' := heap.readBytes pa n
  let bs' := heap.readBytes pb n
  have hm : (round4.byteMemcmp (round4.bytePtr pa) (round4.bytePtr pb)
      (codec.elementSize * JInt.wrap .i64 (xs.length : Int))).run heap =
      .ok (JInt.wrap .i64 (batch1_bytePrefix as' bs'), heap) := by
    rw [batch1_codec_byte_count t codec xs hn]
    have hmin : min (JInt.wrap .i64 (n : Int)) (JInt.wrap .i64 (n : Int)) =
        JInt.wrap .i64 (n : Int) := by
      apply Subtype.ext
      rw [batch1_iMin_val, Int.min_self]
    simpa only [hmin] using batch1_byteMemcmp_run heap (pa, n) (pb, n) hn hn
  have h0 : batch1_bytePrefix as' bs' = 0 ↔ xs = ys := by
    have he := batch1_bytePrefix_zero_iff as' bs' (by
      simp only [as', bs', batch1_readBytes_length])
    apply he.trans
    constructor
    · intro hb
      apply batch1_codec_lists_injective codec xs ys hl
      unfold round4.StoresValues at hx hy
      rw [← hl] at hy
      exact hx.symm.trans (hb.trans hy)
    · intro heq
      unfold round4.StoresValues at hx hy
      rw [← hl] at hy
      exact hx.trans ((congrArg (List.flatMap codec.encode) heq).trans hy.symm)
  have hp := batch1_bytePrefix_cases as' bs'
  have hv : (JInt.wrap .i64 (batch1_bytePrefix as' bs')).val = batch1_bytePrefix as' bs' :=
    ival_wrap _ (by rcases hp with hp | hp | hp <;> rw [hp] <;> omega)
  have hz : ((JInt.wrap .i64 (batch1_bytePrefix as' bs')).val == 0) = decide (xs = ys) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, hv]
    exact h0
  change (match (round4.byteMemcmp (round4.bytePtr pa) (round4.bytePtr pb)
      (codec.elementSize * JInt.wrap .i64 (xs.length : Int))).run heap with
    | .error e => Except.error e
    | .ok (c, after) => Except.ok (c.val == 0, after)) = _
  rw [hm]
  exact congrArg (fun b => Except.ok (b, heap)) hz

/-- Both bit-integer equality methods agree with shape and element equality. -/
theorem MultidimcovArrayV2EqBitint_proven :
    JuliaLean.Proofs.base.array.round4.BitIntegerEqualitySpec := by
  intro t codec heap pa pb da db xs ys hxda hydb hxn hyn hx hy _ _
  have hpos := batch1_codec_size_pos t codec
  have hleX := Nat.le_mul_of_pos_right xs.length hpos
  have hleY := Nat.le_mul_of_pos_right ys.length hpos
  have hvx : (JInt.wrap .i64 (da.prod : Int)).val = xs.length := by
    rw [← hxda]
    exact ival_wrap _ (by omega)
  have hvy : (JInt.wrap .i64 (db.prod : Int)).val = ys.length := by
    rw [← hydb]
    exact ival_wrap _ (by omega)
  constructor
  · by_cases hd : da = db
    · have hl : xs.length = ys.length := by rw [hxda, hydb, hd]
      have hcmp := batch1_bit_compare_run t codec heap pa pb xs ys hl hxn hx hy
      have hshape : decide (da = db) = true := decide_eq_true hd
      simp only [equalBitInteger2171, pure_bind, hshape, ite_true]
      rw [← hxda]
      simpa only [hd, true_and] using hcmp
    · simp only [equalBitInteger2171, pure_bind, hd, decide_false, Bool.false_eq_true,
        ite_false, false_and, batch1_statePure_run]
  · intro _ _
    by_cases hl : xs.length = ys.length
    · have hi : JInt.wrap .i64 (da.prod : Int) = JInt.wrap .i64 (db.prod : Int) := by
        apply Subtype.ext
        rw [hvx, hvy, hl]
      simp only [equalBitIntegerVector, pure_bind]
      rw [if_pos hi, ← hxda]
      exact batch1_bit_compare_run t codec heap pa pb xs ys hl hxn hx hy
    · have hi : JInt.wrap .i64 (da.prod : Int) ≠ JInt.wrap .i64 (db.prod : Int) := by
        intro he
        have he' := congrArg Subtype.val he
        rw [hvx, hvy] at he'
        exact hl (by omega)
      have hxy : xs ≠ ys := fun he => hl (congrArg List.length he)
      simp only [equalBitIntegerVector, pure_bind, hi, ite_false, hxy, decide_false,
        batch1_statePure_run]
end ChatGPTBatch1.Array
end
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion
open JuliaLean JuliaLean.base.array
open JuliaLean.Registry

/-- The promoted midpoint method does not start midpoint computation until
promotion succeeds, preserving all effects of a failed promotion. -/
def MidpointPromotionErrors : Prop :=
  ∀ (W X Y P : Type) (promote : X → Y → ExceptT Error (StateM W) (P × P))
    (midpoint : P → P → ExceptT Error (StateM W) P) (lo : X) (hi : Y)
    (before after : W) (error : Error),
    (promote lo hi).run before = (.error error, after) →
    (midpointPromoted promote midpoint lo hi).run before = (.error error, after)
end JuliaLean.Proofs.base.array.Completion


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array
end JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
theorem JuliaLean.Proofs.base.array.Completion.MidpointPromotionErrors_proven : JuliaLean.Proofs.base.array.Completion.MidpointPromotionErrors := by
  unfold JuliaLean.Proofs.base.array.Completion.MidpointPromotionErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.midpoint, JuliaLean.base.array.midpointPromoted, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

namespace JuliaLean.Proofs.base.array
def entriesCmp1 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-cmp-bytes", juliaFile := "base/array.jl",
    juliaFns := ["cmp(a::Array{UInt8,1}, b::Array{UInt8,1})"],
    statement := "`cmp(a::Vector{UInt8}, b::Vector{UInt8})` (array.jl:2156; `cmp` docstring in operators.jl: \"Return -1, 0, or 1 depending on whether `x` is less than, equal to, or greater than `y`\") for byte vectors of lengths `a.2`, `b.2` whose data start at bytes `a.1`, `b.1`: the result is the lexicographic comparison of the two byte sequences, a proper prefix ordering first, through cmem.jl's `memcmp` over cmem.lean's C library and operators.jl's `cmp` of the lengths; the heap is unchanged.",
    source := "base/array.jl:2156", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round4.ByteArrayComparisonSpec, thm := some ``ChatGPTBatch1.Array.MultidimcovArrayV2CmpBytes_proven,
    notes := "" }
]
def entriesCmp2 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-eq-bitint", juliaFile := "base/array.jl",
    juliaFns := ["==(a::Array{<:BitInteger}, b::Array{<:BitInteger})", "==(a::Vector{<:BitInteger}, b::Vector{<:BitInteger})"],
    statement := "`==(a::Arr, b::Arr) where {Arr <: BitIntegerArray}` and its one-dimensional method (array.jl:2171, 2188; \"use memcmp for == on bit integer types\"), against the documented array equality (`==` docstring in operators.jl and abstractarray.jl: arrays are equal when they have the same shape and equal elements). For arrays of any BitInteger width whose elements are stored in the byte heap through the type's byte representation (`ByteCodec`, the runtime layout, which has no Lean model; its own laws say the encoding has exactly `sizeof(T)` bytes and is invertible), with cmem.jl's `memcmp` over cmem.lean's C library: the result is `true` exactly when the shapes (for the vector method, lengths) agree and the element values agree.",
    source := "base/array.jl:2171", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round4.BitIntegerEqualitySpec, thm := some ``ChatGPTBatch1.Array.MultidimcovArrayV2EqBitint_proven,
    notes := "" }
]
def entriesCmp3 : List JuliaLean.Registry.Entry := [
{ id := "array-midpoint-promotion-errors", juliaFile := "base/array.jl",
  juliaFns := ["midpoint(lo::Integer, hi::Integer)"],
  statement := "The promoted midpoint method does not start midpoint computation until promotion succeeds, preserving all effects of a failed promotion.",
  source := "base/array.jl:2284-2284", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion.MidpointPromotionErrors, thm := some ``JuliaLean.Proofs.base.array.Completion.MidpointPromotionErrors_proven,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." }
]
end JuliaLean.Proofs.base.array

