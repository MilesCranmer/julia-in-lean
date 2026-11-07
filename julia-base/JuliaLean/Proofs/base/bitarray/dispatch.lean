import JuliaLean.base.bitarray
import JuliaLean.Registry.Types

namespace JuliaLean.CompletionState

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

end JuliaLean.CompletionState

namespace JuliaLean.Proofs.base.bitarray.Completion
open JuliaLean JuliaLean.base.bitarray JuliaLean.base.bitarray.Models1Group15

def PrependIteratorConversionErrors : Prop :=
  ∀ (I : Type) (runtime : AllocationData) (target : Ref 1) (items : I)
    (toBitVector : I → ObjectM (Ref 1)) (initial final : ObjectState)
    (error : JuliaLean.base.array.Error),
    (toBitVector items).run initial = (.error error, final) →
    (prependIterableConvert runtime toBitVector target items).run initial = (.error error, final)

def ReverseTupleDispatchErrors : Prop :=
  ∀ (World A D R : Type) (reverseDim : A → D → ExceptT JuliaLean.base.array.Error (StateM World) R)
    (array : A) (dimension : D) (initial final : World) (error : JuliaLean.base.array.Error),
    (reverseDim array dimension).run initial = (.error error, final) →
    (bitArrayReverseTupleDispatch reverseDim array (dimension, ())).run initial = (.error error, final)

theorem prependIteratorConversionErrors : PrependIteratorConversionErrors := by
  intro I runtime target items toBitVector initial final error h
  simp [prependIterableConvert, bitVectorPrependIterableDispatch, h]

theorem reverseTupleDispatchErrors : ReverseTupleDispatchErrors := by
  intro World A D R reverseDim array dimension initial final error h
  exact h

end JuliaLean.Proofs.base.bitarray.Completion

namespace JuliaLean.Proofs.base.bitarray.Completion
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

def EqualityShapeMismatch : Prop :=
  ∀ (N M : Nat) (left : BitArray N) (right : BitArray M)
    (memcmp : (Nat × I64) → (Nat × I64) → I64 → BitMutationM I64)
    (state : MutableMemory U64), bitArraySizeRanked left ≠ bitArraySizeRanked right →
    (bitArrayEqualNative memcmp left right).run state = (.ok false, state)

theorem equalityShapeMismatch : EqualityShapeMismatch := by
  intro N M left right memcmp state h
  simp [bitArrayEqualNative, bitArrayEqualWith, h]

end JuliaLean.Proofs.base.bitarray.Completion

namespace JuliaLean.Proofs.base.bitarray.Completion
open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.base.bitarray.Models1Group15

abbrev Contains {N : Nat} (state : ObjectState) (reference : Ref N) (header : BitArray N) :=
  state.objects[reference.identity]? = some (⟨N, header⟩ : Sigma BitArray)

def MappedWordConversionFailure : Prop :=
  ∀ (Raw Converted : Type) (conversion : WordAssignment Raw Converted)
    (chunks : Nat) (index : I64) (raw : Raw) (state final : ObjectState) (error : Error),
    conversion.asWord raw = none →
    (conversion.convert raw).run state = (.error error, final) →
    (assignMappedWord conversion chunks index raw).run state = (.error error, final)

def UnaryMapEmpty : Prop :=
  ∀ (D N : Nat) (Raw Converted Masked Tail TailConverted : Type)
    (f : U64 → ObjectM Raw) (andMask : Raw → U64 → ObjectM Masked)
    (orMask : U64 → Masked → ObjectM Tail)
    (assignment : WordAssignment Raw Converted) (tailAssignment : WordAssignment Tail TailConverted)
    (destination : Ref D) (source : Ref N) (dest : BitArray D) (A : BitArray N)
    (state : ObjectState), Contains state destination dest → Contains state source A →
    A.len = int 0 → 0 ≤ dest.len.val →
    (bitMapUnaryGeneric f andMask orMask assignment tailAssignment destination source).run state =
      (.ok destination, state)

def BinaryMapEmpty : Prop :=
  ∀ (D N K : Nat) (Raw Converted Masked Tail TailConverted : Type)
    (f : U64 → U64 → ObjectM Raw) (andMask : Raw → U64 → ObjectM Masked)
    (orMask : U64 → Masked → ObjectM Tail)
    (assignment : WordAssignment Raw Converted) (tailAssignment : WordAssignment Tail TailConverted)
    (destination : Ref D) (left : Ref N) (right : Ref K)
    (dest : BitArray D) (A : BitArray N) (B : BitArray K) (state : ObjectState),
    Contains state destination dest → Contains state left A → Contains state right B →
    0 ≤ A.len.val → 0 ≤ B.len.val → 0 ≤ dest.len.val →
    (A.len = int 0 ∨ B.len = int 0) →
    (bitMapBinaryGeneric f andMask orMask assignment tailAssignment destination left right).run state =
      (.ok destination, state)

theorem mappedWordConversionFailure : MappedWordConversionFailure := by
  intro Raw Converted conversion chunks index raw state final error hraw hconvert
  simp [assignMappedWord, hraw, hconvert]

theorem unaryMapEmpty : UnaryMapEmpty := by
  intro D N Raw Converted Masked Tail TailConverted f andMask orMask assignment tailAssignment destination source dest A state hdest hsource hempty hnonneg
  have hcap : ¬ (int 0 > dest.len) := by change ¬ (dest.len.val < 0); omega
  simp only [Contains] at hdest hsource
  simp [bitMapUnaryGeneric, readObject, hdest, hsource, hempty, hcap]

theorem binaryMapEmpty : BinaryMapEmpty := by
  intro D N K Raw Converted Masked Tail TailConverted f andMask orMask assignment tailAssignment destination left right dest A B state hdest hleft hright ha hb hd hempty
  have hzero : (int 0 : I64).val = 0 := rfl
  have hcap : ¬ (int 0 > dest.len) := by change ¬ (dest.len.val < 0); omega
  have hmin : (if A.len < B.len then A.len else B.len) = int 0 := by
    rcases hempty with h | h
    · rw [h]
      split
      · rfl
      · rename_i hnot
        apply Subtype.ext
        have hval : ¬ 0 < B.len.val := hnot
        change B.len.val = 0
        omega
    · rw [h]
      have hnot : ¬ A.len < int 0 := by change ¬ A.len.val < 0; omega
      simp [hnot]
  simp only [Contains] at hdest hleft hright
  simp only [bitMapBinaryGeneric, readObject, JuliaLean.CompletionState.runBind,
    JuliaLean.CompletionState.runGet, hdest, hleft, hright, dite_true, ↓reduceDIte,
    JuliaLean.CompletionState.runPure]
  rw [hmin]
  simp only [hcap, ite_false]
  rcases hempty with h | h <;> simp [h]

end JuliaLean.Proofs.base.bitarray.Completion


namespace JuliaLean.Proofs.base.bitarray.Completion
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray
open JuliaLean.base.bitarray.Models1Group15

def AllocatingMapShapeError : Prop :=
  ∀ (N K : Nat) (F R : Type) (runtime : AllocationData)
    (mapBang : F → (rank : Nat) → Ref rank → Ref N → Ref K → ObjectM R)
    (f : F) (left : Ref N) (right : Ref K) (A : BitArray N) (B : BitArray K)
    (state : ObjectState) (message : String),
    Contains state left A → Contains state right B →
    Models1Group16.binaryShape A B = .error (.dimensionMismatch message) →
    (bitMapGeneric runtime mapBang f left right).run state =
      (.error (.dimensionMismatch message), state)

theorem allocatingMapShapeError : AllocatingMapShapeError := by
  intro N K F R runtime mapBang f left right A B state message ha hb hshape
  simp only [Contains] at ha hb
  simp [bitMapGeneric, readObject, ha, hb, hshape]
  rfl

end JuliaLean.Proofs.base.bitarray.Completion


namespace JuliaLean.Proofs.base.bitarray.Completion
open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

def PrependConstructorDispatchError : Prop :=
  ∀ (World B I A R : Type) (toBitArray : I → ExceptT Error (StateM World) A)
    (prepend : B → A → ExceptT Error (StateM World) R) (target : B) (items : I)
    (initial final : World) (error : Error),
    (toBitArray items).run initial = (.error error, final) →
    (bitVectorPrependIterableDispatch toBitArray prepend target items).run initial = (.error error, final)

theorem prependConstructorDispatchError : PrependConstructorDispatchError := by
  intro World B I A R construct prepend target items initial final error h
  simp [bitVectorPrependIterableDispatch, h]

end JuliaLean.Proofs.base.bitarray.Completion


namespace JuliaLean.Proofs.base.bitarray.dispatch
open JuliaLean.Registry
def entries : List Entry := [
  { id := "bitarray-prepend-iterator-conversion-errors", juliaFile := "base/bitarray.jl",
    juliaFns := ["prepend!(::BitVector, items)"],
    statement := "A failing BitVector conversion preserves its exception and preceding effects before target mutation.",
    source := "base/bitarray.jl:795", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Completion.PrependIteratorConversionErrors, thm := some ``JuliaLean.Proofs.base.bitarray.Completion.prependIteratorConversionErrors },
  { id := "bitarray-reverse-tuple-dispatch-errors", juliaFile := "base/bitarray.jl",
    juliaFns := ["_reverse(::BitArray, ::Tuple{Integer})"],
    statement := "The singleton dimension-tuple overload preserves the selected dimension method exception and preceding effects.",
    source := "base/bitarray.jl:1225", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Completion.ReverseTupleDispatchErrors, thm := some ``JuliaLean.Proofs.base.bitarray.Completion.reverseTupleDispatchErrors },
  { id := "bitarray-equality-shape-mismatch", juliaFile := "base/bitarray.jl",
    juliaFns := ["==(::BitArray, ::BitArray)"],
    statement := "Unequal public shapes return false without reading either chunk vector or changing memory, including rank-one public size dispatch.",
    source := "base/bitarray.jl:1206", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Completion.EqualityShapeMismatch, thm := some ``JuliaLean.Proofs.base.bitarray.Completion.equalityShapeMismatch },
  { id := "bitarray-mapped-word-conversion-failure", juliaFile := "base/bitarray.jl",
    juliaFns := ["bit_map!(f, dest::BitArray, A::BitArray)", "bit_map!(f, dest::BitArray, A::BitArray, B::BitArray)"],
    statement := "A failed destination-word conversion preserves the exception and conversion effects before the corresponding store.",
    source := "base/bitarray.jl:1795,1814", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Completion.MappedWordConversionFailure, thm := some ``JuliaLean.Proofs.base.bitarray.Completion.mappedWordConversionFailure },
  { id := "bitarray-unary-map-empty", juliaFile := "base/bitarray.jl",
    juliaFns := ["bit_map!(f, dest::BitArray, A::BitArray)"],
    statement := "An empty source and valid nonnegative destination return the same destination without calling the function or changing any object or memory.",
    source := "base/bitarray.jl:1795", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Completion.UnaryMapEmpty, thm := some ``JuliaLean.Proofs.base.bitarray.Completion.unaryMapEmpty },
  { id := "bitarray-binary-map-empty", juliaFile := "base/bitarray.jl",
    juliaFns := ["bit_map!(f, dest::BitArray, A::BitArray, B::BitArray)"],
    statement := "When either source is empty and all public lengths are nonnegative, mapping returns the same destination without calling the function or changing memory.",
    source := "base/bitarray.jl:1814", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Completion.BinaryMapEmpty, thm := some ``JuliaLean.Proofs.base.bitarray.Completion.binaryMapEmpty },
  { id := "bitarray-allocating-map-shape-error", juliaFile := "base/bitarray.jl",
    juliaFns := ["bit_map(f, A::BitArray, B::BitArray)"],
    statement := "A zip-shape DimensionMismatch propagates unchanged before allocation or calling the selected mapping method.",
    source := "base/bitarray.jl:1783", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Completion.AllocatingMapShapeError, thm := some ``JuliaLean.Proofs.base.bitarray.Completion.allocatingMapShapeError },
  { id := "bitarray-prepend-constructor-dispatch-error", juliaFile := "base/bitarray.jl",
    juliaFns := ["prepend!(::BitVector, items)"],
    statement := "Prepending any iterable preserves a constructor exception and preceding effects independently of the constructor result type or selected prepend method.",
    source := "base/bitarray.jl:795", status := .proven,
    prop := ``JuliaLean.Proofs.base.bitarray.Completion.PrependConstructorDispatchError, thm := some ``JuliaLean.Proofs.base.bitarray.Completion.prependConstructorDispatchError }
]
end JuliaLean.Proofs.base.bitarray.dispatch
