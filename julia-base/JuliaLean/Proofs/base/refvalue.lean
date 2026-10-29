import JuliaLean.base.refvalue
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.refvalue

open JuliaLean JuliaLean.Registry JuliaLean.base.pointer JuliaLean.base.refpointer
open JuliaLean.base.refvalue

/-- A RefValue exposes its field through constructors, assignment and indexing, and its unsafe
pointer conversions address either the object or the stored referent as Julia specifies. -/
def RefValueContract : Prop :=
  ∀ {T X P E : Type}
    (allocatedinline isBits isconcretetype ismutabletype : Type → Bool)
    (convertInput : X → Except E T) (convertInferred : T → Except E T)
    (pointerFromObjRef : {A : Type} → A → Ptr Unit)
    (atomicPointerRef : Ptr (Ptr Unit) → RefValueMemoryOrder → Ptr Unit)
    (address : Ptr Unit) (x : X) (sameTypeX : T),
    (isBits T →
      isassigned isBits (refValueDefault (T := T) isBits address) = true) ∧
    (¬ isBits T →
      isassigned isBits (refValueDefault (T := T) isBits address) = false) ∧
    (∀ (b : RefValue T) (value : T), b.x = .assigned value →
      isassigned isBits b = true) ∧
    (∀ (uninitializedValue : T), isBits T = true →
      getindex (E := E) uninitializedValue (refValueDefault (T := T) isBits address) =
        .ok uninitializedValue) ∧
    (∀ (b : RefValue T) (value : T), b.x = .assigned value →
      getindex (E := E) value b = .ok value) ∧
    (∀ (uninitializedValue : T) (b : RefValue T), ¬ isBits T →
      b.x = .undefined → getindex (E := E) uninitializedValue b = .error .undefRefError) ∧
    (∀ error : E, convertInput x = .error error →
      refValueTyped convertInput address x = .error (.conversionError error)) ∧
    (∀ (value : T), convertInput x = .ok value →
      ∃ b : RefValue T, refValueTyped convertInput address x = .ok b ∧
        b.address = address ∧ getindex (E := E) value b = .ok value) ∧
    (∀ error : E, convertInferred sameTypeX = .error error →
      refValueInferred convertInferred address sameTypeX = .error (.conversionError error)) ∧
    (∀ (value : T), convertInferred sameTypeX = .ok value →
      ∃ b : RefValue T, refValueInferred convertInferred address sameTypeX = .ok b ∧
        b.address = address ∧ getindex (E := E) value b = .ok value) ∧
    (∀ (b : RefValue T) (value : T), convertInput x = .ok value →
      ∃ updated : RefValue T, setindex! convertInput b x = .ok updated ∧
        updated.address = b.address ∧ getindex (E := E) value updated = .ok value ∧
        isassigned isBits updated = true) ∧
    (∀ (b : RefValue T) error, convertInput x = .error error →
      setindex! convertInput b x = .error (.conversionError error)) ∧
    (∀ (b : RefValue T), allocatedinline T = true →
      unsafeConvert (T := T) (P := P) (E := E) allocatedinline isconcretetype ismutabletype
        pointerFromObjRef atomicPointerRef b =
        .ok (convertPtrType (S := P) (pointerFromObjRef b))) ∧
    (∀ (b : RefValue T) (value : T), allocatedinline T = false →
      isconcretetype T = true → ismutabletype T = true → b.x = .assigned value →
      unsafeConvert (T := T) (P := P) (E := E) allocatedinline isconcretetype ismutabletype
        pointerFromObjRef atomicPointerRef b =
        .ok (convertPtrType (S := P) (pointerFromObjRef value))) ∧
    (∀ (b : RefValue T), allocatedinline T = false → isconcretetype T = true →
      ismutabletype T = true → b.x = .undefined →
      unsafeConvert (T := T) (P := P) (E := E) allocatedinline isconcretetype ismutabletype
        pointerFromObjRef atomicPointerRef b = .error .undefRefError) ∧
    (∀ (b : RefValue T), allocatedinline T = false →
      (isconcretetype T && ismutabletype T) = false →
      let p := atomicPointerRef (convertPtrType (S := Ptr Unit) (pointerFromObjRef b)) .monotonic
      if p.address = C_NULL.address then
        unsafeConvert (T := T) (P := P) (E := E) allocatedinline isconcretetype ismutabletype
          pointerFromObjRef atomicPointerRef b = .error .undefRefError
      else
        unsafeConvert (T := T) (P := P) (E := E) allocatedinline isconcretetype ismutabletype
          pointerFromObjRef atomicPointerRef b = .ok (convertPtrType (S := P) p)) ∧
    (∀ b : RefValue AnyElement,
      (unsafeConvertAny pointerFromObjRef b).address = (pointerFromObjRef b).address)

theorem refValueContract_proven : RefValueContract := by
  intro T X P E allocatedinline isBits isconcretetype ismutabletype convertInput
    convertInferred pointerFromObjRef atomicPointerRef address x sameTypeX
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    simp [refValueDefault, isassigned, h]
  · intro h
    simp [refValueDefault, isassigned, h]
  · intro b value h
    simp [isassigned, h]
  · intro uninitializedValue h
    simp [refValueDefault, getindex, h]
  · intro b value h
    simp [getindex, h]
  · intro uninitializedValue b _ h
    simp [getindex, h]
  · intro error h
    simp [refValueTyped, h]
  · intro value h
    exact ⟨⟨address, .assigned value⟩, by simp [refValueTyped, h], rfl, rfl⟩
  · intro error h
    simp [refValueInferred, refValueTyped, h]
  · intro value h
    exact ⟨⟨address, .assigned value⟩, by simp [refValueInferred, refValueTyped, h], rfl, rfl⟩
  · intro b value h
    exact ⟨{ b with x := .assigned value }, by simp [setindex!, h], rfl, rfl, rfl⟩
  · intro b error h
    simp [setindex!, h]
  · intro b h
    simp [unsafeConvert, h]
  · intro b value hi hc hm hx
    simp [unsafeConvert, hi, hc, hm, hx]
  · intro b hi hc hm hx
    simp [unsafeConvert, hi, hc, hm, hx]
  · intro b hi hc
    dsimp
    split <;> simp_all [unsafeConvert]
  · intro b
    rfl

/-- Registry entry for the `base/refvalue.jl` contract. -/
def refValueEntry : Entry := {
  id := "misccov-refvalue"
  juliaFile := "base/refvalue.jl"
  juliaFns := [
    "RefValue{T}()", "RefValue{T}(x)", "RefValue(x::T)", "isassigned(::RefValue)",
    "unsafe_convert(P, ::RefValue{T})", "unsafe_convert(Ptr{Any}, ::RefValue{Any})",
    "getindex(::RefValue)", "setindex!(::RefValue, x)"
  ]
  statement := "RefValue constructors store converted values; isassigned and indexing distinguish undefined references from assigned values; setindex! preserves reference identity; and unsafe_convert returns the stored referent or reference address, throwing UndefRefError for an undefined slot."
  source := "base/refvalue.jl:5-60"
  status := .proven
  prop := ``RefValueContract
  thm := some ``refValueContract_proven
}

def entries : List Entry := [refValueEntry]

end JuliaLean.Proofs.base.refvalue
