import JuliaLean.base.strings.stringview
import JuliaLean.Core

/-! Models for `base/strings/stringview.jl` at Julia `bbfa0ce4150`. -/

namespace JuliaLean.StringsCovA.StringView

def StorageContract : Prop :=
  (∀ v a, ctor v a = ⟨v, a⟩) ∧
  (∀ s, toVector s = s.bytes) ∧ (∀ s, toArray s = s.bytes) ∧
  (∀ s, toString s = s.bytes) ∧ (∀ s, copy s = ⟨s.bytes, s.address⟩) ∧
  (∀ intern s, toSymbol intern s = intern s.bytes) ∧
  (∀ s, pointer s = s.address) ∧ (∀ s i, pointerAt s i = s.address + i - 1) ∧
  (∀ s, subPointer s = s.parent.address + s.offset) ∧
  (∀ s i, subPointerAt s i = s.parent.address + s.offset + i - 1) ∧
  (∀ s, unsafeConvertU8 s = pointer s) ∧ (∀ s, unsafeConvertI8 s = pointer s) ∧
  (∀ s, cconvertU8 s = s) ∧ (∀ s, cconvertI8 s = s)

theorem storageContract : StorageContract := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def ByteContract : Prop :=
  (∀ s, sizeof s = s.bytes.length) ∧ (∀ s, ncodeunits s = s.bytes.length) ∧
  (∀ s, codeunitType s = 8) ∧
  (∀ s i, codeunit s i = if 1 ≤ i ∧ i ≤ s.bytes.length then
    .ok (s.bytes.getD (i.toNat - 1) 0) else .error .boundsError) ∧
  (∀ s, codeunits s = s.bytes) ∧
  (∀ s, subCodeunits s = (s.parent.bytes.drop s.offset).take s.ncodeunits) ∧
  (∀ cmpBytes a b, cmp cmpBytes a b = cmpBytes a.bytes b.bytes) ∧
  (∀ a b, eq a b = (a.bytes == b.bytes))

theorem byteContract : ByteContract := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def EmptyOperations : Prop :=
  typeminCodeUnits = ⟨[], 0⟩ ∧
  ∀ kind, typeminType kind = .ok ⟨[], 0⟩ ∧ typeminValue kind = .ok ⟨[], 0⟩ ∧
    one kind = .ok ⟨[], 0⟩ ∧ oneunit kind = .ok ⟨[], 0⟩

theorem emptyOperations_refuted : ¬ EmptyOperations := by
  intro h
  have hs := (h.2 .subarray).1
  change (Except.error (.methodError "SubArray()") : Jl View) = .ok ⟨[], 0⟩ at hs
  cases hs

def BehaviorContract : Prop :=
  (∀ s, isascii s = s.bytes.all (· < 0x80)) ∧
  (∀ hashBytes s h, hash hashBytes s h = hashBytes s.bytes h) ∧
  (∀ emit s, write emit s = emit s.bytes) ∧
  (∀ emit s, print emit s = ()) ∧
  (∀ f s i, thisind f s i = f s.bytes i) ∧
  (∀ f s i, nextind f s i = f s.bytes i) ∧
  (∀ this s i, isvalid this s i =
    (decide (1 ≤ i ∧ i ≤ s.bytes.length) && decide (this s.bytes i = i)))

theorem behaviorContract : BehaviorContract := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def SliceChompReplaceContract : Prop :=
  (∀ valid next s i j, getindexRange valid next s i j =
    if j < i then .ok ⟨[], s.address⟩
    else if !(1 ≤ i ∧ j ≤ s.bytes.length) then .error .boundsError
    else if !valid s.bytes i || !valid s.bytes j then .error (.argumentError "StringIndexError")
    else let stop := next s.bytes j - 1
      .ok ⟨(s.bytes.drop (i.toNat - 1)).take (stop - i + 1).toNat,
        s.address + i.toNat - 1⟩) ∧
  (∀ s, chomp s =
    let bytes := match s.bytes.reverse with
      | 0x0a :: 0x0d :: rest => rest.reverse
      | 0x0a :: rest => rest.reverse
      | _ => s.bytes
    ⟨bytes, s.address⟩) ∧
  (∀ (α : Type) (impl : View → List α → Int → α) s pairs count,
    replace impl s pairs count = impl s pairs count)

theorem sliceChompReplaceContract : SliceChompReplaceContract := by
  repeat' apply And.intro
  all_goals intros <;> rfl

end JuliaLean.StringsCovA.StringView
