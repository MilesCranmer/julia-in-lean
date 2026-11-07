import JuliaLean.base.strings.lazy
import JuliaLean.Core
import JuliaLean.base.hashing
import JuliaLean.base.strings.util

namespace JuliaLean.StringsCovA.LazyFaithful

open JuliaLean

def PrivateCtorProperty : Prop :=
  (∀ parts cached,
    privateCtor ⟨.ok parts⟩ ⟨.ok cached⟩ = .ok ⟨parts, false, cached⟩) ∧
  (∀ error str, privateCtor ⟨.error error⟩ str = .error error) ∧
  (∀ parts error, privateCtor ⟨.ok parts⟩ ⟨.error error⟩ = .error error)

theorem privateCtor_proven : PrivateCtorProperty := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

def CtorProperty : Prop := ∀ args compact,
  (ctor args compact).parts = args ∧
  (ctor args compact).compact = compact ∧
  (ctor args compact).cache = none

theorem ctor_proven : CtorProperty := by
  intro args compact
  exact ⟨rfl, rfl, rfl⟩

def LazyStrProperty : Prop :=
  (∀ parseatom sourceFile text flags,
    flags ≠ [] → flags ≠ ["c"] →
    lazyStr parseatom sourceFile text flags = .error (.argumentErrorFlags flags)) ∧
  (∀ parseatom sourceFile text flags expansion,
    lazyStr parseatom sourceFile text flags = .ok expansion →
    expansion.compact = (flags == ["c"]))

theorem lazyStr_proven : LazyStrProperty := by
  constructor
  · intro parseatom sourceFile text flags hne hnc
    simp [lazyStr, hne, hnc]
  · intro parseatom sourceFile text flags expansion h
    by_cases bad : !flags.isEmpty && !(flags == ["c"])
    · unfold lazyStr at h
      rw [if_pos bad] at h
      contradiction
    · cases hl : lazyLoop parseatom sourceFile text (text.bytes.length + 1)
          (Strings.ix 1) (Strings.ix 1) [] with
      | error error =>
          unfold lazyStr at h
          rw [if_neg bad, hl] at h
          cases h
      | ok parts =>
          unfold lazyStr at h
          rw [if_neg bad, hl] at h
          cases h
          rfl

def ToStringProperty : Prop :=
  (∀ parts compact cached concurrent,
    toString ⟨parts, compact, some cached⟩ concurrent = ⟨.ok cached, some cached⟩) ∧
  (∀ parts compact rendered,
    sprintParts parts compact = .ok rendered →
    toString ⟨parts, compact, none⟩ none = ⟨.ok rendered, some rendered⟩) ∧
  (∀ parts compact rendered competing,
    sprintParts parts compact = .ok rendered →
    toString ⟨parts, compact, none⟩ (some competing) = ⟨.ok competing, some competing⟩) ∧
  (∀ parts compact error concurrent,
    sprintParts parts compact = .error error →
    toString ⟨parts, compact, none⟩ concurrent = ⟨.error error, concurrent⟩) ∧
  (∀ part compact output,
    printParts compact compact [part] output = part.print compact compact output)

theorem toString_proven : ToStringProperty := by
  refine ⟨fun _ _ _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro parts compact rendered h
    simp only [toString]
    rw [h]
  · intro parts compact rendered competing h
    simp only [toString]
    rw [h]
  · intro parts compact error concurrent h
    simp only [toString]
    rw [h]
  · intro part compact output
    cases h : part.print compact compact output with
    | error error => rw [printParts, h]; rfl
    | ok next => rw [printParts, h]; rfl

def HashProperty : Prop :=
  (∀ s h secret concurrent string,
    (toString s concurrent).outcome = .ok string →
    (hash s h secret concurrent).outcome =
      .ok (IntFuncsCov.Hashing.hashBytes string.bytes h secret) ∧
    (hash s h secret concurrent).cache = (toString s concurrent).cache) ∧
  (∀ s h secret concurrent error,
    (toString s concurrent).outcome = .error error →
    (hash s h secret concurrent).outcome = .error error ∧
    (hash s h secret concurrent).cache = (toString s concurrent).cache)

theorem hash_proven : HashProperty := by
  constructor <;> intro s h secret concurrent value hs <;> simp [hash, hs]

def LastindexProperty : Prop :=
  (∀ s concurrent string,
    (toString s concurrent).outcome = .ok string →
    (lastindex s concurrent).outcome = .ok (Strings.lastindex string) ∧
    (lastindex s concurrent).cache = (toString s concurrent).cache) ∧
  (∀ s concurrent error,
    (toString s concurrent).outcome = .error error →
    (lastindex s concurrent).outcome = .error error ∧
    (lastindex s concurrent).cache = (toString s concurrent).cache)

theorem lastindex_proven : LastindexProperty := by
  constructor <;> intro s concurrent value hs <;> simp [lastindex, hs]

def Iterate0Property : Prop :=
  (∀ s concurrent string,
    (toString s concurrent).outcome = .ok string →
    (iterate0 s concurrent).outcome = .ok (Strings.iterate string (Strings.ix 1)) ∧
    (iterate0 s concurrent).cache = (toString s concurrent).cache) ∧
  (∀ s concurrent error,
    (toString s concurrent).outcome = .error error →
    (iterate0 s concurrent).outcome = .error error ∧
    (iterate0 s concurrent).cache = (toString s concurrent).cache)

theorem iterate0_proven : Iterate0Property := by
  constructor <;> intro s concurrent value hs <;> simp [iterate0, hs]

def IterateAtProperty : Prop :=
  (∀ s i concurrent string index,
    (toString s concurrent).outcome = .ok string →
    integerToInt i = .ok index →
    (iterateAt s i concurrent).outcome = .ok (Strings.iterate string index) ∧
    (iterateAt s i concurrent).cache = (toString s concurrent).cache) ∧
  (∀ s i concurrent error,
    (toString s concurrent).outcome = .error error →
    (iterateAt s i concurrent).outcome = .error error) ∧
  (∀ s i concurrent string error,
    (toString s concurrent).outcome = .ok string →
    integerToInt i = .error error →
    (iterateAt s i concurrent).outcome = .error error)

theorem iterateAt_proven : IterateAtProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intro s i concurrent string index hs hi
    simp [iterateAt, hs, hi]
  · intro s i concurrent error hs
    simp [iterateAt, hs]
  · intro s i concurrent string error hs hi
    simp [iterateAt, hs, hi]

def IsequalProperty : Prop :=
  (∀ a b leftConcurrent rightConcurrent leftString rightString,
    (toString a leftConcurrent).outcome = .ok leftString →
    (toString b rightConcurrent).outcome = .ok rightString →
    (isequal a b leftConcurrent rightConcurrent).outcome =
      .ok (leftString.bytes == rightString.bytes)) ∧
  (∀ a b leftConcurrent rightConcurrent error,
    (toString a leftConcurrent).outcome = .error error →
    (isequal a b leftConcurrent rightConcurrent).outcome = .error error) ∧
  (∀ a b leftConcurrent rightConcurrent leftString error,
    (toString a leftConcurrent).outcome = .ok leftString →
    (toString b rightConcurrent).outcome = .error error →
    (isequal a b leftConcurrent rightConcurrent).outcome = .error error)

theorem isequal_proven : IsequalProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b leftConcurrent rightConcurrent leftString rightString hl hr
    simp [isequal, hl, hr]
  · intro a b leftConcurrent rightConcurrent error hl
    simp [isequal, hl]
  · intro a b leftConcurrent rightConcurrent leftString error hl hr
    simp [isequal, hl, hr]

def EqProperty : Prop :=
  (∀ a b leftConcurrent rightConcurrent leftString rightString,
    (toString a leftConcurrent).outcome = .ok leftString →
    (toString b rightConcurrent).outcome = .ok rightString →
    (eq a b leftConcurrent rightConcurrent).outcome =
      .ok (leftString.bytes == rightString.bytes)) ∧
  (∀ a b leftConcurrent rightConcurrent error,
    (toString a leftConcurrent).outcome = .error error →
    (eq a b leftConcurrent rightConcurrent).outcome = .error error) ∧
  (∀ a b leftConcurrent rightConcurrent leftString error,
    (toString a leftConcurrent).outcome = .ok leftString →
    (toString b rightConcurrent).outcome = .error error →
    (eq a b leftConcurrent rightConcurrent).outcome = .error error)

theorem eq_proven : EqProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b leftConcurrent rightConcurrent leftString rightString hl hr
    simp [eq, hl, hr]
  · intro a b leftConcurrent rightConcurrent error hl
    simp [eq, hl]
  · intro a b leftConcurrent rightConcurrent leftString error hl hr
    simp [eq, hl, hr]

def NcodeunitsProperty : Prop :=
  (∀ s concurrent string,
    (toString s concurrent).outcome = .ok string →
    (ncodeunits s concurrent).outcome = .ok (Strings.ncodeunits string) ∧
    (ncodeunits s concurrent).cache = (toString s concurrent).cache) ∧
  (∀ s concurrent error,
    (toString s concurrent).outcome = .error error →
    (ncodeunits s concurrent).outcome = .error error ∧
    (ncodeunits s concurrent).cache = (toString s concurrent).cache)

theorem ncodeunits_proven : NcodeunitsProperty := by
  constructor <;> intro s concurrent value hs <;> simp [ncodeunits, hs]

def CodeunitTypeProperty : Prop := ∀ s, codeunitType s = .uint8

theorem codeunitType_proven : CodeunitTypeProperty := by
  intro s
  rfl

def CodeunitAtProperty : Prop :=
  (∀ s i concurrent string index,
    (toString s concurrent).outcome = .ok string →
    integerToInt i = .ok index →
    (codeunitAt s i concurrent).outcome = liftStringResult (Strings.codeunit string index) ∧
    (codeunitAt s i concurrent).cache = (toString s concurrent).cache) ∧
  (∀ s i concurrent error,
    (toString s concurrent).outcome = .error error →
    (codeunitAt s i concurrent).outcome = .error error) ∧
  (∀ s i concurrent string error,
    (toString s concurrent).outcome = .ok string →
    integerToInt i = .error error →
    (codeunitAt s i concurrent).outcome = .error error)

theorem codeunitAt_proven : CodeunitAtProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intro s i concurrent string index hs hi
    simp [codeunitAt, hs, hi]
  · intro s i concurrent error hs
    simp [codeunitAt, hs]
  · intro s i concurrent string error hs hi
    simp [codeunitAt, hs, hi]

def CodeunitsProperty : Prop :=
  (∀ s concurrent string,
    (toString s concurrent).outcome = .ok string →
    (codeunits s concurrent).outcome = .ok ⟨string⟩ ∧
    (codeunits s concurrent).cache = (toString s concurrent).cache) ∧
  (∀ s concurrent error,
    (toString s concurrent).outcome = .error error →
    (codeunits s concurrent).outcome = .error error ∧
    (codeunits s concurrent).cache = (toString s concurrent).cache)

theorem codeunits_proven : CodeunitsProperty := by
  constructor <;> intro s concurrent value hs <;> simp [codeunits, hs]

def IsvalidProperty : Prop :=
  (∀ s i concurrent string index,
    (toString s concurrent).outcome = .ok string →
    integerToInt i = .ok index →
    (isvalid s i concurrent).outcome = .ok (Strings.isvalidAt string index) ∧
    (isvalid s i concurrent).cache = (toString s concurrent).cache) ∧
  (∀ s i concurrent error,
    (toString s concurrent).outcome = .error error →
    (isvalid s i concurrent).outcome = .error error) ∧
  (∀ s i concurrent string error,
    (toString s concurrent).outcome = .ok string →
    integerToInt i = .error error →
    (isvalid s i concurrent).outcome = .error error)

theorem isvalid_proven : IsvalidProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intro s i concurrent string index hs hi
    simp [isvalid, hs, hi]
  · intro s i concurrent error hs
    simp [isvalid, hs]
  · intro s i concurrent string error hs hi
    simp [isvalid, hs, hi]

end JuliaLean.StringsCovA.LazyFaithful
