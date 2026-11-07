import JuliaLean.base.sort
import JuliaLean.Proofs.base.sort.compatibility_properties
/-! Keyword wrappers and scratch-space methods from `base/sort.jl`
(master `bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

open JuliaLean

def SortKeywordWrappersCorrect : Prop :=
  (∀ (I O R : Type) (ord : Bool → O) (core : I → O → R) (itr : I),
    issortedKeyword (R := R) ord core itr .true_ = core itr (ord true)) ∧
  (∀ (I O R : Type) (ord : Bool → O) (core : I → O → R) (itr : I) rev,
    rev ≠ .true_ →
    issortedKeyword (R := R) ord core itr rev = core itr (ord false)) ∧
  (∀ (V K O R : Type) (ord : RevChoice → O) (core : V → K → O → R)
      (v : V) (k : K) rev,
    partialsortKeyword (R := R) ord core v k rev = core v k (ord rev)) ∧
  (∀ (V X O R : Type) (first last : V → Int)
      (core : V → X → Int → Int → O → R) (v : V) (x : X) (o : O),
    searchOrderWrapper (R := R) first last core v x o = core v x (first v) (last v) o) ∧
  (∀ (V X O R : Type) (ord : RevChoice → O) (core : V → X → O → R)
      (v : V) (x : X) rev,
    searchKeywordWrapper (R := R) ord core v x rev = core v x (ord rev))

theorem sortKeywordWrappersCorrect : SortKeywordWrappersCorrect := by
  refine ⟨by simp [issortedKeyword, reverseRequested], ?_, by simp [partialsortKeyword],
    by simp [searchOrderWrapper], by simp [searchKeywordWrapper]⟩
  intro I O R ord core itr rev h
  cases rev <;> simp_all [issortedKeyword, reverseRequested]

def GeneratedKeywordCorrect : Prop :=
  (∀ syms, getkwExpansion syms = syms.map ("_" ++ ·)) ∧
  (∀ kw name v default, kwLookup kw name = some v → v ≠ .missing →
    generatedKeywordGetter kw name default = (kw, v)) ∧
  (∀ kw name default, kwLookup kw name = none →
    generatedKeywordGetter kw name default = (kw ++ [(name, default)], default)) ∧
  (∀ kw name default, kwLookup kw name = some .missing →
    generatedKeywordGetter kw name default = (kw ++ [(name, default)], default))

theorem generatedKeywordCorrect : GeneratedKeywordCorrect := by
  refine ⟨by simp [getkwExpansion], ?_, ?_, ?_⟩
  · intro kw name v default h hv
    simp [generatedKeywordGetter, h, hv]
  · intro kw name default h
    simp [generatedKeywordGetter, h]
  · intro kw name default h
    simp [generatedKeywordGetter, h]

def MakeScratchCorrect : Prop :=
  (∀ t n, (makeScratchNothing t n).backing.length = n ∧
    (makeScratchNothing t n).viewLength = n) ∧
  (∀ s n, (makeScratchSame s n).backing.length = max s.length n ∧
    (makeScratchSame s n).viewLength = max s.length n) ∧
  (∀ s t n r, makeScratchOther s t n = .ok r →
    r.backing.length ≥ s.length ∧ r.viewType = t)

theorem makeScratchCorrect : MakeScratchCorrect := by
  refine ⟨by simp [makeScratchNothing], by simp [makeScratchSame], ?_⟩
  intro s t n r h
  simp only [makeScratchOther] at h
  split at h
  · cases h
    exact ⟨Nat.le_max_left _ _, rfl⟩
  · contradiction

end JuliaLean.SortTuplesCov
