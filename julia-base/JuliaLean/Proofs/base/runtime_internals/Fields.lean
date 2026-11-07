import JuliaLean.base.runtime_internals
import JuliaLean.Proofs.base.runtime_internals.Common


section
namespace JuliaLean.RuntimeCov.Fields

open JuliaLean.RuntimeCov

/-! ## Refuted: `hasfield` always returns a boolean -/

/-- The `hasfield` docstring (lines 444-466): "Return a boolean indicating
whether `T` has `name` as one of its own fields", for any `T::Type`. -/
def HasfieldTotal : Prop :=
  ∀ (wrapper : TName → Option DTy) (t : Ty) (name : Sym), ∃ b, hasfield wrapper t name = .ok b

/-- `Union{}` (and, on master, the `TypeEq` kind of `Type{Int}`) have no
`fieldindex` method. -/
theorem hasfieldTotal_refuted : ¬ HasfieldTotal := by
  intro h
  obtain ⟨b, hb⟩ := h (fun _ => none) .bottom "name"
  simp [hasfield, fieldindex, bind, Except.bind] at hb

def FieldsBodies : Prop :=
  -- a concrete non-tuple struct: `fieldname` returns the i-th name and rejects
  -- indices outside `1:nfields` with `ArgumentError`
  (∀ d : DTy, d.tn.isNamedTuple = false → d.tn.abstract = false → d.tn.isTuple = false →
      ∀ i : Int, 1 ≤ i → i ≤ d.tn.names.length →
      fieldname (.dt d) i = .ok (.sym (d.tn.names.getD (i - 1).toNat ""))) ∧
  (∀ d : DTy, d.tn.isNamedTuple = false → d.tn.abstract = false → d.tn.isTuple = false →
      ∀ i : Int, (i < 1 ∨ d.tn.names.length < i) → ∃ m, fieldname (.dt d) i = .error (.argumentError m)) ∧
  (∀ d : DTy, d.tn.abstract = true → d.tn.isTuple = false →
      ∀ i, ∃ m, fieldname (.dt d) i = .error (.argumentError m)) ∧
  -- tuple types: names are indices, out of range is a `BoundsError`
  (∀ d : DTy, d.tn.isTuple = true → d.tn.isNamedTuple = false → d.tn.abstract = false →
      d.isvatuple = false → ∀ i : Int, 1 ≤ i → i ≤ d.ntypes → fieldname (.dt d) i = .ok (.idx i)) ∧
  (∀ d : DTy, d.tn.isTuple = true → d.tn.isNamedTuple = false → d.tn.abstract = false →
      d.isvatuple = false → ∀ i : Int, (i < 1 ∨ d.ntypes < i) → fieldname (.dt d) i = .error .boundsError) ∧
  (∀ i, fieldname .typeEq i = .error (.argumentError "type does not have definite field names")) ∧
  -- `fieldname(t::UnionAll, i)` delegates to the unwrapped `DataType`
  (∀ b i d, isTupleType b = false → unwrap b = .dt d →
      fieldname (.unionAll b) i = FieldName.sym <$> fieldnameDT d i) ∧
  -- `fieldnames` of a struct has exactly `fieldcount` entries
  (∀ d : DTy, d.tn.isNamedTuple = false → d.tn.abstract = false → d.tn.isTuple = false →
      fieldnames (.dt d) = .ok (d.tn.names.map .sym) ∧ fieldcount (.dt d) = .ok d.tn.names.length) ∧
  fieldnames .bottom = .error (.argumentError "The empty type does not have field names since it does not have instances.") ∧
  (∃ m, fieldcount .bottom = .error (.argumentError m)) ∧
  -- `fieldcount` of a union of one type name agrees with its members
  (∀ a b n, typenameNoerror (.union a b) ≠ none → fieldcountNoerror a = some n →
      fieldcountNoerror b = some n → (unwrap (.union a b) = .union a b) →
      fieldcount (.union a b) = .ok n) ∧
  (∀ t, fieldcountNoerrorPub t = fieldcountNoerror t) ∧
  -- `fieldindex(T, name, false)` of a struct is its 1-based position or 0
  (∀ d : DTy, d.tn.isNamedTuple = false → ∀ name,
      fieldindexDT d name false = .ok (match d.tn.names.idxOf? name with
        | some k => (k : Int) + 1 | none => 0)) ∧
  (∀ d : DTy, d.tn.isNamedTuple = false → ∀ name, name ∉ d.tn.names →
      fieldindexDT d name true = .error .fieldError) ∧
  -- `hasfield` on a struct: exactly its own field names
  (∀ w (d : DTy), d.tn.isNamedTuple = false → ∀ name,
      hasfield w (.dt d) name = .ok (decide (name ∈ d.tn.names))) ∧
  -- the non-throwing union query never throws
  (∀ w t name, (∃ a b, t = .union a b) ∨ (∃ b, t = .unionAll b) →
      ∃ k, fieldindex w t name false = .ok k) ∧
  (∀ (α : Type) (rt : Ty → Option α) t, argumentDatatype rt t = rt t) ∧
  (∀ b, nameof (.unionAll b) = nameof b) ∧
  (∀ d, nameof (.dt d) = .ok d.tn.name ∧ parentmoduleT (.dt d) = .ok d.tn.module) ∧
  (∀ b, parentmoduleT (.unionAll b) = parentmoduleT b) ∧
  -- field constness: immutable structs and out-of-bounds fields are const;
  -- atomic fields only exist in mutable structs, within bounds
  (∀ d : DTy, d.tn.mutable = false → ∀ s, isconstIdx (.dt d) s = true) ∧
  (∀ d : DTy, ∀ s : Int, (s < 1 ∨ d.tn.names.length < s) → isconstIdx (.dt d) s = true) ∧
  (∀ t s, isfieldatomicIdx t s = true → ∃ d, unwrap t = .dt d ∧ d.tn.mutable = true ∧
      1 ≤ s ∧ s ≤ d.tn.names.length) ∧
  (∀ d : DTy, d.tn.isNamedTuple = false → d.tn.mutable = true → ∀ s, s ∉ d.tn.names →
      isconstSym (.dt d) s = .ok true) ∧
  (∀ t s, (∀ d, unwrap t ≠ .dt d) → isconstSym t s = .ok false ∧ isfieldatomicSym t s = .ok false) ∧
  (∀ off d i, fieldoffsetIdx off d i = off d i) ∧
  (∀ off d name, d.tn.isNamedTuple = false → name ∉ d.tn.names →
      fieldoffsetName off d name = .error .fieldError) ∧
  (∀ off k i, fieldoffsetEgal off k i = off k i) ∧
  (∀ (τ : Type) (ft : Ty → Nat → τ) t n, fieldcount t = .ok n → (fieldtypes ft t).map List.length = .ok n) ∧
  propertynames .array = .ok [] ∧
  (∀ x p, propertynamesPrivate x p = propertynames x) ∧
  (∀ ns s, hasproperty (.module ns) s = .ok (decide (s ∈ ns)))

theorem idxOf?_none_iff {name : Sym} {ns : List Sym} : ns.idxOf? name = none ↔ name ∉ ns := by
  simp [List.idxOf?_eq_none_iff]

theorem fieldsBodies_proven : FieldsBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d h1 h2 h3 i hi1 hi2
    have h5 : ¬ (d.tn.names.length : Int) < i := by omega
    have h6 : ¬ i < 1 := by omega
    simp [fieldname, isTupleType, h3, fieldnameDT, fieldnamesRaw, h1, h2, bind, Except.bind, h5, h6,
      Functor.map, Except.map]
  · intro d h1 h2 h3 i hi
    rcases hi with hi | hi
    · have : ¬ i > (d.tn.names.length : Int) := by omega
      simp [fieldname, isTupleType, h3, fieldnameDT, fieldnamesRaw, h1, h2, bind, Except.bind, this, hi,
        Functor.map, Except.map]
    · simp [fieldname, isTupleType, h3, fieldnameDT, fieldnamesRaw, h1, h2, bind, Except.bind, hi,
        Functor.map, Except.map]
  · intro d h1 h3 i
    simp [fieldname, isTupleType, h3, fieldnameDT, h1, Functor.map, Except.map]
  · intro d h1 h2 h3 h4 i hi1 hi2
    have : ¬ (i < 1 ∨ i > (d.ntypes : Int)) := by omega
    simp [fieldname, isTupleType, h1, fieldcount, unwrap, datatypeFieldcount, h2, h3, h4, bind,
      Except.bind, this]
  · intro d h1 h2 h3 h4 i hi
    have : (i < 1 ∨ i > (d.ntypes : Int)) := by omega
    simp [fieldname, isTupleType, h1, fieldcount, unwrap, datatypeFieldcount, h2, h3, h4, bind,
      Except.bind, this]
  · intro i; simp [fieldname, isTupleType]
  · intro b i d hb hu
    have : unwrap (.unionAll b) = .dt d := hu
    simp only [fieldname, isTupleType, hb, Bool.false_eq_true, ↓reduceIte, this]
  · intro d h1 h2 h3
    simp [fieldnames, isTupleType, h3, unwrap, fieldcount, datatypeFieldcount, h1, h2, fieldnamesRaw,
      bind, Except.bind, pure, Except.pure]
  · rfl
  · exact ⟨_, rfl⟩
  · intro a b n htn ha hb hu
    simp only [fieldcount, hu, fieldcountNoerror]
    simp [htn, ha, hb]
  · intro _; rfl
  · intro d h name
    simp only [fieldindexDT, jlFieldIndex, fieldnamesRaw, h, Bool.false_eq_true, ↓reduceIte]
    cases hk : d.tn.names.idxOf? name <;> simp [bind, Except.bind, pure, Except.pure]
  · intro d h name hn
    have : d.tn.names.idxOf? name = none := idxOf?_none_iff.mpr hn
    simp [fieldindexDT, jlFieldIndex, fieldnamesRaw, h, this, bind, Except.bind]
  · intro w d h name
    simp only [hasfield, fieldindex, fieldindexDT, jlFieldIndex, fieldnamesRaw, h, Bool.false_eq_true,
      ↓reduceIte]
    cases hk : d.tn.names.idxOf? name with
    | none =>
      have := idxOf?_none_iff.mp hk
      simp [bind, Except.bind, pure, Except.pure, this]
    | some k =>
      have hm : name ∈ d.tn.names := by
        by_cases hc : name ∈ d.tn.names
        · exact hc
        · rw [idxOf?_none_iff.mpr hc] at hk; cases hk
      simp [bind, Except.bind, pure, Except.pure, hm] <;> omega
  · intro w t name ht
    rcases ht with ⟨a, b, rfl⟩ | ⟨b, rfl⟩
    · simp only [fieldindex, fieldindexGeneric]
      cases fieldindexNoerror name (.union a b) with
      | none => exact ⟨0, rfl⟩
      | some idx => exact ⟨idx, by simp⟩
    · simp only [fieldindex, fieldindexGeneric]
      cases fieldindexNoerror name (.unionAll b) with
      | none => exact ⟨0, rfl⟩
      | some idx => exact ⟨idx, by simp⟩
  · intro _ _ _; rfl
  · intro b; rfl
  · intro d; exact ⟨rfl, rfl⟩
  · intro b; rfl
  · intro d h s; simp [isconstIdx, unwrap, h]
  · intro d s hs
    have : ¬ (1 ≤ s ∧ s ≤ (d.tn.names.length : Int)) := by omega
    simp [isconstIdx, unwrap, this]
  · intro t s h
    unfold isfieldatomicIdx at h
    split at h
    · rename_i d hd
      refine ⟨d, hd, ?_⟩
      split at h
      · simp at h
      · rename_i hm
        split at h
        · simp at h
        · rename_i hb
          simp at hm
          exact ⟨hm, by omega, by omega⟩
    · simp at h
  · intro d h1 h2 s hs
    have : d.tn.names.idxOf? s = none := idxOf?_none_iff.mpr hs
    simp [isconstSym, unwrap, fieldindexDT, jlFieldIndex, fieldnamesRaw, h1, this, bind, Except.bind,
      pure, Except.pure, isconstIdx, h2]
  · intro t s h
    constructor
    · unfold isconstSym; split
      · rename_i d hd; exact absurd hd (h d)
      · rfl
    · unfold isfieldatomicSym; split
      · rename_i d hd; exact absurd hd (h d)
      · rfl
  · intro _ _ _; rfl
  · intro off d name h hn
    have : d.tn.names.idxOf? name = none := idxOf?_none_iff.mpr hn
    simp [fieldoffsetName, fieldindexDT, jlFieldIndex, fieldnamesRaw, h, this, bind, Except.bind]
  · intro _ _ _; rfl
  · intro τ ft t n h; simp [fieldtypes, h, bind, Except.bind, pure, Except.pure, Except.map]
  · rfl
  · intro _ _; rfl
  · intro ns s; simp [hasproperty, propertynames, bind, Except.bind, pure, Except.pure]
end JuliaLean.RuntimeCov.Fields
end
