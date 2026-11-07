import JuliaLean.base.runtime_internals
import JuliaLean.Proofs.base.runtime_internals.Common


section
namespace JuliaLean.RuntimeCov.Layout

open JuliaLean.RuntimeCov

/-! ## Documentation claims (refuted) -/

/-- The `datatype_haspadding` docstring, lines 693-699: "Return whether the
fields of instances of this type are packed in memory, with no intervening
padding bits". With bit 0 of `flags` being `haspadding` (line 637), that is
the negation of the padding bit. -/
def HaspaddingDoc : Prop :=
  ∀ l : DataTypeLayout, haspadding l = !(l.flags % 2 == 1)

theorem haspaddingDoc_refuted : ¬ HaspaddingDoc := by
  intro h
  have := h ⟨16, 2, 0, -1, 8, 1⟩
  revert this; decide

/-- The `datatype_fielddesc_type` docstring, lines 744-752: "Return the size in
bytes of each field-description entry in the layout array". -/
def FielddescTypeDoc : Prop :=
  ∀ l : DataTypeLayout, fielddescType l < 3 → fielddescType l = entryBytes (fielddescType l)

theorem fielddescTypeDoc_refuted : ¬ FielddescTypeDoc := by
  intro h
  have := h ⟨16, 2, 0, -1, 8, 0⟩ (by decide)
  revert this; decide

/-- The `datatype_npointers` docstring signature, lines 725-729: `::Int`. -/
def NpointersReturnType : Prop :=
  ∀ l : DataTypeLayout, ∃ n : Int, npointers l = .int n

theorem npointersReturnType_refuted : ¬ NpointersReturnType := by
  intro h
  obtain ⟨n, hn⟩ := h ⟨16, 2, 2, 0, 8, 0⟩
  simp [npointers] at hn

/-! ## Proven properties -/

/-- Each layout query on a `DataType` reads the layout once, throwing
`UndefRefError` for a null layout; the bit accessors decode the documented
flag fields; `LLT_ALIGN` rounds up to a multiple of a power-of-two size;
aligned sizes of inline values cover their size; field descriptors are
bounds-checked and decoded as documented. -/
def LayoutBodies : Prop :=
  (∀ dt, datatypeFieldtypes dt = dt.fieldtypes) ∧
  (∀ dt, dt.layout = none → layoutOf dt = .error .undefRefError ∧
      alignmentDT dt = .error .undefRefError ∧ haspaddingDT dt = .error .undefRefError ∧
      isbitsegalDT dt = .error .undefRefError ∧ nfieldsDT dt = .error .undefRefError ∧
      npointersDT dt = .error .undefRefError ∧ pointerfreeDT dt = .error .undefRefError ∧
      fielddescTypeDT dt = .error .undefRefError ∧ arrayelemDT dt = .error .undefRefError ∧
      layoutsizeDT dt = .error .undefRefError) ∧
  (∀ dt l, dt.layout = some l →
      alignmentDT dt = .ok (.int l.alignment) ∧ haspaddingDT dt = .ok (l.flags % 2 == 1) ∧
      isbitsegalDT dt = .ok ((l.flags / 128) % 2 != 0) ∧ nfieldsDT dt = .ok (.uint32 l.nfields) ∧
      npointersDT dt = .ok (.uint32 l.npointers) ∧ pointerfreeDT dt = .ok (l.npointers == 0) ∧
      fielddescTypeDT dt = .ok ((l.flags / 2) % 4) ∧ arrayelemDT dt = .ok ((l.flags / 8) % 4) ∧
      layoutsizeDT dt = .ok l.size) ∧
  (∀ l, fielddescType l < 4 ∧ arrayelem l < 4) ∧
  (∀ i s a, uniontypeLayout i s a = (i, s, a)) ∧
  (∀ x k, lltAlign x (2 ^ k) % 2 ^ k = 0 ∧ x ≤ lltAlign x (2 ^ k) ∧ lltAlign x (2 ^ k) < x + 2 ^ k) ∧
  (∀ p s a, s ≤ alignedSizeof p (.inlineType s (2 ^ a))) ∧
  (∀ p s a, s ≤ alignedSizeof p (.inlineUnion s (2 ^ a))) ∧
  (∀ p, alignedSizeof p .boxed = p ∧ alignedSizeof p .boxedUnion = p) ∧
  (∀ rt s, gcAlignment rt s = rt s) ∧
  (∀ p o, (fieldDescOf p o).isptr = (p % 2 != 0) ∧ (fieldDescOf p o).size = p / 2 ∧
      (fieldDescOf p o).isforeign = false) ∧
  (∀ dt, dt.layout = none → mkDataTypeFieldDesc dt = .error .undefRefError) ∧
  (∀ l es (i : Int), (i < 1 ∨ l.nfields < i) → fieldDescAt l es i = .error .boundsError) ∧
  (∀ l es (i : Int), 1 ≤ i → i ≤ l.nfields → fielddescType l = 3 →
      fieldDescAt l es i = .ok ⟨true, true, 0, 0⟩) ∧
  (∀ l es (i : Int) p o, 1 ≤ i → i ≤ l.nfields → fielddescType l ≠ 3 →
      es[(i - 1).toNat]? = some (p, o) → fieldDescAt l es i = .ok (fieldDescOf p o)) ∧
  (∀ l, isLayoutOpaque l = true ↔ l.nfields = 0 ∧ l.npointers ≠ 0) ∧
  (∀ dt, isValidIntrinsicElptr true dt = true) ∧
  (∀ dt, dt.isConcrete = false → isValidIntrinsicElptr false dt = false) ∧
  (∀ dt, issingletontype dt = true → dt.hasInstance = true)

theorem lltAlign_pow (x k : Nat) :
    lltAlign x (2 ^ k) % 2 ^ k = 0 ∧ x ≤ lltAlign x (2 ^ k) ∧ lltAlign x (2 ^ k) < x + 2 ^ k := by
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  unfold lltAlign
  have hm : (x + 2 ^ k - 1) % 2 ^ k < 2 ^ k := Nat.mod_lt _ hp
  have hle : (x + 2 ^ k - 1) % 2 ^ k ≤ x + 2 ^ k - 1 := Nat.mod_le _ _
  refine ⟨?_, ?_, ?_⟩
  · have := Nat.div_add_mod (x + 2 ^ k - 1) (2 ^ k)
    have e : x + 2 ^ k - 1 - (x + 2 ^ k - 1) % 2 ^ k = 2 ^ k * ((x + 2 ^ k - 1) / 2 ^ k) := by omega
    rw [e]; simp
  · omega
  · omega

theorem layoutBodies_proven : LayoutBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; rfl
  · intro dt h
    simp [layoutOf, h, alignmentDT, haspaddingDT, isbitsegalDT, nfieldsDT, npointersDT, pointerfreeDT,
      fielddescTypeDT, arrayelemDT, layoutsizeDT, bind, Except.bind]
  · intro dt l h
    simp [layoutOf, h, alignmentDT, haspaddingDT, isbitsegalDT, nfieldsDT, npointersDT, pointerfreeDT,
      fielddescTypeDT, arrayelemDT, layoutsizeDT, bind, Except.bind, pure, Except.pure, alignment,
      haspadding, isbitsegal, nfields, npointers, fielddescType, arrayelem, layoutsize]
  · intro l; exact ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩
  · intro _ _ _; rfl
  · intro x k; exact lltAlign_pow x k
  · intro p s a; exact (lltAlign_pow s a).2.1
  · intro p s a; exact (lltAlign_pow s a).2.1
  · intro p; exact ⟨rfl, rfl⟩
  · intro _ _; rfl
  · intro p o; exact ⟨rfl, rfl, rfl⟩
  · intro dt h; simp [mkDataTypeFieldDesc, h]
  · intro l es i h
    have : ¬ (1 ≤ i ∧ i ≤ (l.nfields : Int)) := by omega
    simp [fieldDescAt, this]
  · intro l es i h1 h2 h3
    have : (1 ≤ i ∧ i ≤ (l.nfields : Int)) := ⟨h1, h2⟩
    simp [fieldDescAt, this, h3]
  · intro l es i p o h1 h2 h3 h4
    have : (1 ≤ i ∧ i ≤ (l.nfields : Int)) := ⟨h1, h2⟩
    have hidx : (i - 1).toNat = i.toNat - 1 := by omega
    rw [hidx] at h4
    simp [fieldDescAt, this, h3, h4]
  · intro l; simp [isLayoutOpaque]
  · intro _; rfl
  · intro dt h; simp [isValidIntrinsicElptr, h]
  · intro dt h; simp [issingletontype] at h; exact h.1
end JuliaLean.RuntimeCov.Layout
end
