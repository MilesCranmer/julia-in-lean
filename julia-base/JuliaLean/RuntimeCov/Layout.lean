import JuliaLean.RuntimeCov.Common

/-!
`base/runtime_internals.jl:620-813, 1194-1212`: the `DataTypeLayout` record
read from `dt.layout`, its accessor functions, union layouts, aligned sizes,
field descriptors, and the layout predicates.  A layout is the record the
runtime stores; its `flags` bits follow the C struct comment at lines 637-646
(bit 0 `haspadding`, bits 1-2 `fielddesc_type`, bits 3-4 the array element
kind, bit 7 `isbitsegal`).
-/

namespace JuliaLean.RuntimeCov.Layout

open JuliaLean.RuntimeCov

/-- `struct DataTypeLayout`, base/runtime_internals.jl:624-640. -/
structure DataTypeLayout where
  size : Nat
  nfields : Nat
  npointers : Nat
  firstptr : Int
  alignment : Nat
  flags : Nat
  deriving DecidableEq, Repr

/-- A `DataType` as far as the layout queries see it: `none` is a null
`layout` pointer. -/
structure DT where
  layout : Option DataTypeLayout
  fieldtypes : List String
  hasInstance : Bool
  isConcrete : Bool
  isArray : Bool
  deriving DecidableEq, Repr

/-- The Julia type of a returned integer (the docstrings declare result types). -/
inductive JNum where
  | int (n : Int)
  | uint32 (n : Nat)
  | uint16 (n : Nat)
  deriving DecidableEq, Repr

/-- `datatype_fieldtypes(x)`, line 622: the runtime's field-type vector. -/
def datatypeFieldtypes (dt : DT) : List String := dt.fieldtypes

/-- `DataTypeLayout(dt)`, lines 642-646. -/
def layoutOf (dt : DT) : Rt DataTypeLayout :=
  match dt.layout with
  | none => .error .undefRefError
  | some l => .ok l

/-- `datatype_alignment(dtl)`, line 656 (`Int(dtl.alignment)`), and the
`DataType` method, line 655. -/
def alignment (l : DataTypeLayout) : JNum := .int l.alignment
def alignmentDT (dt : DT) : Rt JNum := do let l ← layoutOf dt; pure (alignment l)

/-- `datatype_haspadding(dtl)`, line 702, and the `DataType` method, line 701. -/
def haspadding (l : DataTypeLayout) : Bool := l.flags % 2 == 1
def haspaddingDT (dt : DT) : Rt Bool := do let l ← layoutOf dt; pure (haspadding l)

/-- `datatype_isbitsegal(dtl)`, line 713, and line 712. -/
def isbitsegal (l : DataTypeLayout) : Bool := (l.flags / 128) % 2 != 0
def isbitsegalDT (dt : DT) : Rt Bool := do let l ← layoutOf dt; pure (isbitsegal l)

/-- `datatype_nfields(dtl)`, line 723 (the `UInt32` field), and line 722. -/
def nfields (l : DataTypeLayout) : JNum := .uint32 l.nfields
def nfieldsDT (dt : DT) : Rt JNum := do let l ← layoutOf dt; pure (nfields l)

/-- `datatype_npointers(dtl)`, line 731 (the `UInt32` field), and line 730. -/
def npointers (l : DataTypeLayout) : JNum := .uint32 l.npointers
def npointersDT (dt : DT) : Rt JNum := do let l ← layoutOf dt; pure (npointers l)

/-- `datatype_pointerfree(dt)`, lines 739-742. -/
def pointerfreeDT (dt : DT) : Rt Bool := do let l ← layoutOf dt; pure (l.npointers == 0)

/-- `datatype_fielddesc_type(dtl)`, line 754 (`(flags >> 1) & 3`), and line 753. -/
def fielddescType (l : DataTypeLayout) : Nat := (l.flags / 2) % 4
def fielddescTypeDT (dt : DT) : Rt Nat := do let l ← layoutOf dt; pure (fielddescType l)

/-- `datatype_arrayelem(dtl)`, line 767 (`(flags >> 3) & 3`), and line 766. -/
def arrayelem (l : DataTypeLayout) : Nat := (l.flags / 8) % 4
def arrayelemDT (dt : DT) : Rt Nat := do let l ← layoutOf dt; pure (arrayelem l)

/-- `datatype_layoutsize(dtl)`, line 770, and line 769. -/
def layoutsize (l : DataTypeLayout) : Nat := l.size
def layoutsizeDT (dt : DT) : Rt Nat := do let l ← layoutOf dt; pure (layoutsize l)

/-- `uniontype_layout(T)`, lines 658-663: the runtime's inline flag, size and alignment. -/
def uniontypeLayout (isinline : Bool) (sz al : Nat) : Bool × Nat × Nat := (isinline, sz, al)

/-- `LLT_ALIGN(x, sz)`, line 665: `(x + sz - 1) & -sz`, which for a power of
two `sz` clears the low bits of `x + sz - 1`. -/
def lltAlign (x sz : Nat) : Nat := (x + sz - 1) - (x + sz - 1) % sz

/-- What `aligned_sizeof` knows about `T`, lines 668-688. -/
inductive SizeQuery where
  | inlineUnion (sz al : Nat)
  | boxedUnion
  | inlineType (size al : Nat)
  | boxed
  deriving DecidableEq, Repr

/-- `aligned_sizeof(T)`, lines 668-688 (`Type{Union{}}` is handled as
`Core.TypeofBottom` by the caller of `inlineType`). -/
def alignedSizeof (ptrSize : Nat) : SizeQuery → Nat
  | .inlineUnion sz al => lltAlign sz al
  | .inlineType size al => lltAlign size al
  | .boxedUnion | .boxed => ptrSize

/-- `gc_alignment(sz)` and `gc_alignment(T)`, lines 690-691: the runtime's answer. -/
def gcAlignment (rt : Nat → Nat) (sz : Nat) : Nat := rt sz

/-- `struct FieldDesc` and `FieldDesc(fd::FieldDescStorage)`, lines 774-787. -/
structure FieldDesc where
  isforeign : Bool
  isptr : Bool
  size : Nat
  offset : Nat
  deriving DecidableEq, Repr

def fieldDescOf (ptrsize offset : Nat) : FieldDesc := ⟨false, ptrsize % 2 != 0, ptrsize / 2, offset⟩

/-- `DataTypeFieldDesc(dt)`, lines 791-794. -/
def mkDataTypeFieldDesc (dt : DT) : Rt DT :=
  match dt.layout with
  | none => .error .undefRefError
  | some _ => .ok dt

/-- `getindex(dtfd, i)`, lines 797-813: `entries` are the `(ptrsize, offset)`
pairs stored after the layout header. -/
def fieldDescAt (l : DataTypeLayout) (entries : List (Nat × Nat)) (i : Int) : Rt FieldDesc :=
  if ¬ (1 ≤ i ∧ i ≤ l.nfields) then .error .boundsError
  else if fielddescType l = 3 then .ok ⟨true, true, 0, 0⟩
  else match entries[(i - 1).toNat]? with
    | some (p, o) => .ok (fieldDescOf p o)
    | none => .error .boundsError

/-- `is_datatype_layoutopaque(dt)`, lines 1194-1196. -/
def isLayoutOpaque (l : DataTypeLayout) : Bool := l.nfields == 0 && l.npointers != 0

/-- `is_valid_intrinsic_elptr(ety)`, lines 1198-1203 (`isAny` for `ety === Any`). -/
def isValidIntrinsicElptr (isAny : Bool) (dt : DT) : Bool :=
  if isAny then true
  else if !dt.isConcrete then false
  else if dt.isArray then false
  else match dt.layout with
    | some l => !isLayoutOpaque l
    | none => false

/-- `issingletontype(t)`, line 1212. -/
def issingletontype (dt : DT) : Bool :=
  dt.hasInstance && match dt.layout with
    | some l => l.size == 0 && l.npointers == 0
    | none => false

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

/-- Bytes of one field-description entry: `FieldDescStorage{UInt8/16/32}` hold
two integers of 1, 2 or 4 bytes (codes 0, 1, 2). -/
def entryBytes : Nat → Nat
  | 0 => 2
  | 1 => 4
  | 2 => 8
  | _ => 0

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
