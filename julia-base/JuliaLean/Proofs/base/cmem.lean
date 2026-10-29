import JuliaLean.base.cmem
import JuliaLean.Registry.Types

/-!
# Properties of `base/cmem.jl`

Settled specifications for the Julia C-memory wrappers. Each contract is stated on the
source-mirrored definitions of `JuliaLean.base.cmem` and follows from the C-standard operation
laws carried by its `CMemoryOps` parameter. `StandardC` below gives one concrete implementation
of those laws: the four C routines are external to Julia, and the refutation of
`NegativeLengthRejected` instantiates the parameter with it.
-/

namespace JuliaLean.Proofs.base.cmem

open JuliaLean JuliaLean.base.cmem JuliaLean.base.pointer JuliaLean.Registry

def cvoidPointer {T : Type} (pointer : Ptr T) : Ptr Unit := convertPtrType pointer

/-- `memcpy` copies each source byte and leaves all other bytes unchanged for disjoint ranges. -/
def MemcpyNoOverlap : Prop :=
  ∀ {D S I : Type} (calls : CMemoryOps) (toCsize : I → Jl CSizeT)
    (memory : ByteHeap) (destination : Ptr D) (source : Ptr S) (n : I) (size : CSizeT),
    toCsize n = .ok size →
    validRange memory (cvoidPointer destination) size →
    validRange memory (cvoidPointer source) size →
    rangesDisjoint (cvoidPointer destination) (cvoidPointer source) size →
    ∀ (after : ByteHeap) (result : Ptr Unit),
      memcpy calls toCsize memory destination source n = .ok (after, result) →
      result.address = (cvoidPointer destination).address ∧
        copyEffect memory after (cvoidPointer destination) (cvoidPointer source) size

/-- `memmove` copies the original source bytes even when the byte ranges overlap. -/
def MemmoveOverlapSafe : Prop :=
  ∀ {D S I : Type} (calls : CMemoryOps) (toCsize : I → Jl CSizeT)
    (memory : ByteHeap) (destination : Ptr D) (source : Ptr S) (n : I) (size : CSizeT),
    toCsize n = .ok size →
    validRange memory (cvoidPointer destination) size →
    validRange memory (cvoidPointer source) size →
    ∀ (after : ByteHeap) (result : Ptr Unit),
      memmove calls toCsize memory destination source n = .ok (after, result) →
      result.address = (cvoidPointer destination).address ∧
        copyEffect memory after (cvoidPointer destination) (cvoidPointer source) size

/-- `memset` stores the low eight bits of its converted C `int` in every destination byte. -/
def MemsetByteValue : Prop :=
  ∀ {D V I : Type} (calls : CMemoryOps) (toCint : V → Jl CInt)
    (toCsize : I → Jl CSizeT) (memory : ByteHeap) (destination : Ptr D)
    (value : V) (n : I) (cValue : CInt) (size : CSizeT),
    toCint value = .ok cValue →
    toCsize n = .ok size →
    validRange memory (cvoidPointer destination) size →
    ∀ (after : ByteHeap) (result : Ptr Unit),
      memset calls toCint toCsize memory destination value n = .ok (after, result) →
      result.address = (cvoidPointer destination).address ∧
        fillEffect memory after (cvoidPointer destination) size (JInt.wrap .u8 cValue.val)

/-- `memcmp` compares unsigned bytes at the first mismatch and widens its C `int` result exactly. -/
def MemcmpUnsignedSign : Prop :=
  ∀ {A B I : Type} (calls : CMemoryOps) (remCsize : I → Jl CSizeT)
    (memory : ByteHeap) (left : Ptr A) (right : Ptr B) (n : I) (size : CSizeT),
    remCsize n = .ok size →
    validRange memory (cvoidPointer left) size →
    validRange memory (cvoidPointer right) size →
    let cResult := calls.memcmpC memory (cvoidPointer left) (cvoidPointer right) size
    ∀ (result : JuliaLean.base.cmem.NativeInt),
      memcmp calls remCsize memory left right n = .ok result →
      result.val = cResult.val ∧
        memcmpEffect memory (cvoidPointer left) (cvoidPointer right) size cResult

/-- The four wrappers retain their C byte operations, pointer results, and comparison conversion. -/
def CMemoryContract : Prop :=
  MemcpyNoOverlap ∧ MemmoveOverlapSafe ∧ MemsetByteValue ∧ MemcmpUnsignedSign

/-- An exception caused by an inexact integer conversion. -/
def IsInexact {α : Type} (result : Jl α) : Prop :=
  ∃ name, result = .error (.inexactError name)

/- The historical claim that every wrapper rejects negative `BitInteger` lengths. -/
def NegativeLengthRejected : Prop :=
  ∀ {t : IntTy} (calls : CMemoryOps) (memory : ByteHeap)
    (destination source : Ptr Unit) (n : JInt t), n.val < 0 →
    IsInexact (memcpy calls csizeFromInt memory destination source n.val) ∧
    IsInexact (memmove calls csizeFromInt memory destination source n.val) ∧
    IsInexact (memset calls cintFromInt csizeFromInt memory destination (0 : Int) n.val) ∧
    IsInexact (memcmp calls remCsizeInt memory destination source n.val)

/-! ## Proofs of the C-standard contracts -/

theorem memcpyNoOverlap_proven : MemcpyNoOverlap := by
  intro D S I calls toCsize memory destination source n size hconv hvDst hvSrc hdisj
    after result hcall
  have hstep : memcpy calls toCsize memory destination source n
      = .ok (calls.memcpyC memory (convertPtrType destination) (convertPtrType source) size) := by
    simp [memcpy, hconv] <;> rfl
  rw [hstep] at hcall
  have hinj : calls.memcpyC memory (convertPtrType destination) (convertPtrType source) size
      = (after, result) := Except.ok.inj hcall
  have hlaw := calls.memcpyStandard memory (convertPtrType destination) (convertPtrType source) size
    (by simpa only [cvoidPointer] using hvDst)
    (by simpa only [cvoidPointer] using hvSrc)
    (by simpa only [cvoidPointer] using hdisj)
  rw [hinj] at hlaw
  simpa [cvoidPointer, convertPtrType] using hlaw

theorem memmoveOverlapSafe_proven : MemmoveOverlapSafe := by
  intro D S I calls toCsize memory destination source n size hconv hvDst hvSrc after result hcall
  have hstep : memmove calls toCsize memory destination source n
      = .ok (calls.memmoveC memory (convertPtrType destination) (convertPtrType source) size) := by
    simp [memmove, hconv] <;> rfl
  rw [hstep] at hcall
  have hinj : calls.memmoveC memory (convertPtrType destination) (convertPtrType source) size
      = (after, result) := Except.ok.inj hcall
  have hlaw := calls.memmoveStandard memory (convertPtrType destination) (convertPtrType source) size
    (by simpa only [cvoidPointer] using hvDst)
    (by simpa only [cvoidPointer] using hvSrc)
  rw [hinj] at hlaw
  simpa [cvoidPointer, convertPtrType] using hlaw

theorem memsetByteValue_proven : MemsetByteValue := by
  intro D V I calls toCint toCsize memory destination value n cValue size hconvV hconvN hvDst
    after result hcall
  have hstep : memset calls toCint toCsize memory destination value n
      = .ok (calls.memsetC memory (convertPtrType destination) cValue size) := by
    simp [memset, hconvV, hconvN] <;> rfl
  rw [hstep] at hcall
  have hinj : calls.memsetC memory (convertPtrType destination) cValue size = (after, result) :=
    Except.ok.inj hcall
  have hlaw := calls.memsetStandard memory (convertPtrType destination) cValue size
    (by simpa only [cvoidPointer] using hvDst)
  rw [hinj] at hlaw
  simpa [cvoidPointer, convertPtrType] using hlaw

theorem cintVal_in64 (value : CInt) : (JInt.wrap .i64 value.val).val = value.val := by
  have hb := value.property
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb
  show wrapInt .i64 value.val = value.val
  exact wrapInt_of_inRange .i64 value.val (by
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb ⊢
    omega)

theorem memcmpUnsignedSign_proven : MemcmpUnsignedSign := by
  intro A B I calls remCsize memory left right n size hconv hvL hvR
  dsimp only
  intro result hcall
  have hstep : memcmp calls remCsize memory left right n
      = .ok (intFromCint (calls.memcmpC memory (convertPtrType left) (convertPtrType right) size)) := by
    simp [memcmp, hconv] <;> rfl
  rw [hstep] at hcall
  have hresult : result
      = intFromCint (calls.memcmpC memory (convertPtrType left) (convertPtrType right) size) :=
    (Except.ok.inj hcall).symm
  have hlaw := calls.memcmpStandard memory (convertPtrType left) (convertPtrType right) size
    (by simpa only [cvoidPointer] using hvL)
    (by simpa only [cvoidPointer] using hvR)
  simp only [cvoidPointer] at hlaw ⊢
  constructor
  · rw [hresult]
    exact cintVal_in64 _
  · exact hlaw

theorem cMemoryContract_proven : CMemoryContract :=
  ⟨memcpyNoOverlap_proven, memmoveOverlapSafe_proven, memsetByteValue_proven,
    memcmpUnsignedSign_proven⟩

/-! ## A concrete C standard-library implementation

The C `memcpy`, `memmove`, `memset` and `memcmp` routines are external to Julia, so the model
takes them as the `CMemoryOps` parameter. The implementation below satisfies the C-standard
operation laws; the negative-length refutation instantiates the parameter with it. -/

namespace StandardC

/-- The all-zero byte heap. -/
def trivialHeap : ByteHeap := ⟨fun _ => ⟨0, by decide⟩, fun _ => false⟩

theorem csize_toNat_le (size : CSizeT) : size.val.toNat ≤ 2 ^ 64 := by
  have hb := size.property
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb
  omega

theorem readByte_writeByte (heap : ByteHeap) (address : Nat) (value : Byte) (target : Nat) :
    (heap.writeByte address value).readByte target =
      if addressMod target = addressMod address then value else heap.readByte target := by
  simp [ByteHeap.readByte, ByteHeap.writeByte, addressMod] <;> rfl

/-- One copy step: write the pre-call source byte for `offset` at `destination + offset`. -/
def copyStep (destination source : Ptr Unit) (heap working : ByteHeap) (offset : Nat) : ByteHeap :=
  working.writeByte (pointerAddress destination + offset)
    (heap.readByte (pointerAddress source + offset))

/-- C `memcpy`/`memmove` body: every destination byte comes from the pre-call source bytes. -/
def copyBytes (destination source : Ptr Unit) (size : CSizeT) (heap : ByteHeap) : ByteHeap :=
  (List.range size.val.toNat).foldl (copyStep destination source heap) heap

theorem copyBytes_fold_at (destination source : Ptr Unit) (heap : ByteHeap) :
    ∀ (bound count offset : Nat), count ≤ bound → bound ≤ 2 ^ 64 → offset < count →
      ((List.range count).foldl (copyStep destination source heap) heap).readByte
          (pointerAddress destination + offset) =
        heap.readByte (pointerAddress source + offset) := by
  intro bound count
  induction count with
  | zero => intro offset _ _ hoff; exact absurd hoff (Nat.not_lt_zero offset)
  | succ count ih =>
    intro offset hcount hbound hoff
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      copyStep, readByte_writeByte]
    by_cases heq : offset = count
    · subst heq; simp [addressMod]
    · rw [if_neg (by
        simp only [addressMod]
        intro hmod
        exact heq (by omega))]
      exact ih offset (by omega) hbound (by omega)

theorem copyBytes_fold_other (destination source : Ptr Unit) (heap : ByteHeap) :
    ∀ (count address : Nat), (∀ offset, offset < count →
        addressMod address ≠ addressMod (pointerAddress destination + offset)) →
      ((List.range count).foldl (copyStep destination source heap) heap).readByte address =
        heap.readByte address := by
  intro count
  induction count with
  | zero => intro _ _; rfl
  | succ count ih =>
    intro address h
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      copyStep, readByte_writeByte, if_neg (h count (by omega))]
    exact ih address fun offset hoff => h offset (by omega)

theorem foldl_validByte (f : ByteHeap → Nat → ByteHeap)
    (preserves : ∀ heap offset, (f heap offset).validByte = heap.validByte)
    (heap : ByteHeap) (count : Nat) :
    ((List.range count).foldl f heap).validByte = heap.validByte := by
  induction count generalizing heap with
  | zero => rfl
  | succ count ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    calc
      (f ((List.range count).foldl f heap) count).validByte =
          ((List.range count).foldl f heap).validByte := preserves _ _
      _ = heap.validByte := ih heap

theorem copyBytes_copyEffect (destination source : Ptr Unit) (size : CSizeT) (heap : ByteHeap) :
    copyEffect heap (copyBytes destination source size heap) destination source size := by
  refine ⟨fun offset hoff =>
    copyBytes_fold_at destination source heap (2 ^ 64) size.val.toNat offset
      (csize_toNat_le size) (by omega) hoff, ?_, ?_⟩
  · intro address haddress
    exact copyBytes_fold_other destination source heap size.val.toNat address haddress
  · exact foldl_validByte (copyStep destination source heap) (by intros; rfl) heap size.val.toNat

/-- One fill step: write `value` at `destination + offset`. -/
def fillStep (destination : Ptr Unit) (value : Byte) (working : ByteHeap) (offset : Nat) : ByteHeap :=
  working.writeByte (pointerAddress destination + offset) value

/-- C `memset` body: every destination byte becomes `value`. -/
def fillBytes (destination : Ptr Unit) (size : CSizeT) (value : Byte) (heap : ByteHeap) : ByteHeap :=
  (List.range size.val.toNat).foldl (fillStep destination value) heap

theorem fillBytes_fold_at (destination : Ptr Unit) (value : Byte) (heap : ByteHeap) :
    ∀ (bound count offset : Nat), count ≤ bound → bound ≤ 2 ^ 64 → offset < count →
      ((List.range count).foldl (fillStep destination value) heap).readByte
          (pointerAddress destination + offset) = value := by
  intro bound count
  induction count with
  | zero => intro offset _ _ hoff; exact absurd hoff (Nat.not_lt_zero offset)
  | succ count ih =>
    intro offset hcount hbound hoff
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      fillStep, readByte_writeByte]
    by_cases heq : offset = count
    · subst heq; simp [addressMod]
    · rw [if_neg (by
        simp only [addressMod]
        intro hmod
        exact heq (by omega))]
      exact ih offset (by omega) hbound (by omega)

theorem fillBytes_fold_other (destination : Ptr Unit) (value : Byte) (heap : ByteHeap) :
    ∀ (count address : Nat), (∀ offset, offset < count →
        addressMod address ≠ addressMod (pointerAddress destination + offset)) →
      ((List.range count).foldl (fillStep destination value) heap).readByte address =
        heap.readByte address := by
  intro count
  induction count with
  | zero => intro _ _; rfl
  | succ count ih =>
    intro address h
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      fillStep, readByte_writeByte, if_neg (h count (by omega))]
    exact ih address fun offset hoff => h offset (by omega)

theorem fillBytes_fillEffect (destination : Ptr Unit) (size : CSizeT) (value : Byte)
    (heap : ByteHeap) :
    fillEffect heap (fillBytes destination size value heap) destination size value := by
  refine ⟨fun offset hoff =>
    fillBytes_fold_at destination value heap (2 ^ 64) size.val.toNat offset
      (csize_toNat_le size) (by omega) hoff, ?_, ?_⟩
  · intro address haddress
    exact fillBytes_fold_other destination value heap size.val.toNat address haddress
  · exact foldl_validByte (fillStep destination value) (by intros; rfl) heap size.val.toNat

def i32Lit (x : Int) (h : -(2 ^ 31 : Int) ≤ x ∧ x < 2 ^ 31) : CInt :=
  ⟨x, by
    have hx : -(2 ^ 31 : Int) ≤ x ∧ x ≤ (2 ^ 31 : Int) - 1 := by omega
    simpa [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] using hx⟩

/-- C `memcmp` body over byte addresses: the sign of the first differing byte pair, `0` when all
`fuel` pairs agree. -/
def cMemcmp (heap : ByteHeap) (left right : Nat) : Nat → CInt
  | 0 => i32Lit 0 (by omega)
  | fuel + 1 =>
    if heap.readByte left = heap.readByte right then cMemcmp heap (left + 1) (right + 1) fuel
    else if (heap.readByte left).val < (heap.readByte right).val then i32Lit (-1) (by omega)
    else i32Lit 1 (by omega)

theorem cMemcmp_scan (heap : ByteHeap) :
    ∀ (fuel left right : Nat),
      ((∀ offset, offset < fuel → heap.readByte (left + offset) = heap.readByte (right + offset)) →
        (cMemcmp heap left right fuel).val = 0) ∧
      (∀ index, index < fuel → heap.readByte (left + index) ≠ heap.readByte (right + index) →
        (∀ offset, offset < index → heap.readByte (left + offset) = heap.readByte (right + offset)) →
        ((cMemcmp heap left right fuel).val < 0 ↔
            (heap.readByte (left + index)).val < (heap.readByte (right + index)).val) ∧
          ((cMemcmp heap left right fuel).val > 0 ↔
            (heap.readByte (left + index)).val > (heap.readByte (right + index)).val)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro left right
    refine ⟨fun _ => ?_, ?_⟩
    · simp [cMemcmp, i32Lit]
    · intro index hi _ _; omega
  | succ fuel ih =>
    intro left right
    by_cases heq : heap.readByte left = heap.readByte right
    · have hstep : cMemcmp heap left right (fuel + 1)
        = cMemcmp heap (left + 1) (right + 1) fuel := by
        simp only [cMemcmp, if_pos heq]
      rw [hstep]
      obtain ⟨h0, h1⟩ := ih (left + 1) (right + 1)
      refine ⟨fun hall => h0 fun offset hoff => ?_, ?_⟩
      · have h := hall (offset + 1) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using h
      · intro index hindex hdiff hprefix
        cases index with
        | zero => exact absurd (by simpa using heq) hdiff
        | succ index' =>
          have hprefix' : ∀ offset, offset < index' →
              heap.readByte (left + 1 + offset) = heap.readByte (right + 1 + offset) := by
            intro offset hoff
            have h := hprefix (offset + 1) (by omega)
            simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using h
          have hdiff' : heap.readByte (left + 1 + index') ≠ heap.readByte (right + 1 + index') :=
            by simpa only [Nat.add_assoc, Nat.add_comm 1 index'] using hdiff
          obtain ⟨e1, e2⟩ := h1 index' (by omega) hdiff' hprefix'
          have hleft : left + 1 + index' = left + (index' + 1) := by omega
          have hright : right + 1 + index' = right + (index' + 1) := by omega
          constructor
          · simpa only [hleft, hright] using e1
          · simpa only [hleft, hright] using e2
    · have hne' : (heap.readByte left).val ≠ (heap.readByte right).val := fun hc =>
        heq (Subtype.ext hc)
      have hstep : cMemcmp heap left right (fuel + 1) =
          if (heap.readByte left).val < (heap.readByte right).val then i32Lit (-1) (by omega)
          else i32Lit 1 (by omega) := by
        simp only [cMemcmp, if_neg heq]
      rw [hstep]
      by_cases hlt : (heap.readByte left).val < (heap.readByte right).val
      · rw [if_pos hlt]
        refine ⟨?_, ?_⟩
        · intro hall
          have firstEqual : heap.readByte left = heap.readByte right := by
            simpa using hall 0 (by omega)
          exact False.elim (heq firstEqual)
        · intro index hindex hdiff hprefix
          cases index with
          | zero =>
            constructor <;> simp [i32Lit] <;> omega
          | succ index' =>
            have firstEqual : heap.readByte left = heap.readByte right := by
              simpa using hprefix 0 (by omega)
            exact False.elim (heq firstEqual)
      · rw [if_neg hlt]
        have hgt : (heap.readByte left).val > (heap.readByte right).val := by omega
        refine ⟨?_, ?_⟩
        · intro hall
          have firstEqual : heap.readByte left = heap.readByte right := by
            simpa using hall 0 (by omega)
          exact False.elim (heq firstEqual)
        · intro index hindex hdiff hprefix
          cases index with
          | zero =>
            constructor <;> simp [i32Lit] <;> omega
          | succ index' =>
            have firstEqual : heap.readByte left = heap.readByte right := by
              simpa using hprefix 0 (by omega)
            exact False.elim (heq firstEqual)

/-- C `memcmp` operation on typed pointers. -/
def cMemcmpOp (memory : ByteHeap) (left right : Ptr Unit) (size : CSizeT) : CInt :=
  cMemcmp memory (pointerAddress left) (pointerAddress right) size.val.toNat

theorem cMemcmpOp_effect (memory : ByteHeap) (left right : Ptr Unit) (size : CSizeT) :
    memcmpEffect memory left right size (cMemcmpOp memory left right size) := by
  obtain ⟨h0, h1⟩ := cMemcmp_scan memory size.val.toNat (pointerAddress left) (pointerAddress right)
  constructor
  · intro index hfd
    obtain ⟨hindex, hprefix, hdiff⟩ := hfd
    exact h1 index hindex hdiff hprefix
  · exact h0

/-- C `memcpy`: copy the pre-call source bytes to the destination and return the destination. -/
def cMemcpy (memory : ByteHeap) (destination source : Ptr Unit) (size : CSizeT) :
    ByteHeap × Ptr Unit :=
  (copyBytes destination source size memory, destination)

/-- C `memmove`: identical byte effect, since every source byte is read before any write. -/
def cMemmove (memory : ByteHeap) (destination source : Ptr Unit) (size : CSizeT) :
    ByteHeap × Ptr Unit :=
  (copyBytes destination source size memory, destination)

/-- C `memset`: fill the destination with the low eight bits of the value. -/
def cMemset (memory : ByteHeap) (destination : Ptr Unit) (value : CInt) (size : CSizeT) :
    ByteHeap × Ptr Unit :=
  (fillBytes destination size (JInt.wrap .u8 value.val) memory, destination)

theorem cMemcpyLaw : MemcpyLaw cMemcpy := by
  intro memory destination source size _ _ _
  exact ⟨rfl, copyBytes_copyEffect destination source size memory⟩

theorem cMemmoveLaw : MemmoveLaw cMemmove := by
  intro memory destination source size _ _
  exact ⟨rfl, copyBytes_copyEffect destination source size memory⟩

theorem cMemsetLaw : MemsetLaw cMemset := by
  intro memory destination value size _
  exact ⟨rfl, fillBytes_fillEffect destination size (JInt.wrap .u8 value.val) memory⟩

theorem cMemcmpLaw : MemcmpLaw cMemcmpOp := by
  intro memory left right size _ _
  exact cMemcmpOp_effect memory left right size

/-- A concrete instance of the C-standard operation laws. -/
def standardCMemoryOps : CMemoryOps where
  memcpyC := cMemcpy
  memmoveC := cMemmove
  memsetC := cMemset
  memcmpC := cMemcmpOp
  memcpyStandard := cMemcpyLaw
  memmoveStandard := cMemmoveLaw
  memsetStandard := cMemsetLaw
  memcmpStandard := cMemcmpLaw

end StandardC

/-- A negative length reaches `memcpy`, `memmove` and `memset` through `ccall`'s `Csize_t`
conversion, so the wrappers reject it. -/
theorem memcpyRejects (calls : CMemoryOps) (memory : ByteHeap) (destination source : Ptr Unit)
    (n : Int) (hn : n < 0) : IsInexact (memcpy calls csizeFromInt memory destination source n) := by
  refine ⟨"UInt64", ?_⟩
  have hn0 : ¬ 0 ≤ n := by omega
  simp [memcpy, csizeFromInt, hn0] <;> rfl

/-- A negative length reaches `memmove` through `ccall`'s `Csize_t` conversion, so the wrapper
rejects it. -/
theorem memmoveRejects (calls : CMemoryOps) (memory : ByteHeap) (destination source : Ptr Unit)
    (n : Int) (hn : n < 0) : IsInexact (memmove calls csizeFromInt memory destination source n) := by
  refine ⟨"UInt64", ?_⟩
  have hn0 : ¬ 0 ≤ n := by omega
  simp [memmove, csizeFromInt, hn0] <;> rfl

/-- A negative length reaches `memset` through `ccall`'s `Csize_t` conversion, so the wrapper
rejects it. -/
theorem memsetRejects (calls : CMemoryOps) (memory : ByteHeap) (destination : Ptr Unit)
    (n : Int) (hn : n < 0) :
    IsInexact (memset calls cintFromInt csizeFromInt memory destination (0 : Int) n) := by
  refine ⟨"UInt64", ?_⟩
  have hn0 : ¬ 0 ≤ n := by omega
  simp [memset, cintFromInt, csizeFromInt, hn0] <;> rfl

/-- `memcmp` always accepts: it passes `n % Csize_t`, which never fails. -/
theorem memcmpAccepts (calls : CMemoryOps) (memory : ByteHeap) (destination source : Ptr Unit)
    (n : Int) : ¬IsInexact (memcmp calls remCsizeInt memory destination source n) := by
  rintro ⟨name, hresult⟩
  simp only [memcmp, remCsizeInt] at hresult
  cases hresult

theorem negativeLengthRejected_refuted : ¬ NegativeLengthRejected := by
  intro rejected
  have hall := rejected StandardC.standardCMemoryOps StandardC.trivialHeap C_NULL C_NULL
    (⟨-1, by decide⟩ : JInt .i64) (by decide)
  exact memcmpAccepts StandardC.standardCMemoryOps StandardC.trivialHeap C_NULL C_NULL (-1)
    hall.2.2.2

/-! ## Registry entries -/

def entries : List Entry := [
  { id := "misccov-memcpy-contract", juliaFile := "base/cmem.jl",
    juliaFns := ["memcpy", "memmove", "memset", "memcmp"],
    statement := "The four wrappers convert pointer and integer arguments for their C calls, apply the standard copy, overlap, fill, and comparison rules to byte memory, and convert the returned pointer or C int as declared.",
    source := "base/cmem.jl:3-56 (wrapper docstrings and methods); C17 7.24.2.1, 7.24.2.2, 7.24.4.1, and 7.24.6.1",
    status := .proven, prop := ``CMemoryContract, thm := some ``cMemoryContract_proven },
  { id := "misccov-memcmp-negative-length", juliaFile := "base/cmem.jl",
    juliaFns := ["memcpy", "memmove", "memset", "memcmp"],
    statement := "All four C memory wrappers reject negative byte counts consistently with an inexact conversion error.",
    source := "base/cmem.jl:12-57; Csize_t argument conversion and n % Csize_t at line 56",
    status := .refuted, prop := ``NegativeLengthRejected,
    thm := some ``negativeLengthRejected_refuted,
    issue := "none found (queries: memcmp, memcmp negative, memcmp Csize_t, memcmp Base.memcmp)",
    notes := "memcpy, memmove and memset pass n to ccall as Csize_t, so a negative n throws InexactError; memcmp passes n % Csize_t and can return normally for an early byte mismatch. Refuted by repro/misccov-memcmp-negative-length.jl, which prints REPRODUCED." },
  { id := "cmem-memcpy-byte-copy", juliaFile := "base/cmem.jl",
    juliaFns := ["memcpy"],
    statement := "For valid, disjoint source and destination byte ranges, memcpy returns the destination pointer, copies the original source bytes, and leaves every other byte unchanged.",
    source := "memcpy docstring and base/cmem.jl:12-15; C17 7.24.2.1",
    status := .proven, prop := ``MemcpyNoOverlap, thm := some ``memcpyNoOverlap_proven },
  { id := "cmem-memmove-overlap-safe", juliaFile := "base/cmem.jl",
    juliaFns := ["memmove"],
    statement := "For valid source and destination byte ranges, memmove returns the destination pointer and copies the original source bytes even when the ranges overlap.",
    source := "memmove docstring and base/cmem.jl:26-29; C17 7.24.2.2",
    status := .proven, prop := ``MemmoveOverlapSafe, thm := some ``memmoveOverlapSafe_proven },
  { id := "cmem-memset-byte-value", juliaFile := "base/cmem.jl",
    juliaFns := ["memset"],
    statement := "For a valid destination byte range, memset returns the destination pointer and fills each byte with the low eight bits of its C int value.",
    source := "memset docstring and base/cmem.jl:40-43; C17 7.24.6.1",
    status := .proven, prop := ``MemsetByteValue, thm := some ``memsetByteValue_proven },
  { id := "cmem-memcmp-unsigned-sign", juliaFile := "base/cmem.jl",
    juliaFns := ["memcmp"],
    statement := "memcmp compares bytes as unsigned values, returns zero for equal byte ranges, and otherwise returns a C int whose sign matches the first differing byte pair before widening it to Int.",
    source := "memcmp docstring and base/cmem.jl:54-57; C17 7.24.4.1",
    status := .proven, prop := ``MemcmpUnsignedSign, thm := some ``memcmpUnsignedSign_proven }
]

end JuliaLean.Proofs.base.cmem