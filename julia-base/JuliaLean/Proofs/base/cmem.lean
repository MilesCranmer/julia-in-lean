import JuliaLean.base.cmem
import JuliaLean.Registry.Types

/-!
# Properties of `base/cmem.jl`

The `StandardC` model in `JuliaLean.base.cmem` implements the four C functions over `ByteHeap`.
Each wrapper property uses that concrete model and its C-standard law field; the historical
negative-length claim remains refuted because `memcmp` converts with `n % Csize_t`.
-/

namespace JuliaLean.Proofs.base.cmem

open JuliaLean JuliaLean.base.cmem JuliaLean.base.pointer JuliaLean.Registry

def cvoidPointer {T : Type} (pointer : Ptr T) : Ptr Unit := convertPtrType pointer

/- The fixed standard-library model makes the C callee's byte behavior part of the specification. -/

/-- On valid disjoint ranges, Julia's `memcpy` wrapper returns the destination and applies the
C model's byte-copy effect. -/
def MemcpyNoOverlap : Prop :=
  ∀ {D S I : Type} (toCsize : I → Jl CSizeT) (memory : ByteHeap)
    (destination : Ptr D) (source : Ptr S) (n : I) (size : CSizeT),
    toCsize n = .ok size →
    validRange memory (cvoidPointer destination) size →
    validRange memory (cvoidPointer source) size →
    rangesDisjoint (cvoidPointer destination) (cvoidPointer source) size →
    ∃ after result,
      memcpy StandardC.standardCMemoryOps toCsize memory destination source n =
        .ok (after, result) ∧
      result.address = (cvoidPointer destination).address ∧
      copyEffect memory after (cvoidPointer destination) (cvoidPointer source) size

/-- On valid ranges, Julia's `memmove` wrapper copies the pre-call source bytes, including when
the ranges overlap. -/
def MemmoveOverlapSafe : Prop :=
  ∀ {D S I : Type} (toCsize : I → Jl CSizeT) (memory : ByteHeap)
    (destination : Ptr D) (source : Ptr S) (n : I) (size : CSizeT),
    toCsize n = .ok size →
    validRange memory (cvoidPointer destination) size →
    validRange memory (cvoidPointer source) size →
    ∃ after result,
      memmove StandardC.standardCMemoryOps toCsize memory destination source n =
        .ok (after, result) ∧
      result.address = (cvoidPointer destination).address ∧
      copyEffect memory after (cvoidPointer destination) (cvoidPointer source) size

/-- On a valid destination range, Julia's `memset` wrapper fills every byte with the low eight
bits of the converted C `int`. -/
def MemsetByteValue : Prop :=
  ∀ {D V I : Type} (toCint : V → Jl CInt) (toCsize : I → Jl CSizeT)
    (memory : ByteHeap) (destination : Ptr D) (value : V) (n : I)
    (cValue : CInt) (size : CSizeT),
    toCint value = .ok cValue →
    toCsize n = .ok size →
    validRange memory (cvoidPointer destination) size →
    ∃ after result,
      memset StandardC.standardCMemoryOps toCint toCsize memory destination value n =
        .ok (after, result) ∧
      result.address = (cvoidPointer destination).address ∧
      fillEffect memory after (cvoidPointer destination) size (JInt.wrap .u8 cValue.val)

/-- On valid ranges, Julia's `memcmp` wrapper returns the `Int` widening of C's unsigned-byte
comparison: zero for equal bytes and the sign of the first mismatch otherwise. -/
def MemcmpUnsignedSign : Prop :=
  ∀ {A B I : Type} (remCsize : I → Jl CSizeT) (memory : ByteHeap)
    (left : Ptr A) (right : Ptr B) (n : I) (size : CSizeT),
    remCsize n = .ok size →
    validRange memory (cvoidPointer left) size →
    validRange memory (cvoidPointer right) size →
    let cResult := StandardC.standardCMemoryOps.memcmpC memory
      (cvoidPointer left) (cvoidPointer right) size
    ∃ result,
      memcmp StandardC.standardCMemoryOps remCsize memory left right n = .ok result ∧
      result.val = (intFromCint cResult).val ∧
      memcmpEffect memory (cvoidPointer left) (cvoidPointer right) size cResult

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

/-! ## Proofs from the concrete C byte model -/

theorem memcpyNoOverlap_proven : MemcpyNoOverlap := by
  intro D S I toCsize memory destination source n size hconv hvDst hvSrc hdisj
  let dst := cvoidPointer destination
  let src := cvoidPointer source
  let call := StandardC.standardCMemoryOps.memcpyC memory dst src size
  have hlaw := StandardC.standardCMemoryOps.memcpyStandard memory dst src size
    (by simpa [dst] using hvDst) (by simpa [src] using hvSrc)
    (by simpa [dst, src] using hdisj)
  refine ⟨call.1, call.2, ?_, ?_, ?_⟩
  · simp [memcpy, hconv, call, dst, src, cvoidPointer,
      StandardC.standardCMemoryOps, StandardC.cMemcpy] <;> rfl
  · simpa [call, dst, StandardC.standardCMemoryOps, StandardC.cMemcpy] using hlaw.1
  · simpa [call, dst, src, StandardC.standardCMemoryOps, StandardC.cMemcpy] using hlaw.2

theorem memmoveOverlapSafe_proven : MemmoveOverlapSafe := by
  intro D S I toCsize memory destination source n size hconv hvDst hvSrc
  let dst := cvoidPointer destination
  let src := cvoidPointer source
  let call := StandardC.standardCMemoryOps.memmoveC memory dst src size
  have hlaw := StandardC.standardCMemoryOps.memmoveStandard memory dst src size
    (by simpa [dst] using hvDst) (by simpa [src] using hvSrc)
  refine ⟨call.1, call.2, ?_, ?_, ?_⟩
  · simp [memmove, hconv, call, dst, src, cvoidPointer,
      StandardC.standardCMemoryOps, StandardC.cMemmove] <;> rfl
  · simpa [call, dst, StandardC.standardCMemoryOps, StandardC.cMemmove] using hlaw.1
  · simpa [call, dst, src, StandardC.standardCMemoryOps, StandardC.cMemmove] using hlaw.2

theorem memsetByteValue_proven : MemsetByteValue := by
  intro D V I toCint toCsize memory destination value n cValue size hconvV hconvN hvDst
  let dst := cvoidPointer destination
  let call := StandardC.standardCMemoryOps.memsetC memory dst cValue size
  have hlaw := StandardC.standardCMemoryOps.memsetStandard memory dst cValue size
    (by simpa [dst] using hvDst)
  refine ⟨call.1, call.2, ?_, ?_, ?_⟩
  · simp [memset, hconvV, hconvN, call, dst, cvoidPointer,
      StandardC.standardCMemoryOps, StandardC.cMemset] <;> rfl
  · simpa [call, dst, StandardC.standardCMemoryOps, StandardC.cMemset] using hlaw.1
  · simpa [call, dst, StandardC.standardCMemoryOps, StandardC.cMemset] using hlaw.2

theorem cintVal_in64 (value : CInt) : (JInt.wrap .i64 value.val).val = value.val := by
  have hb := value.property
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb
  show wrapInt .i64 value.val = value.val
  exact wrapInt_of_inRange .i64 value.val (by
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb ⊢
    omega)

theorem memcmpUnsignedSign_proven : MemcmpUnsignedSign := by
  intro A B I remCsize memory left right n size hconv hvL hvR
  let lhs := cvoidPointer left
  let rhs := cvoidPointer right
  let cResult := StandardC.standardCMemoryOps.memcmpC memory lhs rhs size
  have hlaw := StandardC.standardCMemoryOps.memcmpStandard memory lhs rhs size
    (by simpa [lhs] using hvL) (by simpa [rhs] using hvR)
  refine ⟨intFromCint cResult, ?_, ?_, ?_⟩
  · simp [memcmp, hconv, cResult, lhs, rhs, cvoidPointer,
      StandardC.standardCMemoryOps] <;> rfl
  · simpa [intFromCint, cResult, lhs, rhs, cvoidPointer,
      StandardC.standardCMemoryOps] using cintVal_in64 cResult
  · simpa [lhs, rhs, cResult, StandardC.standardCMemoryOps] using hlaw


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
]

end JuliaLean.Proofs.base.cmem