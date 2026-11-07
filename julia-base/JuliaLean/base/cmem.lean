import JuliaLean.base.pointer

/-!
# Model of `base/cmem.jl`

Typed wrappers for `base/cmem.jl` at Julia commit `f755f49a9e41380d7da126b3c1db9fe7f83dd027`
on a 64-bit platform. C library calls use typed parameters over the shared `ByteHeap` with
C-standard laws for valid byte ranges. Julia's C argument conversions and `n % Csize_t` are
modeled by typed conversion inputs.
-/

namespace JuliaLean.base.cmem

open JuliaLean JuliaLean.base.pointer

abbrev CSizeT := JInt .u64
abbrev CInt := JInt .i32
abbrev NativeInt := JInt .i64

/-- The byte address carried by a typed pointer. -/
def pointerAddress {T : Type} (pointer : Ptr T) : Nat := pointer.address.val.toNat

/-- The pointed-to byte range is valid in the current memory. -/
def validRange {T : Type} (memory : ByteHeap) (pointer : Ptr T) (size : CSizeT) : Prop :=
  memory.validRange (pointerAddress pointer) size.val.toNat

/-- Two byte ranges are disjoint in the 64-bit pointer address space. -/
def rangesDisjoint {T S : Type} (left : Ptr T) (right : Ptr S) (size : CSizeT) : Prop :=
  ∀ i j, i < size.val.toNat → j < size.val.toNat →
    addressMod (pointerAddress left + i) ≠ addressMod (pointerAddress right + j)

/-- The destination contains the source bytes from the pre-call memory and no other byte changes. -/
def copyEffect (before after : ByteHeap) (destination source : Ptr Unit) (size : CSizeT) : Prop :=
  (∀ offset, offset < size.val.toNat →
    after.readByte (pointerAddress destination + offset) =
      before.readByte (pointerAddress source + offset)) ∧
  (∀ address, (∀ offset, offset < size.val.toNat →
      addressMod address ≠ addressMod (pointerAddress destination + offset)) →
    after.readByte address = before.readByte address) ∧
  after.validByte = before.validByte

/-- The destination contains the requested byte at every position and no other byte changes. -/
def fillEffect (before after : ByteHeap) (destination : Ptr Unit) (size : CSizeT)
    (value : JInt .u8) : Prop :=
  (∀ offset, offset < size.val.toNat →
    after.readByte (pointerAddress destination + offset) = value) ∧
  (∀ address, (∀ offset, offset < size.val.toNat →
      addressMod address ≠ addressMod (pointerAddress destination + offset)) →
    after.readByte address = before.readByte address) ∧
  after.validByte = before.validByte

/-- The first byte mismatch, including equality of every preceding byte. -/
def firstDifference (memory : ByteHeap) (left right : Ptr Unit) (size : CSizeT)
    (index : Nat) : Prop :=
  index < size.val.toNat ∧
  (∀ offset, offset < index →
    memory.readByte (pointerAddress left + offset) =
      memory.readByte (pointerAddress right + offset)) ∧
  memory.readByte (pointerAddress left + index) ≠
    memory.readByte (pointerAddress right + index)

def MemcpyLaw (call : ByteHeap → Ptr Unit → Ptr Unit → CSizeT → ByteHeap × Ptr Unit) : Prop :=
  ∀ (memory : ByteHeap) (destination source : Ptr Unit) (size : CSizeT),
    validRange memory destination size →
    validRange memory source size →
    rangesDisjoint destination source size →
    let (after, result) := call memory destination source size
    result.address = destination.address ∧ copyEffect memory after destination source size

def MemmoveLaw (call : ByteHeap → Ptr Unit → Ptr Unit → CSizeT → ByteHeap × Ptr Unit) : Prop :=
  ∀ (memory : ByteHeap) (destination source : Ptr Unit) (size : CSizeT),
    validRange memory destination size →
    validRange memory source size →
    let (after, result) := call memory destination source size
    result.address = destination.address ∧ copyEffect memory after destination source size

def MemsetLaw (call : ByteHeap → Ptr Unit → CInt → CSizeT → ByteHeap × Ptr Unit) : Prop :=
  ∀ (memory : ByteHeap) (destination : Ptr Unit) (value : CInt) (size : CSizeT),
    validRange memory destination size →
    let (after, result) := call memory destination value size
    result.address = destination.address ∧
      fillEffect memory after destination size (JInt.wrap .u8 value.val)

def memcmpEffect (memory : ByteHeap) (left right : Ptr Unit) (size : CSizeT)
    (result : CInt) : Prop :=
  (∀ index, firstDifference memory left right size index →
    (result.val < 0 ↔
        (memory.readByte (pointerAddress left + index)).val <
          (memory.readByte (pointerAddress right + index)).val) ∧
    (result.val > 0 ↔
        (memory.readByte (pointerAddress left + index)).val >
          (memory.readByte (pointerAddress right + index)).val)) ∧
  ((∀ offset, offset < size.val.toNat →
    memory.readByte (pointerAddress left + offset) =
      memory.readByte (pointerAddress right + offset)) → result.val = 0)

def MemcmpLaw (call : ByteHeap → Ptr Unit → Ptr Unit → CSizeT → CInt) : Prop :=
  ∀ (memory : ByteHeap) (left right : Ptr Unit) (size : CSizeT),
    validRange memory left size →
    validRange memory right size →
    let result := call memory left right size
    memcmpEffect memory left right size result

/-- C memory functions over the same explicit byte heap, constrained by the C library contracts. -/
structure CMemoryOps where
  memcpyC : ByteHeap → Ptr Unit → Ptr Unit → CSizeT → ByteHeap × Ptr Unit
  memmoveC : ByteHeap → Ptr Unit → Ptr Unit → CSizeT → ByteHeap × Ptr Unit
  memsetC : ByteHeap → Ptr Unit → CInt → CSizeT → ByteHeap × Ptr Unit
  memcmpC : ByteHeap → Ptr Unit → Ptr Unit → CSizeT → CInt
  memcpyStandard : MemcpyLaw memcpyC
  memmoveStandard : MemmoveLaw memmoveC
  memsetStandard : MemsetLaw memsetC
  memcmpStandard : MemcmpLaw memcmpC

/-- Julia's ccall conversion of an integer argument to `Csize_t`. -/
def csizeFromInt (value : Int) : Jl CSizeT :=
  if 0 ≤ value ∧ value < (2 ^ 64 : Int) then
    .ok (JInt.wrap .u64 value)
  else
    .error (.inexactError "UInt64")

/-- Julia's ccall conversion of an integer argument to `Cint`. -/
def cintFromInt (value : Int) : Jl CInt :=
  if -(2 ^ 31 : Int) ≤ value ∧ value < (2 ^ 31 : Int) then
    .ok (JInt.wrap .i32 value)
  else
    .error (.inexactError "Int32")

/-- `n % Csize_t` for a signed native `Int`, represented as a checked Julia result. -/
def remCsizeInt (value : Int) : Jl CSizeT :=
  .ok (JInt.wrap .u64 value)

/-- Widen a C `int` result to Julia's 64-bit `Int`. -/
def intFromCint (value : CInt) : NativeInt := JInt.wrap .i64 value.val

/--
Julia source: base/cmem.jl:12-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function memcpy(dst::Ptr, src::Ptr, n::Integer)
    @_terminates_globally_meta
    ccall(:memcpy, Ptr{Cvoid}, (Ptr{Cvoid}, Ptr{Cvoid}, Csize_t), dst, src, n)
end
```
-/
def memcpy {D S I : Type} (calls : CMemoryOps) (toCsize : I → Jl CSizeT)
    (memory : ByteHeap) (destination : Ptr D) (source : Ptr S) (n : I) :
    Jl (ByteHeap × Ptr Unit) := do
  let size ← toCsize n
  pure (calls.memcpyC memory (convertPtrType destination) (convertPtrType source) size)

/--
Julia source: base/cmem.jl:26-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function memmove(dst::Ptr, src::Ptr, n::Integer)
    @_terminates_globally_meta
    ccall(:memmove, Ptr{Cvoid}, (Ptr{Cvoid}, Ptr{Cvoid}, Csize_t), dst, src, n)
end
```
-/
def memmove {D S I : Type} (calls : CMemoryOps) (toCsize : I → Jl CSizeT)
    (memory : ByteHeap) (destination : Ptr D) (source : Ptr S) (n : I) :
    Jl (ByteHeap × Ptr Unit) := do
  let size ← toCsize n
  pure (calls.memmoveC memory (convertPtrType destination) (convertPtrType source) size)

/--
Julia source: base/cmem.jl:40-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function memset(p::Ptr, val, n::Integer)
    @_terminates_globally_meta
    ccall(:memset, Ptr{Cvoid}, (Ptr{Cvoid}, Cint, Csize_t), p, val, n)
end
```
-/
def memset {D V I : Type} (calls : CMemoryOps) (toCint : V → Jl CInt)
    (toCsize : I → Jl CSizeT) (memory : ByteHeap) (destination : Ptr D)
    (value : V) (n : I) : Jl (ByteHeap × Ptr Unit) := do
  let cValue ← toCint value
  let size ← toCsize n
  pure (calls.memsetC memory (convertPtrType destination) cValue size)

/--
Julia source: base/cmem.jl:54-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function memcmp(a::Ptr, b::Ptr, n::Integer)
    @_terminates_globally_meta
    ccall(:memcmp, Cint, (Ptr{Cvoid}, Ptr{Cvoid}, Csize_t), a, b, n % Csize_t) % Int
end
```
-/
def memcmp {A B I : Type} (calls : CMemoryOps) (remCsize : I → Jl CSizeT)
    (memory : ByteHeap) (left : Ptr A) (right : Ptr B) (n : I) : Jl NativeInt := do
  let size ← remCsize n
  let result := calls.memcmpC memory (convertPtrType left) (convertPtrType right) size
  pure (intFromCint result)

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
end JuliaLean.base.cmem

namespace JuliaLean.MiscCov.CMem

/-- Process memory: the byte at each address. -/
abbrev Mem := Nat → Nat

/-- `ccall`'s conversion of an `Integer` argument to `Csize_t` (`convert(UInt64, n)`):
`InexactError` outside `0:typemax(UInt64)`. -/
def toCsize (n : Int) : M Nat :=
  if 0 ≤ n ∧ n < 2 ^ 64 then .ok n.toNat else .error .inexactError

/-- `n % Csize_t`: two's-complement reduction modulo `2^64`. -/
def remCsize (n : Int) : Nat := (n % 2 ^ 64).toNat

/-- `ccall`'s conversion of `val` to `Cint` (`convert(Int32, val)`). -/
def toCint (v : Int) : M Int :=
  if -(2 ^ 31) ≤ v ∧ v < 2 ^ 31 then .ok v else .error .inexactError

/-- C `memcpy(dst, src, n)` on non-overlapping ranges: returns `dst`. -/
def cMemcpy (m : Mem) (dst src n : Nat) : Mem × Nat :=
  (fun a => if dst ≤ a ∧ a < dst + n then m (src + (a - dst)) else m a, dst)

/-- C `memmove(dst, src, n)`: as if through a temporary buffer. -/
def cMemmove (m : Mem) (dst src n : Nat) : Mem × Nat :=
  (fun a => if dst ≤ a ∧ a < dst + n then m (src + (a - dst)) else m a, dst)

/-- C `memset(p, c, n)`: stores `(unsigned char)c`. -/
def cMemset (m : Mem) (p : Nat) (c : Int) (n : Nat) : Mem × Nat :=
  (fun a => if p ≤ a ∧ a < p + n then (c % 256).toNat else m a, p)

/-- C `memcmp(a, b, n)`: the sign of the first differing byte pair, `0` if none.
(glibc returns the byte difference; only its sign is specified.) -/
def cMemcmp (m : Mem) : Nat → Nat → Nat → Int
  | _, _, 0 => 0
  | a, b, n + 1 => if m a = m b then cMemcmp m (a + 1) (b + 1) n
    else if m a < m b then -1 else 1

/-- `memcpy(dst::Ptr, src::Ptr, n::Integer)`, `base/cmem.jl:12-15`. -/
def memcpy (m : Mem) (dst src : Nat) (n : Int) : M (Mem × Nat) := do
  let k ← toCsize n
  pure (cMemcpy m dst src k)

/-- `memmove(dst::Ptr, src::Ptr, n::Integer)`, `base/cmem.jl:26-29`. -/
def memmove (m : Mem) (dst src : Nat) (n : Int) : M (Mem × Nat) := do
  let k ← toCsize n
  pure (cMemmove m dst src k)

/-- `memset(p::Ptr, val, n::Integer)`, `base/cmem.jl:40-43`. -/
def memset (m : Mem) (p : Nat) (val : Int) (n : Int) : M (Mem × Nat) := do
  let c ← toCint val
  let k ← toCsize n
  pure (cMemset m p c k)

/-- `memcmp(a::Ptr, b::Ptr, n::Integer)`, `base/cmem.jl:54-57`: the length is `n % Csize_t`
and the `Cint` result is widened with `% Int`. -/
def memcmp (m : Mem) (a b : Nat) (n : Int) : M Int := .ok (cMemcmp m a b (remCsize n))

end JuliaLean.MiscCov.CMem
