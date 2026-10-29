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

end JuliaLean.base.cmem
