import JuliaLean.Proofs.base.abstractarray.memory_safety_access

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

/-- `StringMemory(n)`, `base/iobuffer.jl:166-168`: `_string_n` converts `n` to
`Csize_t` and, on success, returns exactly `n` bytes for `unsafe_wrap`. -/
def stringMemoryAccesses (n : Int) : List Access :=
  if 0 ≤ n ∧ n ≤ 2 ^ 63 - 1 then [span0 n.toNat 0 n.toNat] else []

def StringMemoryInBounds : Prop := ∀ n, accessesSafe (stringMemoryAccesses n)

theorem stringMemoryInBounds_proven : StringMemoryInBounds := by
  intro n
  unfold stringMemoryAccesses
  split <;> simp [accessesSafe, Access.safe, span0]

structure BufferState where
  capacity : Nat
  size : Int
  ptr : Int
  offsetOrCompacted : Int
  mark : Int
  readable : Bool
  writable : Bool
  seekable : Bool
  reinit : Bool
  deriving Repr, DecidableEq

def BufferState.offset (io : BufferState) : Int := max 0 io.offsetOrCompacted

/-- `translate_seek_position`, `base/iobuffer.jl:500-510`, uses widened
arithmetic and clamps back to `Int`. -/
def BufferState.translate (io : BufferState) (n : Int) : Int :=
  max (-2 ^ 63) (min (n + io.offsetOrCompacted + 1) (2 ^ 63 - 1))

/-- Field invariants stated at `base/iobuffer.jl:55-93`, including the
translated-mark relation for a non-seekable buffer proved for reachable
buffers by `JuliaLean.IOBuffers.reachable_inv`. -/
def BufferState.valid (io : BufferState) : Prop :=
  io.capacity < 2 ^ 63 - 1 ∧
  0 ≤ io.offset ∧ io.offset ≤ io.size ∧ io.size ≤ io.capacity ∧
  io.offset + 1 ≤ io.ptr ∧ io.ptr ≤ io.size + 1 ∧
  (io.seekable = false → 0 ≤ io.mark →
    io.offset + 1 ≤ io.translate io.mark ∧ io.translate io.mark ≤ io.ptr)

/-- Dense `peek(from, T)`, `base/iobuffer.jl:418-430`. -/
def ioPeekAccesses (io : BufferState) (width : Nat) : List Access :=
  if io.readable ∧ (width : Int) ≤ io.size - io.ptr + 1 then
    [span0 io.capacity (io.ptr - 1).toNat width]
  else []

/-- `read(from, UInt8)`, `base/iobuffer.jl:438-448`. -/
def ioReadByteAccesses (io : BufferState) : List Access :=
  if io.readable ∧ io.ptr ≤ io.size then
    [at0 io.capacity (io.ptr - 1).toNat]
  else []

/-- Memory-backed `take!`, `base/iobuffer.jl:758-786`. -/
def ioTakeAccesses (io : BufferState) : List Access :=
  if io.reinit then []
  else if io.seekable then
    let count := (io.size - io.offset).toNat
    if count = 0 then [] else [span0 io.capacity io.offset.toNat count]
  else
    let count := (io.size - io.ptr + 1).toNat
    if count = 0 then [] else [span0 io.capacity (io.ptr - 1).toNat count]

def BufferState.usedStart (io : BufferState) : Int :=
  if io.seekable then io.offset + 1
  else if io.mark > -1 then min io.ptr (io.translate io.mark)
  else io.ptr

/-- `get_used_span` followed by the exact-size copy in `unsafe_takestring!` or
`takestring!`, `base/iobuffer.jl:795-859`. -/
def ioTakeStringAccesses (io : BufferState) : List Access :=
  let start := io.usedStart
  let count := (io.size - start + 1).toNat
  if count = 0 then []
  else [span0 io.capacity (start - 1).toNat count, span0 count 0 count]

def IOBufferOperationsInBounds : Prop := ∀ io, io.valid →
  (∀ width, accessesSafe (ioPeekAccesses io width)) ∧
  accessesSafe (ioReadByteAccesses io) ∧
  accessesSafe (ioTakeAccesses io) ∧
  accessesSafe (ioTakeStringAccesses io)

private theorem ioUsedStart_bounds (io : BufferState) (h : io.valid) :
    io.offset + 1 ≤ io.usedStart ∧ io.usedStart ≤ io.size + 1 := by
  unfold BufferState.valid at h
  unfold BufferState.usedStart
  split
  · omega
  · split
    · have hnot : ¬io.seekable = true := by assumption
      have hseek : io.seekable = false := by
        cases hq : io.seekable with
        | false => rfl
        | true => exact (hnot hq).elim
      have hm := h.2.2.2.2.2.2 hseek (by omega)
      omega
    · omega

theorem ioBufferOperationsInBounds_proven : IOBufferOperationsInBounds := by
  intro io hv
  unfold BufferState.valid at hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro width
    unfold ioPeekAccesses accessesSafe
    split
    · intro a ha
      simp only [List.mem_singleton] at ha
      subst a
      simp only [Access.safe, span0]
      have hp : ((io.ptr - 1).toNat : Int) = io.ptr - 1 :=
        Int.toNat_of_nonneg (by omega)
      omega
    · simp
  · unfold ioReadByteAccesses accessesSafe
    split
    · intro a ha
      simp only [List.mem_singleton] at ha
      subst a
      simp only [Access.safe, at0]
      have hp : ((io.ptr - 1).toNat : Int) = io.ptr - 1 :=
        Int.toNat_of_nonneg (by omega)
      omega
    · simp
  · unfold ioTakeAccesses accessesSafe
    split
    · simp
    · split
      · dsimp
        split
        · simp
        · intro a ha
          simp only [List.mem_singleton] at ha
          subst a
          simp only [Access.safe, span0]
          have ho : (io.offset.toNat : Int) = io.offset := Int.toNat_of_nonneg (by omega)
          have hc : ((io.size - io.offset).toNat : Int) = io.size - io.offset :=
            Int.toNat_of_nonneg (by omega)
          omega
      · dsimp
        split
        · simp
        · intro a ha
          simp only [List.mem_singleton] at ha
          subst a
          simp only [Access.safe, span0]
          have hp : ((io.ptr - 1).toNat : Int) = io.ptr - 1 :=
            Int.toNat_of_nonneg (by omega)
          have hc : ((io.size - io.ptr + 1).toNat : Int) = io.size - io.ptr + 1 :=
            Int.toNat_of_nonneg (by omega)
          omega
  · have hs := ioUsedStart_bounds io (by
      unfold BufferState.valid
      exact hv)
    unfold ioTakeStringAccesses accessesSafe
    dsimp
    split
    · simp
    · intro a ha
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · simp only [Access.safe, span0]
        have hp : ((io.usedStart - 1).toNat : Int) = io.usedStart - 1 :=
          Int.toNat_of_nonneg (by omega)
        have hc : ((io.size - io.usedStart + 1).toNat : Int) =
            io.size - io.usedStart + 1 := Int.toNat_of_nonneg (by omega)
        omega
      · simp [Access.safe, span0]

end JuliaLean.MemSafety.G1
