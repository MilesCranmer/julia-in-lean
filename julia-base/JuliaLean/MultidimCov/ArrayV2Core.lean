/-!
Memory-level model of `Array` (master `base/array.jl`, `base/genericmemory.jl`).

An `Array` is a `MemoryRef` (memory plus 1-based offset) and a `size` tuple,
exactly the two fields `ref` and `size` that `base/array.jl` reads and writes
with `getfield`/`setfield!`. A `Memory` slot holds `some x` or `none` for an
`#undef` (or not yet written) slot.

Julia `Int` values are mathematical integers here; every place where
`base/array.jl` relies on `Int` overflow behaviour uses `checkedAdd`,
`checkedMul` (throwing `OverflowError`) or `wrap64` explicitly. A conversion
`Int(x)` of an arbitrary `Integer` is `toInt`, which throws `InexactError`
outside the `Int64` range.
-/

namespace JuliaLean.MultidimCov.ArrayV2

inductive Err where
  | argument
  | bounds
  | inexact
  | overflow
  | concurrency
  | undefRef
  | method
  | dimensionMismatch
  | typeError
  | divide
  /-- `AssertionError` from a failed `@assert`. -/
  | assertion
  /-- `throw(nothing)`. -/
  | thrownNothing
  /-- A `memmove` of a negative number of slots: undefined behaviour in C. -/
  | undefinedBehaviour
  deriving Repr, DecidableEq

abbrev R (α : Type) := Except Err α

@[simp] theorem bind_ok {α β : Type} (x : α) (f : α → R β) :
    ((Except.ok x : R α) >>= f) = f x := rfl
@[simp] theorem bind_error {α β : Type} (e : Err) (f : α → R β) :
    ((Except.error e : R α) >>= f) = .error e := rfl
@[simp] theorem pure_ok {α : Type} (x : α) : (pure x : R α) = .ok x := rfl

def typemaxInt : Int := 9223372036854775807
def typeminInt : Int := -9223372036854775808

/-- Two's-complement reduction into `Int64` (`x % Int`). -/
def wrap64 (x : Int) : Int := (x + 2 ^ 63) % (2 ^ 64) - 2 ^ 63

/-- `unsigned(x)` of an `Int64` value. -/
def uns (x : Int) : Int := x % (2 ^ 64)

/-- `Int(x)` of an arbitrary `Integer` value (`InexactError` outside `Int64`). -/
def toInt (x : Int) : R Int :=
  if typeminInt ≤ x ∧ x ≤ typemaxInt then .ok x else .error .inexact

/-- `checked_add(x::Int, y::Int)` (`base/checked.jl`). -/
def checkedAdd (x y : Int) : R Int :=
  if typeminInt ≤ x + y ∧ x + y ≤ typemaxInt then .ok (x + y) else .error .overflow

/-- `checked_mul(x::Int, y::Int)` (`base/checked.jl`). -/
def checkedMul (x y : Int) : R Int :=
  if typeminInt ≤ x * y ∧ x * y ≤ typemaxInt then .ok (x * y) else .error .overflow

theorem toInt_ok {x : Int} (h0 : -4611686018427387904 ≤ x) (h1 : x ≤ 4611686018427387904) : toInt x = .ok x := by
  unfold toInt typeminInt typemaxInt; split
  · rfl
  · omega

theorem checkedAdd_ok {x y : Int} (h0 : -4611686018427387904 ≤ x + y) (h1 : x + y ≤ 4611686018427387904) :
    checkedAdd x y = .ok (x + y) := by
  unfold checkedAdd typeminInt typemaxInt; split
  · rfl
  · omega

theorem checkedMul_ok {x y : Int} (h0 : -4611686018427387904 ≤ x * y) (h1 : x * y ≤ 4611686018427387904) :
    checkedMul x y = .ok (x * y) := by
  unfold checkedMul typeminInt typemaxInt; split
  · rfl
  · omega

/-- A `Memory{T}`: its length and its slots (1-based; `none` is `#undef`). -/
structure Mem (α : Type) where
  len : Int
  get : Int → Option α

/-- `Memory{T}(undef, n)`: a fresh memory with every slot unset. -/
def Mem.undef (n : Int) : Mem α := ⟨n, fun _ => none⟩

/-- `memoryrefset!`/`unsetindex!` of slot `j`. -/
def Mem.set (m : Mem α) (j : Int) (x : Option α) : Mem α :=
  { m with get := fun k => if k = j then x else m.get k }

/-- `unsafe_copyto!(dest, doffs, src, soffs, n)` on memory: a `memmove` of `n`
slots, reading every source slot before any destination write. -/
def Mem.copy (dest : Mem α) (doffs : Int) (src : Mem α) (soffs n : Int) : Mem α :=
  { dest with get := fun k =>
      if doffs ≤ k ∧ k < doffs + n then src.get (k - doffs + soffs) else dest.get k }

@[simp] theorem Mem.undef_len (n : Int) : (Mem.undef n : Mem α).len = n := rfl
@[simp] theorem Mem.undef_get (n k : Int) : (Mem.undef n : Mem α).get k = none := rfl
@[simp] theorem Mem.set_len (m : Mem α) j x : (m.set j x).len = m.len := rfl
@[simp] theorem Mem.set_get (m : Mem α) j x k :
    (m.set j x).get k = if k = j then x else m.get k := rfl
@[simp] theorem Mem.copy_len (d : Mem α) a s b n : (d.copy a s b n).len = d.len := rfl
@[simp] theorem Mem.copy_get (d : Mem α) a s b n k :
    (d.copy a s b n).get k = if a ≤ k ∧ k < a + n then s.get (k - a + b) else d.get k := rfl

/-- Clearing slots `lo:hi` of a memory one by one (`for j in lo:hi; unsetindex!(mem, j)`). -/
def Mem.unsetRange (m : Mem α) (lo hi : Int) : Mem α :=
  { m with get := fun k => if lo ≤ k ∧ k ≤ hi then none else m.get k }

@[simp] theorem Mem.unsetRange_len (m : Mem α) lo hi : (m.unsetRange lo hi).len = m.len := rfl
@[simp] theorem Mem.unsetRange_get (m : Mem α) lo hi k :
    (m.unsetRange lo hi).get k = if lo ≤ k ∧ k ≤ hi then none else m.get k := rfl

/-- `memoryref(mem, i)` with bounds checking (`base/genericmemory.jl:769`, the
`memoryrefnew` builtin): the slot index `i` must lie in `1:length(mem)`. -/
def memref (m : Mem α) (i : Int) : R Int :=
  if 1 ≤ i ∧ i ≤ m.len then .ok i else .error .bounds

/-- `memoryref(ref, i)` with bounds checking, for a ref at absolute slot `off`
(`base/genericmemory.jl:770`): slot `off + i - 1` must lie in the memory. -/
def refIndex (m : Mem α) (off i : Int) : R Int :=
  if 1 ≤ off + i - 1 ∧ off + i - 1 ≤ m.len then .ok (off + i - 1) else .error .bounds

/-- `unsafe_copyto!(dest::MemoryRef, src::MemoryRef, n)` (`base/genericmemory.jl:198`):
returns early for `n == 0`, bounds-checks `memoryref(dest, n)` and
`memoryref(src, n)`, then `memmove`s. -/
def refCopy (dm : Mem α) (doff : Int) (sm : Mem α) (soff n : Int) : R (Mem α) :=
  if n = 0 then .ok dm else do
  let _ ← refIndex dm doff n
  let _ ← refIndex sm soff n
  if n < 0 then .error .undefinedBehaviour else
  pure (dm.copy doff sm soff n)

/-- `unsafe_copyto!(dest::Memory, doffs, src::Memory, soffs, n)` (`base/genericmemory.jl:223`). -/
def memCopy (dm : Mem α) (doffs : Int) (sm : Mem α) (soffs n : Int) : R (Mem α) :=
  if n = 0 then .ok dm else do
  let d ← memref dm doffs
  let s ← memref sm soffs
  refCopy dm d sm s n

theorem refCopy_ok {dm sm : Mem α} {doff soff n : Int} (hn : 0 ≤ n)
    (hd : n = 0 ∨ (1 ≤ doff ∧ doff + n - 1 ≤ dm.len)) (hs : n = 0 ∨ (1 ≤ soff ∧ soff + n - 1 ≤ sm.len)) :
    refCopy dm doff sm soff n = .ok (dm.copy doff sm soff n) := by
  unfold refCopy refIndex
  by_cases h0 : n = 0
  · subst h0; simp only [if_true]; congr 1
    cases dm; simp only [Mem.copy, Mem.mk.injEq, true_and]; funext k; split <;> first | rfl | omega
  · simp only [h0, if_false]
    rw [if_pos (by omega), bind_ok, if_pos (by omega), bind_ok, if_neg (by omega)]; rfl

theorem memCopy_ok {dm sm : Mem α} {doff soff n : Int} (hn : 0 ≤ n)
    (hd : n = 0 ∨ (1 ≤ doff ∧ doff + n - 1 ≤ dm.len)) (hs : n = 0 ∨ (1 ≤ soff ∧ soff + n - 1 ≤ sm.len)) :
    memCopy dm doff sm soff n = .ok (dm.copy doff sm soff n) := by
  unfold memCopy
  by_cases h0 : n = 0
  · subst h0; simp only [if_true]; congr 1
    cases dm; simp only [Mem.copy, Mem.mk.injEq, true_and]; funext k; split <;> first | rfl | omega
  · simp only [h0, if_false]
    unfold memref
    rw [if_pos (by omega), bind_ok, if_pos (by omega), bind_ok]
    exact refCopy_ok hn (by omega) (by omega)

/-- An `Array{T,N}`: `ref` = (`mem`, `off` = `memoryrefoffset(ref)`) and `size` = `dims`. -/
structure Arr (α : Type) where
  mem : Mem α
  off : Int
  dims : List Int

/-- `length(a) = prod(a.size)`. -/
def length (a : Arr α) : Int := a.dims.foldr (· * ·) 1

@[simp] theorem length_vec (a : Arr α) (n : Int) (h : a.dims = [n]) : length a = n := by
  simp [length, h]

/-- Logical slot `i` (1-based linear index): `memoryref(a.ref, i)`. -/
def Arr.at (a : Arr α) (i : Int) : Option α := a.mem.get (a.off + i - 1)

/-- The logical slots `a[1], …, a[length(a)]`, `none` for `#undef`. -/
def contents (a : Arr α) : List (Option α) :=
  (List.range (length a).toNat).map fun k : Nat => a.at ((k : Int) + 1)

/-- The `ref`/`size` invariant `_growend_internal!` checks before resizing:
the data window `off : off+length-1` lies in the memory. -/
def Valid (a : Arr α) : Prop :=
  1 ≤ a.off ∧ 0 ≤ length a ∧ a.off - 1 + length a ≤ a.mem.len

/-- A one-dimensional array (`Vector`) of length `n`. -/
def IsVec (a : Arr α) (n : Int) : Prop := a.dims = [n]

/-- Sizes any real allocation stays below (Julia caps memory below `typemax(Int)`
bytes, and every allocation of `2^60` elements fails). -/
def Small (a : Arr α) : Prop := a.mem.len ≤ 2 ^ 60

@[simp] theorem contents_length (a : Arr α) : (contents a).length = (length a).toNat := by
  simp [contents]

theorem getElem_contents (a : Arr α) (k : Nat) (h : k < (contents a).length) :
    (contents a)[k] = a.at ((k : Int) + 1) := by
  simp [contents]

/-- Two arrays agree logically when they have the same length and slots. -/
theorem contents_ext {a : Arr α} {l : List (Option α)}
    (hl : (length a).toNat = l.length)
    (hs : ∀ k (hk : k < l.length), a.at ((k : Int) + 1) = l[k]) : contents a = l := by
  apply List.ext_getElem
  · simp [hl]
  · intro k h1 h2
    rw [getElem_contents]
    exact hs k h2

/-- `checkbounds(Bool, a, i)` for a linear index. -/
def inBounds (a : Arr α) (i : Int) : Bool := 1 ≤ i && i ≤ length a

/-- `getindex(A::Array, i::Int)` (`base/essentials.jl`): bounds check, then
`memoryrefget`, which throws `UndefRefError` on an unset slot. -/
def getL (a : Arr α) (i : Int) : R α :=
  if inBounds a i then
    match a.at i with
    | some x => .ok x
    | none => .error .undefRef
  else .error .bounds

/-- `@inbounds a[i]` / `__safe_getindex`: `memoryrefget` without the bounds check. -/
def getU (a : Arr α) (i : Int) : R α :=
  match a.at i with
  | some x => .ok x
  | none => .error .undefRef

/-- Unchecked write of logical slot `i` (`memoryrefset!(memoryrefnew(A.ref, i, false), x)`). -/
def setU (a : Arr α) (i : Int) (x : Option α) : Arr α :=
  { a with mem := a.mem.set (a.off + i - 1) x }

/-- `isassigned(memoryrefnew(a.ref, i, false))`. -/
def assignedU (a : Arr α) (i : Int) : Bool := (a.at i).isSome

@[simp] theorem setU_dims (a : Arr α) i x : (setU a i x).dims = a.dims := rfl
@[simp] theorem setU_off (a : Arr α) i x : (setU a i x).off = a.off := rfl
@[simp] theorem setU_mem_len (a : Arr α) i x : (setU a i x).mem.len = a.mem.len := rfl
@[simp] theorem setU_at (a : Arr α) i x k :
    (setU a i x).at k = if k = i then x else a.at k := by
  simp only [setU, Arr.at, Mem.set_get]
  by_cases h : k = i
  · subst h; simp
  · simp [h]

@[simp] theorem length_setU (a : Arr α) i x : length (setU a i x) = length a := rfl

end JuliaLean.MultidimCov.ArrayV2
