import JuliaLean.MultidimCov.ArrayV2Push

/-!
`Base.wrap(Array, …)` and its checks (master `base/array.jl:3241-3279`, with
`Core.checked_dims` from `base/boot.jl:792-818`), and the `memcmp`-based `cmp`
and `==` of bit-integer arrays (`base/array.jl:2161-2210`).
-/

namespace JuliaLean.MultidimCov.ArrayV2

/-! ### `checked_dims` and `wrap` -/

/-- The loop of `Core._checked_mul_dims(m, d...)` (base/boot.jl:792-809): the wrapped
product and the error flag `neg | (ovflw & !zero)`. `neg` marks a dimension `d`
with `ule_int(typemax_Int, d)` (negative or `typemax(Int)`), `ovflw` a
`checked_smul_int` overflow, `zero` a later zero dimension. -/
def checkedMulLoop : Int → Bool → Bool → Bool → List Int → Int × Bool
  | a, ovflw, neg, zero, [] => (a, neg || (ovflw && !zero))
  | a, ovflw, neg, zero, d :: ds =>
    checkedMulLoop (wrap64 (a * d)) (ovflw || !decide (typeminInt ≤ a * d ∧ a * d ≤ typemaxInt))
      (neg || decide (d < 0 ∨ d = typemaxInt)) (zero || d == 0) ds

/-- `Core.checked_dims(dims...)` (base/boot.jl:812-818): `1` for no dimension, the
dimension itself for one ("defer this check to Memory constructor instead"), and
otherwise the product, `ArgumentError("invalid Array dimensions")` on the flag. -/
def checkedDims : List Int → R Int
  | [] => .ok 1
  | [m] => .ok m
  | m :: ds =>
    let r := checkedMulLoop m false (decide (m < 0 ∨ m = typemaxInt)) false ds
    if r.2 then .error .argument else .ok r.1

/-- base/array.jl:3249 `invalid_wrap_err(len, dims, proddims)`: throws
`DimensionMismatch("Attempted to wrap a MemoryRef of length $len with an Array of size dims=$dims …")`. -/
def m3249 (_len : Int) (_dims : List Int) (_proddims : Int) : R β := .error .dimensionMismatch

/-- base/array.jl:3241 `_wrap(ref::MemoryRef{T}, dims::NTuple{N,Int})` for a ref at slot
`off` of `mem`: `mem_len = length(mem) + 1 - memoryrefoffset(ref)`,
`len = Core.checked_dims(dims...)`, `mem_len >= len || invalid_wrap_err(...)`, return the ref. -/
def m3241 (mem : Mem α) (off : Int) (dims : List Int) : R (Mem α × Int) := do
  let memLen := mem.len + 1 - off
  let len ← checkedDims dims
  if memLen ≥ len then pure (mem, off) else m3249 memLen dims len

/-- `convert(Dims, dims)` of an `NTuple{N,Integer}`: each entry becomes an `Int`. -/
def toDims (dims : List Int) : R (List Int) := dims.mapM toInt

/-- base/array.jl:3254 `wrap(::Type{Array}, m::MemoryRef{T}, dims::NTuple{N,Integer})`. -/
def m3254 (mem : Mem α) (off : Int) (dims0 : List Int) : R (Arr α) := do
  let dims ← toDims dims0
  let r ← m3241 mem off dims
  pure ⟨r.1, r.2, dims⟩

/-- base/array.jl:3260 `wrap(::Type{Array}, m::Memory{T}, dims::NTuple{N,Integer})`
(`memoryref(m)` is the ref at slot 1). -/
def m3260 (mem : Mem α) (dims0 : List Int) : R (Arr α) := do
  let dims ← toDims dims0
  let r ← m3241 mem 1 dims
  pure ⟨r.1, r.2, dims⟩

/-- base/array.jl:3265 `wrap(::Type{Array}, m::MemoryRef{T}, l::Integer)`: `dims = (Int(l),)`. -/
def m3265 (mem : Mem α) (off : Int) (l : Int) : R (Arr α) := do
  let l' ← toInt l
  let r ← m3241 mem off [l']
  pure ⟨r.1, r.2, [l']⟩

/-- base/array.jl:3270 `wrap(::Type{Array}, m::Memory{T}, l::Integer)`: `dims = (Int(l),)`,
but `_wrap(memoryref(m), (l,))` receives `l` itself, a `MethodError` unless `l isa Int`. -/
def m3270 (mem : Mem α) (l : Int) (isInt : Bool) : R (Arr α) := do
  let l' ← toInt l
  if ¬ isInt then .error .method else do
  let r ← m3241 mem 1 [l]
  pure ⟨r.1, r.2, [l']⟩

/-- base/array.jl:3275 `wrap(::Type{Array}, m::Memory{T})`: `memoryref(m)` and `(length(m),)`. -/
def m3275 (mem : Mem α) : Arr α := ⟨mem, 1, [mem.len]⟩

/-- The documented `wrap` result (docstring base/array.jl:3232-3236): for an `Int`
size `dims` (all entries nonnegative, product at most `typemax(Int)`), an array of
that size over the memory starting at the ref (same memory, same first slot) when
the product fits in the memory from the ref on, and `DimensionMismatch` otherwise;
a negative dimension is an `ArgumentError` (as for every `Array` constructor); an
integer outside `Int` is an `InexactError`. -/
def WrapContract (w : Mem α → Int → List Int → R (Arr α)) (mem : Mem α) (off : Int) : Prop :=
  (∀ dims : List Int, (∀ d ∈ dims, typeminInt ≤ d ∧ d ≤ typemaxInt) →
    (∃ d ∈ dims, d < 0) → w mem off dims = .error .argument) ∧
  (∀ dims : List Int, (∀ d ∈ dims, 0 ≤ d ∧ d < typemaxInt) → dims.foldr (· * ·) 1 ≤ typemaxInt →
    (dims.foldr (· * ·) 1 ≤ mem.len + 1 - off → w mem off dims = .ok ⟨mem, off, dims⟩) ∧
    (mem.len + 1 - off < dims.foldr (· * ·) 1 → w mem off dims = .error .dimensionMismatch)) ∧
  (∀ dims : List Int, (∃ d ∈ dims, d < typeminInt ∨ typemaxInt < d) →
    (∀ d ∈ dims, typeminInt ≤ d ∧ d ≤ typemaxInt ∨ d < typeminInt ∨ typemaxInt < d) → w mem off dims = .error .inexact)

/-- Every `wrap` method meets the documented contract for every valid ref
(`1 ≤ off ≤ length(mem) + 1`): tuples of integers (`MemoryRef` and `Memory`) and
a single integer length (`MemoryRef`, and `Memory` with an `Int` length);
`wrap(Array, m)` is the whole memory as a vector. -/
def P3241 : Prop := ∀ {α : Type} (mem : Mem α) (off : Int), 1 ≤ off → off ≤ mem.len + 1 → 0 ≤ mem.len →
    WrapContract m3254 mem off ∧ WrapContract (fun m _ ds => m3260 m ds) mem 1 ∧
    WrapContract (fun m o ds => match ds with | [l] => m3265 m o l | _ => .error .method) mem off ∧
    WrapContract (fun m _ ds => match ds with | [l] => m3270 m l true | _ => .error .method) mem 1 ∧
    (m3275 mem = ⟨mem, 1, [mem.len]⟩)

/-- `wrap(Array, Memory{Int}(undef, 3), -1)` is an array of size `(-1,)`. -/
theorem wrap_negative : m3265 (Mem.undef 3 : Mem Unit) 1 (-1) = .ok ⟨Mem.undef 3, 1, [-1]⟩ := by
  unfold m3265 m3241 checkedDims; rw [toInt_ok (by omega) (by omega)]; rfl

theorem p3241_refuted : ¬ P3241 := by
  intro h
  have := ((h (Mem.undef 3 : Mem Unit) 1 (by omega) (by simp) (by simp)).2.2.1.1 [-1]
    (by intro d hd; simp at hd; subst hd; unfold typeminInt typemaxInt; omega) ⟨-1, by simp, by omega⟩)
  simp only [] at this
  rw [wrap_negative] at this
  cases this

/-! ### `cmp` and `==` with `memcmp` -/

/-- `memcmp(pa, pb, n)` on byte sequences: the difference of the first differing
byte among the first `n`, or `0`. -/
def memcmp : Nat → List Int → List Int → Int
  | 0, _, _ => 0
  | _ + 1, [], _ => 0
  | _ + 1, _, [] => 0
  | n + 1, x :: xs, y :: ys => if x = y then memcmp n xs ys else x - y

/-- `cmp(x::Int, y::Int)`. -/
def cmpInt (x y : Int) : Int := if x < y then -1 else if y < x then 1 else 0

/-- The elements of a fully assigned array. -/
def Elems (a : Arr Int) (xs : List Int) : Prop := contents a = xs.map some

/-- base/array.jl:2161 `cmp(a::Array{UInt8,1}, b::Array{UInt8,1})`:
`c = memcmp(pa, pb, min(length(a), length(b)))`, then `c < 0 ? -1 : c > 0 ? +1 : cmp(length(a), length(b))`. -/
def m2161 (xs ys : List Int) : Int :=
  let c := memcmp (min xs.length ys.length) xs ys
  if c < 0 then -1 else if c > 0 then 1 else cmpInt xs.length ys.length

/-- base/array.jl:2176 `==(a::Arr, b::Arr) where Arr <: BitIntegerArray`:
`size(a) == size(b)` and `memcmp` of the `sizeof(eltype)*length(a)` bytes is zero
(element bytes agree exactly when the elements do). -/
def m2176 (da db : List Int) (xs ys : List Int) : Bool :=
  if da = db then memcmp xs.length xs ys == 0 else false

/-- base/array.jl:2193 `==(a::Arr, b::Arr) where Arr <: BitIntegerArray{1}`:
`length(a) == length(b)` and the `memcmp` of `sizeof(T)*len` bytes is zero. -/
def m2193 (xs ys : List Int) : Bool :=
  if xs.length = ys.length then memcmp xs.length xs ys == 0 else false

/-- Lexicographic comparison of two vectors (the generic `cmp(A::AbstractVector, B)`):
the first differing element decides, otherwise the shorter vector is smaller. -/
def lexCmp : List Int → List Int → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | x :: xs, y :: ys => if x < y then -1 else if y < x then 1 else lexCmp xs ys

theorem memcmp_sign : ∀ (xs ys : List Int),
    let c := memcmp (min xs.length ys.length) xs ys
    (c < 0 → lexCmp xs ys = -1) ∧ (0 < c → lexCmp xs ys = 1) ∧ (c = 0 → lexCmp xs ys = cmpInt xs.length ys.length)
  | [], [] => by simp [memcmp, lexCmp, cmpInt]
  | [], _ :: _ => by simp [memcmp, lexCmp, cmpInt]
  | _ :: _, [] => by simp [memcmp, lexCmp, cmpInt] <;> omega
  | x :: xs, y :: ys => by
    have ih := memcmp_sign xs ys
    simp only [List.length_cons, Nat.add_min_add_right, memcmp, lexCmp] at ih ⊢
    by_cases hxy : x = y
    · subst hxy
      simp only [if_true, Int.lt_irrefl, if_false]
      refine ⟨ih.1, ih.2.1, fun h => ?_⟩
      rw [ih.2.2 h]; unfold cmpInt; push_cast; split <;> split <;> omega
    · rw [if_neg hxy]
      by_cases hl : x < y
      · rw [if_pos hl]; omega
      · rw [if_neg hl, if_pos (by omega)]; omega

/-- `cmp` on byte vectors (base/array.jl:2161) is the lexicographic comparison of
the bytes (the generic `cmp` of vectors): `-1`, `0` or `1`. -/
def P2161 : Prop := ∀ xs ys : List Int, m2161 xs ys = lexCmp xs ys

theorem p2161 : P2161 := by
  intro xs ys
  have h := memcmp_sign xs ys
  simp only [] at h
  unfold m2161; simp only []
  split
  · exact (h.1 (by omega)).symm
  · split
    · exact (h.2.1 (by omega)).symm
    · exact (h.2.2 (by omega)).symm

theorem memcmp_self_eq : ∀ (xs ys : List Int), xs.length = ys.length → (memcmp xs.length xs ys = 0 ↔ xs = ys)
  | [], [], _ => by simp [memcmp]
  | x :: xs, y :: ys, h => by
    simp only [List.length_cons] at h
    simp only [List.length_cons, memcmp, List.cons.injEq]
    by_cases hxy : x = y
    · rw [if_pos hxy, memcmp_self_eq xs ys (by omega)]; simp [hxy]
    · rw [if_neg hxy]; simp [hxy]; omega

/-- `==` on bit-integer arrays (base/array.jl:2176, 2193) agrees with the generic
array `==`: equal sizes (lengths) and equal elements in order. -/
def P2176 : Prop := ∀ (da db : List Int) (xs ys : List Int),
    da.foldr (· * ·) 1 = (xs.length : Int) → db.foldr (· * ·) 1 = (ys.length : Int) →
    (m2176 da db xs ys = true ↔ da = db ∧ xs = ys) ∧ (m2193 xs ys = true ↔ xs = ys)

theorem p2176 : P2176 := by
  intro da db xs ys h1 h2
  refine ⟨?_, ?_⟩
  · unfold m2176
    by_cases hd : da = db
    · subst hd
      have hl : xs.length = ys.length := by omega
      rw [if_pos rfl]; simp only [beq_iff_eq, memcmp_self_eq xs ys hl, true_and]
    · rw [if_neg hd]; simp [hd]
  · unfold m2193
    by_cases hl : xs.length = ys.length
    · rw [if_pos hl]; simp only [beq_iff_eq, memcmp_self_eq xs ys hl]
    · rw [if_neg hl]; simp only [Bool.false_eq_true, false_iff]; intro h; subst h; exact hl rfl

end JuliaLean.MultidimCov.ArrayV2
