import JuliaLean.MultidimCov.ArrayV2Access

/-!
Copying, filling, allocation and range indexing of `Array` (master
`base/array.jl:288-421`, `473`, `981-1096`).

A `Memory{T}` argument is the array view `memArr m` of its slots (offset 1,
size `(length(m),)`), which is exactly how `_copyto_impl!` and `memoryref` see it.
-/

namespace JuliaLean.MultidimCov.ArrayV2

/-- A `Memory` as the slots `memoryref(m, 1), …, memoryref(m, length(m))`. -/
def memArr (m : Mem α) : Arr α := ⟨m, 1, [m.len]⟩

/-- `Array{T,N}(undef, dims)` (`base/boot.jl`): `checked_dims` throws
`ArgumentError("invalid Array dimensions")` for a negative dimension or a size
that overflows `Int`; otherwise a fresh memory of `prod(dims)` unset slots. -/
def newArray (dims : List Int) : R (Arr α) :=
  if dims.all (0 ≤ ·) ∧ dims.foldr (· * ·) 1 ≤ typemaxInt then
    .ok ⟨Mem.undef (dims.foldr (· * ·) 1), 1, dims⟩
  else .error .argument

/-- base/array.jl:299 `_copyto_impl!(dest, doffs, src, soffs, n)`. -/
def m299 (dest : Arr α) (doffs : Int) (src : Arr α) (soffs n : Int) : R (Arr α) :=
  if n = 0 then .ok dest else
  if ¬ n > 0 then .error .argument else
  if ¬ inBounds dest doffs then .error .bounds else
  if ¬ n ≤ length dest - doffs + 1 then .error .bounds else
  if ¬ inBounds src soffs then .error .bounds else
  if ¬ n ≤ length src - soffs + 1 then .error .bounds else do
  let doffs ← toInt doffs
  let soffs ← toInt soffs
  let n ← toInt n
  let m ← refCopy dest.mem (dest.off + doffs - 1) src.mem (src.off + soffs - 1) n
  pure { dest with mem := m }

/-- base/array.jl:288 `copyto!(dest::Array, doffs, src::Array, soffs, n)`. -/
def m288 (dest : Arr α) (doffs : Int) (src : Arr α) (soffs n : Int) : R (Arr α) :=
  m299 dest doffs src soffs n
/-- base/array.jl:290 `copyto!(dest::Array, doffs, src::Memory, soffs, n)`. -/
def m290 (dest : Arr α) (doffs : Int) (src : Mem α) (soffs n : Int) : R (Arr α) :=
  m299 dest doffs (memArr src) soffs n
/-- base/array.jl:292 `copyto!(dest::Memory, doffs, src::Array, soffs, n)`. -/
def m292 (dest : Mem α) (doffs : Int) (src : Arr α) (soffs n : Int) : R (Arr α) :=
  m299 (memArr dest) doffs src soffs n
/-- base/array.jl:296 `copyto!(dest::Array{T}, doffs, src::Array{T}, soffs, n)`. -/
def m296 (dest : Arr α) (doffs : Int) (src : Arr α) (soffs n : Int) : R (Arr α) :=
  m299 dest doffs src soffs n

/-- base/array.jl:321 `_throw_argerror(s)`. -/
def m321 (_s : String) : R α := .error .argument

/-- base/array.jl:323 `_copyto2arg!(dest, src) = copyto!(dest, firstindex(dest), src, firstindex(src), length(src))`. -/
def m323 (dest : Arr α) (src : Arr α) : R (Arr α) := m299 dest 1 src 1 (length src)

/-- base/array.jl:325 `copyto!(dest::Array, src::Array)`. -/
def m325 (dest src : Arr α) : R (Arr α) := m323 dest src
/-- base/array.jl:326 `copyto!(dest::Array, src::Memory)`. -/
def m326 (dest : Arr α) (src : Mem α) : R (Arr α) := m323 dest (memArr src)
/-- base/array.jl:327 `copyto!(dest::Memory, src::Array)`. -/
def m327 (dest : Mem α) (src : Arr α) : R (Arr α) := m323 (memArr dest) src
/-- base/array.jl:330 `copyto!(dest::Array{T}, src::Array{T})`. -/
def m330 (dest src : Arr α) : R (Arr α) := m323 dest src
/-- base/array.jl:331 `copyto!(dest::Array{T}, src::Memory{T})`. -/
def m331 (dest : Arr α) (src : Mem α) : R (Arr α) := m323 dest (memArr src)
/-- base/array.jl:332 `copyto!(dest::Memory{T}, src::Array{T})`. -/
def m332 (dest : Mem α) (src : Arr α) : R (Arr α) := m323 (memArr dest) src

/-- The `copyto!(dest, doffs, src, soffs, n)` contract (docstring
`base/array.jl:282`): `n == 0` returns `dest` untouched, a negative `n` is an
`ArgumentError`, a window outside either array a `BoundsError`; otherwise
`dest[doffs+k-1] = src[soffs+k-1]` for `k ∈ 1:n` and nothing else changes. -/
def CopyContract {D S α : Type} (dA : D → Arr α) (sA : S → Arr α)
    (f : D → Int → S → Int → Int → R (Arr α)) : Prop :=
  ∀ d s doffs soffs n, Valid (dA d) → Valid (sA s) → length (dA d) ≤ 2 ^ 60 → length (sA s) ≤ 2 ^ 60 →
    (n = 0 → f d doffs s soffs n = .ok (dA d)) ∧
    (n < 0 → f d doffs s soffs n = .error .argument) ∧
    (0 < n → ¬ (1 ≤ doffs ∧ doffs + n - 1 ≤ length (dA d) ∧ 1 ≤ soffs ∧ soffs + n - 1 ≤ length (sA s)) →
      f d doffs s soffs n = .error .bounds) ∧
    (0 < n → 1 ≤ doffs → doffs + n - 1 ≤ length (dA d) → 1 ≤ soffs → soffs + n - 1 ≤ length (sA s) →
      ∃ d', f d doffs s soffs n = .ok d' ∧ d'.dims = (dA d).dims ∧ length d' = length (dA d) ∧
        ∀ k, 1 ≤ k → k ≤ length (dA d) →
          d'.at k = if doffs ≤ k ∧ k < doffs + n then (sA s).at (k - doffs + soffs) else (dA d).at k)

theorem m299_contract : CopyContract (α := α) id id m299 := by
  intro d s doffs soffs n hd hs hdl hsl
  simp only [id] at *
  obtain ⟨d1, d2, d3⟩ := hd
  obtain ⟨s1, s2, s3⟩ := hs
  refine ⟨fun h => by unfold m299; rw [if_pos h], fun h => ?_, fun h0 h => ?_, fun h0 h1 h2 h3 h4 => ?_⟩
  · unfold m299; rw [if_neg (by omega), if_pos (by omega)]
  · unfold m299; rw [if_neg (by omega), if_neg (by omega)]
    simp only [inBounds_iff]
    by_cases e1 : 1 ≤ doffs ∧ doffs ≤ length d
    · rw [if_neg (by simpa using e1)]
      by_cases e2 : n ≤ length d - doffs + 1
      · rw [if_neg (by simpa using e2)]
        by_cases e3 : 1 ≤ soffs ∧ soffs ≤ length s
        · rw [if_neg (by simpa using e3), if_pos (by omega)]
        · rw [if_pos (by simpa using e3)]
      · rw [if_pos e2]
    · rw [if_pos (by simpa using e1)]
  · unfold m299; rw [if_neg (by omega), if_neg (by omega)]
    simp only [inBounds_iff]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      toInt_ok (by omega) (by omega), bind_ok, toInt_ok (by omega) (by omega), bind_ok,
      toInt_ok (by omega) (by omega), bind_ok, refCopy_ok (by omega) (by omega) (by omega), bind_ok]
    refine ⟨_, rfl, rfl, rfl, fun k _ _ => ?_⟩
    slot_arith

/-- `copyto!(dest, doffs, src, soffs, n)` on `Array`/`Memory` (rows 288, 290, 292,
296, and `_copyto_impl!` at 299) all satisfy the documented copy contract. -/
def P288 : Prop := ∀ {α : Type}, CopyContract (α := α) id id m288 ∧ CopyContract (α := α) id memArr m290 ∧
    CopyContract (α := α) memArr id m292 ∧ CopyContract (α := α) id id m296 ∧ CopyContract (α := α) id id m299

theorem p288 : P288 := fun {_} => ⟨m299_contract, fun d s => m299_contract d (memArr s),
  fun d s => m299_contract (memArr d) s, m299_contract, m299_contract⟩

/-- `_throw_argerror(s)` always throws `ArgumentError`. -/
def P321 : Prop := ∀ {α : Type} (s : String), (m321 s : R α) = .error .argument
theorem p321 : P321 := fun _ => rfl

/-- The two-argument `copyto!(dest, src)` contract (docstring `base/abstractarray.jl`):
`dest` must be at least as long as `src`; its first `length(src)` slots become
`src`'s and the rest are untouched; a longer non-empty `src` is a `BoundsError`. -/
def Copy2Contract {D S α : Type} (dA : D → Arr α) (sA : S → Arr α) (f : D → S → R (Arr α)) : Prop :=
  ∀ d s, Valid (dA d) → Valid (sA s) → length (dA d) ≤ 2 ^ 60 → length (sA s) ≤ 2 ^ 60 →
    (0 < length (sA s) → length (dA d) < length (sA s) → f d s = .error .bounds) ∧
    (length (sA s) ≤ length (dA d) → ∃ d', f d s = .ok d' ∧ d'.dims = (dA d).dims ∧
      ∀ k, 1 ≤ k → k ≤ length (dA d) → d'.at k = if k ≤ length (sA s) then (sA s).at k else (dA d).at k)

theorem m323_contract : Copy2Contract (α := α) id id m323 := by
  intro d s hd hs hdl hsl
  have hd' := hd; have hs' := hs
  obtain ⟨d1, d2, d3⟩ := hd
  obtain ⟨s1, s2, s3⟩ := hs
  obtain ⟨_, _, hb, hok⟩ := m299_contract d s 1 1 (length s) hd' hs' hdl hsl
  simp only [id] at *
  refine ⟨fun h0 h1 => ?_, fun h => ?_⟩
  · exact hb h0 (by omega)
  · by_cases h0 : length s = 0
    · unfold m323; rw [h0]; refine ⟨d, by unfold m299; rfl, rfl, fun k _ _ => ?_⟩
      rw [if_neg (by omega)]
    · obtain ⟨d', e, hdd, _, hp⟩ := hok (by omega) (by omega) (by omega) (by omega) (by omega)
      refine ⟨d', e, hdd, fun k k1 k2 => ?_⟩
      rw [hp k k1 k2]
      by_cases hk : k ≤ length s
      · rw [if_pos (by omega), if_pos hk]; congr 1; omega
      · rw [if_neg (by omega), if_neg hk]

/-- `copyto!(dest, src)` for every `Array`/`Memory` pairing (rows 323-332). -/
def P323 : Prop := ∀ {α : Type}, Copy2Contract (α := α) id id m323 ∧ Copy2Contract (α := α) id id m325 ∧
    Copy2Contract (α := α) id memArr m326 ∧ Copy2Contract (α := α) memArr id m327 ∧
    Copy2Contract (α := α) id id m330 ∧ Copy2Contract (α := α) id memArr m331 ∧
    Copy2Contract (α := α) memArr id m332

theorem p323 : P323 := fun {_} => ⟨m323_contract, m323_contract, fun d s => m323_contract d (memArr s),
  fun d s => m323_contract (memArr d) s, m323_contract, fun d s => m323_contract d (memArr s),
  fun d s => m323_contract (memArr d) s⟩

/-- base/array.jl:373 `_fill!(A, x)`: `A[i] = x` for `i in eachindex(A)` (`1:length(A)`
for an `Array`), each through the checked `setindex!`. -/
def fillLoop (a : Arr α) (x : α) : Nat → Int → R (Arr α)
  | 0, _ => .ok a
  | k + 1, i => do
    let a ← m1036 a x i
    fillLoop a x k (i + 1)

def m373 (a : Arr α) (x : α) : R (Arr α) := fillLoop a x (length a).toNat 1

/-- base/array.jl:368 `fill!(A::AbstractArray{T}, x)`: convert once, then `_fill!`. -/
def m368 (conv : β → R α) (a : Arr α) (x : β) : R (Arr α) := do
  let x ← conv x
  m373 a x

theorem fillLoop_spec : ∀ (x : α) (k : Nat) (a : Arr α) (i : Int), 1 ≤ i → i - 1 + k ≤ length a →
    ∃ a', fillLoop a x k i = .ok a' ∧ a'.dims = a.dims ∧ a'.off = a.off ∧
      ∀ j, a'.at j = if i ≤ j ∧ j < i + k then some x else a.at j
  | _, 0, a, i, _, _ => ⟨a, rfl, rfl, rfl, fun j => by rw [if_neg (by omega)]⟩
  | x, k + 1, a, i, h1, h2 => by
    unfold fillLoop m1036
    rw [if_neg (by rw [inBounds_iff]; simp; omega), bind_ok]
    obtain ⟨a', e, hd, ho, hp⟩ := fillLoop_spec x k (setU a i (some x)) (i + 1) (by omega)
      (by rw [length_setU]; omega)
    refine ⟨a', e, hd, ho, fun j => ?_⟩
    rw [hp j, setU_at]
    by_cases h : j = i
    · subst h; simp <;> omega
    · rw [if_neg h]; by_cases h' : i + 1 ≤ j ∧ j < i + 1 + k
      · rw [if_pos h', if_pos (by omega)]
      · rw [if_neg h', if_neg (by omega)]

/-- `fill!(A, x)` (docstring `base/array.jl:336`): every element of `A` becomes
`convert(eltype(A), x)` and the shape is unchanged; a failing conversion
propagates before any write. -/
def P368 : Prop := ∀ {α β : Type} (conv : β → R α) (a : Arr α) (x : β), 0 ≤ length a →
    (∀ e, conv x = .error e → m368 conv a x = .error e) ∧
    (∀ y, conv x = .ok y → ∃ a', m368 conv a x = .ok a' ∧ a'.dims = a.dims ∧
      contents a' = List.replicate (length a).toNat (some y)) ∧
    (∀ y : α, ∃ a', m373 a y = .ok a' ∧ a'.dims = a.dims ∧
      contents a' = List.replicate (length a).toNat (some y))

theorem p368 : P368 := by
  intro α β conv a x hl
  have key : ∀ y : α, ∃ a', m373 a y = .ok a' ∧ a'.dims = a.dims ∧
      contents a' = List.replicate (length a).toNat (some y) := by
    intro y
    obtain ⟨a', e, hd, ho, hp⟩ := fillLoop_spec y (length a).toNat a 1 (by omega) (by omega)
    refine ⟨a', e, hd, ?_⟩
    have hla : length a' = length a := by simp [length, hd]
    apply contents_ext (by simp [hla])
    intro k hk
    simp only [List.length_replicate] at hk
    rw [hp, if_pos (by omega)]; simp
  refine ⟨fun e he => ?_, fun y hy => ?_, key⟩
  · unfold m368; rw [he, bind_error]
  · unfold m368; rw [hy, bind_ok]; exact key y

/-- base/array.jl:473 `fill!(a::Union{Array{UInt8},Array{Int8}}, x::Integer)`: convert `x`
to the byte type (range `lo:hi`, `InexactError` outside), then `memset` the
`length(a)` bytes of the data window. -/
def m473 (lo hi : Int) (a : Arr Int) (x : Int) : R (Arr Int) :=
  if lo ≤ x ∧ x ≤ hi then
    .ok { a with mem := { a.mem with get := fun k =>
      if a.off ≤ k ∧ k < a.off + length a then some x else a.mem.get k } }
  else .error .inexact

/-- Byte `fill!`: an in-range value fills every element; an out-of-range value
throws `InexactError` (for `UInt8` `lo:hi = 0:255`, for `Int8` `-128:127`). -/
def P473 : Prop := ∀ (lo hi : Int) (a : Arr Int) (x : Int), 0 ≤ length a →
    ((x < lo ∨ hi < x) → m473 lo hi a x = .error .inexact) ∧
    (lo ≤ x → x ≤ hi → ∃ a', m473 lo hi a x = .ok a' ∧ a'.dims = a.dims ∧
      contents a' = List.replicate (length a).toNat (some x))

theorem p473 : P473 := by
  intro lo hi a x hl
  refine ⟨fun h => ?_, fun h0 h1 => ?_⟩
  · unfold m473; rw [if_neg (by omega)]
  · unfold m473; rw [if_pos ⟨h0, h1⟩]
    refine ⟨_, rfl, rfl, ?_⟩
    apply contents_ext (by simp [length])
    intro k hk
    simp only [List.length_replicate] at hk
    simp only [Arr.at, List.getElem_replicate]
    rw [if_pos (by simp [length] at *; omega)]

/-- base/array.jl:391 `copy(a::Array)`: a fresh memory of `length(a)` slots, the data
window copied with `unsafe_copyto!(memoryref(newmem), ref, length(a))`, same size. -/
def m391 (a : Arr α) : R (Arr α) := do
  let newmem ← refCopy (Mem.undef (length a)) 1 a.mem a.off (length a)
  pure ⟨newmem, 1, a.dims⟩

/-- `copy(a)` (docstring `base/array.jl:380`): same size and the same elements,
`#undef` slots included, in a fresh valid array. -/
def P391 : Prop := ∀ {α : Type} (a : Arr α), Valid a →
    ∃ b, m391 a = .ok b ∧ Valid b ∧ b.dims = a.dims ∧ b.off = 1 ∧ contents b = contents a

theorem p391 : P391 := by
  intro α a ⟨h1, h2, h3⟩
  unfold m391
  rw [refCopy_ok h2 (by simp; omega) (by omega), bind_ok]
  refine ⟨_, rfl, ⟨Int.le_refl 1, h2, show 1 - 1 + length a ≤ length a by omega⟩, rfl, rfl, ?_⟩
  apply contents_ext (by simp [length])
  intro k hk
  simp only [contents_length] at hk
  rw [getElem_contents]
  slot_arith

/-- base/array.jl:402 `_take!(dst, src)`: `dst` takes over `src`'s `ref` and `size`. -/
def m402 (dst src : Arr α) : Arr α :=
  let dst := { dst with mem := src.mem, off := src.off }
  { dst with dims := src.dims }

/-- `_take!` leaves `dst` with exactly `src`'s shape and elements. -/
def P402 : Prop := ∀ {α : Type} (dst src : Arr α),
    (m402 dst src).dims = src.dims ∧ contents (m402 dst src) = contents src
theorem p402 : P402 := fun _ _ => ⟨rfl, rfl⟩

/-! ### `similar` (base/array.jl:414-421) -/

/-- base/array.jl:414 `similar(a::Vector{T}) = Vector{T}(undef, size(a,1))`. -/
def m414 (a : Arr α) : R (Arr α) := newArray [a.dims.headD 1]
/-- base/array.jl:415 `similar(a::Matrix{T}) = Matrix{T}(undef, size(a,1), size(a,2))`. -/
def m415 (a : Arr α) : R (Arr α) := newArray [a.dims.headD 1, a.dims.tail.headD 1]
/-- base/array.jl:416 `similar(a::Vector{T}, S) = Vector{S}(undef, size(a,1))`. -/
def m416 (a : Arr α) : R (Arr β) := newArray [a.dims.headD 1]
/-- base/array.jl:417 `similar(a::Matrix{T}, S) = Matrix{S}(undef, size(a,1), size(a,2))`. -/
def m417 (a : Arr α) : R (Arr β) := newArray [a.dims.headD 1, a.dims.tail.headD 1]
/-- base/array.jl:418 `similar(a::Array{T}, m::Int) = Vector{T}(undef, m)`. -/
def m418 (_a : Arr α) (m : Int) : R (Arr α) := newArray [m]
/-- base/array.jl:419 `similar(a::Array, T, dims::Dims) = Array{T,N}(undef, dims)`. -/
def m419 (_a : Arr α) (dims : List Int) : R (Arr β) := newArray dims
/-- base/array.jl:420 `similar(a::Array{T}, dims::Dims) = Array{T,N}(undef, dims)`. -/
def m420 (_a : Arr α) (dims : List Int) : R (Arr α) := newArray dims
/-- base/array.jl:421 `similar(::Type{Array{T,N}}, dims::Dims) = similar(Array{T}, dims)`. -/
def m421 (dims : List Int) : R (Arr α) := newArray dims

/-- What `similar` promises: a valid array of the requested shape whose elements
are all unset (`#undef`); a negative dimension is an `ArgumentError`. -/
def Fresh (b : Arr α) (dims : List Int) : Prop :=
  b.dims = dims ∧ Valid b ∧ contents b = List.replicate (dims.foldr (· * ·) 1).toNat none

theorem newArray_ok {dims : List Int} (h0 : ∀ d ∈ dims, 0 ≤ d)
    (h1 : dims.foldr (· * ·) 1 ≤ typemaxInt) : ∃ b, (newArray dims : R (Arr α)) = .ok b ∧ Fresh b dims := by
  have hp : 0 ≤ dims.foldr (· * ·) 1 := by
    clear h1
    induction dims with
    | nil => simp
    | cons d ds ih =>
      simp only [List.foldr_cons]
      exact Int.mul_nonneg (h0 d (by simp)) (ih (fun x hx => h0 x (by simp [hx])))
  unfold newArray
  rw [if_pos ⟨by simpa using h0, h1⟩]
  refine ⟨_, rfl, rfl, ⟨Int.le_refl 1, hp, by simp [length]⟩, ?_⟩
  apply contents_ext (by simp [length])
  intro k hk; simp [Arr.at]

theorem newArray_neg {dims : List Int} (h : ∃ d ∈ dims, d < 0) : (newArray dims : R (Arr α)) = .error .argument := by
  unfold newArray
  rw [if_neg]
  intro ⟨h1, _⟩
  obtain ⟨d, hd, hneg⟩ := h
  have := List.all_eq_true.mp h1 d hd
  simp at this; omega

def P414 : Prop := ∀ {α β : Type} (a : Arr α) (dims : List Int),
    (∀ n, IsVec a n → 0 ≤ n → n ≤ typemaxInt →
      (∃ b, m414 a = .ok b ∧ Fresh b [n]) ∧ (∃ b, (m416 a : R (Arr β)) = .ok b ∧ Fresh b [n])) ∧
    (∀ m n, a.dims = [m, n] → 0 ≤ m → 0 ≤ n → m * n ≤ typemaxInt →
      (∃ b, m415 a = .ok b ∧ Fresh b [m, n]) ∧ (∃ b, (m417 a : R (Arr β)) = .ok b ∧ Fresh b [m, n])) ∧
    (∀ m, 0 ≤ m → m ≤ typemaxInt → ∃ b, m418 a m = .ok b ∧ Fresh b [m]) ∧
    (∀ m, m < 0 → m418 a m = .error .argument) ∧
    ((∀ d ∈ dims, 0 ≤ d) → dims.foldr (· * ·) 1 ≤ typemaxInt →
      (∃ b, (m419 a dims : R (Arr β)) = .ok b ∧ Fresh b dims) ∧ (∃ b, m420 a dims = .ok b ∧ Fresh b dims) ∧
      (∃ b, (m421 dims : R (Arr β)) = .ok b ∧ Fresh b dims)) ∧
    ((∃ d ∈ dims, d < 0) → (m419 a dims : R (Arr β)) = .error .argument ∧ m420 a dims = .error .argument ∧
      (m421 dims : R (Arr β)) = .error .argument)

theorem p414 : P414 := by
  intro α β a dims
  refine ⟨fun n hv h0 h1 => ?_, fun m n hv h0 h1 h2 => ?_, fun m h0 h1 => ?_, fun m h => ?_,
    fun h0 h1 => ⟨newArray_ok h0 h1, newArray_ok h0 h1, newArray_ok h0 h1⟩,
    fun h => ⟨newArray_neg h, newArray_neg h, newArray_neg h⟩⟩
  · unfold m414 m416; rw [hv]; simp only [List.headD_cons]
    exact ⟨newArray_ok (by simpa using h0) (by simpa using h1), newArray_ok (by simpa using h0) (by simpa using h1)⟩
  · unfold m415 m417; rw [hv]; simp only [List.headD_cons, List.tail_cons]
    have hd : ∀ d ∈ [m, n], 0 ≤ d := by simp; omega
    have hp : [m, n].foldr (· * ·) 1 ≤ typemaxInt := by simpa using h2
    exact ⟨newArray_ok hd hp, newArray_ok hd hp⟩
  · exact newArray_ok (by simpa using h0) (by simpa using h1)
  · exact newArray_neg ⟨m, by simp, h⟩

end JuliaLean.MultidimCov.ArrayV2
