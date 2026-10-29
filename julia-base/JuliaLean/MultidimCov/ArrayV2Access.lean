import JuliaLean.MultidimCov.ArrayV2Grow

/-!
Element access of `Array` (master `base/array.jl:208-244`, `974-1060`).

An element conversion `x isa T ? x : convert(T, x)::T` is a parameter
`conv : β → R α`; the properties quantify over every such conversion, so they
hold whatever `convert` does (including throwing).
-/

namespace JuliaLean.MultidimCov.ArrayV2

/-- `to_index(i::Integer)` (`base/indices.jl:258-259`): a `Bool` is an
`ArgumentError`, any other `Integer` is `convert(Int, i)`. -/
def toIndex (isBool : Bool) (i : Int) : R Int :=
  if isBool then .error .argument else toInt i

/-- `checkbounds(Bool, A, i::Int)` for an `Array` (linear index in `1:length(A)`). -/
theorem inBounds_iff (a : Arr α) (i : Int) : inBounds a i = true ↔ 1 ≤ i ∧ i ≤ length a := by
  simp [inBounds]

/-- base/array.jl:209 `unsetindex!(A::Array, i::Int)`. -/
def m209 (a : Arr α) (i : Int) : R (Arr α) :=
  if ¬ inBounds a i then .error .bounds else .ok (setU a i none)

/-- base/array.jl:208 `unsetindex!(A::Array, i::Integer) = unsetindex!(A, to_index(i))`. -/
def m208 (a : Arr α) (isBool : Bool) (i : Int) : R (Arr α) := do
  let i ← toIndex isBool i
  m209 a i

/-- base/array.jl:239 `isassigned(a::Vector, i::Int)`. -/
def m239 (a : Arr α) (i : Int) : Bool :=
  if ¬ inBounds a i then false else assignedU a i

/-- base/essentials.jl `getindex(A::Array, i::Int)`. -/
theorem getL_def (a : Arr α) (i : Int) : getL a i =
    if inBounds a i then (match a.at i with | some x => .ok x | none => .error .undefRef)
    else .error .bounds := rfl

/-- base/array.jl:1036 `_setindex!(A::Array{T}, x::T, i::Int)`. -/
def m1036 (a : Arr α) (x : α) (i : Int) : R (Arr α) :=
  if ¬ inBounds a i then .error .bounds else .ok (setU a i (some x))

/-- base/array.jl:1031 `setindex!(A::Array{T}, x, i::Int)`: convert, then `_setindex!`. -/
def m1031 (conv : β → R α) (a : Arr α) (x : β) (i : Int) : R (Arr α) := do
  let x ← conv x
  m1036 a x i

/-- base/array.jl:1055 `__safe_setindex!(A::Vector{Any}, x, i::Int)`: no bounds check. -/
def m1055 (a : Arr α) (x : α) (i : Int) : Arr α := setU a i (some x)

/-- base/array.jl:1057 `__safe_setindex!(A::Vector{T}, x::T, i::Int)`: no bounds check. -/
def m1057 (a : Arr α) (x : α) (i : Int) : Arr α := setU a i (some x)

/-- base/array.jl:1059 `__safe_setindex!(A::Vector{T}, x, i::Int)`: convert, then the unchecked write. -/
def m1059 (conv : β → R α) (a : Arr α) (x : β) (i : Int) : R (Arr α) := do
  let x ← conv x
  pure (m1057 a x i)

/-! ### Cartesian indices (`base/abstractarray.jl:722-728`, `3167-3203`) -/

/-- `checkbounds_indices(Bool, axes(A), I)` for `Array` axes `OneTo(d)`: each index
in `1:d` of its dimension (`OneTo(1)` past the last), and every dimension without
an index of length 1. -/
def checkIdx : List Int → List Int → Bool
  | dims, [] => dims.all (· == 1)
  | dims, i :: is => (1 ≤ i && i ≤ dims.headD 1) && checkIdx dims.tail is

/-- `_sub2ind_recurse(inds, L, ind, I...)`. -/
def sub2indRec : List Int → Int → Int → List Int → Int
  | _, _, ind, [] => ind
  | [], l, ind, i :: is => sub2indRec [] l (ind + (i - 1) * l) is
  | d :: ds, l, ind, i :: is => sub2indRec ds (l * d) (ind + (i - 1) * l) is

/-- `_to_linear_index(A, i1, i2, I...)`: `i1` for a `Vector` (`base/abstractarray.jl:1399`),
else `_sub2ind(size(A), I...)`. -/
def toLinear (a : Arr α) : List Int → Int
  | [] => 1
  | i :: is => if a.dims.length = 1 then i else sub2indRec a.dims 1 1 (i :: is)

/-- base/array.jl:974 `getindex(A::Array, i1::Int, i2::Int, I::Int...)`. -/
def m974 (a : Arr α) (i1 i2 : Int) (is : List Int) : R α :=
  if ¬ checkIdx a.dims (i1 :: i2 :: is) then .error .bounds else getU a (toLinear a (i1 :: i2 :: is))

/-- base/array.jl:1047 `_setindex!(A::Array{T}, x::T, i1::Int, i2::Int, I::Int...)`. -/
def m1047 (a : Arr α) (x : α) (i1 i2 : Int) (is : List Int) : R (Arr α) :=
  if ¬ checkIdx a.dims (i1 :: i2 :: is) then .error .bounds
  else .ok (setU a (toLinear a (i1 :: i2 :: is)) (some x))

/-- base/array.jl:1042 `setindex!(A::Array{T}, x, i1::Int, i2::Int, I::Int...)`. -/
def m1042 (conv : β → R α) (a : Arr α) (x : β) (i1 i2 : Int) (is : List Int) : R (Arr α) := do
  let x ← conv x
  m1047 a x i1 i2 is

/-- base/array.jl:231 `isassigned(a::Array, i::Int...)`: `checkbounds(Bool, a, i...)`, which is
the linear check `1 ≤ i ≤ length(a)` for a single index (`base/abstractarray.jl:690`) and
`checkbounds_indices` otherwise, then `_sub2ind(size(a), i...)`. -/
def m231 (a : Arr α) (is : List Int) : Bool :=
  let inb := match is with
    | [i] => inBounds a i
    | _ => checkIdx a.dims is
  if !inb then false
  else assignedU a (sub2indRec a.dims 1 1 is)

/-! ### Properties -/

/-- `getindex`/`isassigned`/`setindex!`/`unsetindex!` on a linear index
(`isassigned` docstring, `base/essentials.jl:1112`): `isassigned(a, i)` holds
exactly when `a[i]` returns a value; an out-of-range `i` makes `a[i]`, `a[i] = x`
and `unsetindex!(a, i)` throw `BoundsError`; after `a[i] = x` (converted), `a[i]`
is the converted `x` and every other slot, the size and the length are
unchanged; after `unsetindex!(a, i)` slot `i` is unassigned and the rest unchanged. -/
def PLinear : Prop := ∀ {α β : Type} (conv : β → R α) (a : Arr α) (i : Int),
    (m239 a i = true ↔ ∃ x, getL a i = .ok x) ∧
    (¬ (1 ≤ i ∧ i ≤ length a) → getL a i = .error .bounds ∧ m209 a i = .error .bounds ∧
      ∀ x : α, m1036 a x i = .error .bounds) ∧
    (1 ≤ i → i ≤ length a → ∀ x : β,
      (∀ e, conv x = .error e → m1031 conv a x i = .error e) ∧
      (∀ y, conv x = .ok y → ∃ a', m1031 conv a x i = .ok a' ∧ a'.dims = a.dims ∧ getL a' i = .ok y ∧
        ∀ j, j ≠ i → a'.at j = a.at j)) ∧
    (1 ≤ i → i ≤ length a → ∃ a', m209 a i = .ok a' ∧ a'.dims = a.dims ∧ m239 a' i = false ∧
      ∀ j, j ≠ i → a'.at j = a.at j)

theorem pLinear : PLinear := by
  intro α β conv a i
  refine ⟨?_, fun h => ⟨?_, ?_, fun x => ?_⟩, fun h1 h2 x => ⟨fun e he => ?_, fun y hy => ?_⟩,
    fun h1 h2 => ?_⟩
  · unfold m239 getL assignedU
    by_cases hb : inBounds a i
    · simp only [hb, not_true_eq_false, if_false, if_true]
      cases a.at i <;> simp
    · simp [hb]
  · unfold getL; rw [if_neg (by rw [inBounds_iff]; exact h)]
  · unfold m209; rw [if_pos (by rw [inBounds_iff]; exact h)]
  · unfold m1036; rw [if_pos (by rw [inBounds_iff]; exact h)]
  · unfold m1031; rw [he, bind_error]
  · unfold m1031; rw [hy, bind_ok]; unfold m1036
    rw [if_neg (by rw [inBounds_iff]; exact fun h => h ⟨h1, h2⟩)]
    refine ⟨_, rfl, rfl, ?_, fun j hj => by simp [hj]⟩
    unfold getL; rw [if_pos (by rw [inBounds_iff]; simp; omega)]; simp
  · unfold m209; rw [if_neg (by rw [inBounds_iff]; exact fun h => h ⟨h1, h2⟩)]
    refine ⟨_, rfl, rfl, ?_, fun j hj => by simp [hj]⟩
    unfold m239 assignedU; simp

/-- `unsetindex!(A, i::Integer)` converts with `to_index`: a `Bool` index is an
`ArgumentError`, an `Integer` outside `Int` an `InexactError`, and any other index
behaves as `unsetindex!(A, Int(i))`. -/
def P208 : Prop := ∀ {α : Type} (a : Arr α) (i : Int),
    m208 a true i = .error .argument ∧
    ((i < typeminInt ∨ typemaxInt < i) → m208 a false i = .error .inexact) ∧
    (typeminInt ≤ i → i ≤ typemaxInt → m208 a false i = m209 a i)

theorem p208 : P208 := by
  intro α a i
  refine ⟨rfl, fun h => ?_, fun h0 h1 => ?_⟩
  · unfold m208 toIndex toInt; simp only [Bool.false_eq_true, if_false]
    rw [if_neg (by omega), bind_error]
  · unfold m208 toIndex toInt; simp only [Bool.false_eq_true, if_false]
    rw [if_pos ⟨h0, h1⟩, bind_ok]

/-- The unchecked `__safe_setindex!` writes are what `@_safeindex` relies on: for an
in-range index they agree with the checked `setindex!` (the `Vector{Any}`, typed
and converting methods alike), and they never throw except through `convert`. -/
def PSafeSet : Prop := ∀ {α β : Type} (conv : β → R α) (a : Arr α) (i : Int), 1 ≤ i → i ≤ length a →
    (∀ x : α, .ok (m1055 a x i) = m1036 a x i) ∧ (∀ x : α, .ok (m1057 a x i) = m1036 a x i) ∧
    (∀ x : β, m1059 conv a x i = m1031 conv a x i)

theorem pSafeSet : PSafeSet := by
  intro α β conv a i h1 h2
  have hb : ¬ ¬ inBounds a i = true := by rw [inBounds_iff]; simp; omega
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
  · unfold m1036; rw [if_neg hb]; rfl
  · unfold m1036; rw [if_neg hb]; rfl
  · unfold m1059 m1031; cases conv x with
    | error e => rfl
    | ok y => simp only [bind_ok]; unfold m1036; rw [if_neg hb]; rfl

/-- An index tuple `I` is in bounds for an array of size `dims` (manual "Omitted and extra
indices"): each given index lies in `1:d` of its dimension, an index past the last
dimension must be `1`, and every dimension without an index has size `1`. -/
def InCart (dims is : List Int) : Prop :=
  (∀ k (h : k < is.length), 1 ≤ is[k] ∧ is[k] ≤ dims.getD k 1) ∧
  (∀ k, is.length ≤ k → k < dims.length → dims.getD k 1 = 1)

/-- Column-major position of an index tuple (manual "column-major order"), with size `1`
for dimensions past the last: `1 + Σₖ (iₖ - 1)·d₁⋯dₖ₋₁`. -/
def cartPos : List Int → List Int → Int
  | _, [] => 1
  | ds, i :: is => (i - 1) + ds.headD 1 * (cartPos ds.tail is - 1) + 1

/-- Cartesian `getindex`/`setindex!`/`isassigned` on an `Array` with two or more indices,
any number of them (`ndims` of the array arbitrary): indices out of bounds throw
`BoundsError`; in bounds, `A[I...]` is the element at the column-major position of `I`,
`A[I...] = x` writes exactly that slot, and `isassigned(A, I...)` holds exactly when
`A[I...]` returns a value. -/
def PCartesian : Prop := ∀ {α β : Type} (conv : β → R α) (a : Arr α) (i1 i2 : Int) (is : List Int),
    (m231 a (i1 :: i2 :: is) = true ↔ ∃ x, m974 a i1 i2 is = .ok x) ∧
    (¬ InCart a.dims (i1 :: i2 :: is) → m974 a i1 i2 is = .error .bounds ∧
      ∀ x : α, m1047 a x i1 i2 is = .error .bounds) ∧
    (InCart a.dims (i1 :: i2 :: is) →
      m974 a i1 i2 is = getU a (cartPos a.dims (i1 :: i2 :: is)) ∧
      ∀ x : β, (∀ e, conv x = .error e → m1042 conv a x i1 i2 is = .error e) ∧
        (∀ y, conv x = .ok y → m1042 conv a x i1 i2 is =
          .ok (setU a (cartPos a.dims (i1 :: i2 :: is)) (some y))))

/-- `isassigned(a::Array, i)` with one index is linear (docstring of `isassigned`,
base/essentials.jl: false out of bounds or for an undefined reference), and with no
index it tests the only element of an array whose dimensions all have size 1. -/
def PIsassigned : Prop := ∀ {α : Type} (a : Arr α) (i : Int),
    (m231 a [i] = true ↔ 1 ≤ i ∧ i ≤ length a ∧ (a.at i).isSome) ∧
    (m231 a [] = true ↔ InCart a.dims [] ∧ (a.at 1).isSome)

theorem sub2indRec_cartPos : ∀ (is dims : List Int) (l ind : Int),
    sub2indRec dims l ind is = ind + l * (cartPos dims is - 1)
  | [], _, _, _ => by simp [sub2indRec, cartPos]
  | i :: is, [], l, ind => by
    simp only [sub2indRec, cartPos, List.headD_nil, List.tail_nil]
    rw [sub2indRec_cartPos is [] l _]
    rw [show (i - 1) + 1 * (cartPos [] is - 1) + 1 - 1 = (i - 1) + (cartPos [] is - 1) by omega, Int.mul_add,
      Int.mul_comm l (i - 1)]
    omega
  | i :: is, d :: ds, l, ind => by
    simp only [sub2indRec, cartPos, List.headD_cons, List.tail_cons]
    rw [sub2indRec_cartPos is ds (l * d) _]
    generalize cartPos ds is - 1 = X
    have : l * (i - 1 + d * X + 1 - 1) = (i - 1) * l + l * d * X := by
      rw [show i - 1 + d * X + 1 - 1 = (i - 1) + d * X by omega, Int.mul_add, Int.mul_comm l (i - 1),
        Int.mul_assoc]
    omega

theorem getD_tail_one (ds : List Int) (k : Nat) : ds.tail.getD k 1 = ds.getD (k + 1) 1 := by
  cases ds <;> simp

theorem InCart_nil (dims : List Int) : InCart dims [] ↔ ∀ d ∈ dims, d = 1 := by
  unfold InCart
  constructor
  · rintro ⟨_, h⟩ d hd
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hd
    have := h k (Nat.zero_le k) hk
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] at this
  · intro h
    refine ⟨fun k hk => absurd hk (Nat.not_lt_zero k), fun k _ hk => ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact h _ (List.getElem_mem hk)

theorem InCart_cons (dims : List Int) (i : Int) (is : List Int) :
    InCart dims (i :: is) ↔ (1 ≤ i ∧ i ≤ dims.headD 1) ∧ InCart dims.tail is := by
  have h0 : dims.getD 0 1 = dims.headD 1 := by cases dims <;> simp
  unfold InCart
  constructor
  · rintro ⟨h1, h2⟩
    have a0 := h1 0 (by simp)
    rw [List.getElem_cons_zero, h0] at a0
    refine ⟨a0, fun k hk => ?_, fun k hk1 hk2 => ?_⟩
    · have := h1 (k + 1) (by simp; omega)
      rwa [List.getElem_cons_succ, ← getD_tail_one] at this
    · have := h2 (k + 1) (by simp; omega) (by cases dims <;> simp at hk2 ⊢ <;> omega)
      rwa [← getD_tail_one] at this
  · rintro ⟨a0, h1, h2⟩
    refine ⟨fun k hk => ?_, fun k hk1 hk2 => ?_⟩
    · cases k with
      | zero => rw [List.getElem_cons_zero, h0]; exact a0
      | succ k =>
        rw [List.getElem_cons_succ, ← getD_tail_one]
        exact h1 k (by simp at hk; omega)
    · cases k with
      | zero => simp at hk1
      | succ k =>
        rw [← getD_tail_one]
        exact h2 k (by simp at hk1; omega) (by cases dims <;> simp at hk2 ⊢ <;> omega)

theorem checkIdx_iff : ∀ (is dims : List Int), checkIdx dims is = true ↔ InCart dims is
  | [], dims => by
    rw [InCart_nil]; simp [checkIdx]
  | i :: is, dims => by
    rw [InCart_cons, ← checkIdx_iff is dims.tail]
    simp [checkIdx]

theorem cartPos_ones : ∀ (js : List Int), InCart [] js → cartPos [] js = 1
  | [], _ => rfl
  | j :: js, h => by
    rw [InCart_cons] at h
    simp only [cartPos, List.headD_nil, List.tail_nil]
    rw [cartPos_ones js (by simpa using h.2)]
    simp at h; omega

theorem toLinear_cartPos (a : Arr α) (i1 i2 : Int) (is : List Int) (h : InCart a.dims (i1 :: i2 :: is)) :
    toLinear a (i1 :: i2 :: is) = cartPos a.dims (i1 :: i2 :: is) := by
  simp only [toLinear]
  split
  · rename_i hv
    obtain ⟨d, hd⟩ : ∃ d, a.dims = [d] := by
      match hm : a.dims, hv with
      | [d], _ => exact ⟨d, rfl⟩
    rw [hd] at h ⊢
    rw [InCart_cons, InCart_cons] at h
    simp only [List.headD_cons, List.tail_cons, List.headD_nil, List.tail_nil] at h
    simp only [cartPos, List.headD_cons, List.tail_cons, List.headD_nil, List.tail_nil]
    rw [cartPos_ones is h.2.2]
    have : i2 = 1 := by omega
    subst this; omega
  · rw [sub2indRec_cartPos]; omega

theorem pCartesian : PCartesian := by
  intro α β conv a i1 i2 is
  have hs : sub2indRec a.dims 1 1 (i1 :: i2 :: is) = cartPos a.dims (i1 :: i2 :: is) := by
    rw [sub2indRec_cartPos]; omega
  have hci := checkIdx_iff (i1 :: i2 :: is) a.dims
  refine ⟨?_, fun hc => ⟨?_, fun x => ?_⟩, fun hc => ⟨?_, fun x => ⟨fun e he => ?_, fun y hy => ?_⟩⟩⟩
  · unfold m231 m974
    simp only []
    by_cases hc : checkIdx a.dims (i1 :: i2 :: is) = true
    · simp only [hc, Bool.not_true, Bool.false_eq_true, if_false, hs, assignedU, getU,
        toLinear_cartPos a i1 i2 is (hci.mp hc)]
      cases a.at (cartPos a.dims (i1 :: i2 :: is)) <;> simp
    · simp [hc]
  · unfold m974; rw [if_pos (fun h => hc (hci.mp h))]
  · unfold m1047; rw [if_pos (fun h => hc (hci.mp h))]
  · unfold m974; rw [if_neg (fun h => h (hci.mpr hc)), toLinear_cartPos a i1 i2 is hc]
  · unfold m1042; rw [he, bind_error]
  · unfold m1042; rw [hy, bind_ok]; unfold m1047
    rw [if_neg (fun h => h (hci.mpr hc)), toLinear_cartPos a i1 i2 is hc]

theorem pIsassigned : PIsassigned := by
  intro α a i
  refine ⟨?_, ?_⟩
  · unfold m231 assignedU
    have hsub : sub2indRec a.dims 1 1 [i] = i := by rw [sub2indRec_cartPos]; simp [cartPos]; omega
    rw [hsub]
    by_cases hb : inBounds a i = true
    · have := (inBounds_iff a i).mp hb
      simp [hb, this]
    · have : ¬ (1 ≤ i ∧ i ≤ length a) := fun h => hb ((inBounds_iff a i).mpr h)
      simp only [Bool.not_eq_true] at hb
      simp [hb]; omega
  · unfold m231 assignedU
    simp only [sub2indRec]
    rw [← checkIdx_iff]
    by_cases hc : checkIdx a.dims [] = true
    · simp [hc]
    · simp only [Bool.not_eq_true] at hc
      simp [hc]

end JuliaLean.MultidimCov.ArrayV2
