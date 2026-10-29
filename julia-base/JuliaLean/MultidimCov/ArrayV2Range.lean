import JuliaLean.MultidimCov.ArrayV2LiteralsProps

/-!
Indexing an `Array` with ranges, a colon or an index vector (master
`base/array.jl:981-1096`).

A unit range `lo:hi` is given by its first element and its length `n ≥ 0` (a
`UnitRange` stores `hi = lo + n - 1`); an index vector or a step range by its
elements in order. The source `X` of an indexed assignment is given by its values in
order (`unalias` makes the loop read the values `X` had before the call).
-/

namespace JuliaLean.MultidimCov.ArrayV2

/-- `checkbounds(Bool, A, lo:(lo+n-1))` for linear indexing: an empty range, or both ends
in `1:length(A)`. -/
def rangeIn (A : Arr α) (lo n : Int) : Prop := n = 0 ∨ (1 ≤ lo ∧ lo + n - 1 ≤ length A)

instance (A : Arr α) (lo n : Int) : Decidable (rangeIn A lo n) := by unfold rangeIn; infer_instance

/-- base/array.jl:981 `getindex(A::Array, I::AbstractUnitRange{<:Integer})`:
`checkbounds(A, I)`, `X = similar(A, axes(I))`, then `copyto!(X, 1, A, first(I), length(I))`
when nonempty. -/
def m981 (A : Arr α) (lo n : Int) : R (Arr α) :=
  if ¬ rangeIn A lo n then .error .bounds else do
  let X ← newArray [n]
  if n > 0 then m288 X 1 A lo n else pure X

/-- The elements of the `Bool` unit range `f:l`. -/
def boolRange (f l : Bool) : List Bool :=
  if f = l then [f] else if f = false ∧ l = true then [false, true] else []

/-- `getindex(A, LogicalIndex(mask))`: `BoundsError` unless `length(mask) == length(A)`, then
`A[i]` for each `i` with `mask[i]`, in order (an `#undef` element throws `UndefRefError`). -/
def logicalGet (A : Arr α) (mask : List Bool) : R (Arr α) :=
  if (mask.length : Int) ≠ length A then .error .bounds else do
  let idx := ((List.range mask.length).filter fun k => mask.getD k false).map fun (k : Nat) => ((k : Int) + 1)
  let vals ← idx.mapM (getL A)
  let X ← newArray [(vals.length : Int)]
  pure (safeWrites X 1 vals)

/-- base/array.jl:993 `getindex(a::Array, r::AbstractUnitRange{Bool}) = getindex(a, to_index(r))`:
logical indexing with the range's elements as the mask. -/
def m993 (A : Arr α) (f l : Bool) : R (Arr α) := logicalGet A (boolRange f l)

/-- base/array.jl:995 `getindex(A::Array, c::Colon)`: `X = similar(A, length(A))`, then
`unsafe_copyto!(X, 1, A, 1, lI)` when nonempty. -/
def m995 (A : Arr α) : R (Arr α) := do
  let lI := length A
  let X ← newArray [lI]
  if lI > 0 then m276 X 1 A 1 lI else pure X

/-- base/array.jl:1005 `getindex(A::Array{S}, I::AbstractRange{Int}) = S[A[i] for i in I]`: a
`Vector{S}` of `length(I)` filled with the checked reads `A[i]` in order. -/
def m1005 (A : Arr α) (is : List Int) : R (Arr α) := do
  let X ← newArray [(is.length : Int)]
  let vals ← is.mapM (getL A)
  pure (safeWrites X 1 vals)

/-- `setindex_shape_check(X, lI)`: `DimensionMismatch` unless `length(X) == lI`. -/
def shapeCheck (lenX lI : Int) : R Unit := if lenX = lI then .ok () else .error .dimensionMismatch

/-- `@inbounds A[i] = x` for each pair in order: `convert`, then the unchecked write. -/
def writeAt (conv : β → R α) : Arr α → List (Int × β) → R (Arr α)
  | a, [] => .ok a
  | a, (i, x) :: rest => do
    let y ← conv x
    writeAt conv (setU a i (some y)) rest

/-- base/array.jl:1063 `setindex!(A::Array, X::AbstractArray, I::AbstractVector{Int})`:
`setindex_shape_check(X, length(I))`, `checkbounds(A, I)`, then `A[I′[k]] = X′[j]` in order. -/
def m1063 (conv : β → R α) (A : Arr α) (xs : List β) (I : List Int) : R (Arr α) := do
  shapeCheck xs.length I.length
  if ¬ I.all (fun i => 1 ≤ i ∧ i ≤ length A) then .error .bounds else
  writeAt conv A (I.zip xs)

/-- base/array.jl:1078 `setindex!(A::Array{T}, X::Array{T}, I::AbstractUnitRange{Int})`:
`checkbounds(A, I)`, then `setindex_shape_check(X, length(I))`, then
`unsafe_copyto!(A, first(I), X, 1, lI)` when nonempty. -/
def m1078 (A X : Arr α) (lo n : Int) : R (Arr α) :=
  if ¬ rangeIn A lo n then .error .bounds else do
  shapeCheck (length X) n
  if n > 0 then m276 A lo X 1 n else pure A

/-- base/array.jl:1088 `setindex!(A::Array{T}, X::Array{T}, c::Colon)`:
`setindex_shape_check(X, length(A))`, then `unsafe_copyto!(A, 1, X, 1, lI)` when nonempty. -/
def m1088 (A X : Arr α) : R (Arr α) := do
  shapeCheck (length X) (length A)
  if length A > 0 then m276 A 1 X 1 (length A) else pure A

/-! ### Contracts -/

/-- `A[lo:hi]` (manual "Indexing": the elements of `A` at the indices of the range, as a
vector of `length(I)`): the slots `lo..hi` of `A` in order (an `#undef` slot stays unset),
an empty range even out of bounds gives an empty vector, any other range reaching outside
`1:length(A)` throws `BoundsError`. -/
def P981 : Prop := ∀ {α : Type} (A : Arr α) (lo n : Int), Valid A → length A ≤ 2 ^ 58 → 0 ≤ n →
    (rangeIn A lo n → ∃ X, m981 A lo n = .ok X ∧ IsVec X n ∧
      contents X = ((contents A).drop (lo - 1).toNat).take n.toNat) ∧
    (¬ rangeIn A lo n → m981 A lo n = .error .bounds)

/-- `A[:]` (manual "Indexing": every element of `A`, in linear order, as a vector): a new
vector of `length(A)` with `A`'s slots. -/
def P995 : Prop := ∀ {α : Type} (A : Arr α), Valid A → length A ≤ 2 ^ 58 →
    ∃ X, m995 A = .ok X ∧ IsVec X (length A) ∧ contents X = contents A

theorem range_slice_eq {A X : Arr α} {lo n : Int} (hn : 0 ≤ n) (hX : length X = n) (hlo : 1 ≤ lo)
    (hhi : lo + n - 1 ≤ length A) (hat : ∀ k, 1 ≤ k → k ≤ n → X.at k = A.at (k - 1 + lo)) :
    contents X = ((contents A).drop (lo - 1).toNat).take n.toNat := by
  apply contents_ext (by simp [hX]; omega)
  intro k hk
  simp only [List.length_take, List.length_drop, contents_length] at hk
  rw [hat _ (by omega) (by omega)]
  simp only [List.getElem_take, List.getElem_drop]
  rw [getElem_contents]
  congr 1; omega

theorem p981 : P981 := by
  intro α A lo n hA hl hn
  refine ⟨fun hin => ?_, fun hout => by unfold m981; rw [if_pos hout]⟩
  have hnl : n ≤ length A ∨ n = 0 := by unfold rangeIn at hin; omega
  obtain ⟨X, eX, hX⟩ := newArray_ok (α := α) (dims := [n]) (by simpa using hn) (by simp [typemaxInt]; omega)
  unfold m981; rw [if_neg (fun h => h hin), eX, bind_ok]
  by_cases h0 : n = 0
  · subst h0
    refine ⟨X, by simp, hX.1, ?_⟩
    rw [hX.2.2]; simp
  · rw [if_pos (by omega)]
    rcases hin with hin | ⟨h1, h2⟩
    · exact absurd hin h0
    have hXl : length X = n := by simp [length, hX.1]
    unfold m288
    obtain ⟨Y, eY, hdY, _, hpY⟩ := m299_vec (c := n) hX.2.1 hA (by omega) (by omega) (doffs := 1) (soffs := lo) hn
      (Int.le_refl 1) (by omega) h1 h2
    refine ⟨Y, eY, by unfold IsVec; rw [hdY, hX.1], ?_⟩
    have hYl : length Y = n := by simp [length, hdY, hX.1]
    exact range_slice_eq hn hYl h1 h2 (fun k k1 k2 => by
      rw [hpY k k1 (by omega), if_pos ⟨k1, by omega⟩])

theorem p995 : P995 := by
  intro α A hA hl
  have h0 := hA.2.1
  obtain ⟨X, eX, hX⟩ := newArray_ok (α := α) (dims := [length A]) (by simpa using h0) (by simp [typemaxInt]; omega)
  have hXl : length X = length A := by simp [length, hX.1]
  unfold m995
  simp only []
  rw [eX, bind_ok]
  by_cases hz : length A = 0
  · rw [if_neg (by omega)]
    refine ⟨X, rfl, hX.1, ?_⟩
    have hc : contents A = [] := List.eq_nil_of_length_eq_zero (by simp [contents_length, hz])
    rw [hX.2.2, hc]; simp [hz]
  · rw [if_pos (by omega)]
    obtain ⟨Y, eY, hdY, _, _, hpY⟩ := p276 X A 1 1 (length A) hX.2.1 hA h0 (Int.le_refl 1) (by omega)
      (Int.le_refl 1) (by omega) (by omega) (by omega)
    refine ⟨Y, eY, by unfold IsVec; rw [hdY, hX.1], ?_⟩
    have hYl : length Y = length A := by simp [length, hdY, hX.1]
    apply contents_ext (by simp [hYl])
    intro k hk
    simp only [contents_length] at hk
    rw [hpY _ (by omega) (by omega), if_pos ⟨by omega, by omega⟩, getElem_contents]
    congr 1; omega

theorem mapM_getL_ok {A : Arr α} : ∀ (is : List Int), (∀ i ∈ is, inBounds A i = true ∧ (A.at i).isSome) →
    ∃ vs, is.mapM (getL A) = .ok vs ∧ vs.map some = is.map A.at
  | [], _ => ⟨[], rfl, rfl⟩
  | i :: is, h => by
    obtain ⟨h1, h2⟩ := h i (by simp)
    obtain ⟨vs, e, hv⟩ := mapM_getL_ok is (fun j hj => h j (by simp [hj]))
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h2
    refine ⟨x :: vs, ?_, by simp [hv, hx]⟩
    simp only [List.mapM_cons, e, bind_ok, pure_ok]
    unfold getL; rw [if_pos h1]; simp [hx]

theorem mapM_getL_bounds {A : Arr α} : ∀ (is : List Int), (∃ i ∈ is, inBounds A i = false) →
    (∀ i ∈ is, inBounds A i = true → (A.at i).isSome) → is.mapM (getL A) = .error .bounds
  | [], h, _ => by simp at h
  | i :: is, ⟨j, hj, hjb⟩, h => by
    simp only [List.mapM_cons]
    by_cases hi : inBounds A i = true
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (h i (by simp) hi)
      have hg : getL A i = .ok x := by unfold getL; rw [if_pos hi]; simp [hx]
      simp only [List.mem_cons] at hj
      rcases hj with rfl | hj
      · rw [hi] at hjb; cases hjb
      rw [hg, bind_ok, mapM_getL_bounds is ⟨j, hj, hjb⟩ (fun k hk => h k (by simp [hk])), bind_error]
    · have hg : getL A i = .error .bounds := by unfold getL; rw [if_neg hi]
      rw [hg, bind_error]

/-- `A[r]` for a non-unit `Int` range (docstring of `getindex`; manual "Indexing"): the
elements `A[i]` for `i` in `r`, in order, as a vector of `length(r)`; an index outside
`1:length(A)` throws `BoundsError` (when every in-bounds element is assigned). -/
def P1005 : Prop := ∀ {α : Type} (A : Arr α) (is : List Int), is.length ≤ 2 ^ 58 →
    ((∀ i ∈ is, inBounds A i = true ∧ (A.at i).isSome) →
      ∃ X, m1005 A is = .ok X ∧ IsVec X is.length ∧ contents X = is.map A.at) ∧
    ((∃ i ∈ is, inBounds A i = false) → (∀ i ∈ is, inBounds A i = true → (A.at i).isSome) →
      m1005 A is = .error .bounds)

theorem p1005 : P1005 := by
  intro α A is hl
  obtain ⟨X, eX, hX⟩ := newArray_ok (α := α) (dims := [(is.length : Int)]) (by simp) (by simp [typemaxInt]; omega)
  refine ⟨fun h => ?_, fun h1 h2 => ?_⟩
  · obtain ⟨vs, e, hv⟩ := mapM_getL_ok is h
    have hvl : vs.length = is.length := by simpa using congrArg List.length hv
    refine ⟨safeWrites X 1 vs, by simp [m1005, eX, e], by unfold IsVec; rw [(safeWrites_spec vs X 1).1, hX.1], ?_⟩
    rw [contents_safeWrites_full (by simp [length, hX.1, hvl]), hv]
  · simp [m1005, eX, mapM_getL_bounds is h1 h2]

/-- `writeAt` leaves every slot that no pair targets, and gives each targeted slot the
value of its last pair. -/
def lastWrite (old : Option α) (k : Int) (ps : List (Int × α)) : Option α :=
  match (ps.reverse.find? fun p => p.1 = k) with
  | some p => some p.2
  | none => old

theorem writeAt_spec (conv : β → R α) : ∀ (ps : List (Int × β)) (a : Arr α) (ys : List α),
    convList conv (ps.map Prod.snd) = .ok ys →
    ∃ a', writeAt conv a ps = .ok a' ∧ a'.dims = a.dims ∧ a'.off = a.off ∧ a'.mem.len = a.mem.len ∧
      ∀ k, a'.at k = lastWrite (a.at k) k ((ps.map Prod.fst).zip ys)
  | [], a, ys, h => by
    simp [convList] at h; subst h
    exact ⟨a, rfl, rfl, rfl, rfl, fun k => by simp [lastWrite]⟩
  | (i, x) :: ps, a, ys, h => by
    simp only [List.map_cons, convList] at h
    cases hx : conv x with
    | error e => rw [hx, bind_error] at h; cases h
    | ok y =>
      rw [hx, bind_ok] at h
      cases hps : convList conv (ps.map Prod.snd) with
      | error e => rw [hps, bind_error] at h; cases h
      | ok zs =>
        rw [hps, bind_ok, pure_ok, Except.ok.injEq] at h
        subst h
        obtain ⟨a', e, h1, h2, h3, h4⟩ := writeAt_spec conv ps (setU a i (some y)) zs hps
        refine ⟨a', by simp [writeAt, hx, e], by rw [h1]; rfl, by rw [h2]; rfl, by rw [h3]; rfl, fun k => ?_⟩
        rw [h4 k, setU_at]
        simp only [lastWrite, List.map_cons, List.zip_cons_cons, List.reverse_cons, List.find?_append]
        cases hf : ((ps.map Prod.fst).zip zs).reverse.find? (fun p => p.1 = k) with
        | some p => simp
        | none =>
          simp only [Option.none_or, List.find?_singleton]
          by_cases hk : k = i
          · subst hk; simp
          · simp [hk, Ne.symm hk]

/-- `A[I] = X` for an index vector `I` (docstring of `setindex!`; the indexed assignment
`A[I] = X` of the manual): `DimensionMismatch` unless `length(X) == length(I)`, then
`BoundsError` for an index outside `1:length(A)`; otherwise each `A[I[k]]` receives
`X[k]` converted, in order, so a repeated index keeps its last value, and every other
slot keeps its value. -/
def P1063 : Prop := ∀ {α β : Type} (conv : β → R α) (A : Arr α) (xs : List β) (I : List Int),
    (xs.length ≠ I.length → m1063 conv A xs I = .error .dimensionMismatch) ∧
    (xs.length = I.length → (∃ i ∈ I, i < 1 ∨ length A < i) → m1063 conv A xs I = .error .bounds) ∧
    (xs.length = I.length → (∀ i ∈ I, 1 ≤ i ∧ i ≤ length A) → ∀ ys, convList conv xs = .ok ys →
      ∃ A', m1063 conv A xs I = .ok A' ∧ A'.dims = A.dims ∧ ∀ k, A'.at k = lastWrite (A.at k) k (I.zip ys))

theorem p1063 : P1063 := by
  intro α β conv A xs I
  refine ⟨fun h => ?_, fun h hb => ?_, fun h hin ys hys => ?_⟩
  · have h' : (xs.length : Int) ≠ I.length := by omega
    simp [m1063, shapeCheck, h']
  · have : ¬ (I.all fun i => 1 ≤ i ∧ i ≤ length A) = true := by
      obtain ⟨i, hi, hb⟩ := hb
      rw [List.all_eq_true]; intro hall; have := hall i hi; simp at this; omega
    have h' : (xs.length : Int) = I.length := by omega
    simp only [m1063, shapeCheck, h', if_true, bind_ok]; rw [if_pos this]
  · have hall : (I.all fun i => 1 ≤ i ∧ i ≤ length A) = true := by
      rw [List.all_eq_true]; intro i hi; simpa using hin i hi
    have hz : (I.zip xs).map Prod.snd = xs := by rw [List.map_snd_zip]; omega
    have hf : (I.zip xs).map Prod.fst = I := by rw [List.map_fst_zip]; omega
    obtain ⟨A', e, h1, -, -, h4⟩ := writeAt_spec conv (I.zip xs) A ys (by rw [hz]; exact hys)
    have h' : (xs.length : Int) = I.length := by omega
    refine ⟨A', by simp only [m1063, shapeCheck, h', if_true, bind_ok, hall, not_true_eq_false, if_false]; exact e,
      h1, fun k => by rw [h4 k, hf]⟩

/-- `A[lo:hi] = X` for `X::Array{T}` of `A`'s element type (manual "Indexed assignment"):
`BoundsError` for a nonempty range outside `1:length(A)` (checked first), then
`DimensionMismatch` unless `length(X) == length(lo:hi)`; otherwise slot `lo+k-1`
receives `X`'s slot `k` (also when `X === A`) and every other slot keeps its value.
`A[:] = X` is the same for the range `1:length(A)`. -/
def P1078 : Prop := ∀ {α : Type} (A X : Arr α) (lo n : Int), Valid A → Valid X → length A ≤ 2 ^ 58 →
    length X ≤ 2 ^ 58 → 0 ≤ n →
    (¬ rangeIn A lo n → m1078 A X lo n = .error .bounds) ∧
    (rangeIn A lo n → length X ≠ n → m1078 A X lo n = .error .dimensionMismatch) ∧
    (rangeIn A lo n → length X = n → ∃ A', m1078 A X lo n = .ok A' ∧ A'.dims = A.dims ∧
      ∀ k, 1 ≤ k → k ≤ length A → A'.at k = if lo ≤ k ∧ k < lo + n then X.at (k - lo + 1) else A.at k) ∧
    (length X ≠ length A → m1088 A X = .error .dimensionMismatch) ∧
    (length X = length A → ∃ A', m1088 A X = .ok A' ∧ A'.dims = A.dims ∧
      ∀ k, 1 ≤ k → k ≤ length A → A'.at k = X.at k)

theorem p1078 : P1078 := by
  intro α A X lo n hA hX hlA hlX hn
  have hA0 := hA.2.1
  refine ⟨fun h => by unfold m1078; rw [if_pos h], fun h hne => ?_, fun h heq => ?_, fun hne => ?_, fun heq => ?_⟩
  · unfold m1078; rw [if_neg (fun h' => h' h)]; simp [shapeCheck, hne]
  · unfold m1078; rw [if_neg (fun h' => h' h)]; simp only [shapeCheck, heq, if_true, bind_ok]
    by_cases h0 : n = 0
    · subst h0; rw [if_neg (by omega)]
      exact ⟨A, rfl, rfl, fun k _ _ => by rw [if_neg (by omega)]⟩
    · rw [if_pos (by omega)]
      rcases h with h | ⟨h1, h2⟩
      · exact absurd h h0
      obtain ⟨A', e, hd, _, _, hp⟩ := p276 A X lo 1 n hA hX hn h1 h2 (Int.le_refl 1) (by omega) (by omega) (by omega)
      exact ⟨A', e, hd, hp⟩
  · unfold m1088; simp [shapeCheck, hne]
  · unfold m1088; simp only [shapeCheck, heq, if_true, bind_ok]
    by_cases h0 : length A = 0
    · rw [if_neg (by omega)]
      exact ⟨A, rfl, rfl, fun k k1 k2 => by omega⟩
    · rw [if_pos (by omega)]
      obtain ⟨A', e, hd, _, _, hp⟩ := p276 A X 1 1 (length A) hA hX hA.2.1 (Int.le_refl 1) (by omega)
        (Int.le_refl 1) (by omega) (by omega) (by omega)
      refine ⟨A', e, hd, fun k k1 k2 => ?_⟩
      rw [hp k k1 k2, if_pos ⟨k1, by omega⟩]; congr 1; omega

end JuliaLean.MultidimCov.ArrayV2
