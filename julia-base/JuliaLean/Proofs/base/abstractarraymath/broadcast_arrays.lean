import JuliaLean.base.abstractarraymath

namespace JuliaLean.BroadcastCov.ArrayMath

def BasicArrayMethods : Prop :=
  (∀ x, isrealArray x = x.data.all (fun z => z.2 == i64 0)) ∧
  (∀ x, iszeroArray x = x.data.all (fun z => z == (i64 0, i64 0))) ∧
  (∀ xs, isrealRealArray xs = true) ∧
  (∀ x, (vecArray x).shape = [x.data.length] ∧ (vecArray x).data = x.data) ∧
  (∀ x, vecVector x = x) ∧
  (∀ t s, subTuple t s = t.drop s.length) ∧
  (∀ x, (conjugate x).data = x.data.map (fun z => (z.1, -z.2))) ∧
  (∀ x, identityArray x = x) ∧
  (∀ xs, conjugateNested xs = xs.map conjugate) ∧
  (∀ x, (realArray x).data = x.data.map (fun z => (z.1, i64 0))) ∧
  (∀ x, (imagArray x).data = x.data.map (fun z => (z.2, i64 0))) ∧
  (∀ x, (negateArray x).data = x.data.map (fun z => (-z.1, -z.2)))

theorem basicArrayMethods : BasicArrayMethods := by
  constructor
  · intro x; rfl
  constructor
  · intro x; rfl
  constructor
  · intro xs; rfl
  constructor
  · intro x; exact ⟨rfl, rfl⟩
  constructor
  · intro x; rfl
  constructor
  · intro t s
    induction s generalizing t with
    | nil => simp [subTuple]
    | cons _ s ih =>
      cases t <;> simp [subTuple, ih]
  constructor
  · intro x; rfl
  constructor
  · intro x; rfl
  constructor
  · intro xs; rfl
  constructor
  · intro x; rfl
  constructor
  · intro x; rfl
  · intro x; rfl

def DimensionMethods : Prop :=
  (∀ x dims,
    dropDims x dims =
      if dims.all (fun d => decide (1 ≤ d ∧ d ≤ x.shape.length)) &&
          dims.all (fun d => x.shape.getD (d - 1) 0 == 1) && noDuplicates dims then
        .ok { x with shape := eraseDims x.shape dims 1 }
      else .error .argumentError) ∧
  (∀ x dim, dropDim x dim = dropDims x [dim]) ∧
  (∀ x dims,
    insertDims x dims =
      let total := x.shape.length + dims.length
      if dims.all (fun d => decide (1 ≤ d ∧ d ≤ total)) && noDuplicates dims then
        .ok { x with shape := buildInserted x.shape dims total 0 }
      else .error .argumentError) ∧
  (∀ x dim, insertDim x dim = insertDims x [dim])

theorem dimensionMethods : DimensionMethods := by
  exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

def WrapperMethods : Prop :=
  (∀ shape data shift,
    circshiftReal shape data shift = JuliaLean.Multidim.circshift shape data [shift]) ∧
  (∀ shape data shifts,
    circshiftDims shape data shifts = JuliaLean.Multidim.circshift shape data shifts) ∧
  (∀ xs, toTuple xs = xs) ∧
  (∀ x, toTupleInteger x = [x]) ∧
  (∀ shape inner outer,
    repeatInnerOuter shape inner outer = JuliaLean.Multidim.repeatSize shape inner outer)

theorem wrapperMethods : WrapperMethods := by
  exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ _ => rfl⟩

end JuliaLean.BroadcastCov.ArrayMath
