import JuliaLean.base.abstractarray

namespace JuliaLean.AbstractArraySpecs.CatTyped

/-- Empty arrays still contribute their declared element type to promotion. -/
theorem empty_array_eltype {U : Universe} (t : U.Ty) (a : Arr (U.Val t))
    (_ : a.data = []) : eltype (Item.array t a) = t := rfl

/-- An invalid dimension is rejected before allocation or any store. -/
theorem catT_invalid_dims {U : Universe} (ops : Ops U) (t : U.Ty)
    (dims : List Int) (xs : List (Item U))
    (h : dims2cat dims = .error .argumentError) :
    catT ops t dims xs = .error .argumentError := by
  simp [catT, h, bind, Except.bind]

/-- An allocation error is returned before zero initialization or copying. -/
theorem catT_allocation_error {U : Universe} (ops : Ops U) (t : U.Ty)
    (dims : List Int) (x : Item U) (xs : List (Item U)) (ds : List Bool)
    (s : List I64) (e : Err) (hd : dims2cat dims = .ok ds)
    (hs : shape ds (x :: xs) = .ok s)
    (ha : ops.similar t x s = .error e) :
    catT ops t dims (x :: xs) = .error e := by
  simp [catT, hd, hs, ha, bind, Except.bind]

/-- On an in-bounds scalar view, a conversion failure is observable even when
the view contains no cells. -/
theorem dense_scalar_conversion_error {U : Universe}
    (convert : (s t : U.Ty) → U.Val s → R (U.Val t))
    (s t : U.Ty) (a : CatOut (U.Val t)) (inds : List (I64 × I64))
    (x : U.Val s) (e : Err) (hb : rangesInBounds a inds = true)
    (hc : convert s t x = .error e) :
    denseCopy convert a inds (.scalar s x) = .error e := by
  simp [denseCopy, fillRanges, hb, hc, bind, Except.bind]

end JuliaLean.AbstractArraySpecs.CatTyped
