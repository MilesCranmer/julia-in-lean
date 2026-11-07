import JuliaLean.base.abstractset

namespace JuliaLean.BitSetsCov.Coll

open Bugs

/-- An input with a wider element type is checked even when the destination
already contains its maximum number of values. -/
def AbstractUnionConversionError : Prop :=
  ∀ convert m s x y value e,
    convert x = .ok value → convert y = .error e →
    abstractUnionConvert convert m false s [x, y] = (insert s value, some e)

theorem abstractUnionConversionError : AbstractUnionConversionError := by
  intro convert m s x y value e hx hy
  simp [abstractUnionConvert, hx, hy]

/-! ## Closed row properties -/

def AbstractBasicSpec : Prop :=
  (∀ d t, abstractEltype d t = if d then t else 0) ∧
  (∀ s n, abstractSizehint s n = s) ∧
  (∀ same dst src, abstractCopyBang same dst src = if same then dst else unionOne [] src)

def AbstractUnionSpec : Prop :=
  (∀ s sets, abstractUnion s sets = unionMany [] (s :: sets)) ∧
  (∀ s, abstractUnionUnary s = s) ∧
  (∀ s sets, abstractUnionBangMany s sets = unionMany s sets) ∧
  (∀ s itr m, abstractUnionBangOne s itr m false = unionOne s itr) ∧
  maxValuesGeneric = 9223372036854775807 ∧
  (∀ b, maxValuesSmall b = 2 ^ (8 * b)) ∧
  (∀ a b, maxValuesUnion a b = if maxValuesGeneric - a < b then maxValuesGeneric else a + b) ∧
  maxValuesBool = 2 ∧ maxValuesNothing = 1

def AbstractIntersectSpec : Prop :=
  (∀ s itr itrs, abstractIntersect s itr itrs =
    let candidates := itr :: itrs
    let first := candidates.foldl (fun best x => if x.length < best.length then x else best) itr
    intersectMany (intersectOne s first) (candidates.erase first)) ∧
  (∀ s, abstractIntersectUnary s = abstractUnionUnary s) ∧
  (∀ s itr, abstractIntersectTwo s itr = if s.length < itr.length then intersectOne s itr else intersectOne itr s) ∧
  (∀ s xs, abstractIntersectBangMany s xs = intersectMany s xs) ∧
  (∀ s t, abstractIntersectBangSet s t = intersectOne s t) ∧
  (∀ s t, abstractIntersectBangItr s t = intersectOne s (ofList t))

def AbstractSetdiffSpec : Prop :=
  (∀ s xs, abstractSetdiff s xs = setdiffMany s xs) ∧
  (∀ s, abstractSetdiffUnary s = abstractUnionUnary s) ∧
  (∀ s xs, abstractSetdiffBangMany s xs = setdiffMany s xs) ∧
  (∀ s x, abstractSetdiffBangItr s x = setdiffOne s x)

def AbstractSymdiffSpec : Prop :=
  (∀ s xs, abstractSymdiff s xs = symdiffMany [] (s :: xs)) ∧
  (∀ s, abstractSymdiffUnary s = symdiffOne s []) ∧
  (∀ s xs, abstractSymdiffBangMany s xs = symdiffMany s xs) ∧
  (∀ s x, abstractSymdiffBangItr s x = symdiffOne s (ofList x)) ∧
  (∀ s x, abstractSymdiffBangSet s x = symdiffOne s x)

def AbstractCompareSpec : Prop :=
  (∀ setA fastB a b, abstractIssubset setA fastB a b =
    if !fastB && b.length > 70 then subset a (ofList b)
    else if setA && a.length > b.length then false else subset a b) ∧
  (∀ t, hasfastinType t = t) ∧ (∀ t, hasfastinValue t = t) ∧
  (∀ a b, superset a b = subset b a) ∧
  (∀ a y, subsetFix a y = subset y a) ∧ (∀ a y, supersetFix a y = superset y a) ∧
  (∀ a b, properSuperset a b = properSubset b a) ∧
  (∀ a b, properSubsetConverted a b = properSubset (ofList a) (ofList b)) ∧
  (∀ a y, properSupersetFix a y = properSuperset y a) ∧
  (∀ a y, properSubsetFix a y = properSubset y a) ∧
  (∀ a b, notSubset a b = !subset a b) ∧ (∀ a b, notSuperset a b = notSubset b a) ∧
  (∀ a y, notSupersetFix a y = notSuperset y a) ∧ (∀ a y, notSubsetFix a y = notSubset y a)

def AbstractSetequalSpec : Prop :=
  (∀ a b, abstractSetequalSet a b = setequal a b) ∧
  (∀ a b, abstractSetequalLeft a b = abstractSetequalSet a (ofList b)) ∧
  (∀ a b, abstractSetequalRight a b = if a.length < (ofList b).length then false else abstractSetequalSet (ofList a) b) ∧
  (∀ a b, abstractSetequalGeneric a b = abstractSetequalSet (ofList a) (ofList b)) ∧
  (∀ a y, abstractSetequalFix a y = abstractSetequalGeneric y a)

def AbstractDisjointFilterSpec : Prop :=
  (∀ a b, abstractIsdisjoint a b =
    if b.length < a.length then disjointEq (fun x y => decide (x = y)) b a
    else if b.length < 70 then disjointEq (fun x y => decide (x = y)) a b
    else disjointEq (fun x y => decide (x = y)) a (ofList b)) ∧
  (∀ a y, abstractIsdisjointFix a y = abstractIsdisjoint y a) ∧
  (∀ a b, rangeDisjoint a b =
    if a.len = 0 || b.len = 0 then .value true else
      let av := rangeValues a; let bv := rangeValues b
      overlappingRangeIsdisjoint (av.foldl min a.first) a.step (bv.foldl min b.first) b.step) ∧
  (∀ a b, overlappingRangeGeneric a b =
    disjointEq (fun x y => decide (x = y)) ((rangeValues a).map Int.natAbs) ((rangeValues b).map Int.natAbs)) ∧
  (∀ a b, abstractLt a b = properSubset a b) ∧ (∀ a b, abstractLe a b = subset a b) ∧
  (∀ p s, abstractFilter p s = mapfilter p insert s []) ∧
  (∀ p s, abstractUnsafeFilter p s = mapfilter (fun x => !p x) erase s s) ∧
  (∀ p f itr res, mapfilter p f itr res = itr.foldl (fun out x => if p x then f out x else out) res)

theorem abstractBasicSpec : AbstractBasicSpec := by simp [AbstractBasicSpec, abstractEltype, abstractSizehint, abstractCopyBang]
theorem abstractUnionSpec : AbstractUnionSpec := by
  have h : ∀ s itr m, abstractUnionBangOne s itr m false = unionOne s itr := by
    intro s itr
    induction itr generalizing s with
    | nil => simp [abstractUnionBangOne, unionOne]
    | cons x xs ih => simp [abstractUnionBangOne, unionOne, ih]
  simp [AbstractUnionSpec, abstractUnion, abstractUnionUnary, abstractUnionBangMany,
    h, maxValuesGeneric, maxValuesSmall, maxValuesUnion, maxValuesBool, maxValuesNothing]
theorem abstractIntersectSpec : AbstractIntersectSpec := by simp [AbstractIntersectSpec, abstractIntersect, abstractIntersectUnary, abstractIntersectTwo, abstractIntersectBangMany, abstractIntersectBangSet, abstractIntersectBangItr]
theorem abstractSetdiffSpec : AbstractSetdiffSpec := by simp [AbstractSetdiffSpec, abstractSetdiff, abstractSetdiffUnary, abstractSetdiffBangMany, abstractSetdiffBangItr]
theorem abstractSymdiffSpec : AbstractSymdiffSpec := by simp [AbstractSymdiffSpec, abstractSymdiff, abstractSymdiffUnary, abstractSymdiffBangMany, abstractSymdiffBangItr, abstractSymdiffBangSet]
theorem abstractCompareSpec : AbstractCompareSpec := by simp [AbstractCompareSpec, abstractIssubset, hasfastinType, hasfastinValue, superset, subsetFix, supersetFix, properSuperset, properSubsetConverted, properSupersetFix, properSubsetFix, notSubset, notSuperset, notSupersetFix, notSubsetFix]
theorem abstractSetequalSpec : AbstractSetequalSpec := by simp [AbstractSetequalSpec, abstractSetequalSet, abstractSetequalLeft, abstractSetequalRight, abstractSetequalGeneric, abstractSetequalFix]
theorem abstractDisjointFilterSpec : AbstractDisjointFilterSpec := by simp [AbstractDisjointFilterSpec, abstractIsdisjoint, abstractIsdisjointFix, rangeDisjoint, overlappingRangeGeneric, abstractLt, abstractLe, abstractFilter, abstractUnsafeFilter, mapfilter]
end JuliaLean.BitSetsCov.Coll
