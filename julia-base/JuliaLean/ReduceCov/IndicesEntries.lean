import JuliaLean.ReduceCov.IndicesProofs
import JuliaLean.ReduceCov.Traits
import JuliaLean.Registry.Types

/-! Row-level properties for `base/indices.jl` on master `bbfa0ce4150`. -/

namespace JuliaLean.ReduceCov.IndicesEntries

open JuliaLean.Registry
open JuliaLean.ReduceCov
open JuliaLean.ReduceCov.Indices

def IndexStyleRows : Prop :=
  (∀ a, indexStyle1 a = indexStyleTy a) ∧
  indexStyleBottom = .linear ∧
  indexStyleBottomSlurp = .error (.methodError "IndexStyle") ∧
  indexStyleAbstractArray = .cartesian ∧
  indexStyleArray = .linear ∧
  indexStyleRange = .linear ∧
  (∀ a b, indexStyleN a [b] = indexStyleCombine (indexStyle1 a) (indexStyle1 b)) ∧
  (∀ a b rest, indexStyleN a (b :: rest) = indexStyleCombine (indexStyle1 a) (indexStyleN b rest)) ∧
  indexStyleCombine .linear .linear = .linear ∧
  (∀ a b, (a ≠ .linear ∨ b ≠ .linear) → indexStyleCombine a b = .cartesian) ∧
  indexStyleLinearIndices = .linear

theorem indexStyleRows_proven : IndexStyleRows := by
  refine ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl, rfl, ?_, rfl⟩
  intro a b h
  cases a <;> cases b <;> simp_all [indexStyleCombine]

def PromoteShapeRows : Prop :=
  promoteShape00 = .ok [] ∧
  (∀ a b, promoteShape11 a b = if a ≠ b then
    .error (promoteShapeMismatch (.dims [a]) (some (.dims [b])) none) else .ok [a]) ∧
  (∀ a1 a2 b1, promoteShape21 a1 a2 b1 = if a1 ≠ b1 ∨ a2 ≠ 1 then
    .error (promoteShapeMismatch (.dims [a1, a2]) (some (.dims [b1])) none) else .ok [a1, a2]) ∧
  (∀ a1 b1 b2, promoteShape12 a1 b1 b2 = promoteShape21 b1 b2 a1) ∧
  (∀ a1 a2 b1 b2, promoteShape22 a1 a2 b1 b2 = if a1 ≠ b1 ∨ a2 ≠ b2 then
    .error (promoteShapeMismatch (.dims [a1, a2]) (some (.dims [b1, b2])) none) else .ok [a1, a2]) ∧
  (∀ a b, promoteShapeDims a b = if a.length < b.length then promoteShapeDimsGe b a else promoteShapeDimsGe a b) ∧
  (∀ ax bx, promoteShapeArrays ax bx = promoteShapeAxes ax bx) ∧
  (∀ a b, promoteShapeAxes a b = if a.length < b.length then promoteShapeAxesGe b a else promoteShapeAxesGe a b)

theorem promoteShapeRows_proven : PromoteShapeRows := by
  simp [PromoteShapeRows, promoteShape00, promoteShape11, promoteShape21, promoteShape12,
    promoteShape22, promoteShapeDims, promoteShapeArrays, promoteShapeAxes]

def SetindexRows : Prop :=
  (∀ sx I, setindexMismatch sx I = match I with
    | [i] => .dimensionMismatch s!"tried to assign {sx.foldl (· * ·) 1} elements to {i} destinations"
    | _ => .dimensionMismatch s!"tried to assign {dims2string sx} array to {dims2string I} destination") ∧
  (∀ sx i, setindexShapeCheck1 sx i = if sx.foldl (· * ·) 1 = i then .ok true
    else .error (setindexMismatch sx [i])) ∧
  shapesMatch00 = true ∧
  (∀ a, shapesMatchA0 a = a.all (· = 1)) ∧
  (∀ b, shapesMatch0B b = b.all (· = 1)) ∧
  (∀ x a y b, shapesMatch (x :: a) (y :: b) = (x = y && shapesMatch a b)) ∧
  (∀ sx shape, setindexShapeCheck sx shape =
    let ok : Bool := if sx.length = 1 ∨ shape.length = 1 then
      decide (sx.foldl (· * ·) 1 = shape.foldl (· * ·) 1) else shapesMatch sx shape
    if ok then .ok true else .error (setindexMismatch sx shape)) ∧
  setindexShapeCheckScalar = .error
    (argErr "indexed assignment with a single value to possibly many locations is not supported")

theorem setindexRows_proven : SetindexRows := by
  unfold SetindexRows
  refine ⟨?_, ?_⟩
  · intro sx I
    cases I with
    | nil => rfl
    | cons i rest => cases rest <;> rfl
  · simp [setindexShapeCheck1, shapesMatch00, shapesMatchA0, shapesMatch0B, shapesMatch,
      setindexShapeCheck, setindexShapeCheckScalar]

/-! Each `to_index` overload has its own model. -/

def m243 (i : IV) : RJ CI := toIndex i
def m259 (b : Bool) : RJ CI := .error (argErr s!"invalid index: {b} of type Bool")
def m260 (bs : List Bool) : RJ CI := .ok (.logical bs)
def m261 (xs : List I64) : RJ CI := .ok (.arr xs)
def m262 : RJ CI := .ok (.arr [])
def m263 : RJ CI := .error (argErr "invalid index")
def m265 : RJ CI := .error (argErr "colons must be converted by to_indices(...)")
def m266 : RJ CI := .error (argErr "invalid index")

def m310 (drop : List IV → List IV) (route : List IV → List IV → RJ (List CI))
    (I : List IV) : RJ (List CI) := route (drop I) I
def m311 (linear : List IV) (route : List IV → List IV → RJ (List CI))
    (I : List IV) : RJ (List CI) := route linear I
def m312 (axes : List IV) (route : List IV → List IV → RJ (List CI))
    (I : List IV) : RJ (List CI) := route axes I
def m313 (fallback : List IV → RJ (List CI)) (J : List IV) : RJ (List CI) := fallback J
def m314 : List IV := []
def m315 : List IV → List IV
  | [] => []
  | i :: rest => i :: m315 rest
def m318 : RJ (List CI) := .ok []
def m319 (I : List I64) : RJ (List CI) := .ok (I.map CI.int)
def m320 (isArray : Bool) (I : List IV) : RJ (List CI) := toIndicesInds isArray I
def m321 : RJ (List CI) := .ok []
def m322 (isArray : Bool) : List IV → RJ (List CI)
  | [] => .ok []
  | i :: rest => do pure ((← toIndexA isArray i) :: (← m322 isArray rest))

def ToIndexRows : Prop :=
  (∀ i, m243 i = toIndex i) ∧
  (∀ b, m259 b = .error (argErr s!"invalid index: {b} of type Bool")) ∧
  (∀ bs, m260 bs = .ok (.logical bs)) ∧
  (∀ xs, m261 xs = .ok (.arr xs)) ∧ m262 = .ok (.arr []) ∧
  m263 = .error (argErr "invalid index") ∧
  m265 = .error (argErr "colons must be converted by to_indices(...)") ∧
  m266 = .error (argErr "invalid index") ∧
  (∀ drop route I, m310 drop route I = route (drop I) I) ∧
  (∀ linear route I, m311 linear route I = route linear I) ∧
  (∀ axes route I, m312 axes route I = route axes I) ∧
  (∀ fallback J, m313 fallback J = fallback J) ∧ m314 = [] ∧
  (∀ i rest, m315 (i :: rest) = i :: m315 rest) ∧ m318 = .ok [] ∧
  (∀ I, m319 I = .ok (I.map CI.int)) ∧
  (∀ isArray I, m320 isArray I = toIndicesInds isArray I) ∧ m321 = .ok [] ∧
  (∀ isArray i rest, m322 isArray (i :: rest) = do
    pure ((← toIndexA isArray i) :: (← m322 isArray rest)))

theorem toIndexRows_proven : ToIndexRows := by
  simp [ToIndexRows, m243, m259, m260, m261, m262, m263, m265, m266, m310, m311,
    m312, m313, m314, m315, m318, m319, m320, m321, m322]

def SliceRows : Prop :=
  (∀ S, SliceM.ofSlice S = S) ∧
  (∀ r, SliceM.convert r = .slice r.toUnitRange) ∧
  (∀ S, SliceM.axes S = [S.axes1]) ∧
  (∀ r, SliceM.axes1 r = .ident r) ∧
  (∀ r, SliceM.axes1OneTo r = r) ∧
  (∀ r, SliceM.first r = r.first) ∧ (∀ r, SliceM.last r = r.last) ∧
  (∀ r, SliceM.size r = [r.len]) ∧
  (∀ S i, SliceM.getindexInt S i = do checkbounds S (.int i); pure [i.val]) ∧
  (∀ S i, SliceM.getindexStepRange S i = do checkbounds S i; pure i.elems) ∧
  (∀ r, SliceM.show_ r = "Base.Slice(" ++ r.str ++ ")") ∧
  (∀ r, SliceM.iterate r = r.vals) ∧
  (∀ S I, SliceM.getindexIdent S I = do checkbounds S (.urange (.ident I)); pure (UR.ident I).vals)

theorem sliceRows_proven : SliceRows := by
  simp [SliceRows, SliceM.ofSlice, SliceM.convert, SliceM.axes, SliceM.axes1,
    SliceM.axes1OneTo, SliceM.first, SliceM.last, SliceM.size, SliceM.getindexInt,
    SliceM.getindexStepRange, SliceM.show_, SliceM.iterate, SliceM.getindexIdent]

def IdentityRows : Prop :=
  (∀ S, IdentM.ofIdent S = S) ∧
  (∀ r, IdentM.convert r = .ident r.toUnitRange) ∧
  (∀ S, IdentM.axes S = [S.axes1]) ∧
  (∀ r, IdentM.axes1 r = .ident r) ∧ (∀ r, IdentM.axes1OneTo r = r) ∧
  (∀ r, IdentM.first r = r.first) ∧ (∀ r, IdentM.last r = r.last) ∧
  (∀ r, IdentM.size r = [r.len]) ∧ (∀ r, IdentM.unsafeLength r = r.len) ∧
  (∀ S i k, IdentM.getindexInteger S i k = do checkbounds S i; pure [k]) ∧
  (∀ b, IdentM.getindexBool b = .error (argErr s!"invalid index: {b} of type Bool")) ∧
  (∀ S i, IdentM.getindexUnitRange S i = do checkbounds S i; pure i.elems) ∧
  (∀ S a b, IdentM.getindexBoolUnitRange S a b = do
    checkbounds S (.brange a b); pure (rangeLen (if a then S.first else S.last) (bInt b) 1)) ∧
  (∀ S i, IdentM.getindexStepRange S i = do checkbounds S i; pure i.elems) ∧
  (∀ S I, IdentM.getindexIdent S I = do checkbounds S (.urange (.ident I)); pure (UR.ident I).vals) ∧
  (∀ r, IdentM.show_ r = "Base.IdentityUnitRange(" ++ r.str ++ ")") ∧
  (∀ r, IdentM.iterate r = r.vals) ∧
  (∀ n I, oneToGetIdent n I = do checkbounds (.oneTo n) (.urange (.ident I)); pure (UR.ident I).vals)

theorem identityRows_proven : IdentityRows := by
  simp [IdentityRows, IdentM.ofIdent, IdentM.convert, IdentM.axes, IdentM.axes1,
    IdentM.axes1OneTo, IdentM.first, IdentM.last, IdentM.size, IdentM.unsafeLength,
    IdentM.getindexInteger, IdentM.getindexBool, IdentM.getindexUnitRange,
    IdentM.getindexBoolUnitRange, IdentM.getindexStepRange, IdentM.getindexIdent,
    IdentM.show_, IdentM.iterate, oneToGetIdent]

def LinearConstructorRows : Prop :=
  (∀ L, convertToUnitRanges L = ⟨L.inds.map UR.toUnitRange⟩) ∧
  linearIndicesEmpty = ⟨[]⟩ ∧
  (∀ rs, linearIndicesRanges rs = ⟨rs.map id⟩) ∧
  (∀ axes, linearIndicesOf axes = if axes = [] then linearIndicesEmpty else linearIndicesRanges axes) ∧
  (∀ n, convert2indInt (.int n) = .ok (.oneTo (if n.val < 0 then i64 0 else n))) ∧
  (∀ r, convert2indRange r = .unit (i64 r.first) (i64 r.last))

theorem linearConstructorRows_proven : LinearConstructorRows := by
  simp [LinearConstructorRows, convertToUnitRanges, linearIndicesEmpty, linearIndicesRanges,
    linearIndicesOf, convert2indInt, convert2indRange]

def LinearPromotionRows : Prop :=
  (∀ r1 r2, promoteRuleLinIdx r1 r2 = .linIdx (List.zipWith RT.promote r1 r2)) ∧
  (∀ r1 r2, RT.promote r1 r2 = match r1, r2 with | .oneTo, .oneTo => .oneTo | _, _ => .unitRange)

theorem linearPromotionRows_proven : LinearPromotionRows := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro r1 r2
  cases r1 <;> cases r2 <;> rfl

def LinearValueRows : Prop :=
  (∀ L : LinIdx, L.axes = L.inds.map UR.axes1) ∧
  (∀ L : LinIdx, L.size = L.inds.map UR.len) ∧
  (∀ (L : LinIdx) (i : I64), L.isassigned i = L.inBounds i.val) ∧
  (∀ (L : LinIdx) (i : I64), L.get i = if L.inBounds i.val then .ok i.val else .error boundsErr) ∧
  (∀ L : LinIdx, L.copy = L) ∧
  (∀ r : UR, LinIdx.iterate1 r = r.axes1.vals) ∧
  (∀ (L : LinIdx) (i : Int), L.iterateN 1 i = if i > L.length then [] else [i]) ∧
  (∀ L : LinIdx, L.firstN = 1) ∧ (∀ r : UR, LinIdx.first1 r = r.axes1.first) ∧
  (∀ L : LinIdx, L.lastN = L.length) ∧ (∀ r : UR, LinIdx.last1 r = r.axes1.last) ∧
  (∀ L : LinIdx, L.str = "LinearIndices((" ++ ", ".intercalate (L.inds.map UR.str) ++
    (if L.inds.length = 1 then "," else "") ++ "))")

theorem linearValueRows_proven : LinearValueRows := by
  simp [LinearValueRows, LinIdx.axes, LinIdx.size, LinIdx.isassigned, LinIdx.get, LinIdx.copy,
    LinIdx.iterate1, LinIdx.iterateN, LinIdx.firstN, LinIdx.first1, LinIdx.lastN,
    LinIdx.last1, LinIdx.str]

private def entry (id : String) (fns : List String) (statement source : String)
    (prop thm : Lean.Name) (status : Status := .proven) (issue : String := "") : Entry :=
  { id, juliaFile := "base/indices.jl", juliaFns := fns, statement, source, status,
    prop, thm := some thm, issue }

def entries : List Entry := []

end JuliaLean.ReduceCov.IndicesEntries
