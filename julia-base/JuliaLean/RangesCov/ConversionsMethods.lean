import JuliaLean.RangesCov.Convert
import JuliaLean.RangesCov.Compare
import JuliaLean.Ranges.Operations

namespace JuliaLean.RangesCov
namespace ConversionsMethods

open JuliaLean JuliaLean.Registry

def IntersectOneToBehaviour : Prop := ∀ r s,
  Compare.intersectOneTo r s = Colon.oneTo (Ranges.Num.min r.stop s.stop)
def UnionOneToBehaviour : Prop := ∀ r s,
  Compare.unionOneTo r s = Colon.oneTo (Ranges.Num.max r.stop s.stop)
def IntersectUnitBehaviour : Prop := ∀ r s,
  Compare.intersectUnit r s = Colon.colonPromote2 (Ranges.Num.max (Ranges.first r) (Ranges.first s))
    (Ranges.Num.min (Ranges.last r) (Ranges.last s))
def IntersectScalarBehaviour : Prop := ∀ i r, Compare.intersectScalar i r = do
  let m ← Ranges.contains i r
  Ranges.rangeStartLength (Ranges.Num.max i (Ranges.first r)) (Ranges.Num.lit .bool (if m then 1 else 0))
def IntersectScalarRightBehaviour : Prop := ∀ r i,
  Compare.intersectScalarRight r i = Compare.intersectScalar i r

theorem intersectOneToBehaviour_proven : IntersectOneToBehaviour := fun _ _ => rfl
theorem unionOneToBehaviour_proven : UnionOneToBehaviour := fun _ _ => rfl
theorem intersectUnitBehaviour_proven : IntersectUnitBehaviour := fun _ _ => rfl
theorem intersectScalarBehaviour_proven : IntersectScalarBehaviour := fun _ _ => rfl
theorem intersectScalarRightBehaviour_proven : IntersectScalarRightBehaviour := fun _ _ => rfl

def FirstStepLastBehaviour : Prop := ∀ r,
  Ranges.firstStepLastAscending r =
    if (Ranges.step r).val < 0 then (Ranges.last r, Ranges.Num.neg (Ranges.step r), Ranges.first r)
    else (Ranges.first r, Ranges.Num.pos (Ranges.step r), Ranges.last r)
theorem firstStepLastBehaviour_proven : FirstStepLastBehaviour := fun _ => rfl

def IntersectGenericBehaviour : Prop := ∀ (α : Type) [BEq α] (r1 r2 : List α) (mem : α → List α → Bool),
  Compare.intersectGeneric r1 r2 mem =
    if r1.length > r2.length then (r2.eraseDups.filter fun x => mem x r1)
    else r1.eraseDups.filter fun x => mem x r2
theorem intersectGenericBehaviour_proven : IntersectGenericBehaviour := fun _ _ _ _ _ => rfl

def IntersectManyBehaviour : Prop := ∀ (α : Type) (inter : α → α → α) r1 r2 r3 rs,
  Compare.intersectMany inter r1 r2 r3 rs = rs.foldl inter (inter (inter r1 r2) r3)
theorem intersectManyBehaviour_proven : IntersectManyBehaviour := fun _ _ _ _ _ _ => rfl

def IsSubsetOneToBehaviour : Prop := ∀ r s,
  Compare.issubsetOneTo r s = decide (r.stop.val ≤ s.stop.val)
theorem isSubsetOneToBehaviour_proven : IsSubsetOneToBehaviour := fun _ _ => rfl

/-- The four dispatch-specific `el_same` bodies, base/range.jl:1321-1324. -/
def elSameBoth (_T a _b : Convert.RT) : Convert.RT := a
def elSameLeft (_T a _b : Convert.RT) : Convert.RT := a
def elSameRight (_T _a b : Convert.RT) : Convert.RT := b
def elSameFallback (promoteTypejoin : Convert.RT → Convert.RT → Convert.RT)
    (_T a b : Convert.RT) : Convert.RT := promoteTypejoin a b

def ElSameBothBehaviour : Prop := ∀ T a b, elSameBoth T a b = a
def ElSameLeftBehaviour : Prop := ∀ T a b, elSameLeft T a b = a
def ElSameRightBehaviour : Prop := ∀ T a b, elSameRight T a b = b
def ElSameFallbackBehaviour : Prop := ∀ f T a b, elSameFallback f T a b = f a b
theorem elSameBothBehaviour_proven : ElSameBothBehaviour := fun _ _ _ => rfl
theorem elSameLeftBehaviour_proven : ElSameLeftBehaviour := fun _ _ _ => rfl
theorem elSameRightBehaviour_proven : ElSameRightBehaviour := fun _ _ _ => rfl
theorem elSameFallbackBehaviour_proven : ElSameFallbackBehaviour := fun _ _ _ _ => rfl

def PromoteUnitBehaviour : Prop := ∀ a b,
  Convert.promoteUnit a b = Convert.elSame (Convert.pt a b) (.unit a) (.unit b)
def PromoteOneToBehaviour : Prop := ∀ a b,
  Convert.promoteOneTo a b = Convert.elSame (Convert.pt a b) (.oneTo a) (.oneTo b)
def PromoteOneToUrBehaviour : Prop := ∀ a e,
  Convert.promoteOneToUR a e = Convert.promoteUnitUR a e
def PromoteUnitUrBehaviour : Prop := ∀ a e,
  Convert.promoteUnitUR a e = Convert.promoteUnit a e
theorem promoteUnitBehaviour_proven : PromoteUnitBehaviour := fun _ _ => rfl
theorem promoteOneToBehaviour_proven : PromoteOneToBehaviour := fun _ _ => rfl
theorem promoteOneToUrBehaviour_proven : PromoteOneToUrBehaviour := fun _ _ => rfl
theorem promoteUnitUrBehaviour_proven : PromoteUnitUrBehaviour := fun _ _ => rfl

def unitSame (r : Rng) : Rng := r
def oneToSame (r : Rng) : Rng := r
def abstractUnitSame (r : Rng) : Rng := r
def stepTsSame (r : Rng) : Rng := r
def stepTSame (r : Rng) : Rng := r
def stepSame (r : Rng) : Rng := r
def srlSame (r : Ranges.RngLen) : Ranges.RngLen := r
def linSame (r : Convert.LinI) : Convert.LinI := r

def UnitSameBehaviour : Prop := ∀ r, unitSame r = r
def OneToSameBehaviour : Prop := ∀ r, oneToSame r = r
def AbstractUnitSameBehaviour : Prop := ∀ r, abstractUnitSame r = r
def StepTsSameBehaviour : Prop := ∀ r, stepTsSame r = r
def StepTSameBehaviour : Prop := ∀ r, stepTSame r = r
def StepSameBehaviour : Prop := ∀ r, stepSame r = r
def SrlSameBehaviour : Prop := ∀ r, srlSame r = r
def LinSameBehaviour : Prop := ∀ r, linSame r = r
theorem unitSameBehaviour_proven : UnitSameBehaviour := fun _ => rfl
theorem oneToSameBehaviour_proven : OneToSameBehaviour := fun _ => rfl
theorem abstractUnitSameBehaviour_proven : AbstractUnitSameBehaviour := fun _ => rfl
theorem stepTsSameBehaviour_proven : StepTsSameBehaviour := fun _ => rfl
theorem stepTSameBehaviour_proven : StepTSameBehaviour := fun _ => rfl
theorem stepSameBehaviour_proven : StepSameBehaviour := fun _ => rfl
theorem srlSameBehaviour_proven : SrlSameBehaviour := fun _ => rfl
theorem linSameBehaviour_proven : LinSameBehaviour := fun _ => rfl

def OneToConvertBehaviour : Prop := ∀ T r,
  Convert.oneToOfOneTo T r = Colon.oneToT T r.stop
def UnitAbstractConvertBehaviour : Prop := ∀ T r,
  Convert.unitRangeOfAbstractUnit T r = Colon.unitRangeT T (Ranges.first r) (Ranges.last r)
def AbstractUnitFromUnitBehaviour : Prop := ∀ T r, r.kind ≠ .oneTo →
  Convert.abstractUnitRangeT T r = Convert.unitRangeOfUnit T r
def AbstractUnitFromOneToBehaviour : Prop := ∀ T r, r.kind = .oneTo →
  Convert.abstractUnitRangeT T r = Convert.oneToOfOneTo T r
theorem oneToConvertBehaviour_proven : OneToConvertBehaviour := fun _ _ => rfl
theorem unitAbstractConvertBehaviour_proven : UnitAbstractConvertBehaviour := fun _ _ => rfl
theorem abstractUnitFromUnitBehaviour_proven : AbstractUnitFromUnitBehaviour := by
  intro T r h; simp [Convert.abstractUnitRangeT, h]
theorem abstractUnitFromOneToBehaviour_proven : AbstractUnitFromOneToBehaviour := by
  intro T r h; simp [Convert.abstractUnitRangeT, h]

def OrdinalRangeTsBehaviour : Prop := ∀ T S r,
  Convert.ordinalRangeTS T S r = Convert.stepRangeOfRange T S r
def OrdinalRangeTtBehaviour : Prop := ∀ T r,
  Convert.ordinalRangeTT T r = Convert.abstractUnitRangeT T r
theorem ordinalRangeTsBehaviour_proven : OrdinalRangeTsBehaviour := fun _ _ _ => rfl
theorem ordinalRangeTtBehaviour_proven : OrdinalRangeTtBehaviour := fun _ _ => rfl

def PromoteStepBehaviour : Prop := ∀ a b c d,
  Convert.promoteStep a b c d =
    let s := Convert.pt b d
    Convert.elSame (Convert.pt a c) (.step a s) (.step c s)
def PromoteStepUrBehaviour : Prop := ∀ a b e,
  Convert.promoteStepUR a b e = Convert.promoteStep a b e e
theorem promoteStepBehaviour_proven : PromoteStepBehaviour := fun _ _ _ _ => rfl
theorem promoteStepUrBehaviour_proven : PromoteStepUrBehaviour := fun _ _ _ => rfl

def StepFromRangeBehaviour : Prop := ∀ T S r,
  Convert.stepRangeOfRange T S r = do
    let a ← Ranges.Num.cast T (Ranges.first r)
    let s ← Ranges.Num.cast S (Ranges.step r)
    let b ← Ranges.Num.cast T (Ranges.last r)
    Colon.stepRangeTS T S a s b
def StepFromOrdinalBehaviour : Prop := ∀ r,
  Convert.stepRangeOfOrdinal r = Colon.stepRangeTS (Ranges.first r).ty (Ranges.step r).ty
    (Ranges.first r) (Ranges.step r) (Ranges.last r)
def StepTFromOrdinalBehaviour : Prop := ∀ T r,
  Convert.stepRangeTOfOrdinal T r = Colon.stepRangeTS T (Ranges.step r).ty
    (Ranges.first r) (Ranges.step r) (Ranges.last r)
def StepSFromRangeBehaviour : Prop := ∀ S r,
  Convert.stepRangeS S r = Convert.stepRangeOfRange (Ranges.first r).ty S r
def StepFromSrlBehaviour : Prop := ∀ r,
  Convert.stepRangeOfSrl r = Convert.stepRangeOfCounted r.elementTy r
def StepTFromSrlBehaviour : Prop := ∀ T r,
  Convert.stepRangeOfCounted T r = do
    let a0 ← Ranges.countedFirst r
    let b0 ← Ranges.countedLast r
    let a ← Ranges.Num.cast T a0
    let s ← Ranges.Num.cast r.stride.ty r.stride
    let b ← Ranges.Num.cast T b0
    Colon.stepRangeTS T r.stride.ty a s b
theorem stepFromRangeBehaviour_proven : StepFromRangeBehaviour := fun _ _ _ => rfl
theorem stepFromOrdinalBehaviour_proven : StepFromOrdinalBehaviour := fun _ => rfl
theorem stepTFromOrdinalBehaviour_proven : StepTFromOrdinalBehaviour := fun _ _ => rfl
theorem stepSFromRangeBehaviour_proven : StepSFromRangeBehaviour := fun _ _ => rfl
theorem stepFromSrlBehaviour_proven : StepFromSrlBehaviour := fun _ => rfl
theorem stepTFromSrlBehaviour_proven : StepTFromSrlBehaviour := fun _ _ => rfl

def PromoteSrlBehaviour : Prop := ∀ T1 R1 S1 L1 T2 R2 S2 L2,
  Convert.promoteSrl T1 R1 S1 L1 T2 R2 S2 L2 =
    let R := Convert.pt R1 R2
    let S := Convert.pt S1 S2
    let L := Convert.pt L1 L2
    Convert.elSame (Convert.pt T1 T2) (.srl T1 R S L) (.srl T2 R S L)
def PromoteSrlOrBehaviour : Prop := ∀ T R S L E,
  Convert.promoteSrlOR T R S L E = Convert.promoteSrl T R S L E E E (.bit .i64)
theorem promoteSrlBehaviour_proven : PromoteSrlBehaviour := fun _ _ _ _ _ _ _ _ => rfl
theorem promoteSrlOrBehaviour_proven : PromoteSrlOrBehaviour := fun _ _ _ _ _ => rfl

def SrlFromSrlBehaviour : Prop := ∀ T R S L r,
  Convert.srlOfSrl T R S L r = do
    let ref ← Ranges.Num.cast R r.ref
    let st ← Ranges.Num.cast S r.stride
    let len ← Ranges.Num.cast L r.len
    let off ← Ranges.Num.cast L r.offset
    if len.val < 0 then throw (.argumentError "length cannot be negative")
    if off.val < 1 ∨ off.val > max 1 len.val then throw (.argumentError "StepRangeLen: offset")
    pure ⟨ref, st, len, off, T⟩
def SrlTFromSrlBehaviour : Prop := ∀ T r,
  Convert.srlTOfSrl T r = do
    let ref ← Ranges.Num.cast T r.ref
    let st ← Ranges.Num.cast T r.stride
    Convert.srlOfSrl T T T (Ranges.Num.promote (.bit .i64) r.len.ty) ⟨ref, st, r.len, r.offset, T⟩
def SrlFromRangeBehaviour : Prop := ∀ T R S L r,
  Convert.srlOfRange T R S L r = do
    let ref ← Ranges.Num.cast R (Ranges.first r)
    let st ← Ranges.Num.cast S (Ranges.step r)
    let len ← Ranges.length r
    Convert.srlOfSrl T R S L ⟨ref, st, len, Ranges.Num.lit (.bit .i64) 1, T⟩
def SrlTFromRangeBehaviour : Prop := ∀ T r,
  Convert.srlTOfRange T r = do
    let len ← Ranges.length r
    Convert.srlOfRange T T T (Ranges.Num.promote (.bit .i64) len.ty) r
def SrlAutoFromRangeBehaviour : Prop := ∀ r,
  Convert.srlOfRangeAuto r = Convert.srlTOfRange (Ranges.first r).ty r
theorem srlFromSrlBehaviour_proven : SrlFromSrlBehaviour := fun _ _ _ _ _ => rfl
theorem srlTFromSrlBehaviour_proven : SrlTFromSrlBehaviour := fun _ _ => rfl
theorem srlFromRangeBehaviour_proven : SrlFromRangeBehaviour := fun _ _ _ _ _ => rfl
theorem srlTFromRangeBehaviour_proven : SrlTFromRangeBehaviour := fun _ _ => rfl
theorem srlAutoFromRangeBehaviour_proven : SrlAutoFromRangeBehaviour := fun _ => rfl

def PromoteLinBehaviour : Prop := ∀ T1 L1 T2 L2,
  Convert.promoteLin T1 L1 T2 L2 =
    let L := Convert.pt L1 L2
    Convert.elSame (Convert.pt T1 T2) (.lin T1 L) (.lin T2 L)
def PromoteLinOrBehaviour : Prop := ∀ T L E,
  Convert.promoteLinOR T L E = Convert.promoteLin T L E L
def PromoteLinSrlBehaviour : Prop := ∀ A L T R S L2,
  Convert.promoteLinSrl A L T R S L2 = Convert.promoteSrl A A A L T R S L2
theorem promoteLinBehaviour_proven : PromoteLinBehaviour := fun _ _ _ _ => rfl
theorem promoteLinOrBehaviour_proven : PromoteLinOrBehaviour := fun _ _ _ => rfl
theorem promoteLinSrlBehaviour_proven : PromoteLinSrlBehaviour := fun _ _ _ _ _ _ => rfl

def LinFromRangeBehaviour : Prop := ∀ T L r, Convert.linOfRange T L r = do
  let a ← Ranges.Num.cast T (Ranges.first r)
  let b ← Ranges.Num.cast T (Ranges.last r)
  let n ← Ranges.length r
  let n ← Ranges.Num.cast L n
  if n.val < 0 then .error (.argumentError "negative length")
  else .ok ⟨a, b, n⟩
def LinTFromRangeBehaviour : Prop := ∀ T r,
  Convert.linTOfRange T r = do
    let n ← Ranges.length r
    Convert.linOfRange T n.ty r
def LinAutoFromRangeBehaviour : Prop := ∀ r,
  Convert.linOfRangeAuto r = Convert.linTOfRange (Ranges.first r).ty r
theorem linFromRangeBehaviour_proven : LinFromRangeBehaviour := fun _ _ _ => rfl
theorem linTFromRangeBehaviour_proven : LinTFromRangeBehaviour := fun _ _ => rfl
theorem linAutoFromRangeBehaviour_proven : LinAutoFromRangeBehaviour := fun _ => rfl

def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/range.jl", juliaFns := [fn], statement := statement,
    source := source, status := .proven, prop := prop, thm := some thm }

def entries : List Entry := [
  entry "rangescov-r1196-intersect-oneto" "intersect(::OneTo, ::OneTo)" "The intersection stop is the minimum stop." "base/range.jl:1196" ``IntersectOneToBehaviour ``intersectOneToBehaviour_proven,
  entry "rangescov-r1197-union-oneto" "union(::OneTo, ::OneTo)" "The union stop is the maximum stop." "base/range.jl:1197" ``UnionOneToBehaviour ``unionOneToBehaviour_proven,
  entry "rangescov-r1199-intersect-unit" "intersect(::AbstractUnitRange, ::AbstractUnitRange)" "Unit-range intersection runs from the maximum first to the minimum last." "base/range.jl:1199" ``IntersectUnitBehaviour ``intersectUnitBehaviour_proven,
  entry "rangescov-r1201-intersect-scalar" "intersect(::Integer, ::AbstractUnitRange)" "Scalar intersection starts at max(i, first(r)) and has membership length zero or one." "base/range.jl:1201" ``IntersectScalarBehaviour ``intersectScalarBehaviour_proven,
  entry "rangescov-r1203-intersect-scalar-right" "intersect(::AbstractUnitRange, ::Integer)" "The right-scalar method delegates with reversed arguments." "base/range.jl:1203" ``IntersectScalarRightBehaviour ``intersectScalarRightBehaviour_proven,
  entry "rangescov-r1219-first-step-last" "first_step_last_ascending(::StepRange)" "Descending ranges swap endpoints and negate the step; ascending ranges keep them." "base/range.jl:1219-1225" ``FirstStepLastBehaviour ``firstStepLastBehaviour_proven,
  entry "rangescov-r1267-intersect-generic" "intersect(::AbstractRange, ::AbstractRange)" "Generic intersection iterates the shorter unique range and filters by membership." "base/range.jl:1267-1275" ``IntersectGenericBehaviour ``intersectGenericBehaviour_proven,
  entry "rangescov-r1277-intersect-many" "intersect(::AbstractRange, ::AbstractRange, ::AbstractRange, ...)" "Variadic intersection is a left fold after the first three ranges." "base/range.jl:1277-1283" ``IntersectManyBehaviour ``intersectManyBehaviour_proven,
  entry "rangescov-r1305-subset-oneto" "issubset(::OneTo, ::OneTo)" "OneTo inclusion compares stops." "base/range.jl:1305" ``IsSubsetOneToBehaviour ``isSubsetOneToBehaviour_proven,
  entry "rangescov-r1321-el-same" "el_same(T, AbstractArray{T}, AbstractArray{T})" "When both containers have the promoted element type, the first is returned." "base/range.jl:1321" ``ElSameBothBehaviour ``elSameBothBehaviour_proven,
  entry "rangescov-r1322-el-same" "el_same(T, AbstractArray{T}, AbstractArray{S})" "When the first container has the promoted element type, it is returned." "base/range.jl:1322" ``ElSameLeftBehaviour ``elSameLeftBehaviour_proven,
  entry "rangescov-r1323-el-same" "el_same(T, AbstractArray{S}, AbstractArray{T})" "When the second container has the promoted element type, it is returned." "base/range.jl:1323" ``ElSameRightBehaviour ``elSameRightBehaviour_proven,
  entry "rangescov-r1324-el-same" "el_same(::Type, a, b)" "The fallback returns promote_typejoin(a,b)." "base/range.jl:1324" ``ElSameFallbackBehaviour ``elSameFallbackBehaviour_proven,
  entry "rangescov-r1326-promote-unit" "promote_rule(::UnitRange, ::UnitRange)" "UnitRange promotion applies el_same to the promoted element type." "base/range.jl:1326-1327" ``PromoteUnitBehaviour ``promoteUnitBehaviour_proven,
  entry "rangescov-r1328-unit-same" "UnitRange{T}(::UnitRange{T})" "The identity constructor returns its argument." "base/range.jl:1328" ``UnitSameBehaviour ``unitSameBehaviour_proven,
  entry "rangescov-r1331-promote-oneto" "promote_rule(::OneTo, ::OneTo)" "OneTo promotion applies el_same to the promoted element type." "base/range.jl:1331-1332" ``PromoteOneToBehaviour ``promoteOneToBehaviour_proven,
  entry "rangescov-r1333-oneto-same" "OneTo{T}(::OneTo{T})" "The identity constructor returns its argument." "base/range.jl:1333" ``OneToSameBehaviour ``oneToSameBehaviour_proven,
  entry "rangescov-r1334-oneto-convert" "OneTo{T}(::OneTo)" "Conversion rebuilds OneTo from the stored stop." "base/range.jl:1334" ``OneToConvertBehaviour ``oneToConvertBehaviour_proven,
  entry "rangescov-r1336-promote-oneto-unit" "promote_rule(::OneTo, ::AbstractUnitRange)" "OneTo promotion delegates through UnitRange." "base/range.jl:1336-1337" ``PromoteOneToUrBehaviour ``promoteOneToUrBehaviour_proven,
  entry "rangescov-r1339-promote-unit-ur" "promote_rule(::UnitRange, ::AbstractUnitRange)" "Abstract unit promotion substitutes its element type into UnitRange." "base/range.jl:1339-1340" ``PromoteUnitUrBehaviour ``promoteUnitUrBehaviour_proven,
  entry "rangescov-r1341-unit-abstract" "UnitRange{T}(::AbstractUnitRange)" "Conversion rebuilds UnitRange from first and last." "base/range.jl:1341" ``UnitAbstractConvertBehaviour ``unitAbstractConvertBehaviour_proven,
  entry "rangescov-r1344-abstract-unit-same" "AbstractUnitRange{T}(::AbstractUnitRange{T})" "The identity constructor returns its argument." "base/range.jl:1344" ``AbstractUnitSameBehaviour ``abstractUnitSameBehaviour_proven,
  entry "rangescov-r1345-abstract-unit-unit" "AbstractUnitRange{T}(::UnitRange)" "Conversion delegates to UnitRange{T}." "base/range.jl:1345" ``AbstractUnitFromUnitBehaviour ``abstractUnitFromUnitBehaviour_proven,
  entry "rangescov-r1346-abstract-unit-oneto" "AbstractUnitRange{T}(::OneTo)" "Conversion delegates to OneTo{T}." "base/range.jl:1346" ``AbstractUnitFromOneToBehaviour ``abstractUnitFromOneToBehaviour_proven,
  entry "rangescov-r1348-ordinal-convert" "OrdinalRange{T,S}(::OrdinalRange)" "Conversion delegates to StepRange{T,S}." "base/range.jl:1348" ``OrdinalRangeTsBehaviour ``ordinalRangeTsBehaviour_proven,
  entry "rangescov-r1349-ordinal-unit" "OrdinalRange{T,T}(::AbstractUnitRange)" "Conversion delegates to AbstractUnitRange{T}." "base/range.jl:1349" ``OrdinalRangeTtBehaviour ``ordinalRangeTtBehaviour_proven,
  entry "rangescov-r1351-promote-step" "promote_rule(::StepRange, ::StepRange)" "StepRange promotion separately promotes step and element types." "base/range.jl:1351-1355" ``PromoteStepBehaviour ``promoteStepBehaviour_proven,
  entry "rangescov-r1356-step-ts-same" "StepRange{T,S}(::StepRange{T,S})" "The identity constructor returns its argument." "base/range.jl:1356" ``StepTsSameBehaviour ``stepTsSameBehaviour_proven,
  entry "rangescov-r1357-step-t-same" "StepRange{T}(::StepRange{T})" "The identity constructor returns its argument." "base/range.jl:1357" ``StepTSameBehaviour ``stepTSameBehaviour_proven,
  entry "rangescov-r1358-step-same" "StepRange(::StepRange)" "The identity constructor returns its argument." "base/range.jl:1358" ``StepSameBehaviour ``stepSameBehaviour_proven,
  entry "rangescov-r1360-promote-step-ur" "promote_rule(::StepRange, ::AbstractUnitRange)" "Promotion treats the unit range as a StepRange with identical type parameters." "base/range.jl:1360-1361" ``PromoteStepUrBehaviour ``promoteStepUrBehaviour_proven,
  entry "rangescov-r1362-step-from-range" "StepRange{T,S}(::AbstractRange)" "Conversion converts first, step and last before constructing StepRange." "base/range.jl:1362-1363" ``StepFromRangeBehaviour ``stepFromRangeBehaviour_proven,
  entry "rangescov-r1364-step-from-ordinal" "StepRange(::OrdinalRange)" "The constructor uses the source element and step types." "base/range.jl:1364" ``StepFromOrdinalBehaviour ``stepFromOrdinalBehaviour_proven,
  entry "rangescov-r1365-step-t-from-ordinal" "StepRange{T}(::OrdinalRange)" "The constructor fixes the element type and keeps the source step type." "base/range.jl:1365" ``StepTFromOrdinalBehaviour ``stepTFromOrdinalBehaviour_proven,
  entry "rangescov-r1366-step-s-from-range" "(StepRange{T,S} where T)(::AbstractRange)" "The partial constructor takes the source element type." "base/range.jl:1366" ``StepSFromRangeBehaviour ``stepSFromRangeBehaviour_proven,
  entry "rangescov-r1367-step-from-srl" "StepRange(::StepRangeLen)" "The constructor takes the source element type." "base/range.jl:1367" ``StepFromSrlBehaviour ``stepFromSrlBehaviour_proven,
  entry "rangescov-r1368-step-t-from-srl" "StepRange{T}(::StepRangeLen)" "The constructor converts counted first, step and last." "base/range.jl:1368" ``StepTFromSrlBehaviour ``stepTFromSrlBehaviour_proven,
  entry "rangescov-r1370-promote-srl" "promote_rule(::StepRangeLen, ::StepRangeLen)" "StepRangeLen promotion promotes reference, step and length storage independently." "base/range.jl:1370-1373" ``PromoteSrlBehaviour ``promoteSrlBehaviour_proven,
  entry "rangescov-r1374-srl-same" "StepRangeLen{T,R,S,L}(::StepRangeLen{T,R,S,L})" "The identity constructor returns its argument." "base/range.jl:1374" ``SrlSameBehaviour ``srlSameBehaviour_proven,
  entry "rangescov-r1375-srl-convert" "StepRangeLen{T,R,S,L}(::StepRangeLen)" "Conversion converts all four stored fields before reconstruction." "base/range.jl:1375-1376" ``SrlFromSrlBehaviour ``srlFromSrlBehaviour_proven,
  entry "rangescov-r1377-srl-t-convert" "StepRangeLen{T}(::StepRangeLen)" "Conversion converts reference and step to T while retaining length and offset." "base/range.jl:1377-1378" ``SrlTFromSrlBehaviour ``srlTFromSrlBehaviour_proven,
  entry "rangescov-r1380-promote-srl-range" "promote_rule(::StepRangeLen, ::AbstractRange)" "Promotion represents the other range as an Int-length StepRangeLen." "base/range.jl:1380-1381" ``PromoteSrlOrBehaviour ``promoteSrlOrBehaviour_proven,
  entry "rangescov-r1382-srl-from-range" "StepRangeLen{T,R,S,L}(::AbstractRange)" "Conversion uses converted first, step and length." "base/range.jl:1382-1383" ``SrlFromRangeBehaviour ``srlFromRangeBehaviour_proven,
  entry "rangescov-r1384-srl-t-from-range" "StepRangeLen{T}(::AbstractRange)" "Conversion uses T(first), T(step) and length." "base/range.jl:1384-1385" ``SrlTFromRangeBehaviour ``srlTFromRangeBehaviour_proven,
  entry "rangescov-r1386-srl-auto" "StepRangeLen(::AbstractRange)" "The outer constructor uses the source element type." "base/range.jl:1386" ``SrlAutoFromRangeBehaviour ``srlAutoFromRangeBehaviour_proven,
  entry "rangescov-r1388-promote-lin" "promote_rule(::LinRange, ::LinRange)" "LinRange promotion promotes length storage and element types." "base/range.jl:1388-1391" ``PromoteLinBehaviour ``promoteLinBehaviour_proven,
  entry "rangescov-r1392-lin-same" "LinRange{T,L}(::LinRange{T,L})" "The identity constructor returns its argument." "base/range.jl:1392" ``LinSameBehaviour ``linSameBehaviour_proven,
  entry "rangescov-r1393-lin-from-range" "LinRange{T,L}(::AbstractRange)" "Conversion uses converted first, last and length." "base/range.jl:1393" ``LinFromRangeBehaviour ``linFromRangeBehaviour_proven,
  entry "rangescov-r1394-lin-t-from-range" "LinRange{T}(::AbstractRange)" "The partial constructor uses typeof(length(r))." "base/range.jl:1394" ``LinTFromRangeBehaviour ``linTFromRangeBehaviour_proven,
  entry "rangescov-r1395-lin-auto" "LinRange(::AbstractRange{T})" "The outer constructor uses the source element type." "base/range.jl:1395" ``LinAutoFromRangeBehaviour ``linAutoFromRangeBehaviour_proven,
  entry "rangescov-r1397-promote-lin-ordinal" "promote_rule(::LinRange, ::OrdinalRange)" "Promotion represents the ordinal range as a LinRange of the same length type." "base/range.jl:1397-1398" ``PromoteLinOrBehaviour ``promoteLinOrBehaviour_proven,
  entry "rangescov-r1400-promote-lin-srl" "promote_rule(::LinRange, ::StepRangeLen)" "Promotion represents the LinRange as a StepRangeLen with repeated element storage types." "base/range.jl:1400-1401" ``PromoteLinSrlBehaviour ``promoteLinSrlBehaviour_proven
]

end ConversionsMethods
end JuliaLean.RangesCov
