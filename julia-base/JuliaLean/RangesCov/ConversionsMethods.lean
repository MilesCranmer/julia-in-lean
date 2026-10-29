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

def entries : List Entry := []

end ConversionsMethods
end JuliaLean.RangesCov
