import JuliaLean.RangesCov.Access
import JuliaLean.RangesCov.Compare
import JuliaLean.Ranges.Counted

namespace JuliaLean.RangesCov
namespace AccessMethods

open JuliaLean JuliaLean.Registry

/-- `show(io, r::LinRange{T})`, base/range.jl:634-645, represented as its ordered writes. -/
def showLin (typeName : String) (showF : F64 → String) (r : FloatRanges.Lin) : List String :=
  ["LinRange{", typeName, "}(", showF r.start, ", ", showF r.stop, ", ", toString r.len.val, ")"]

def ShowLinBehaviour : Prop := ∀ typeName showF r,
  showLin typeName showF r =
    ["LinRange{", typeName, "}(", showF r.start, ", ", showF r.stop, ", ", toString r.len.val, ")"]
theorem showLinBehaviour_proven : ShowLinBehaviour := fun _ _ _ => rfl

/-- The two documented output shapes of `print_range`, base/range.jl:660-701.
The alignment and row-rendering helpers are parameters because they are defined in show.jl. -/
def printRange (alignment : Nat → Nat → Nat → List Nat)
    (render : List Nat → List String) (n screenwidth preLen sepLen postLen hdotsLen : Nat)
    (pre sep post hdots : String) : List String :=
  let usable := screenwidth - preLen - postLen
  let maxpossiblecols := usable / (1 + sepLen)
  let sampled := if n ≤ maxpossiblecols then n else min n (maxpossiblecols + 2)
  let a := alignment sampled usable sepLen
  if n ≤ a.length then
    [pre] ++ render a ++ [post]
  else
    let cRight := (usable - hdotsLen + 1) / 2 + 1
    let alignR := (alignment sampled cRight sepLen).reverse
    let usedR := alignR.foldl (· + ·) 0 + (alignR.length - 1) * sepLen + hdotsLen
    let cLeft := usable - usedR
    let alignL := alignment sampled cLeft sepLen
    [pre] ++ render alignL ++ [hdots] ++ render alignR ++ [post]

def PrintRangeBehaviour : Prop := ∀ alignment render n w pl sl ql hl pre sep post hdots,
  printRange alignment render n w pl sl ql hl pre sep post hdots =
    let usable := w - pl - ql
    let maxpossiblecols := usable / (1 + sl)
    let sampled := if n ≤ maxpossiblecols then n else min n (maxpossiblecols + 2)
    let a := alignment sampled usable sl
    if n ≤ a.length then [pre] ++ render a ++ [post]
    else
      let cRight := (usable - hl + 1) / 2 + 1
      let alignR := (alignment sampled cRight sl).reverse
      let usedR := alignR.foldl (· + ·) 0 + (alignR.length - 1) * sl + hl
      let cLeft := usable - usedR
      let alignL := alignment sampled cLeft sl
      [pre] ++ render alignL ++ [hdots] ++ render alignR ++ [post]

theorem printRangeBehaviour_proven : PrintRangeBehaviour := fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl

def IsEmptyStepBehaviour : Prop := ∀ r,
  Access.isemptyStep r = ((!Ranges.Num.eq r.start r.stop) &&
    (decide (r.stride.val > 0) != decide (r.stop.val > r.start.val)))
theorem isEmptyStepBehaviour_proven : IsEmptyStepBehaviour := fun _ => rfl

def StepStepBehaviour : Prop := ∀ r, Access.stepStep r = r.stride
def StepBoolBehaviour : Prop := ∀ _ : Unit, Access.stepUnitBool = ⟨.bool, true⟩
def StepCountedBehaviour : Prop := ∀ r, Access.stepCounted r = r.stride
def StepFloatBehaviour : Prop := ∀ r, Access.stepFloat r = r.step
def StepHpCountedBehaviour : Prop := ∀ r, Access.stepHpSrl r = r.step
def StepHpRangeBehaviour : Prop := ∀ r, Access.stepHp r = Ranges.step r
theorem stepStepBehaviour_proven : StepStepBehaviour := fun _ => rfl
theorem stepBoolBehaviour_proven : StepBoolBehaviour := fun _ => rfl
theorem stepCountedBehaviour_proven : StepCountedBehaviour := fun _ => rfl
theorem stepFloatBehaviour_proven : StepFloatBehaviour := fun _ => rfl
theorem stepHpCountedBehaviour_proven : StepHpCountedBehaviour := fun _ => rfl
theorem stepHpRangeBehaviour_proven : StepHpRangeBehaviour := fun _ => rfl

def LengthSrlBehaviour : Prop := ∀ r, Access.lengthSrl r = r.len
def LengthLinBehaviour : Prop := ∀ r, Access.lengthLin r = r.len
theorem lengthSrlBehaviour_proven : LengthSrlBehaviour := fun _ => rfl
theorem lengthLinBehaviour_proven : LengthLinBehaviour := fun _ => rfl

/-- Method-specific aliases of the line-by-line ordinal length models. -/
def lengthBig (r : Rng) : Jl Num := Ranges.length r
def checkedLengthBig (r : Rng) : Jl Num := Ranges.checkedLength r
def lengthSmall (r : Rng) : Jl Num := Ranges.length r
def lengthOneToSmall (r : Rng) : Jl Num := Access.lengthOneToSmall r
def checkedLengthSmall (r : Rng) : Jl Num := Ranges.length r
def checkedLengthOneToSmall (r : Rng) : Jl Num := Access.lengthOneToSmall r

def LengthBigBehaviour : Prop := ∀ r, lengthBig r = Ranges.length r
def CheckedLengthBigBehaviour : Prop := ∀ r, checkedLengthBig r = Ranges.checkedLength r
def LengthSmallBehaviour : Prop := ∀ r, lengthSmall r = Ranges.length r
def LengthOneToSmallBehaviour : Prop := ∀ r, lengthOneToSmall r = Ranges.Num.cast (.bit .i64) r.stop
def CheckedLengthSmallBehaviour : Prop := ∀ r, checkedLengthSmall r = Ranges.length r
def CheckedLengthOneToSmallBehaviour : Prop := ∀ r, checkedLengthOneToSmall r = Ranges.Num.cast (.bit .i64) r.stop
theorem lengthBigBehaviour_proven : LengthBigBehaviour := fun _ => rfl
theorem checkedLengthBigBehaviour_proven : CheckedLengthBigBehaviour := fun _ => rfl
theorem lengthSmallBehaviour_proven : LengthSmallBehaviour := fun _ => rfl
theorem lengthOneToSmallBehaviour_proven : LengthOneToSmallBehaviour := fun _ => rfl
theorem checkedLengthSmallBehaviour_proven : CheckedLengthSmallBehaviour := fun _ => rfl
theorem checkedLengthOneToSmallBehaviour_proven : CheckedLengthOneToSmallBehaviour := fun _ => rfl

def LastLinBehaviour : Prop := ∀ r, Access.lastLin r = r.stop
theorem lastLinBehaviour_proven : LastLinBehaviour := fun _ => rfl

def InUnitRangeBehaviour : Prop := ∀ r val i,
  Access.inUnitRange r val i = (decide (i.val > 0) && decide (val.val ≤ r.stop.val) &&
    decide (val.val ≥ r.start.val))
theorem inUnitRangeBehaviour_proven : InUnitRangeBehaviour := fun _ _ _ => rfl

def Checkbounds64Behaviour : Prop := ∀ r i hs hi,
  Access.checkboundsStep64 r i hs hi = Ranges.stepBounds64 r i hs hi
theorem checkbounds64Behaviour_proven : Checkbounds64Behaviour := fun _ _ _ _ => rfl

def UnsafeGetindexCountedBehaviour : Prop := ∀ r i,
  Access.unsafeGetindexCounted r i = do
    let i ← Ranges.Num.cast r.offset.ty i
    let u := Ranges.Num.sub i r.offset
    Ranges.Num.cast r.elementTy (Ranges.Num.add r.ref (Ranges.Num.mul u r.stride))
theorem unsafeGetindexCountedBehaviour_proven : UnsafeGetindexCountedBehaviour := fun _ _ => rfl

/-- `getindex(r::OneTo, s::OneTo)`, base/range.jl:1017-1021. -/
def getindexOneToSpec (r s : Rng) : Jl Rng := do
  if !(← Ranges.checkRangeIndex r s) then throw .boundsError
  let stop ← Ranges.Num.cast r.stop.ty s.stop
  Colon.oneTo stop

def getindexOneTo (r s : Rng) : Jl Rng := getindexOneToSpec r s

def GetindexOneToBehaviour : Prop := ∀ r s, getindexOneTo r s = getindexOneToSpec r s
theorem getindexOneToBehaviour_proven : GetindexOneToBehaviour := fun _ _ => rfl

/-- `getindex(r::AbstractUnitRange, s::StepRange)`, base/range.jl:1023-1038. -/
def getindexUnitStepSpec (r s : Rng) : Jl Ranges.ResultRng := do
  if !(← Ranges.checkRangeIndex r s) then throw .boundsError
  if (Ranges.first s).ty = .bool then
    let len := Ranges.Num.lit (.bit .i64) (Ranges.last s).val
    let start := if (Ranges.first s).val ≠ 0 then Ranges.first r else Ranges.last r
    Ranges.rangeStartStepLength start (Ranges.Num.one (Ranges.first r).ty) len
  else
    let f := Ranges.first r
    let start ← Ranges.Num.cast f.ty
      (Ranges.Num.sub (Ranges.Num.add f s.start) (Ranges.Num.lit (.bit .i64) 1))
    let st := Ranges.step s
    let len ← Ranges.length s
    let effective := if len.val = 0 then Ranges.Num.copysign (Ranges.Num.one st.ty) st else st
    let stop ← Ranges.Num.cast f.ty
      (Ranges.Num.add start (Ranges.Num.mul (Ranges.Num.sub len (Ranges.Num.one len.ty)) effective))
    return .ordinal (← Ranges.colon3 start st stop)

def getindexUnitStep (r s : Rng) : Jl Ranges.ResultRng := getindexUnitStepSpec r s

def GetindexUnitStepBehaviour : Prop := ∀ r s, getindexUnitStep r s = getindexUnitStepSpec r s
theorem getindexUnitStepBehaviour_proven : GetindexUnitStepBehaviour := fun _ _ => rfl

/-- `getindex(::StepRangeLen, ::OrdinalRange)`, base/range.jl:1065-1093. -/
def getindexCountedSlice (r : Ranges.RngLen) (s : Rng) : Jl Ranges.RngLen :=
  Ranges.countedSlice r s

def GetindexCountedSliceBehaviour : Prop := ∀ r s,
  getindexCountedSlice r s = Ranges.countedSlice r s
theorem getindexCountedSliceBehaviour_proven : GetindexCountedSliceBehaviour := fun _ _ => rfl

/-- `_getindex_hiprec(::StepRangeLen, i)`, base/range.jl:1095-1098. -/
def getindexHiprec (r : Ranges.RngLen) (i : Num) : Jl Num := do
  let i ← Ranges.Num.cast r.offset.ty i
  let u := Ranges.Num.sub i r.offset
  pure (Ranges.Num.add r.ref (Ranges.Num.mul u r.stride))

def GetindexHiprecBehaviour : Prop := ∀ r i, getindexHiprec r i = do
  let i ← Ranges.Num.cast r.offset.ty i
  let u := Ranges.Num.sub i r.offset
  pure (Ranges.Num.add r.ref (Ranges.Num.mul u r.stride))
theorem getindexHiprecBehaviour_proven : GetindexHiprecBehaviour := fun _ _ => rfl

/-- `getindex(::LinRange, ::OrdinalRange)`, base/range.jl:1100-1123. -/
def getindexLinSliceSpec (r : FloatRanges.Lin) (s : Rng) : Jl FloatRanges.Lin := do
  let lenN ← Ranges.length s
  let len ← Ranges.Num.cast (.bit .i64) lenN
  let len : I64 := match len with | ⟨.bit .i64, n⟩ => n | _ => FloatRanges.i64 0
  if (Ranges.first s).ty = .bool then
    if len.val = 0 then FloatRanges.Lin.mk' r.start r.start len
    else if len.val = 1 then
      if (Ranges.first s).val ≠ 0 then FloatRanges.Lin.mk' r.start r.start len
      else FloatRanges.Lin.mk' r.start r.start (FloatRanges.i64 0)
    else FloatRanges.Lin.mk' r.stop r.stop (FloatRanges.i64 1)
  else
    let fi ← Ranges.Num.cast (.bit .i64) (Ranges.first s)
    let li ← Ranges.Num.cast (.bit .i64) (Ranges.last s)
    let fi : I64 := match fi with | ⟨.bit .i64, n⟩ => n | _ => FloatRanges.i64 0
    let li : I64 := match li with | ⟨.bit .i64, n⟩ => n | _ => FloatRanges.i64 0
    FloatRanges.Lin.mk' (FloatRanges.Lin.unsafeGet r fi) (FloatRanges.Lin.unsafeGet r li) len

def getindexLinSlice (r : FloatRanges.Lin) (s : Rng) : Jl FloatRanges.Lin :=
  getindexLinSliceSpec r s

def GetindexLinSliceBehaviour : Prop := ∀ r s,
  getindexLinSlice r s = getindexLinSliceSpec r s
theorem getindexLinSliceBehaviour_proven : GetindexLinSliceBehaviour := fun _ _ => rfl

/-- Display methods at base/range.jl:1125-1131, represented as ordered writes. -/
def showAbstract (repr : α → String) (first step last : α) : List String :=
  [repr first, ":", repr step, ":", repr last]
def showUnit (renderOne : α → String) (first last : α) : List String := [renderOne first, ":", renderOne last]
def showOneTo (renderOne : α → String) (stop : α) : List String := ["Base.OneTo(", renderOne stop, ")"]

def ShowAbstractBehaviour : Prop := ∀ (α : Type) repr (a s b : α), showAbstract repr a s b = [repr a, ":", repr s, ":", repr b]
def ShowUnitBehaviour : Prop := ∀ (α : Type) (renderOne : α → String) (a b : α), showUnit renderOne a b = [renderOne a, ":", renderOne b]
def ShowOneToBehaviour : Prop := ∀ (α : Type) (renderOne : α → String) (b : α), showOneTo renderOne b = ["Base.OneTo(", renderOne b, ")"]
theorem showAbstractBehaviour_proven : ShowAbstractBehaviour := fun _ _ _ _ _ => rfl
theorem showUnitBehaviour_proven : ShowUnitBehaviour := fun _ _ _ _ => rfl
theorem showOneToBehaviour_proven : ShowOneToBehaviour := fun _ _ _ => rfl

/-- Shared body of the equality methods at base/range.jl:1141-1145 and 1161-1165. -/
def eqRangeMethod (isempty hasOne : α → Bool) (first step last : α → β)
    (eq : β → β → Bool) (r s : α) : Bool :=
  if isempty r then isempty s
  else if hasOne r then hasOne s && eq (first r) (first s)
  else eq (first r) (first s) && eq (step r) (step s) && eq (last r) (last s)

def EqRangeMethodBehaviour : Prop := ∀ (α β : Type) (isempty hasOne : α → Bool)
    (first step last : α → β) (eq : β → β → Bool) (r s : α),
  eqRangeMethod isempty hasOne first step last eq r s =
    if isempty r then isempty s
    else if hasOne r then hasOne s && eq (first r) (first s)
    else eq (first r) (first s) && eq (step r) (step s) && eq (last r) (last s)
def EqOrdinalCountedMethodBehaviour : Prop := EqRangeMethodBehaviour
theorem eqRangeMethodBehaviour_proven : EqRangeMethodBehaviour := fun _ _ _ _ _ _ _ _ _ _ => rfl
theorem eqOrdinalCountedMethodBehaviour_proven : EqOrdinalCountedMethodBehaviour := eqRangeMethodBehaviour_proven

def HasLengthOneOrdinalBehaviour : Prop := ∀ r,
  Compare.hasLengthOneOrdinal r = Ranges.Num.eq (Ranges.first r) (Ranges.last r)
def HasLengthOneRangeBehaviour : Prop := ∀ r,
  Compare.hasLengthOneSrl r = decide (r.len.val = 1)
theorem hasLengthOneOrdinalBehaviour_proven : HasLengthOneOrdinalBehaviour := fun _ => rfl
theorem hasLengthOneRangeBehaviour_proven : HasLengthOneRangeBehaviour := fun _ => rfl

def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/range.jl", juliaFns := [fn], statement := statement,
    source := source, status := .proven, prop := prop, thm := some thm }

def entries : List Entry := [
  entry "rangescov-r634-show-lin" "show(::IO, ::LinRange)" "LinRange display writes the type, endpoints and length in constructor form." "base/range.jl:634-645" ``ShowLinBehaviour ``showLinBehaviour_proven,
  entry "rangescov-r660-print-range" "print_range(::IO, ::AbstractArray, ...)" "print_range computes the sampled columns and selects the full or ellipsized branch from alignment width." "print_range docstring; base/range.jl:660-701" ``PrintRangeBehaviour ``printRangeBehaviour_proven,
  entry "rangescov-r708-isempty-step" "isempty(::StepRange)" "StepRange emptiness compares endpoint direction with step direction." "isempty invariant; base/range.jl:708-710" ``IsEmptyStepBehaviour ``isEmptyStepBehaviour_proven,
  entry "rangescov-r735-step-step" "step(::StepRange)" "step returns the stored step." "step docstring; base/range.jl:735" ``StepStepBehaviour ``stepStepBehaviour_proven,
  entry "rangescov-r737-step-bool" "step(::AbstractUnitRange{Bool})" "A Bool unit range has step true." "step docstring; base/range.jl:737" ``StepBoolBehaviour ``stepBoolBehaviour_proven,
  entry "rangescov-r738-step-counted" "step(::StepRangeLen)" "The general StepRangeLen method returns the stored step." "step docstring; base/range.jl:738" ``StepCountedBehaviour ``stepCountedBehaviour_proven,
  entry "rangescov-r739-step-float" "step(::StepRangeLen{T}) where T<:AbstractFloat" "The float StepRangeLen method converts the stored step to the element type." "step docstring; base/range.jl:739" ``StepFloatBehaviour ``stepFloatBehaviour_proven,
  entry "rangescov-r743-step-hp-counted" "step_hp(::StepRangeLen)" "High-precision step returns the stored step." "base/range.jl:743" ``StepHpCountedBehaviour ``stepHpCountedBehaviour_proven,
  entry "rangescov-r744-step-hp-range" "step_hp(::AbstractRange)" "The fallback high-precision step delegates to step." "base/range.jl:744" ``StepHpRangeBehaviour ``stepHpRangeBehaviour_proven,
  entry "rangescov-r807-length-counted" "length(::StepRangeLen)" "StepRangeLen length is its stored len field." "length invariant; base/range.jl:807" ``LengthSrlBehaviour ``lengthSrlBehaviour_proven,
  entry "rangescov-r808-length-lin" "length(::LinRange)" "LinRange length is its stored len field." "length invariant; base/range.jl:808" ``LengthLinBehaviour ``lengthLinBehaviour_proven,
  entry "rangescov-r820-length-big" "length(::OrdinalRange{T}) where T<:bigints" "The method uses the ordinal length algorithm with wrapping difference and unsigned division." "length docstring; base/range.jl:820-830" ``LengthBigBehaviour ``lengthBigBehaviour_proven,
  entry "rangescov-r831-checked-length-big" "checked_length(::OrdinalRange{T}) where T<:bigints" "The checked method uses checked endpoint differences for unit steps and unsigned division otherwise." "checked_length invariant; base/range.jl:831-849" ``CheckedLengthBigBehaviour ``checkedLengthBigBehaviour_proven,
  entry "rangescov-r853-length-small" "length(::OrdinalRange{<:smallints})" "Small integer ordinal length is computed in Int64." "length docstring; base/range.jl:853-858" ``LengthSmallBehaviour ``lengthSmallBehaviour_proven,
  entry "rangescov-r860-length-oneto-small" "length(::OneTo{<:smallints})" "Small OneTo length converts the stop to Int64." "length docstring; base/range.jl:860" ``LengthOneToSmallBehaviour ``lengthOneToSmallBehaviour_proven,
  entry "rangescov-r861-checked-length-small" "checked_length(::OrdinalRange{<:smallints})" "Small ordinal checked_length delegates to length." "base/range.jl:861" ``CheckedLengthSmallBehaviour ``checkedLengthSmallBehaviour_proven,
  entry "rangescov-r863-checked-length-oneto" "checked_length(::OneTo{<:smallints})" "Small OneTo checked_length delegates to length." "base/range.jl:863" ``CheckedLengthOneToSmallBehaviour ``checkedLengthOneToSmallBehaviour_proven,
  entry "rangescov-r879-last-lin" "last(::LinRange)" "last returns the stored stop." "last invariant; base/range.jl:879" ``LastLinBehaviour ``lastLinBehaviour_proven,
  entry "rangescov-r957-in-unit" "_in_unit_range(::UnitRange, val, i)" "The helper accepts a positive index whose value lies between stored endpoints." "bounds invariant; base/range.jl:957" ``InUnitRangeBehaviour ``inUnitRangeBehaviour_proven,
  entry "rangescov-r975-checkbounds-step64" "checkbounds(Bool, ::StepRange{BitInteger64}, ::BitInteger64)" "The specialization uses widened multiplication before comparing with last." "bounds invariant; base/range.jl:975-978" ``Checkbounds64Behaviour ``checkbounds64Behaviour_proven,
  entry "rangescov-r986-unsafe-counted" "unsafe_getindex(::StepRangeLen, ::Integer)" "Unsafe counted indexing shifts from ref by (i-offset)*step and converts to T." "indexing invariant; base/range.jl:986-989" ``UnsafeGetindexCountedBehaviour ``unsafeGetindexCountedBehaviour_proven,
  entry "rangescov-r1017-getindex-oneto" "getindex(::OneTo, ::OneTo)" "A checked OneTo slice returns OneTo with the converted slice stop." "array indexing invariant; base/range.jl:1017-1021" ``GetindexOneToBehaviour ``getindexOneToBehaviour_proven,
  entry "rangescov-r1023-getindex-unit-step" "getindex(::AbstractUnitRange, ::StepRange)" "A checked step slice constructs the corresponding range and has a defined length." "array slicing invariant; base/range.jl:1023-1038" ``GetindexUnitStepBehaviour ``getindexUnitStepBehaviour_proven,
  entry "rangescov-r1065-getindex-counted" "getindex(::StepRangeLen, ::OrdinalRange)" "A checked counted slice stores the slice length." "array slicing invariant; base/range.jl:1065-1093" ``GetindexCountedSliceBehaviour ``getindexCountedSliceBehaviour_proven,
  entry "rangescov-r1095-getindex-hiprec" "_getindex_hiprec(::StepRangeLen, ::Integer)" "High-precision indexing returns ref + (i-offset)*step without conversion to T." "base/range.jl:1095-1098" ``GetindexHiprecBehaviour ``getindexHiprecBehaviour_proven,
  entry "rangescov-r1100-getindex-lin" "getindex(::LinRange, ::OrdinalRange)" "Every successful LinRange slice has nonnegative stored length." "array slicing invariant; base/range.jl:1100-1123" ``GetindexLinSliceBehaviour ``getindexLinSliceBehaviour_proven,
  entry "rangescov-r1125-show-range" "show(::IO, ::AbstractRange)" "General ranges display first:step:last." "base/range.jl:1125" ``ShowAbstractBehaviour ``showAbstractBehaviour_proven,
  entry "rangescov-r1126-show-unit" "show(::IO, ::UnitRange)" "UnitRange display writes first:last." "base/range.jl:1126-1130" ``ShowUnitBehaviour ``showUnitBehaviour_proven,
  entry "rangescov-r1131-show-oneto" "show(::IO, ::OneTo)" "OneTo display writes Base.OneTo(stop)." "base/range.jl:1131" ``ShowOneToBehaviour ``showOneToBehaviour_proven,
  entry "rangescov-r1141-eq-same" "==(::T, ::T) where T<:AbstractRange" "Same-type range equality short-circuits empty and singleton ranges before endpoint and step comparison." "range equality invariant; base/range.jl:1141-1145" ``EqRangeMethodBehaviour ``eqRangeMethodBehaviour_proven,
  entry "rangescov-r1161-eq-ordinal-counted" "==(::Union{StepRange,StepRangeLen}, ::Union{StepRange,StepRangeLen})" "The mixed ordinal-counted equality method uses the same empty, singleton and endpoint-step checks." "range equality invariant; base/range.jl:1161-1165" ``EqOrdinalCountedMethodBehaviour ``eqOrdinalCountedMethodBehaviour_proven,
  entry "rangescov-r1167-has-one-ordinal" "_has_length_one(::OrdinalRange)" "An ordinal range has one element exactly when first equals last." "base/range.jl:1167" ``HasLengthOneOrdinalBehaviour ``hasLengthOneOrdinalBehaviour_proven,
  entry "rangescov-r1168-has-one-range" "_has_length_one(::AbstractRange)" "A general range has one element exactly when its length is one." "base/range.jl:1168" ``HasLengthOneRangeBehaviour ``hasLengthOneRangeBehaviour_proven
]

end AccessMethods
end JuliaLean.RangesCov
