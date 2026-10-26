import JuliaLean.Core

namespace JuliaLean.ArrayCov

structure TypeLayoutModel where
  id : Int
  isBits : Bool
  hasBitPadding : Bool
  isSingleton : Bool
  alignedSize : JInt64
  deriving Repr, DecidableEq

structure AxisModel where
  first : JInt64
  length : JInt64
  deriving Repr, DecidableEq

structure ReinterpretInputModel where
  values : List Int
  rank : Int
  firstAxis : AxisModel
  deriving Repr, DecidableEq

structure ReinterpretConstructedModel where
  parent : ReinterpretInputModel
  rank : Int
  source : TypeLayoutModel
  target : TypeLayoutModel
  reshaped : Bool
  readable : Bool
  writable : Bool
  deriving Repr, DecidableEq

inductive ReinterpretConstructError where
  | targetNotBits | sourceNotBits | targetBitPadding | sourceBitPadding
  | zeroDimSize | singletonTarget | nonIntegral | badFirstAxis
  | nonMultiple | sourceSingleton | wrongFirstAxis
  deriving Repr, DecidableEq

abbrev ReinterpretConstructJl (α : Type) := Except ReinterpretConstructError α

def reinterpret14ThrowBits (_source target culprit : TypeLayoutModel) :
    ReinterpretConstructJl Unit :=
  if culprit.id = target.id then .error .targetNotBits else .error .sourceNotBits

def reinterpret18ThrowSizeZero (_source _target : TypeLayoutModel) (_message : String) :
    ReinterpretConstructJl Unit := .error .zeroDimSize

def reinterpret23ThrowSingleton (_source _target : TypeLayoutModel) :
    ReinterpretConstructJl Unit := .error .singletonTarget

def reinterpret27ThrowBitPadding (_source target culprit : TypeLayoutModel) :
    ReinterpretConstructJl Unit :=
  if culprit.id = target.id then .error .targetBitPadding else .error .sourceBitPadding

def reinterpret74ThrowNonIntegral (_source _target : TypeLayoutModel) (_dim : JInt64) :
    ReinterpretConstructJl Unit := .error .nonIntegral

def reinterpret80ThrowAxes (_source _target : TypeLayoutModel) (_axis : AxisModel) :
    ReinterpretConstructJl Unit := .error .badFirstAxis

def reinterpret108ThrowMultiple (_source _target : TypeLayoutModel) :
    ReinterpretConstructJl Unit := .error .nonMultiple

def reinterpret113ThrowSizeOne (_array : ReinterpretInputModel) (_target : TypeLayoutModel) :
    ReinterpretConstructJl Unit := .error .wrongFirstAxis

def reinterpret119ThrowSingletonSource (_source _target : TypeLayoutModel) :
    ReinterpretConstructJl Unit := .error .sourceSingleton

def ReinterpretErrorHelpersCorrect : Prop :=
  (∀ source target culprit, reinterpret14ThrowBits source target culprit =
      if culprit.id = target.id then .error .targetNotBits else .error .sourceNotBits) ∧
  (∀ source target message, reinterpret18ThrowSizeZero source target message =
      .error .zeroDimSize) ∧
  (∀ source target, reinterpret23ThrowSingleton source target = .error .singletonTarget) ∧
  (∀ source target culprit, reinterpret27ThrowBitPadding source target culprit =
      if culprit.id = target.id then .error .targetBitPadding else .error .sourceBitPadding) ∧
  (∀ source target dim, reinterpret74ThrowNonIntegral source target dim = .error .nonIntegral) ∧
  (∀ source target axis, reinterpret80ThrowAxes source target axis = .error .badFirstAxis) ∧
  (∀ source target, reinterpret108ThrowMultiple source target = .error .nonMultiple) ∧
  (∀ array target, reinterpret113ThrowSizeOne array target = .error .wrongFirstAxis) ∧
  (∀ source target, reinterpret119ThrowSingletonSource source target = .error .sourceSingleton)

theorem reinterpretErrorHelpersCorrect : ReinterpretErrorHelpersCorrect := by
  simp [ReinterpretErrorHelpersCorrect, reinterpret14ThrowBits,
    reinterpret18ThrowSizeZero, reinterpret23ThrowSingleton,
    reinterpret27ThrowBitPadding, reinterpret74ThrowNonIntegral,
    reinterpret80ThrowAxes, reinterpret108ThrowMultiple, reinterpret113ThrowSizeOne,
    reinterpret119ThrowSingletonSource]

def reinterpret73Construct (subpadding : TypeLayoutModel → TypeLayoutModel → Bool)
    (source target : TypeLayoutModel) (array : ReinterpretInputModel) :
    ReinterpretConstructJl ReinterpretConstructedModel := do
  if !target.isBits then throw .targetNotBits
  if !source.isBits then throw .sourceNotBits
  if target.hasBitPadding then throw .targetBitPadding
  if source.hasBitPadding then throw .sourceBitPadding
  if array.rank = 0 && target.alignedSize != source.alignedSize then throw .zeroDimSize
  if array.rank != 0 && source.alignedSize != target.alignedSize then
    if target.isSingleton then
      if !source.isSingleton then throw .singletonTarget
    else
      let remainder ← JInt.remInt (array.firstAxis.length * source.alignedSize)
        target.alignedSize |>.mapError fun _ => .nonIntegral
      if remainder.val != 0 then throw .nonIntegral
    if array.firstAxis.first.val != 1 then throw .badFirstAxis
  let readable := subpadding target source
  let writable := subpadding source target
  pure ⟨array, array.rank, source, target, false, readable, writable⟩

def reinterpret107ConstructReshape
    (subpadding : TypeLayoutModel → TypeLayoutModel → Bool)
    (source target : TypeLayoutModel) (array : ReinterpretInputModel) :
    ReinterpretConstructJl ReinterpretConstructedModel := do
  if !target.isBits then throw .targetNotBits
  if !source.isBits then throw .sourceNotBits
  if target.hasBitPadding then throw .targetBitPadding
  if source.hasBitPadding then throw .sourceBitPadding
  let rank ← if source.alignedSize = target.alignedSize then pure array.rank
    else if target.alignedSize < source.alignedSize then do
      if target.isSingleton then throw .singletonTarget
      let remainder ← JInt.remInt source.alignedSize target.alignedSize
        |>.mapError fun _ => .nonMultiple
      if remainder.val != 0 then throw .nonMultiple
      pure (array.rank + 1)
    else do
      if source.isSingleton then throw .sourceSingleton
      let remainder ← JInt.remInt target.alignedSize source.alignedSize
        |>.mapError fun _ => .nonMultiple
      if remainder.val != 0 then throw .nonMultiple
      let rank := array.rank - 1
      if rank < 0 then throw .zeroDimSize
      let expected ← JInt.div target.alignedSize source.alignedSize
        |>.mapError fun _ => .wrongFirstAxis
      if array.firstAxis.first.val != 1 || array.firstAxis.length != expected then
        throw .wrongFirstAxis
      pure rank
  let readable := subpadding target source
  let writable := subpadding source target
  pure ⟨array, rank, source, target, true, readable, writable⟩

def ReinterpretConstructorsCorrect : Prop :=
  (∀ subpadding source target array,
      reinterpret73Construct subpadding source target array = do
        if !target.isBits then throw .targetNotBits
        if !source.isBits then throw .sourceNotBits
        if target.hasBitPadding then throw .targetBitPadding
        if source.hasBitPadding then throw .sourceBitPadding
        if array.rank = 0 && target.alignedSize != source.alignedSize then throw .zeroDimSize
        if array.rank != 0 && source.alignedSize != target.alignedSize then
          if target.isSingleton then
            if !source.isSingleton then throw .singletonTarget
          else
            let remainder ← JInt.remInt (array.firstAxis.length * source.alignedSize)
              target.alignedSize |>.mapError fun _ => .nonIntegral
            if remainder.val != 0 then throw .nonIntegral
          if array.firstAxis.first.val != 1 then throw .badFirstAxis
        let readable := subpadding target source
        let writable := subpadding source target
        pure ⟨array, array.rank, source, target, false, readable, writable⟩) ∧
  (∀ subpadding source target array,
      reinterpret107ConstructReshape subpadding source target array = do
        if !target.isBits then throw .targetNotBits
        if !source.isBits then throw .sourceNotBits
        if target.hasBitPadding then throw .targetBitPadding
        if source.hasBitPadding then throw .sourceBitPadding
        let rank ← if source.alignedSize = target.alignedSize then pure array.rank
          else if target.alignedSize < source.alignedSize then do
            if target.isSingleton then throw .singletonTarget
            let remainder ← JInt.remInt source.alignedSize target.alignedSize
              |>.mapError fun _ => .nonMultiple
            if remainder.val != 0 then throw .nonMultiple
            pure (array.rank + 1)
          else do
            if source.isSingleton then throw .sourceSingleton
            let remainder ← JInt.remInt target.alignedSize source.alignedSize
              |>.mapError fun _ => .nonMultiple
            if remainder.val != 0 then throw .nonMultiple
            let rank := array.rank - 1
            if rank < 0 then throw .zeroDimSize
            let expected ← JInt.div target.alignedSize source.alignedSize
              |>.mapError fun _ => .wrongFirstAxis
            if array.firstAxis.first.val != 1 || array.firstAxis.length != expected then
              throw .wrongFirstAxis
            pure rank
        let readable := subpadding target source
        let writable := subpadding source target
        pure ⟨array, rank, source, target, true, readable, writable⟩)

theorem reinterpretConstructorsCorrect : ReinterpretConstructorsCorrect := by
  constructor <;> intros <;> rfl

end JuliaLean.ArrayCov
