import JuliaLean.Core
import JuliaLean.ArrayCov.ReinterpretAccess

namespace JuliaLean.ArrayCov

structure FieldLayoutModel where
  offset : Nat
  size : Nat
  packed : Bool
  typeId : Int
  deriving Repr, DecidableEq

structure LayoutInfoModel where
  typeId : Int
  isBits : Bool
  primitive : Bool
  bitSize : Nat
  alignedSize : Nat
  datatypePadding : Bool
  bitPadding : Bool
  fields : List FieldLayoutModel
  deriving Repr, DecidableEq

inductive PaddingRouteError where
  | argument | padding
  deriving Repr, DecidableEq

abbrev PaddingJl (α : Type) := Except PaddingRouteError α

def reinterpret738ShowError (source target : String) : String :=
  s!"Padding of type {source} is not compatible with type {target}."

def setTrueRange (used : List Bool) (offset count : Nat) : List Bool :=
  (List.range count).foldl (fun result index => result.set (offset + index) true) used

def reinterpret756FillFields
    (recurse : Int → Nat → List Bool → PaddingJl (List Bool)) :
    List FieldLayoutModel → Nat → List Bool → PaddingJl (List Bool)
  | [], _, used => .ok used
  | field :: rest, offset, used => do
      let used ← recurse field.typeId (offset + field.offset) used
      reinterpret756FillFields recurse rest offset used

def reinterpret756FillNonpadding
    (recurse : Int → Nat → List Bool → PaddingJl (List Bool))
    (layout : LayoutInfoModel) (offset : Nat) (used : List Bool) :
    PaddingJl (List Bool) :=
  if layout.primitive then
    .ok (setTrueRange used offset ((layout.bitSize + 7) / 8))
  else reinterpret756FillFields recurse layout.fields offset used

def reinterpret747Nonpadding
    (fill : LayoutInfoModel → Nat → List Bool → PaddingJl (List Bool))
    (layout : LayoutInfoModel) : PaddingJl (List Bool) := do
  if layout.bitPadding then throw .argument
  let used := List.replicate layout.alignedSize false
  fill layout 0 used

def cycleSubpadding : List Bool → List Bool → Nat → Nat → Nat → Bool
  | _, _, _, _, 0 => true
  | source, target, sourceIndex, targetIndex, fuel + 1 =>
      if source.getD sourceIndex false && !target.getD targetIndex false then false
      else
        let sourceIndex := if sourceIndex + 1 ≥ source.length then 0 else sourceIndex + 1
        let targetIndex := if targetIndex + 1 ≥ target.length then 0 else targetIndex + 1
        if sourceIndex = 0 && targetIndex = 0 then true
        else cycleSubpadding source target sourceIndex targetIndex fuel

def reinterpret772ArraySubpadding (isPacked : LayoutInfoModel → Bool)
    (nonpadding : LayoutInfoModel → PaddingJl (List Bool))
    (source target : LayoutInfoModel) : PaddingJl Bool := do
  if isPacked target then return true
  if isPacked source then return false
  let sourceUsed ← nonpadding source
  let targetUsed ← nonpadding target
  if targetUsed.isEmpty then return true
  if sourceUsed.isEmpty then return false
  return cycleSubpadding sourceUsed targetUsed 0 0
    (sourceUsed.length * targetUsed.length + 1)

def reinterpret812StructSubpadding (nonpadding : LayoutInfoModel → PaddingJl (List Bool))
    (output input : LayoutInfoModel) : PaddingJl Bool := do
  let outputUsed ← nonpadding output
  let inputUsed ← nonpadding input
  pure (outputUsed == inputUsed)

def reinterpret816PackedSize (nonpadding : LayoutInfoModel → PaddingJl (List Bool))
    (layout : LayoutInfoModel) : PaddingJl Nat :=
  if !layout.datatypePadding then .ok layout.alignedSize
  else (nonpadding layout).map (·.count true)

def reinterpret824IsPacked (layout : LayoutInfoModel) : Bool := !layout.datatypePadding

def reinterpret828HasBitPadding (anyField : List FieldLayoutModel → Bool)
    (isUnion : LayoutInfoModel → Bool) (anyUnion : LayoutInfoModel → Bool)
    (layout : LayoutInfoModel) : Bool :=
  if layout.primitive then layout.bitSize % 8 != 0
  else if isUnion layout then anyUnion layout
  else anyField layout.fields

def ReinterpretPaddingMapCorrect : Prop :=
  (∀ source target, reinterpret738ShowError source target =
      s!"Padding of type {source} is not compatible with type {target}.") ∧
  (∀ recurse layout offset used, reinterpret756FillNonpadding recurse layout offset used =
      if layout.primitive then
        .ok (setTrueRange used offset ((layout.bitSize + 7) / 8))
      else reinterpret756FillFields recurse layout.fields offset used) ∧
  (∀ fill layout, reinterpret747Nonpadding fill layout = do
      if layout.bitPadding then throw .argument
      fill layout 0 (List.replicate layout.alignedSize false)) ∧
  (∀ packed nonpadding source target, reinterpret772ArraySubpadding packed nonpadding source target = do
      if packed target then return true
      if packed source then return false
      let sourceUsed ← nonpadding source
      let targetUsed ← nonpadding target
      if targetUsed.isEmpty then return true
      if sourceUsed.isEmpty then return false
      return cycleSubpadding sourceUsed targetUsed 0 0
        (sourceUsed.length * targetUsed.length + 1)) ∧
  (∀ nonpadding output input, reinterpret812StructSubpadding nonpadding output input = do
      let outputUsed ← nonpadding output
      let inputUsed ← nonpadding input
      pure (outputUsed == inputUsed)) ∧
  (∀ nonpadding layout, reinterpret816PackedSize nonpadding layout =
      if !layout.datatypePadding then .ok layout.alignedSize
      else (nonpadding layout).map (·.count true)) ∧
  (∀ layout, reinterpret824IsPacked layout = !layout.datatypePadding) ∧
  (∀ fields union unions layout, reinterpret828HasBitPadding fields union unions layout =
      if layout.primitive then layout.bitSize % 8 != 0
      else if union layout then unions layout else fields layout.fields)

theorem reinterpretPaddingMapCorrect : ReinterpretPaddingMapCorrect := by
  simp [ReinterpretPaddingMapCorrect, reinterpret738ShowError,
    reinterpret756FillNonpadding, reinterpret747Nonpadding,
    reinterpret772ArraySubpadding, reinterpret812StructSubpadding,
    reinterpret816PackedSize, reinterpret824IsPacked, reinterpret828HasBitPadding]

def overwriteBytes (output : List UInt8) (offset : Nat) (bytes : List UInt8) : List UInt8 :=
  output.take offset ++ bytes ++ output.drop (offset + bytes.length)

def reinterpret839CopyToPackedFields
    (recurse : Int → List UInt8 → PaddingJl (List UInt8)) :
    List FieldLayoutModel → List UInt8 → PaddingJl (List UInt8)
  | [], _input => .ok []
  | field :: rest, input => do
      let bytes ← if field.packed then
        pure ((input.drop field.offset).take field.size)
      else recurse field.typeId (input.drop field.offset)
      let tail ← reinterpret839CopyToPackedFields recurse rest input
      pure (bytes ++ tail)

def reinterpret839CopyToPacked
    (packedSize : LayoutInfoModel → Nat)
    (recurse : Int → List UInt8 → PaddingJl (List UInt8))
    (layout : LayoutInfoModel) (input : List UInt8) : PaddingJl (List UInt8) :=
  if layout.primitive then .ok (input.take (packedSize layout))
  else reinterpret839CopyToPackedFields recurse layout.fields input

def reinterpret859CopyFromPackedFields
    (recurse : Int → List UInt8 → PaddingJl (List UInt8)) :
    List FieldLayoutModel → List UInt8 → List UInt8 → Nat → PaddingJl (List UInt8)
  | [], _packed, output, _ => .ok output
  | field :: rest, packed, output, readOffset => do
      let fieldBytes ← if field.packed then pure ((packed.drop readOffset).take field.size)
        else recurse field.typeId (packed.drop readOffset)
      let output := overwriteBytes output field.offset fieldBytes
      reinterpret859CopyFromPackedFields recurse rest packed output (readOffset + fieldBytes.length)

def reinterpret859CopyFromPacked
    (packedSize : LayoutInfoModel → Nat)
    (recurse : Int → List UInt8 → PaddingJl (List UInt8))
    (layout : LayoutInfoModel) (packed : List UInt8) : PaddingJl (List UInt8) :=
  if layout.primitive then .ok (packed.take (packedSize layout))
  else reinterpret859CopyFromPackedFields recurse layout.fields packed
    (List.replicate layout.alignedSize 0) 0

def ReinterpretPackedCopiesCorrect : Prop :=
  (∀ size recurse layout input, reinterpret839CopyToPacked size recurse layout input =
      if layout.primitive then .ok (input.take (size layout))
      else reinterpret839CopyToPackedFields recurse layout.fields input) ∧
  (∀ size recurse layout packed, reinterpret859CopyFromPacked size recurse layout packed =
      if layout.primitive then .ok (packed.take (size layout))
      else reinterpret859CopyFromPackedFields recurse layout.fields packed
        (List.replicate layout.alignedSize 0) 0)

theorem reinterpretPackedCopiesCorrect : ReinterpretPackedCopiesCorrect := by
  simp [ReinterpretPackedCopiesCorrect, reinterpret839CopyToPacked,
    reinterpret859CopyFromPacked]

def reinterpret879Scalar
    (nonpadding : LayoutInfoModel → PaddingJl (List Bool))
    (structSubpadding : LayoutInfoModel → LayoutInfoModel → PaddingJl Bool)
    (paddingRoute : LayoutInfoModel → LayoutInfoModel → List UInt8 → PaddingJl (List UInt8))
    (output input : LayoutInfoModel) (bytes : List UInt8) : PaddingJl (List UInt8) := do
  if !output.isBits || !input.isBits then throw .argument
  if output.bitPadding || input.bitPadding then throw .argument
  let outputSize ← reinterpret816PackedSize nonpadding output
  let inputSize ← reinterpret816PackedSize nonpadding input
  if outputSize != inputSize then throw .argument
  let samePadding ← structSubpadding output input
  if (reinterpret824IsPacked input && reinterpret824IsPacked output) || samePadding then
    pure (bytes.take output.alignedSize)
  else paddingRoute output input bytes

def reinterpret910Padding
    (copyTo : LayoutInfoModel → List UInt8 → PaddingJl (List UInt8))
    (copyFrom : LayoutInfoModel → List UInt8 → PaddingJl (List UInt8))
    (output input : LayoutInfoModel) (bytes : List UInt8) : PaddingJl (List UInt8) :=
  if !input.fields.isEmpty && reinterpret824IsPacked output then copyTo input bytes
  else if !output.fields.isEmpty && reinterpret824IsPacked input then copyFrom output bytes
  else do
    let packed ← copyTo input bytes
    copyFrom output packed

def reinterpret934String (checkReadable : ReinterpretAccessJl Unit)
    (copyString : List UInt8 → String) (bytes : List UInt8) :
    Except ReinterpretAccessError String :=
  if bytes.isEmpty then .ok ""
  else do
    checkReadable
    pure (copyString bytes)

def ReinterpretScalarPaddingCorrect : Prop :=
  (∀ nonpadding same padding output input bytes,
      reinterpret879Scalar nonpadding same padding output input bytes = do
      if !output.isBits || !input.isBits then throw .argument
      if output.bitPadding || input.bitPadding then throw .argument
      let outputSize ← reinterpret816PackedSize nonpadding output
      let inputSize ← reinterpret816PackedSize nonpadding input
      if outputSize != inputSize then throw .argument
      let samePadding ← same output input
      if (reinterpret824IsPacked input && reinterpret824IsPacked output) || samePadding then
        pure (bytes.take output.alignedSize)
      else padding output input bytes) ∧
  (∀ to unpack output input bytes, reinterpret910Padding to unpack output input bytes =
      if !input.fields.isEmpty && reinterpret824IsPacked output then to input bytes
      else if !output.fields.isEmpty && reinterpret824IsPacked input then unpack output bytes
      else do let packed ← to input bytes; unpack output packed) ∧
  (∀ readable copy bytes, reinterpret934String readable copy bytes =
      if bytes.isEmpty then .ok "" else do readable; pure (copy bytes))

theorem reinterpretScalarPaddingCorrect : ReinterpretScalarPaddingCorrect := by
  simp [ReinterpretScalarPaddingCorrect, reinterpret879Scalar,
    reinterpret910Padding, reinterpret934String]

end JuliaLean.ArrayCov
