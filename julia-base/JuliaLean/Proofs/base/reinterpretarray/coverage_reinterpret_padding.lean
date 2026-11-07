import JuliaLean.base.reinterpretarray
import JuliaLean.Core
import JuliaLean.Proofs.base.reinterpretarray.coverage_reinterpret_access

namespace JuliaLean.ArrayCov

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
