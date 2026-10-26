import JuliaLean.ArrayCov.ReinterpretConstruct
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry
open JuliaLean.ArrayCov

abbrev RAError (α : Type) := Except String α

def ra14 (showType : T → String) (source target culprit : T) : RAError Unit :=
  .error ("cannot reinterpret `" ++ showType source ++ "` as `" ++ showType target ++
    "`, type `" ++ showType culprit ++ "` is not a bits type")
def RA14Property : Prop := ∀ (T : Type) showType source target culprit,
  ra14 (showType : T → String) source target culprit =
    .error ("cannot reinterpret `" ++ showType source ++ "` as `" ++ showType target ++
      "`, type `" ++ showType culprit ++ "` is not a bits type")
theorem ra14Property : RA14Property := by unfold RA14Property; intros; rfl

def ra18 (showType : T → String) (source target : T) (message : String) : RAError Unit :=
  .error ("cannot reinterpret a zero-dimensional `" ++ showType source ++ "` array to `" ++
    showType target ++ "` which is of a " ++ message ++ " size")
def RA18Property : Prop := ∀ (T : Type) showType source target message,
  ra18 (showType : T → String) source target message =
    .error ("cannot reinterpret a zero-dimensional `" ++ showType source ++ "` array to `" ++
      showType target ++ "` which is of a " ++ message ++ " size")
theorem ra18Property : RA18Property := by unfold RA18Property; intros; rfl

def ra23 (showType : T → String) (source target : T) : RAError Unit :=
  .error ("cannot reinterpret a `" ++ showType source ++ "` array to `" ++ showType target ++
    "` which is a singleton type")
def RA23Property : Prop := ∀ (T : Type) showType source target,
  ra23 (showType : T → String) source target =
    .error ("cannot reinterpret a `" ++ showType source ++ "` array to `" ++ showType target ++
      "` which is a singleton type")
theorem ra23Property : RA23Property := by unfold RA23Property; intros; rfl

def ra27 (showType : T → String) (source target culprit : T) : RAError Unit :=
  .error ("cannot reinterpret a `" ++ showType source ++ "` array to `" ++ showType target ++
    "` because type `" ++ showType culprit ++ "` contains non-byte-aligned primitive fields")
def RA27Property : Prop := ∀ (T : Type) showType source target culprit,
  ra27 (showType : T → String) source target culprit =
    .error ("cannot reinterpret a `" ++ showType source ++ "` array to `" ++ showType target ++
      "` because type `" ++ showType culprit ++ "` contains non-byte-aligned primitive fields")
theorem ra27Property : RA27Property := by unfold RA27Property; intros; rfl

def RA73Property : Prop := ∀ subpadding source target array,
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
    pure ⟨array, array.rank, source, target, false,
      subpadding target source, subpadding source target⟩
theorem ra73Property : RA73Property := by unfold RA73Property; intros; rfl

def ra74 (showType : T → String) (showInt : I → String)
    (source target : T) (dim : I) : RAError Unit :=
  .error ("cannot reinterpret an `" ++ showType source ++ "` array to `" ++ showType target ++
    "` whose first dimension has size `" ++ showInt dim ++
    "`. The resulting array would have a non-integral first dimension.")
def RA74Property : Prop := ∀ (T I : Type) showType showInt source target dim,
  ra74 (showType : T → String) (showInt : I → String) source target dim =
    .error ("cannot reinterpret an `" ++ showType source ++ "` array to `" ++ showType target ++
      "` whose first dimension has size `" ++ showInt dim ++
      "`. The resulting array would have a non-integral first dimension.")
theorem ra74Property : RA74Property := by unfold RA74Property; intros; rfl

def ra80 (showType : T → String) (showAxis : A → String)
    (source target : T) (axis : A) : RAError Unit :=
  .error ("cannot reinterpret a `" ++ showType source ++ "` array to `" ++ showType target ++
    "` when the first axis is " ++ showAxis axis ++ ". Try reshaping first.")
def RA80Property : Prop := ∀ (T A : Type) showType showAxis source target axis,
  ra80 (showType : T → String) (showAxis : A → String) source target axis =
    .error ("cannot reinterpret a `" ++ showType source ++ "` array to `" ++ showType target ++
      "` when the first axis is " ++ showAxis axis ++ ". Try reshaping first.")
theorem ra80Property : RA80Property := by unfold RA80Property; intros; rfl

def RA107Property : Prop := ∀ subpadding source target array,
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
    pure ⟨array, rank, source, target, true,
      subpadding target source, subpadding source target⟩
theorem ra107Property : RA107Property := by unfold RA107Property; intros; rfl

def ra108 (showType : T → String) (size : T → String) (source target : T) : RAError Unit :=
  .error ("`reinterpret(reshape, T, a)` requires that one element size (got " ++ size target ++
    ") and the other (got " ++ size source ++ ") be an integer multiple of the other")
def RA108Property : Prop := ∀ (T : Type) showType size source target,
  ra108 (showType : T → String) (size : T → String) source target =
    .error ("`reinterpret(reshape, T, a)` requires that one element size (got " ++ size target ++
      ") and the other (got " ++ size source ++ ") be an integer multiple of the other")
theorem ra108Property : RA108Property := by unfold RA108Property; intros; rfl

def ra113 (message : A → T → String) (a : A) (target : T) : RAError Unit :=
  .error (message a target)
def RA113Property : Prop := ∀ (A T : Type) message a target,
  ra113 (message : A → T → String) a target = .error (message a target)
theorem ra113Property : RA113Property := by unfold RA113Property; intros; rfl

def ra119 (message : S → T → String) (source : S) (target : T) : RAError Unit :=
  .error (message source target)
def RA119Property : Prop := ∀ (S T : Type) message source target,
  ra119 (message : S → T → String) source target = .error (message source target)
theorem ra119Property : RA119Property := by unfold RA119Property; intros; rfl

private def raConstructEntry (line : Nat) (fn statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-reinterpretarray-line{line}", juliaFile := "base/reinterpretarray.jl",
    juliaFns := [fn], statement, source, status := .proven, prop, thm := some thm }

def reinterpretConstructReviewEntries : List Entry := [
  raConstructEntry 14 "throwbits" "throwbits always throws ArgumentError with the source, target, and non-bits culprit in order." "base/reinterpretarray.jl:14-17" ``RA14Property ``ra14Property,
  raConstructEntry 18 "throwsize0" "throwsize0 always throws the zero-dimensional element-size ArgumentError." "base/reinterpretarray.jl:18-22" ``RA18Property ``ra18Property,
  raConstructEntry 23 "throwsingleton" "throwsingleton always throws the singleton-target ArgumentError." "base/reinterpretarray.jl:23-26" ``RA23Property ``ra23Property,
  raConstructEntry 27 "throwbitpadding" "throwbitpadding always throws the non-byte-aligned-field ArgumentError with the culprit type." "base/reinterpretarray.jl:27-31" ``RA27Property ``ra27Property,
  raConstructEntry 73 "reinterpret(::Type,::AbstractArray)" "Non-reshape reinterpret performs every bits, padding, size, divisibility, and axis check in source order before constructing the view." "base/reinterpretarray.jl:73-103" ``RA73Property ``ra73Property,
  raConstructEntry 74 "thrownonint" "thrownonint always throws the non-integral-first-dimension ArgumentError." "base/reinterpretarray.jl:74-79" ``RA74Property ``ra74Property,
  raConstructEntry 80 "throwaxes1" "throwaxes1 always throws the non-one-based-first-axis ArgumentError." "base/reinterpretarray.jl:80-84" ``RA80Property ``ra80Property,
  raConstructEntry 107 "reinterpret(reshape,::Type,::AbstractArray)" "Reshaping reinterpret preserves all bits and padding checks, element-size branches, rank changes, first-axis validation, and view flags." "base/reinterpretarray.jl:107-144" ``RA107Property ``ra107Property,
  raConstructEntry 108 "throwintmult" "throwintmult always throws the incompatible-element-size ArgumentError." "base/reinterpretarray.jl:108-112" ``RA108Property ``ra108Property,
  raConstructEntry 113 "throwsize1" "throwsize1 always throws the required-first-axis ArgumentError produced from its array and target." "base/reinterpretarray.jl:113-118" ``RA113Property ``ra113Property,
  raConstructEntry 119 "throwfromsingleton" "throwfromsingleton always throws the singleton-source ArgumentError." "base/reinterpretarray.jl:119-123" ``RA119Property ``ra119Property
]

end JuliaLean.MultidimCov
