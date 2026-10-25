import JuliaLean.HashOps.Proofs

/-! Deterministic differential rows, mirrored line by line by a Julia script. -/

namespace JuliaLean.HashOps.Validation

open JuliaLean JuliaLean.Promotion JuliaLean.HashOps

private def intPairs : List (Num × Num) := [
  (.int .i8 (JInt.lit .i8 (-1)), .int .i64 (JInt.lit .i64 (-1))),
  (.int .u8 (JInt.lit .u8 1), .int .u64 (JInt.lit .u64 1)),
  (.int .i16 (JInt.lit .i16 255), .int .u32 (JInt.lit .u32 255)),
  (.int .i32 (JInt.lit .i32 0), .int .u64 (JInt.lit .u64 0))]

private def textByte : Text := ⟨[104, 233], [0x68, 0xc3, 0xa9], true⟩
private def textChars : Text := ⟨[104, 233], [], false⟩

private def red : AnnotatedText := ⟨[120], [⟨1, 1⟩]⟩
private def blue : AnnotatedText := ⟨[120], [⟨1, 2⟩]⟩

def differential : IO Unit := do
  for ((a, b), i) in intPairs.zipIdx do
    IO.println s!"INT {i} {hashNum a .seed == hashNum b .seed}"
  IO.println s!"STRING {hashText textByte 0 == hashText textChars 0}"
  IO.println s!"ANNOTATED_ORDER {annotatedIsequal red blue} {annotatedIsless red blue} {annotatedIsless blue red} {annotatedCmp red blue}"
  let annotatedError := match hashNonByteAnnotated ⟨[104, 233], []⟩ 0 with
    | .error _ => true
    | .ok _ => false
  IO.println s!"ANNOTATED_HASH {annotatedError}"
  IO.println s!"ARRAY_SHORT {hashArray ⟨[(1, 7)], List.range 7⟩ 0 == hashArray ⟨[(1, 7)], List.range 7⟩ 0}"
  IO.println s!"ARRAY_MEDIUM {hashArray ⟨[(1, 8)], List.range 8⟩ 0 == hashArray ⟨[(1, 8)], List.range 8⟩ 0}"
  IO.println s!"DICT_PERM {dictHash [(1, 2), (3, 4)] 0 == dictHash [(3, 4), (1, 2)] 0}"
  IO.println s!"SET_PERM {setHash [1, 2, 3] 0 == setHash [3, 1, 2] 0}"
  IO.println s!"WIDEN_SUB {widenSub .u8 (JInt.lit .u8 0) (JInt.lit .u8 255)}"
  IO.println "COUNT 12"

end JuliaLean.HashOps.Validation
