import JuliaLean.Serialization.Model

/-!
Differential checks of the model against Julia. The expected bytes are what
`serialize(io, x)` wrote on Julia 1.15.0-DEV.126 (master `bbfa0ce4150`), with the
8-byte header removed; each value also decodes
back to itself with nothing left over.
-/

namespace JuliaLean.Serialization.Validation

open JuliaLean JuliaLean.Serialization

/-- The bytes `serialize(Serializer(io), x)` writes. -/
def enc (x : V) : Bytes := (ser ES.init x).1

/-- `deserialize(serialize(x))` returns `x` and consumes the whole stream. -/
def rt (x : V) : Bool :=
  match deserialize (serialize x) with
  | .ok (.v y, []) => y == x
  | _ => false

-- (1, 2)
example : enc (.tup [.int .i64 1, .int .i64 2]) = [0x14, 0x02, 0xe0, 0xe1] := by decide
-- "abc", "abcdefgh"
example : enc (.str [97, 98, 99]) = [0x21, 0x03, 0x61, 0x62, 0x63] := by decide
example : enc (.str [97, 98, 99, 100, 101, 102, 103, 104]) =
    [0x39, 0x21, 0x08, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68] := by decide
-- :abc, :abcdefghi
example : enc (.sym [97, 98, 99]) = [0x01, 0x03, 0x61, 0x62, 0x63] := by decide
example : enc (.sym [97, 98, 99, 100, 101, 102, 103, 104, 105]) =
    [0x01, 0x09, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69] := by decide
-- Int32(5), 5, 100, 2^40, Int32(-1), -1
example : enc (.int .i32 5) = [0xc3] := by decide
example : enc (.int .i64 5) = [0xe4] := by decide
example : enc (.int .i64 100) = [0x31, 0x64, 0x00, 0x00, 0x00] := by decide
example : enc (.int .i64 (2 ^ 40)) = [0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00] := by decide
example : enc (.int .i32 (-1)) = [0x06, 0xff, 0xff, 0xff, 0xff] := by decide
example : enc (.int .i64 (-1)) = [0x31, 0xff, 0xff, 0xff, 0xff] := by decide
-- 'a', '\xc0', true, nothing
example : enc (.char 0x61000000) = [0x0f, 0x61] := by decide
example : enc (.char 0xc0000000) = [0x0f, 0xc0] := by decide
example : enc (.bool true) = [0x4d] := by decide
example : enc .nothing = [0x4e] := by decide
-- Any[1, :x]
example : enc (.anyvec [some (.int .i64 1), some (.sym [120])]) =
    [0x15, 0x46, 0xe1, 0xe0, 0x7d] := by decide
-- [1, 2]
example : enc (.ivec .i64 [1, 2]) = [0x15, 0x00, 0x08, 0xe1, 0x01, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] := by decide
-- Bool[1, 0, 0], UInt8[1, 2]
example : enc (.bvec [true, false, false]) = [0x15, 0x45, 0xe2, 0x81, 0x02] := by decide
example : enc (.ivec .u8 [1, 2]) = [0x15, 0xe1, 0x01, 0x02] := by decide
-- Ref{Any}(1)
example : enc (.refv (some (.int .i64 1))) = [0x35, 0x10, 0x01, 0x08, 0x52, 0x65, 0x66, 0x56,
    0x61, 0x6c, 0x75, 0x65, 0x1f, 0x4e, 0x9e, 0x44, 0x01, 0x00, 0x00, 0x00, 0x46, 0xe0] := by decide
-- 1:3
example : enc (.urange 1 3) = [0x34, 0x10, 0x01, 0x09, 0x55, 0x6e, 0x69, 0x74, 0x52, 0x61,
    0x6e, 0x67, 0x65, 0x1f, 0x4e, 0x9e, 0x44, 0x01, 0x00, 0x00, 0x00, 0x00, 0x08, 0xe0,
    0xe2] := by decide
-- (a = 1, b = "x")
example : enc (.ntup [[97], [98]] [.int .i64 1, .str [120]]) = [0x34, 0x10, 0x01, 0x0a,
    0x4e, 0x61, 0x6d, 0x65, 0x64, 0x54, 0x75, 0x70, 0x6c, 0x65, 0x1f, 0x4e, 0x9b, 0x44, 0x02,
    0x00, 0x00, 0x00, 0x14, 0x02, 0x66, 0x67, 0x10, 0x53, 0x1f, 0x4e, 0x9b, 0x44, 0x02, 0x00,
    0x00, 0x00, 0x00, 0x08, 0x00, 0x21, 0xe0, 0x21, 0x01, 0x78] := by decide
-- :(f(x))
example : enc (.expr [99, 97, 108, 108] [.sym [102], .sym [120]]) =
    [0x16, 0x02, 0x56, 0x6b, 0x7d] := by decide
-- (Int8(1), 0x0002, 1.5f0, Float16(1.0))
example : enc (.tup [.int .i8 1, .int .u16 2, .flt .f32 0x3fc00000, .flt .f16 0x3c00]) =
    [0x14, 0x04, 0x02, 0x01, 0x05, 0x02, 0x00, 0x0d, 0x00, 0x00, 0xc0, 0x3f, 0x0c, 0x00,
      0x3c] := by decide

/-- Values with sharing, cycles, interned symbols and types, and length boundaries. -/
def corpus : List V := [
  .tup [.int .i64 1, .int .i64 2], .str [97, 98, 99, 100, 101, 102, 103, 104], .sym [97, 98, 99, 100, 101, 102, 103, 104, 105],
  .tup [.sym [97, 98, 99, 100, 101, 102, 103, 104, 105], .sym [97, 98, 99, 100, 101, 102, 103, 104, 105], .sym [103, 101, 116, 105, 110, 100, 101, 120]],
  .int .i128 (-(2 ^ 127)), .int .u128 (2 ^ 128 - 1), .int .i64 (2 ^ 31), .int .i64 (-(2 ^ 31) - 1),
  .int .i64 (-(2 ^ 31)), .int .i32 32, .int .i32 33, .int .i64 33, .int .u8 255, .int .i16 (-1),
  .flt .f64 0x7ff8000000000001, .flt .f16 0x8000, .char 0xf09f9880, .char 0xc3a90000,
  .anyvec [none, some (.back 0), some (.str [108, 111, 110, 103, 101, 114, 32, 116, 104, 97, 110, 32, 115, 101, 118, 101, 110])],
  .tup [.anyvec [], .back 0, .back 0],
  .refv (some (.back 0)), .refv none,
  .tup [.refv (some (.int .i64 1)), .refv (some (.int .i64 2)), .back 0],
  .expr [98, 108, 111, 99, 107] [.expr [99, 97, 108, 108] [.back 0], .str [97, 98, 99, 100, 101, 102, 103, 104, 105, 106], .back 2],
  .bvec ((List.replicate 130 true) ++ [false]), .bvec [], .ivec .i32 [-1, 0, 7], .ivec .u8 [],
  .urange 5 (-2), .tup [.urange 0 1, .urange (2 ^ 40) 3],
  .ntup [] [], .ntup [[97, 98, 99, 100, 101, 102, 103, 104, 105, 106]] [.sym [97, 98, 99, 100, 101, 102, 103, 104, 105, 106]],
  .tup [.ntup [[97]] [.bool true], .ntup [[97]] [.bool false]],
  .str (List.replicate 255 0x61), .str (List.replicate 256 0x61),
  .sym (List.replicate 255 0x61), .sym (List.replicate 256 0x61),
  .tup (List.replicate 255 .nothing), .tup (List.replicate 256 .nothing),
  .expr [99, 97, 108, 108] (List.replicate 256 (.int .i64 0)),
  .tup [.sym [95, 114, 101, 115, 101, 114, 118, 101, 100, 95], .sym []]]

example : corpus.all rt = true := by decide +kernel

end JuliaLean.Serialization.Validation
