import JuliaLean.stdlib.Base64.src.Base64

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

abbrev U32 := JInt .u32

/-- `POLY`, `src/crc32c.c:56`. -/
def POLY : U32 := JInt.lit .u32 0x82f63b78

/-- One step of `crc = crc & 1 ? (crc >> 1) ^ POLY : crc >> 1`, `src/crc32c.c:463`. -/
def crcBit (c : U32) : U32 :=
  if (band c (JInt.lit .u32 1)).val == 1 then bxor (shr c 1) POLY else shr c 1

/-- `crc32c_table[0][n]`, `src/crc32c.c:460-471`. -/
def crcTable0 (n : Nat) : U32 := Nat.repeat crcBit 8 (JInt.lit .u32 n)

/-- `crc = crc32c_table[0][(crc ^ *buf++) & 0xff] ^ (crc >> 8)`, `src/crc32c.c:434-437`. -/
def crcByte (c : U32) (b : Byte) : U32 :=
  bxor (crcTable0 (band (bxor c (JInt.rem .u32 b)) (JInt.lit .u32 0xff)).val.toNat) (shr c 8)

/-- `jl_crc32c(crc, buf, len)` on the bytes `xs`: `crc ^ 0xffffffff`, the byte loop,
and `^ 0xffffffff` again. -/
def jl_crc32c (crc : U32) (xs : List Byte) : U32 :=
  bxor (xs.foldl crcByte (bxor crc (JInt.lit .u32 0xffffffff))) (JInt.lit .u32 0xffffffff)

end JuliaLean.Base64Uuid
