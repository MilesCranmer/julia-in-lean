import JuliaLean.base.uuid
import JuliaLean.base.strings.io

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

/-- `uuid_version(u)`, `UUIDs.jl:29`. -/
def uuid_version (u : UUID) : Nat := bn (JInt.rem .u8 (band (shr u.value 76) (JInt.lit .u128 0xf)))

/-- The RFC 4122 variant field: the two most significant bits of octet 8. -/
def uuid_variant (u : UUID) : Nat := (shr u.value 62).val.toNat % 4

/-- `_build_uuid1(rng, timestamp)` with `u = rand(rng, UInt128)`, `UUIDs.jl:71-89`. -/
def build_uuid1 (r : U128) (timestamp : U64) : UUID :=
  let u := band r (JInt.lit .u128 0x00000000000000003fffffffffffffff)
  let u := bor u (JInt.lit .u128 0x00000000000010008000010000000000)
  let ts_low := band timestamp (JInt.lit .u64 0xffffffff)
  let ts_mid := band (shr timestamp 32) (JInt.lit .u64 0xffff)
  let ts_hi := band (shr timestamp 48) (JInt.lit .u64 0x0fff)
  let u := bor u (shl (JInt.rem .u128 ts_low) 96)
  let u := bor u (shl (JInt.rem .u128 ts_mid) 80)
  let u := bor u (shl (JInt.rem .u128 ts_hi) 64)
  ⟨u⟩

/-- `uuid4(rng)` with `u = rand(rng, UInt128)`, `UUIDs.jl:116-121`. -/
def uuid4 (r : U128) : UUID :=
  let u := band r (JInt.lit .u128 0xffffffffffff0fff3fffffffffffffff)
  ⟨bor u (JInt.lit .u128 0x00000000000040008000000000000000)⟩

/-- `_build_uuid7(rng, timestamp)` with `bytes = rand(rng, UInt128)`, `UUIDs.jl:195-205`. -/
def build_uuid7 (r : U128) (timestamp : U128) : UUID :=
  let bytes := band r (JInt.lit .u128 0x0000000000000fff3fffffffffffffff)
  let bytes := bor bytes (JInt.lit .u128 0x00000000000070008000000000000000)
  ⟨bor bytes (shl timestamp 80)⟩

/-- The code units of a (valid) string given by its characters. -/
def utf8 (s : List Char) : List Byte := s.flatMap (fun c => utf8Enc c.toNat)

/-- The 16 big-endian bytes of `ns.value`, `UUIDs.jl:146-151`. -/
def nsBytes (ns : UUID) : List Byte :=
  ((List.range 16).foldl (fun (acc : List Byte × U128) _ =>
      let (bs, v) := acc
      (bs ++ [JInt.rem .u8 (shr v 120)], shl v 8)) ([], ns.value)).1

/-- The message `uuid5(ns, name)` passes to `SHA.sha1`, `UUIDs.jl:146-152`. -/
def uuid5Message (ns : UUID) (name : List Char) : Jle (List Byte) :=
  (unescape_string name).map (nsBytes ns ++ ·)

/-- The rest of `uuid5`, `UUIDs.jl:153-161`, applied to the digest `h` (20 bytes for
SHA-1); indexing a digest shorter than 16 bytes throws `BoundsError`. -/
def uuid5Finish (h : List Byte) : Jle UUID :=
  if h.length < 16 then .error (.jl .boundsError) else
  let h := h.set 6 (bor (band (h.getD 6 (b8 0)) (b8 0x0f)) (b8 0x50))
  let h := h.set 8 (bor (band (h.getD 8 (b8 0)) (b8 0x3f)) (b8 0x80))
  .ok ⟨(List.range 16).foldl (fun (v : U128) idx => bor (shl v 8) (JInt.rem .u128 (h.getD idx (b8 0))))
    (JInt.lit .u128 0)⟩

/-- `uuid5(ns, name)`, `UUIDs.jl:145-162`, for a hash function `sha1`. -/
def uuid5 (sha1 : List Byte → List Byte) (ns : UUID) (name : List Char) : Jle UUID :=
  (uuid5Message ns name).bind (fun msg => uuid5Finish (sha1 msg))

end JuliaLean.Base64Uuid
