import JuliaLean.stdlib.UUIDs.src.UUIDs

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

/-- `uuid4` sets version 4 and the RFC 4122 variant for every random value. -/
def Uuid4Bits : Prop :=
  ∀ r : U128, uuid_version (uuid4 r) = 4 ∧ uuid_variant (uuid4 r) = 2

/-- `uuid1` sets version 1 and the RFC 4122 variant for every random value and time. -/
def Uuid1Bits : Prop :=
  ∀ (r : U128) (ts : U64), uuid_version (build_uuid1 r ts) = 1 ∧ uuid_variant (build_uuid1 r ts) = 2

/-- `uuid7` sets version 7 and the variant for every random value and every timestamp
that fits RFC 9562's 48-bit `unix_ts_ms` field. -/
def Uuid7Bits : Prop :=
  ∀ (r ts : U128), ts.val < 2 ^ 48 →
    uuid_version (build_uuid7 r ts) = 7 ∧ uuid_variant (build_uuid7 r ts) = 2

/-- `uuid5` sets version 5 and the variant, whatever the SHA-1 digest. -/
def Uuid5Bits : Prop :=
  ∀ (sha1 : List Byte → List Byte) (ns : UUID) (name : List Char) (u : UUID),
    uuid5 sha1 ns name = .ok u → uuid_version u = 5 ∧ uuid_variant u = 2

/-- RFC 4122 section 4.3, which the `uuid5` docstring cites: the hash input is the
namespace ID followed by the name (its UTF-8 code units). -/
def Uuid5HashesName : Prop :=
  ∀ (ns : UUID) (name : List Char), uuid5Message ns name = .ok (nsBytes ns ++ utf8 name)

end JuliaLean.Base64Uuid
