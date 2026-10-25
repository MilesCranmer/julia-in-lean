import JuliaLean.Base64Uuid.Decode
import JuliaLean.Base64Uuid.Uuid
import JuliaLean.Base64Uuid.Crc

/-!
Properties of Base64, UUIDs and CRC32c promised by docstrings, the Base64 manual
(`stdlib/Base64/docs/src/index.md`), RFC 4122/9562, or obvious invariants.
-/

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

/-! ### Base64 -/

/-- `base64decode(base64encode(x)) == x` for every byte vector `x` that fits in memory
(fewer than `2^48` bytes; `read` returns at most `typemax(Int)` bytes). -/
def EncodeDecodeRoundtrip : Prop :=
  ∀ x : List Byte, x.length < 2 ^ 48 → base64decode (base64encode x) = some (.ok x)

/-- Writing the bytes of `x` to a `Base64EncodePipe` in any sequence of `write` calls
(single bytes or vectors) and closing it produces `base64encode(x)`. -/
def EncodeStreamSplit : Prop :=
  ∀ ops : List WriteOp, encodeStream ops = base64encode (ops.flatMap WriteOp.data)

/-- `read(pipe, k)` for each `k` in `ks`, then `read(pipe)`: the concatenated bytes. -/
def splitRead : List Nat → DPipe → Option (Jle (List Byte))
  | [], pipe => match readAll pipe with
    | none => none
    | some (.error e) => some (.error e)
    | some (.ok (b, _)) => some (.ok b)
  | k :: ks, pipe => match readN pipe k with
    | none => none
    | some (.error e) => some (.error e)
    | some (.ok (a, pipe)) => match splitRead ks pipe with
      | none => none
      | some (.error e) => some (.error e)
      | some (.ok b) => some (.ok (a ++ b))

/-- Reading a `Base64DecodePipe` in pieces, `read(pipe, k₁)`, ..., then `read(pipe)`,
yields the same bytes as `base64decode` of its source. -/
def DecodeStreamSplit : Prop :=
  ∀ (s : List Byte) (ks : List Nat) (x : List Byte),
    base64decode s = some (.ok x) → splitRead ks (DPipe.new s) = some (.ok x)

/-- `m` successive `read(pipe, UInt8)` calls. -/
def readBytesN : Nat → DPipe → Option (Jle DPipe)
  | 0, pipe => some (.ok pipe)
  | m + 1, pipe => match readByte pipe with
    | none => none
    | some (.error e) => some (.error e)
    | some (.ok (_, pipe)) => readBytesN m pipe

/-- `eof` docstring, `base/io.jl:211-213`: "it is always safe to read one byte after
seeing `eof` return `false`". -/
def EofThenReadByte : Prop :=
  ∀ (s : List Byte) (m : Nat) (pipe : DPipe),
    readBytesN m (DPipe.new s) = some (.ok pipe) → eof pipe = false →
      ∃ b pipe', readByte pipe = some (.ok (b, pipe'))

/-- `readbytes!(pipe, data, nb)` returns (normally or by throwing) for every source,
destination and count. -/
def ReadbytesTerminates : Prop :=
  ∀ (s : List Byte) (data : Vec) (nb : Int), ∃ fuel, readbytesF fuel (DPipe.new s) data nb ≠ none

/-- `readbytes!` docstring, `base/io.jl:1298-1299`: the size of `b` "will never be
decreased". -/
def ReadbytesNoShrink : Prop :=
  ∀ (s : List Byte) (data : Vec) (nb : Int) (fuel : Nat) (pipe : DPipe) (data' : Vec) (n : Nat),
    readbytesF fuel (DPipe.new s) data nb = some (.ok (pipe, data', n)) → data.len ≤ data'.len

/-- The alphabet and padding characters of `s`, the ones `decode` does not ignore. -/
def significant (s : List Byte) : List Byte := s.filter (fun c => decode c != CODE_IGN)

/-- The Base64 manual's notion of misplaced padding: some `'='` lies outside the last
two positions of the last group of four significant characters. -/
def misplacedPadding (s : List Byte) : Bool :=
  let cs := significant s
  let lastStart := (cs.length - 1) / 4 * 4
  (List.range cs.length).any (fun j =>
    bn (cs.getD j (b8 0)) == 61 && !(j ≥ lastStart && j % 4 ≥ 2))

/-- Base64 manual (`stdlib/Base64/docs/src/index.md`, master): "if the data has padding
outside of its specified location in the last 0-2 characters of the last group of four
alphabet characters ..., the data is rejected with `ArgumentError: malformed base64
sequence`." -/
def DecodeRejectsMidPadding : Prop :=
  ∀ s : List Byte, misplacedPadding s = true →
    base64decode s = some (.error (argErr "malformed base64 sequence"))

/-! ### UUIDs -/

/-- `UUID(string(u)) == u` for every `u`. -/
def UuidStringRoundtrip : Prop :=
  ∀ u : UUID, parseUUID (uuidString u) = .ok u

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

/-! ### CRC32c -/

/-- `crc32c(data2, crc32c(data1)) == crc32c([data1; data2])` (`CRC32c.jl:21-22`) for the
dense and the generic vector methods, which agree. -/
def Crc32cChunks : Prop :=
  ∀ (a b : List Byte) (crc : U32),
    crc32cDense b (crc32cDense a crc) = crc32cDense (a ++ b) crc ∧
    crc32cVec b (crc32cVec a crc) = crc32cVec (a ++ b) crc ∧
    crc32cVec a crc = crc32cDense a crc

/-- `crc32c(io, nb, crc)` checksums the next `min(nb, bytesavailable)` bytes and
consumes them; `crc32c(io, crc)` checksums all remaining bytes (`CRC32c.jl:60-68`). -/
def Crc32cIo : Prop :=
  ∀ (io : List Byte) (nb : Int) (crc : U32), 0 ≤ nb →
    crc32cIoNb io nb crc = .ok (crc32cDense (io.take nb.toNat) crc, io.drop nb.toNat) ∧
    (io.length < 2 ^ 63 → crc32cIo io crc = .ok (crc32cDense io crc, []))

/-- `crc32c(io::IOStream, crc)` checksums all remaining bytes of the file
(`CRC32c.jl:25-28`: "`crc32c(io, crc)` to checksum all the remaining bytes. Hence you can
do `open(crc32c, filename)`"). -/
def Crc32cStreamAll : Prop :=
  ∀ (f : IOStreamF) (crc : U32), f.pos ≤ f.content.length →
    crc32cIOStream f crc = .ok (crc32cDense (f.content.drop f.pos) crc)

end JuliaLean.Base64Uuid
