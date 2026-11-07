import JuliaLean.stdlib.Base64.src.decode
import JuliaLean.Proofs.base.uuid.Props
import JuliaLean.Proofs.stdlib.UUIDs.src.UUIDs.Props
import JuliaLean.Proofs.stdlib.CRC32c.src.CRC32c.Props

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

end JuliaLean.Base64Uuid
