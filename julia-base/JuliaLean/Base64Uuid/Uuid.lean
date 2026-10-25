import JuliaLean.Base64Uuid.Basic
import JuliaLean.ParsePrint.IntParse

/-!
Model of `base/uuid.jl` (`UUID`, `string`, `parse`/`tryparse`) and
`stdlib/UUIDs/src/UUIDs.jl` (`uuid_version`, `uuid1`, `uuid4`, `uuid5`, `uuid7`) at
master `bbfa0ce4150`, plus `unescape_string` (`base/strings/io.jl:535-590`), which
`uuid5` calls.

The random generators are modelled by their deterministic cores: `uuid4 r` and
`_build_uuid1 r ts`, `_build_uuid7 r ts` take the value `r = rand(rng, UInt128)` and
the timestamp as arguments, so properties quantify over every value the RNG and the
clock can produce. SHA-1 is not modelled: `uuid5` is split into the message it hashes
(`uuid5Message`) and the bit manipulation of the digest (`uuid5Finish`).

1.13.2 parses with a different implementation (a loop over `codeunit(s, i)` with
`__convert_digit`, `base/uuid.jl` at `v1.13.2`), which accepts the same strings.
-/

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

abbrev U128 := JInt .u128
abbrev U64 := JInt .u64

/-- `struct UUID; value::UInt128; end`, `base/uuid.jl:8-10`. -/
structure UUID where
  value : U128
  deriving Repr, DecidableEq

/-- `UUID(u::NTuple{2, UInt64})`, `base/uuid.jl:12`. -/
def UUID.ofPair (hi lo : U64) : UUID :=
  ⟨bor (shl (JInt.rem .u128 hi) 64) (JInt.rem .u128 lo)⟩

/-- `hex_chars`, `base/char.jl:308-311`: `'0':'9'` then `'a':'z'`. -/
def hex_chars : List Byte :=
  ((List.range 10).map (fun i => b8 (48 + i))) ++ ((List.range 26).map (fun i => b8 (97 + i)))

/-- `groupings = [36:-1:25; 23:-1:20; 18:-1:15; 13:-1:10; 8:-1:1]`, `base/uuid.jl:98`. -/
def groupings : List Nat :=
  (List.range 12).map (36 - ·) ++ (List.range 4).map (23 - ·) ++ (List.range 4).map (18 - ·) ++
    (List.range 4).map (13 - ·) ++ (List.range 8).map (8 - ·)

/-- `string(u::UUID)`, `base/uuid.jl:100-115`: a 36-byte string, filled from the last
hex digit backwards, then the four dashes. The initial contents of the fresh string
are never read (every position is stored), and are modelled as zeros. -/
def uuidString (u : UUID) : List Byte :=
  let (a, _) := groupings.foldl
    (fun (acc : List Byte × U128) (i : Nat) =>
      let (a, v) := acc
      (a.set (i - 1) (hex_chars.getD (bn (JInt.rem .u8 (band v (JInt.lit .u128 0xf)))) (b8 0)), shr v 4))
    (List.replicate 36 (b8 0), u.value)
  ((((a.set 8 (b8 45)).set 13 (b8 45)).set 18 (b8 45)).set 23 (b8 45))

/-- `takebytes(units, y, n)`, `base/uuid.jl:44-57`: the next `n` bytes as a
little-endian `UInt64` (first byte lowest), the remaining iteration, and whether there
were `n`. `units` is the not-yet-iterated rest of the code units. -/
def takebytes (units : List Byte) (n : Nat) : U64 × List Byte × Bool :=
  let rec go : Nat → Nat → U64 → List Byte → U64 × List Byte × Bool
    | 0, _, w, y => (w, y, true)
    | _ + 1, _, w, [] => (w, [], false)
    | m + 1, k, w, b :: y => go m (k + 1) (bor w (shl (JInt.rem .u64 b) (8 * k))) y
  go n 0 (JInt.lit .u64 0) units

/-- `parseuuid(units)`, `base/uuid.jl:62-79`; `none` is `Parsers.INVALID`. -/
def parseuuid (units : List Byte) : Option UUID :=
  let (a, y, ok1) := takebytes units 8
  let (b, y, ok2) := takebytes y 5
  let (c, y, ok3) := takebytes y 5
  let (d, y, ok4) := takebytes y 5
  let (e, y, ok5) := takebytes y 5
  let (f, y, ok6) := takebytes y 8
  if !(ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && y.isEmpty) then none else
  let m := JInt.lit .u64 0xff
  let dashes := bor (bor (bor (band b m) (shl (band c m) 8)) (shl (band d m) 16)) (shl (band e m) 24)
  if dashes != JInt.lit .u64 (45 * 0x01010101) then none else
  let w2 := bor (shr b 8) (shl (shr c 8) 32)
  let w3 := bor (shr d 8) (shl (shr e 8) 32)
  if !(IntParse.ishexdigits8 a && IntParse.ishexdigits8 w2 && IntParse.ishexdigits8 w3 &&
      IntParse.ishexdigits8 f) then none else
  some (UUID.ofPair (bor (shl (IntParse.hexdigits8 a) 32) (IntParse.hexdigits8 w2))
    (bor (shl (IntParse.hexdigits8 w3) 32) (IntParse.hexdigits8 f)))

/-- `tryparse(UUID, s)`, `base/uuid.jl:83-86`; `s` is given by its UTF-8 code units. -/
def tryparseUUID (s : List Byte) : Option UUID := parseuuid s

/-- `UUID(s)` = `parse(UUID, s)`, `base/uuid.jl:88-96`. -/
def parseUUID (s : List Byte) : Jle UUID :=
  match tryparseUUID s with
  | some u => .ok u
  | none => .error (argErr "Malformed UUID string")

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

/-- UTF-8 encoding of a code point `n ≤ 0x10ffff`, as `print(io, Char(n))` writes it
(`Char(::UInt32)`, `base/char.jl`); surrogates get their three-byte encoding. -/
def utf8Enc (n : Nat) : List Byte :=
  if n < 0x80 then [b8 n]
  else if n < 0x800 then [b8 (0xc0 + n / 64), b8 (0x80 + n % 64)]
  else if n < 0x10000 then [b8 (0xe0 + n / 4096), b8 (0x80 + n / 64 % 64), b8 (0x80 + n % 64)]
  else [b8 (0xf0 + n / 262144), b8 (0x80 + n / 4096 % 64), b8 (0x80 + n / 64 % 64), b8 (0x80 + n % 64)]

/-- The code units of a (valid) string given by its characters. -/
def utf8 (s : List Char) : List Byte := s.flatMap (fun c => utf8Enc c.toNat)

def isHexDigitC (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- The digit loop of the `\x`, `\u`, `\U` branch, `base/strings/io.jl:545-551`:
`(n, k, rest)` after reading at most `m` hex digits; `k` is the loop counter at exit. -/
def hexEscLoop (m : Nat) : Nat → Nat → List Char → Nat × Nat × List Char
  | n, k, a =>
    let k := k + 1
    if k ≤ m then
      match a with
      | [] => (n, k, a)
      | nc :: a' =>
        match isHexDigitC nc with
        | some d => hexEscLoop m (n * 16 + d) k a'
        | none => (n, k, a)
    else (n, k, a)

/-- The octal digit loop, `base/strings/io.jl:562-567`. -/
def octEscLoop : Nat → Nat → List Char → Nat × List Char
  | n, k, a =>
    let k := k + 1
    if k ≤ 3 then
      match a with
      | [] => (n, a)
      | c :: a' => if '0' ≤ c ∧ c ≤ '7' then octEscLoop (n * 8 + (c.toNat - '0'.toNat)) k a' else (n, a)
    else (n, a)

/-- `unescape_string(s)` with `keep = ()`, `base/strings/io.jl:535-590`: the bytes it
prints. The fuel is the number of characters left, which bounds the iterations. -/
def unescapeLoop : Nat → List Char → Jle (List Byte)
  | 0, _ => .ok []
  | _ + 1, [] => .ok []
  | fuel + 1, c :: a =>
    if !a.isEmpty && c == '\\' then
      match a with
      | [] => .ok []
      | c :: a =>
        if c == 'x' || c == 'u' || c == 'U' then
          let m := if c == 'x' then 2 else if c == 'u' then 4 else 8
          let (n, k, a) := hexEscLoop m 0 0 a
          if k == 1 || n > 0x10ffff then
            .error (argErr (if m == 2 then "invalid hex (\\x) escape sequence"
              else if m == 4 then "invalid unicode (\\u) escape sequence"
              else "invalid unicode (\\U) escape sequence"))
          else
            let out := if m == 2 then [b8 n] else utf8Enc n
            (unescapeLoop fuel a).map (out ++ ·)
        else if '0' ≤ c ∧ c ≤ '7' then
          let (n, a) := octEscLoop (c.toNat - '0'.toNat) 1 a
          if n > 255 then .error (argErr "octal escape sequence out of range")
          else (unescapeLoop fuel a).map ([b8 n] ++ ·)
        else
          let e : Option Nat :=
            if c == 'a' then some 7 else if c == 'b' then some 8 else if c == 't' then some 9
            else if c == 'n' then some 10 else if c == 'v' then some 11 else if c == 'f' then some 12
            else if c == 'r' then some 13 else if c == 'e' then some 27
            else if c == '\\' || c == '"' then some c.toNat else none
          match e with
          | none => .error (argErr "invalid escape sequence")
          | some e => (unescapeLoop fuel a).map (utf8Enc e ++ ·)
    else (unescapeLoop fuel a).map (utf8Enc c.toNat ++ ·)

def unescape_string (s : List Char) : Jle (List Byte) := unescapeLoop s.length s

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
