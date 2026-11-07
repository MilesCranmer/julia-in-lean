import JuliaLean.base.hashing
import JuliaLean.base.int
import JuliaLean.base.strings.string
import JuliaLean.base.strings.substring
import JuliaLean.base.strings.io
import JuliaLean.Runtime.Strings

/-!
# Callee bindings for `base/hashing.jl`: strings and byte paths

Bindings of the records the installed hashing model leaves as callbacks for string hashing (Julia
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`):
* `String` (`JStr`): pointer loads of its bytes (`hash(::String)`, hashing.jl:652-654, here
  `hashStringBound`, the one `hash(::String)` adapter, also used by `base/strings/lazy.lean`) and its
  `codeunits` array (`hash(::AbstractString)` for a `UInt8` code unit, hashing.jl:649-650);
* `SubString{String}`: the installed `substring.hashSubString` with that pointer
  (strings/substring.jl:203-204);
* any other `AbstractString`: the program's own interface methods (`ncodeunits`, `codeunit`,
  `iterate`) are typed parameters, and `UTF8Units` (hashing.jl:107-145) decodes each `Char`
  through the installed `reinterpret(UInt32, ::Char)` (the raw `Char` bits, `base/char.jl`) and
  `bswap(::UInt32)` (`int.bswap`).

`hashAbstractString` returns `Option Word`: `none` when the string's `iterate` never ends (the chunk
loop `hashIteratorChunks` of hash_bytes(iter, ...) is a `partial_fixpoint`).
-/

namespace JuliaLean.Bindings.base.hashing

open JuliaLean
open JuliaLean.base.hashing

/-! ## 1. `String` and `SubString{String}` pointers -/

/-- A `Ptr{UInt8}` into a `String`'s bytes: the string and a byte offset from `pointer(s)`. -/
structure StringPtr where
  string : JuliaLean.Strings.JStr
  offset : Int

/-- `unsafe_load(ptr, index)`: the byte at `pointer + index - 1`. -/
def stringPtrByte (ptr : StringPtr) (index : Nat) : UInt8 :=
  ptr.string.bytes.getD (ptr.offset + Int.ofNat index - 1).toNat 0

/-- `pointerref(Ptr{UInt32/UInt64}, index, align)` on a little-endian machine. -/
def stringPtrWord (ptr : StringPtr) (index width : Nat) : Int :=
  (List.range width).foldl (fun word byteIndex =>
    word + Int.ofNat (stringPtrByte ptr (index + byteIndex)).toNat * 2 ^ (8 * byteIndex)) 0

def addStringPtr (ptr : StringPtr) (offset : Int) : StringPtr :=
  { ptr with offset := ptr.offset + offset }

/-- The pointer reads of `hash_bytes(::Ptr{UInt8}, ...)` (hashing.jl:296-299, 509-647) on a
`String`'s bytes; `convert(Ptr{T}, ptr)` keeps the address. -/
def stringPointerOps : HashPointerOps StringPtr where
  Ptr32 := StringPtr
  Ptr64 := StringPtr
  convert32 := id
  convert64 := id
  add32 := addStringPtr
  add64 := addStringPtr
  load8 := stringPtrByte
  pointerref32 := fun ptr index _ => JInt.wrap .u32 (stringPtrWord ptr index 4)
  pointerref64 := fun ptr index _ => JInt.wrap .u64 (stringPtrWord ptr index 8)

/-- `hash(data::String, h)` (hashing.jl:652-654): `pointer(data)`, `sizeof(data)` bytes, and the
alignment `sizeof(Int) = 8` of a `String`'s data. `GC.@preserve` does not change the value. -/
def hashStringBound (s : JuliaLean.Strings.JStr) (h : Word) : Word :=
  JuliaLean.base.hashing.hashString stringPointerOps (fun _ value => value)
    (fun value => ⟨value, 0⟩) (fun value => value.bytes.length) 8 s h

/-- `pointer(::String)` and pointer addition for the installed `SubString` hash. -/
def subStringPointerOps : JuliaLean.base.strings.substring.PointerOps JuliaLean.Strings.JStr where
  Pointer := StringPtr
  pointer := fun s => ⟨s, 0⟩
  add := fun ptr offset => addStringPtr ptr offset.val

/-- `hash(data::SubString{String}, h)` (strings/substring.jl:203-204): `sizeof` of a
`SubString{String}` is its `ncodeunits`, and `hash_bytes` uses its default alignment 1. -/
def subStringHashOps : JuliaLean.base.strings.substring.HashOps JuliaLean.Strings.JStr where
  Secret := HashSecret
  pointerOps := subStringPointerOps
  sizeof := fun s => s.ncodeunits
  secret := hashSecret
  hashBytes := fun _ ptr n h secret => hashBytesPointer stringPointerOps ptr n.val.toNat h secret

def hashSubStringBound (s : JuliaLean.base.strings.substring.SubString JuliaLean.Strings.JStr)
    (h : Word) : Word :=
  JuliaLean.base.strings.substring.hashSubString subStringHashOps h s

/-- A valid `SubString{String}`: its code units lie inside the parent. -/
def ValidSubString (s : JuliaLean.base.strings.substring.SubString JuliaLean.Strings.JStr) : Prop :=
  0 ≤ s.offset.val ∧ 0 ≤ s.ncodeunits.val ∧
    s.offset.val + s.ncodeunits.val ≤ s.string.bytes.length

/-- The bytes of `String(s)` for a `SubString{String}`. -/
def subStringBytes (s : JuliaLean.base.strings.substring.SubString JuliaLean.Strings.JStr) :
    List UInt8 :=
  (s.string.bytes.drop s.offset.val.toNat).take s.ncodeunits.val.toNat

/-! ## 2. `hash(::AbstractString)` (hashing.jl:649-650) for every string type

A string type's own methods are the `AbstractString` interface (strings/basic.jl): its code-unit
type, `ncodeunits`, `codeunit(s, i)` and `iterate`. -/

/-- The interface methods of a program's `AbstractString` type `S` with iteration state `St`.
`codeunit` is consulted only when `codeunitIsUInt8` holds (`codeunit(::Type{S}) <: UInt8`). -/
structure StringMethods (S St : Type) where
  codeunitIsUInt8 : Bool
  ncodeunits : S → Nat
  codeunit : S → Int → UInt8
  iterate : S → Option (JuliaLean.base.char.JChar × St)
  iterateFrom : S → St → Option (JuliaLean.base.char.JChar × St)

/-- `codeunits(s)` (strings/basic.jl:788-789) as the array `hash_bytes` reads: indices
`1:ncodeunits(s)`, `getindex(s::CodeUnits, i) = codeunit(s.s, i)` (strings/basic.jl:1672). -/
def codeunitsArray {S St : Type} (methods : StringMethods S St) (s : S) : HashByteArray :=
  { firstIndex := 1, length := methods.ncodeunits s, get := methods.codeunit s }

/-- `UTF8Units(s)` iteration (hashing.jl:107-145): the program's `iterate`, then
`bswap(reinterpret(UInt32, char))`. `reinterpret(UInt32, ::Char)` returns the `Char`'s raw bits
(`base/char.jl`; the installed `JChar` is those bits). -/
def utf8Iterator {S St : Type} [Inhabited St] (methods : StringMethods S St) (s : S) :
    UTF8Iterator S St JuliaLean.base.char.JChar where
  string := s
  defaultState := default
  first := methods.iterate
  next := methods.iterateFrom
  reinterpretUInt32 := fun c => JInt.wrap .u32 (Int.ofNat c.toNat)
  bswapUInt32 := JuliaLean.base.int.bswap

/-- `hash(data::AbstractString, h)` for a program's string type; `none` if its `iterate` never
ends. -/
def hashAbstractStringBound {S St : Type} [Inhabited St] (methods : StringMethods S St) (s : S)
    (h : Word) : Option Word :=
  JuliaLean.base.hashing.hashAbstractString (utf8Iterator methods s)
    (fun _ => methods.codeunitIsUInt8) (codeunitsArray methods) s h

/-- `String`'s own methods: `codeunit(::String) = UInt8` and `iterate(::String, i)`, the installed
`strings.string.stringIterate` (strings/string.jl:508-538).
`invoke(hash, Tuple{AbstractString, UInt}, s, h)` runs `hashAbstractStringBound stringMethods`. -/
def stringMethods : StringMethods JuliaLean.Strings.JStr (JInt .i64) where
  codeunitIsUInt8 := true
  ncodeunits := fun s => s.bytes.length
  codeunit := fun s i => s.bytes.getD (i - 1).toNat 0
  iterate := fun s => JuliaLean.base.strings.string.stringIterate s (JInt.lit .i64 1)
  iterateFrom := JuliaLean.base.strings.string.stringIterate

/-- The bytes `UTF8Units` emits for the characters `iterate` returns: each character's UTF-8
encoding as `write(io, ::Char)` emits it (the installed `strings.io.charUtf8Bytes`, io.jl:973-980,
the same `bswap(reinterpret(UInt32, c))` low-byte-first loop). -/
inductive IteratedBytes {S St : Type} (methods : StringMethods S St) (s : S) :
    Option (JuliaLean.base.char.JChar × St) → List UInt8 → Prop where
  | done : IteratedBytes methods s none []
  | step {c : JuliaLean.base.char.JChar} {state : St} {rest : List UInt8} :
      IteratedBytes methods s (methods.iterateFrom s state) rest →
      IteratedBytes methods s (some (c, state))
        (JuliaLean.base.strings.io.charUtf8Bytes c ++ rest)

/-- The UTF-8 byte sequence of a string: its code units when they are bytes, otherwise the
encoding of the characters it iterates. -/
def Utf8BytesOf {S St : Type} (methods : StringMethods S St) (s : S) (bytes : List UInt8) : Prop :=
  if methods.codeunitIsUInt8 then
    (List.range (methods.ncodeunits s)).map (fun i => methods.codeunit s (Int.ofNat i + 1)) = bytes
  else IteratedBytes methods s (methods.iterate s) bytes

/-! ## 3. Restated properties -/

/-- `hashing-byte-path-equivalence`, restated over the three byte paths Julia reaches: the
`String` pointer path (alignment 8), the `SubString{String}` pointer path (alignment 1), and the
`UTF8Units` iterator path of a string type without byte code units, each against the array
path over the same bytes. -/
def HashBytePathAgreementBound : Prop :=
  (∀ (s : JuliaLean.Strings.JStr) (h : Word),
    hashStringBound s h = hashBytesArray (codeunitsArray stringMethods s) h hashSecret) ∧
  (∀ (s : JuliaLean.base.strings.substring.SubString JuliaLean.Strings.JStr) (h : Word)
    (small : (subStringBytes s).length < 2 ^ 62),
    ValidSubString s →
      hashSubStringBound s h =
        hashBytesArray (codeunitsArray stringMethods ⟨subStringBytes s, small⟩) h hashSecret) ∧
  (∀ (S St : Type) [Inhabited St] (methods : StringMethods S St) (u : S)
    (s : JuliaLean.Strings.JStr) (h : Word),
    methods.codeunitIsUInt8 = false → Utf8BytesOf methods u s.bytes →
      hashUTF8Units (utf8Iterator methods u) ⟨u⟩ h hashSecret =
        some (hashBytesArray (codeunitsArray stringMethods s) h hashSecret))

/-- `hashops-string-hash`, restated: strings of any type with the same UTF-8 bytes have the same
hash for every seed, `hash(::String)` agrees with the generic `AbstractString` method, and a
`SubString{String}` hashes as its `String` copy. -/
def StringHashConsistencyBound : Prop :=
  HashBytePathAgreementBound ∧
  (∀ (S St : Type) [Inhabited St] (methods : StringMethods S St) (u : S)
    (s : JuliaLean.Strings.JStr) (h : Word),
    Utf8BytesOf methods u s.bytes →
      hashAbstractStringBound methods u h = some (hashStringBound s h)) ∧
  (∀ (s : JuliaLean.Strings.JStr) (h : Word),
    hashAbstractStringBound stringMethods s h = some (hashStringBound s h)) ∧
  (∀ (s : JuliaLean.base.strings.substring.SubString JuliaLean.Strings.JStr) (h : Word)
    (small : (subStringBytes s).length < 2 ^ 62),
    ValidSubString s → hashSubStringBound s h = hashStringBound ⟨subStringBytes s, small⟩ h)

/-! ## 4. Evaluated checks (Julia values on 1.13.2 and nightly) -/

section Checks

/-- `"hé∀😀"` as bytes. -/
private def sample : JuliaLean.Strings.JStr :=
  ⟨[0x68, 0xc3, 0xa9, 0xe2, 0x88, 0x80, 0xf0, 0x9f, 0x98, 0x80], by decide⟩

/-- `UTF32String(['h', 'é', '∀', '😀'])`: a program string type with `UInt32` code units that
iterates a `Vector{Char}` (the raw `Char` bits of each character). -/
private def utf32Methods : StringMethods (List JuliaLean.base.char.JChar) Nat where
  codeunitIsUInt8 := false
  ncodeunits := List.length
  codeunit := fun _ _ => 0
  iterate := fun cs => cs[0]?.map fun c => (c, 1)
  iterateFrom := fun cs i => cs[i]?.map fun c => (c, i + 1)

-- invoke(hash, Tuple{AbstractString, UInt}, s, h) == hash(s, h): the codeunits array path and the
-- String pointer path
example : hashAbstractStringBound stringMethods sample (JInt.lit .u64 0) =
    some (hashStringBound sample (JInt.lit .u64 0)) := by decide +kernel
example : hashAbstractStringBound stringMethods sample (JInt.lit .u64 0xffffffffffffffff) =
    some (hashStringBound sample (JInt.lit .u64 0xffffffffffffffff)) := by decide +kernel
-- hash(SubString(s), h) == hash(s, h)
example : hashSubStringBound ⟨sample, JInt.lit .i64 0, JInt.lit .i64 10⟩ (JInt.lit .u64 0) =
    hashStringBound sample (JInt.lit .u64 0) := by decide +kernel
-- hash(UTF32String(Char[]), 3) == hash("", 3)
example : hashAbstractStringBound utf32Methods [] (JInt.lit .u64 3) =
    some (hashStringBound ⟨[], by decide⟩ (JInt.lit .u64 3)) := by decide +kernel
-- hash(UTF32String(['h', 'é', '∀', '😀']), h) == hash("hé∀😀", h): the UTF8Units iterator path.
-- Its ten bytes take one step of the chunk loop (the second read is short), unfolded once
-- through the fixpoint equation.
example : hashAbstractStringBound utf32Methods [0x68000000, 0xc3a90000, 0xe2888000, 0xf09f9880]
    (JInt.lit .u64 0) = some (hashStringBound sample (JInt.lit .u64 0)) := by
  simp only [hashAbstractStringBound, hashAbstractString, hashBytesDispatch, hashUTF8Units,
    hashBytesIterator]
  unfold hashIteratorChunks
  decide +kernel

end Checks

end JuliaLean.Bindings.base.hashing
