import JuliaLean.base.hashing
import JuliaLean.Registry.Types

/-!
# Properties of `base/hashing.jl`

The propositions state behavior promised by the `hash` docstring and the observable byte,
integer, floating-point, and compiler-node hashing invariants. Julia dispatch remains an interface.
-/

namespace JuliaLean.Proofs.base.hashing

open JuliaLean JuliaLean.Promotion JuliaLean.base.hashing JuliaLean.Registry

def HashRespectEq {α : Type} (eq : α → α → Bool) (hash : α → Word → Word) : Prop :=
  ∀ x y h, eq x y = true → hash x h = hash y h

def HashRespectEq32 {α : Type} (eq : α → α → Bool) (hash : α → Word32 → Word32) : Prop :=
  ∀ x y h, eq x y = true → hash x h = hash y h

def SmallIntegerHashConsistency : Prop :=
  (∀ x y : SmallInteger, ∀ h : Word, x.value = y.value →
    hashSmallInteger x h = hashSmallInteger y h) ∧
  (∀ x : JInt .i64, ∀ y : Word, ∀ h : Word, x.val = y.val →
    hashInt64 x h = hashUInt64 y h) ∧
  (∀ x : SmallInteger, ∀ y : JInt .i64, ∀ h : Word, x.value = y.val →
    hashSmallInteger x h = hashInt64 y h) ∧
  (∀ x : SmallInteger, ∀ y : Word, ∀ h : Word, x.value = y.val →
    hashSmallInteger x h = hashUInt64 y h)

def Float16HashConsistent : Prop :=
  ∀ x : Fl half, ∀ h : Word,
    hashFloat16 standardHashFloat16Ops x h =
      hashFloat64 standardHashFloat64Ops (standardHashFloat16Ops.toFloat64 x) h ∧
    (standardHashFloat16Ops.isfinite x = true →
      standardHashFloat16Ops.isequalI64 (standardHashFloat16Ops.fptosi x) x = true →
      hashFloat16 standardHashFloat16Ops x h =
        hashInt64 (standardHashFloat16Ops.fptosi x) h)

def integerAbs : Int → Int := fun x => Int.ofNat x.natAbs

def integerTopSetBit (x : Int) : Int :=
  if x = 0 then 0 else Int.ofNat (x.natAbs.log2 + 1)

def integerCeilDiv (x y : Int) : Int := x / y + if x % y = 0 then 0 else 1

def integerShiftRight (x : Int) (bits : Int) : Int := x / Int.ofNat (2 ^ bits.toNat)

def integerUInt8 (x : Int) : UInt8 := UInt8.ofNat (x.toNat % 256)

def integerUInt64 (x : Int) : Word := JInt.lit .u64 x

def integerUInt32 (x : Int) : Word32 := JInt.lit .u32 x

def codeUnitsForInt (x : Int) : IntegerCodeUnits Int :=
  integerCodeUnitsCtor integerAbs integerTopSetBit integerCeilDiv (fun a b => max a b) x

def IntegerCodeUnitsLittleEndian : Prop :=
  ∀ x : Int,
    let units := codeUnitsForInt x
    units.numBytes = Int.ofNat (max 1 ((x.natAbs.log2 + 8) / 8)) ∧
    lengthIntegerCodeUnits units = units.numBytes ∧
    (sizeIntegerCodeUnits units).1 = units.numBytes ∧
    (∀ i : Nat,
      getindexIntegerCodeUnits integerShiftRight integerUInt8 units (Int.ofNat (i + 1)) =
        UInt8.ofNat ((x.natAbs / 2 ^ (8 * i)) % 256)) ∧
    (∀ i : Nat,
      (loadLEArrayU64Units integerShiftRight integerUInt64 units (Int.ofNat (i + 1))).val =
        Int.ofNat ((x.natAbs / 2 ^ (8 * i)) % 2 ^ 64)) ∧
    (∀ i : Nat,
      (loadLEArrayU32Units integerShiftRight integerUInt32 units (Int.ofNat (i + 1))).val =
        Int.ofNat ((x.natAbs / 2 ^ (8 * i)) % 2 ^ 32))

def normalizedRealDecomposition {α : Type} (ops : RealHashOps α)
    (decomposition : Int × Int × Int) : Int × Int × Int := Id.run do
  let (num0, pow0, den0) := decomposition
  if num0 = 0 && den0 = 0 then return (0, 0, 0)
  if num0 = 0 then return (0, 0, if den0 > 0 then 1 else -1)
  if den0 = 0 then return (if num0 > 0 then 1 else -1, 0, 0)
  let (num, den) := if den0 < 0 then (-num0, -den0) else (num0, den0)
  let numZ := ops.trailingZeros num
  let denZ := ops.trailingZeros den
  (ops.shiftRight num numZ, pow0 + Int.ofNat numZ - Int.ofNat denZ,
    ops.shiftRight den denZ)

def RealHashIsequal : Prop :=
  ∀ (α : Type) (ops : RealHashOps α) (isequal : α → α → Bool)
    (x y : α) (h : Word),
    (∀ seed, ops.hashNaN seed = hashNaNCanonical seed) →
    (∀ sign seed, ops.hashSignedZero sign seed = hashSignedZeroCanonical sign seed) →
    (∀ sign seed, ops.hashInfinity sign seed = hashInfinityCanonical sign seed) →
    isequal x y = true →
    normalizedRealDecomposition ops (ops.decompose x) =
      normalizedRealDecomposition ops (ops.decompose y) →
    hashReal ops hashFloat64Canonical hashIntegerInt hashInt64 hashUInt64 x h =
      hashReal ops hashFloat64Canonical hashIntegerInt hashInt64 hashUInt64 y h

inductive IteratorEmits {State : Type} (iter : HashByteIterator State) :
    State → List UInt8 → Prop where
  | done {state : State} (h : iter.next state = none) : IteratorEmits iter state []
  | step {state : State} {byte : UInt8} {nextState : State} {rest : List UInt8}
      (hnext : iter.next state = some (byte, nextState))
      (hrest : IteratorEmits iter nextState rest) :
      IteratorEmits iter state (byte :: rest)

def IteratorEmitsBytes {State : Type} (iter : HashByteIterator State)
    (bytes : List UInt8) : Prop :=
  match iter.first with
  | none => bytes = []
  | some (byte, state) => ∃ rest, IteratorEmits iter state rest ∧ bytes = byte :: rest

def arrayBytes (arr : HashByteArray) : List UInt8 :=
  (List.range arr.length).map (fun i => arr.get (arr.firstIndex + Int.ofNat i))

def PointerLoadsMatchArray {Ptr : Type} (ops : HashPointerOps Ptr) (ptr : Ptr)
    (arr : HashByteArray) : Prop :=
  (∀ offset : Nat, 0 < offset →
    ops.load8 ptr offset = arr.get (arr.firstIndex + Int.ofNat (offset - 1))) ∧
  (∀ offset align : Nat, 0 < offset →
    loadLE ops.convert64 ops.add64 ops.pointerref64 ptr (Int.ofNat offset) align =
      loadLEArrayU64 arr (arr.firstIndex + Int.ofNat (offset - 1))) ∧
  (∀ offset align : Nat, 0 < offset →
    loadLE ops.convert32 ops.add32 ops.pointerref32 ptr (Int.ofNat offset) align =
      loadLEArrayU32 arr (arr.firstIndex + Int.ofNat (offset - 1)))

def HashBytePathAgreement : Prop :=
  (∀ (arr : HashByteArray) (seed : Word) (secret : HashSecret),
    (∀ (Ptr : Type) (ops : HashPointerOps Ptr) (ptr : Ptr) (alignment : Nat),
      PointerLoadsMatchArray ops ptr arr →
      hashBytesArray arr seed secret = hashBytesPointer ops ptr arr.length seed secret alignment)) ∧
  (∀ (State : Type) (arr : HashByteArray) (iter : HashByteIterator State) (seed : Word) (secret : HashSecret),
    IteratorEmitsBytes iter (arrayBytes arr) →
      hashBytesArray arr seed secret = hashBytesIterator iter seed secret)

def StringHashConsistency : Prop :=
  HashBytePathAgreement ∧
  (∀ (S State Char : Type) (ops : UTF8Iterator S State Char)
    (codeunitIsUInt8 : S → Bool) (codeunits : S → HashByteArray)
    (byteString charString : S) (h : Word),
    codeunitIsUInt8 byteString = true → codeunitIsUInt8 charString = false →
    IteratorEmitsBytes (utf8ByteIterator ops ⟨charString⟩)
      (arrayBytes (codeunits byteString)) →
    hashAbstractString ops codeunitIsUInt8 codeunits byteString h =
      hashAbstractString ops codeunitIsUInt8 codeunits charString h) ∧
  (∀ (S State Char Ptr : Type) (utf8Ops : UTF8Iterator S State Char)
    (pointerOps : HashPointerOps Ptr) (codeunitIsUInt8 : S → Bool)
    (codeunits : S → HashByteArray) (preserve : S → Word → Word)
    (pointer : S → Ptr) (sizeof : S → Nat) (sizeofInt : Nat) (data : S) (h : Word),
    codeunitIsUInt8 data = true → sizeof data = (codeunits data).length →
    PointerLoadsMatchArray pointerOps (pointer data) (codeunits data) →
    (∀ value, preserve data value = value) →
    hashString pointerOps preserve pointer sizeof sizeofInt data h =
      hashAbstractString utf8Ops codeunitIsUInt8 codeunits data h)

def AnnotatedStringHash : Prop :=
  ∀ (S A State Char : Type) (utf8Ops : UTF8Iterator S State Char)
    (codeunitIsUInt8 : S → Bool) (codeunits : S → HashByteArray)
    (parent : A → S) (annotationFree : A → Bool)
    (hashAnnotated : A → Word → Jl Word) (value : A) (h : Word),
    codeunitIsUInt8 (parent value) = false → annotationFree value = true →
    hashAnnotated value h = .ok
      (hashAbstractString utf8Ops codeunitIsUInt8 codeunits (parent value) h)

def IntegerHashSignMixing : Prop :=
  ∀ (x : Int) (h : Word), 0 < x →
    hashIntegerInt (-x) h = hashIntegerInt x (xorWord h (JInt.lit .u64 1))

def FieldHashEquivalent {X Y : Type} (ops : HashFieldOps X Y)
    (hash : Y → Word → Word) (x y : X) : Prop :=
  ops.fields x = ops.fields y ∧
  ∀ i, i < ops.fields x →
    ops.isdefined x (i + 1) = ops.isdefined y (i + 1) ∧
    (ops.isdefined x (i + 1) = true →
      ∀ h, hash (ops.getfield x (i + 1)) h = hash (ops.getfield y (i + 1)) h)

def StructuralHashIsequal : Prop :=
  (∀ (α : Type) (eq : α → α → Bool) (hash : α → Word → Word)
    (x y : α) (h : Word), HashRespectEq eq hash → eq x y = true →
      hashQuoteNode64 hash x h = hashQuoteNode64 hash y h) ∧
  (∀ (A B : Type) (eqA : A → A → Bool) (eqB : B → B → Bool)
    (hashA : A → Word → Word) (hashB : B → Word → Word)
    (edges edges' : A) (values values' : B) (h : Word),
    HashRespectEq eqA hashA → HashRespectEq eqB hashB →
    eqA edges edges' = true → eqB values values' = true →
    hashPhiNode64 hashA hashB edges values h =
      hashPhiNode64 hashA hashB edges' values' h) ∧
  (∀ (α : Type) (eq : α → α → Bool) (hash : α → Word → Word)
    (x y : α) (h : Word), HashRespectEq eq hash → eq x y = true →
      hashPhiCNode64 hash x h = hashPhiCNode64 hash y h) ∧
  (∀ (α : Type) (eq : α → α → Bool) (hash : α → Word32 → Word32)
    (x y : α) (h : Word32), HashRespectEq32 eq hash → eq x y = true →
      hashQuoteNode32 hash x h = hashQuoteNode32 hash y h) ∧
  (∀ (A B : Type) (eqA : A → A → Bool) (eqB : B → B → Bool)
    (hashA : A → Word32 → Word32) (hashB : B → Word32 → Word32)
    (edges edges' : A) (values values' : B) (h : Word32),
    HashRespectEq32 eqA hashA → HashRespectEq32 eqB hashB →
    eqA edges edges' = true → eqB values values' = true →
    hashPhiNode32 hashA hashB edges values h =
      hashPhiNode32 hashA hashB edges' values' h) ∧
  (∀ (α : Type) (eq : α → α → Bool) (hash : α → Word32 → Word32)
    (x y : α) (h : Word32), HashRespectEq32 eq hash → eq x y = true →
      hashPhiCNode32 hash x h = hashPhiCNode32 hash y h) ∧
  (∀ (H A Tags : Type) (eqHead : H → H → Bool) (eqArgs : A → A → Bool)
    (hashHead : H → Word → Word) (hashArgs : A → Word → Tags → Word)
    (head head' : H) (args args' : A) (tags : Tags) (arraySeed h : Word),
    HashRespectEq eqHead hashHead →
    (∀ a b seed, eqArgs a b = true → hashArgs a seed tags = hashArgs b seed tags) →
    eqHead head head' = true → eqArgs args args' = true →
    hashExpr head args hashHead hashArgs tags arraySeed h =
      hashExpr head' args' hashHead hashArgs tags arraySeed h) ∧
  (∀ (X Y : Type) (ops : HashFieldOps X Y) (hash : Y → Word → Word)
    (x y : X) (h : Word), FieldHashEquivalent ops hash x y →
    hashCodeInfo ops hash x h = hashCodeInfo ops hash y h ∧
    hashDebugInfo ops hash x h = hashDebugInfo ops hash y h) ∧
  (∀ (α : Type) (eq : α → α → Bool) (objectid : α → Word) (x y : α),
    eq x y = true → objectid x = objectid y → hashSymbol objectid x = hashSymbol objectid y) ∧
  (∀ (M N : Type) (eqM : M → M → Bool) (eqN : N → N → Bool)
    (hashM : M → Word → Word) (hashN : N → Word → Word)
    (x y : GlobalRef M N) (h : Word), HashRespectEq eqM hashM → HashRespectEq eqN hashN →
    eqM x.mod y.mod = true → eqN x.name y.name = true →
    hashGlobalRef hashM hashN x h = hashGlobalRef hashM hashN y h) ∧
  (∀ (T U F : Type) (eqT : T → T → Bool) (eqU : U → U → Bool) (eqF : F → F → Bool)
    (hashT : T → Word → Word) (hashU : U → Word → Word) (hashF : F → Word → Word)
    (x y : PartialStruct T U F) (h : Word),
    HashRespectEq eqT hashT → HashRespectEq eqU hashU → HashRespectEq eqF hashF →
    eqT x.typ y.typ = true → eqU x.undefs y.undefs = true → eqF x.fields y.fields = true →
    hashPartialStruct hashT hashU hashF x h = hashPartialStruct hashT hashU hashF y h)

/-! Nothing to promise:
- `hash(data::Any)@40`: selects the documented default seed, then dispatches to the two-argument method.
- `hash(w::WeakRef,h::UInt)@41`: forwards the weak reference's value to generic hash dispatch.
- `_jl_type_hash(T::Type)@44`: calls the Julia runtime type-hash intrinsic.
- `hash(T::Type,h::UInt)@45`: forwards the runtime type hash to UInt hashing.
- `hash(@nospecialize(data),h::UInt)@46`: the generic identity fallback delegates to objectid and UInt hashing.
- `mul_parts@48`, `hash_mix@52`, `hash_mix_linear@55`, `hash_finalizer@56`, `hash_64_64@63`, `hash_64_32@64`, `hash_32_32@65`: private hash primitives whose public behavior is covered by the numeric and byte-hash properties.
- `_hash_shl!@199`: internal shift adapter; generic Real hashing states its public value contract.
- `load_le@296`, `load_le_array(::Type{UInt64})@378`, `load_le_array(::Type{UInt32})@390`, `concat_shift@479`, `read_uint64_from_uint8_iter(iter,state)@484`, `read_uint64_from_uint8_iter(iter)@495`: byte-load helpers whose observable result is covered by `hashing-byte-path-equivalence`.
-/

private def entry (id : String) (juliaFns : List String) (statement source : String)
    (prop : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/hashing.jl", juliaFns := juliaFns,
    statement := statement, source := source, status := .todo, prop := prop }

def entries : List Entry := [
  entry "hashops-small-integer-hash"
    ["hash(::UInt64,::UInt)", "hash(::Int64,::UInt)",
     "hash(::Union{Bool,Int8,UInt8,Int16,UInt16,Int32,UInt32},::UInt)"]
    "For every seed, machine integers of widths through 64 bits with equal numeric values have equal hashes."
    "hash docstring base/hashing.jl:12-20; integer methods base/hashing.jl:75-77"
    ``SmallIntegerHashConsistency,
  entry "promotion-float16-hash-consistent"
    ["hash(::Float16,::UInt)", "hash(::Float64,::UInt)", "hash(::Int64,::UInt)"]
    "For every Float16 value and seed, its hash equals the hash of its Float64 conversion, and equals the Int64 hash whenever the value is an exactly equal finite Int64."
    "isequal hash contract; base/hashing.jl:165-196"
    ``Float16HashConsistent,
  entry "hashops-decomposed-real-hash"
    ["hash(::Real,::UInt)", "hash_integer", "decompose"]
    "Equal Real values with the same normalized decomposition have equal hashes for every seed, including zero, infinity, and NaN cases."
    "hash docstring base/hashing.jl:12-20; generic Real method base/hashing.jl:200-245"
    ``RealHashIsequal,
  entry "hashops-string-hash"
    ["hash(::AbstractString,::UInt)", "hash(::String,::UInt)", "utf8units", "iterate(::UTF8Units)", "codeunits"]
    "Valid byte-backed and character-iterated strings with the same UTF-8 byte sequence hash equally for every seed."
    "hash docstring base/hashing.jl:12-20; byte and string methods base/hashing.jl:101-145,378-473,509-654"
    ``StringHashConsistency,
  { id := "hashops-annotated-non8-hash", juliaFile := "base/hashing.jl",
    juliaFns := ["hash(::AbstractString,::UInt)", "iterate(::UTF8Units)", "hash(::AnnotatedString,::UInt)"],
    statement := "An annotation-free AnnotatedString over a non-UInt8 AbstractString hashes successfully and equals the hash of its isequal underlying string.",
    source := "hash docstring base/hashing.jl:12-20; AnnotatedString equality base/strings/annotated.jl:232-233",
    status := .todo, prop := ``AnnotatedStringHash,
    notes := "Existing reproducer: repro/hashops-annotated-non8-hash.jl." },
  entry "intfuncscov-hash-structural"
    ["hash(::QuoteNode,::UInt)", "hash(::PhiNode,::UInt)", "hash(::PhiCNode,::UInt)",
     "hash(::Expr,::UInt)", "hash(::CodeInfo,::UInt)", "hash(::DebugInfo,::UInt)",
     "hash(::Symbol)", "hash(::GlobalRef,::UInt)", "hash(::PartialStruct,::UInt)"]
    "Equal compiler-IR values hash equally for each seed when their field hash functions respect equality."
    "hash docstring base/hashing.jl:12-20; structural methods base/hashing.jl:251-293"
    ``StructuralHashIsequal,
  entry "hashing-integer-codeunits"
    ["IntegerCodeUnits(::Integer)", "size(::IntegerCodeUnits)", "length(::IntegerCodeUnits)",
     "getindex(::IntegerCodeUnits,::Int)", "load_le_array(::Type{UInt64},::IntegerCodeUnits,::Int)",
     "load_le_array(::Type{UInt32},::IntegerCodeUnits,::Int)", "codeunits(::Integer)"]
    "Integer code units contain the minimal whole-byte magnitude in little-endian order, including zero as one byte."
    "Integer code-unit comment and methods base/hashing.jl:79-99"
    ``IntegerCodeUnitsLittleEndian,
  entry "hashing-byte-path-equivalence"
    ["hash_bytes(::Ptr{UInt8},::Int,::UInt64,::NTuple{4,UInt64})",
     "hash_bytes(::AbstractArray{UInt8},::UInt64,::NTuple{4,UInt64})",
     "hash_bytes(iter,::UInt64,::NTuple{4,UInt64})", "load_le", "load_le_array",
     "concat_shift", "read_uint64_from_uint8_iter"]
    "Pointer, array, and iterator hashing return the same value for the same finite byte sequence and seed."
    "base/hashing.jl:296-647; 48-byte chunking and tail branches"
    ``HashBytePathAgreement,
  entry "hashing-integer-sign-mix"
    ["hash_integer", "_hash_integer"]
    "Hashing a positive integer's negative toggles the seed's low sign bit while preserving its magnitude-byte stream."
    "base/hashing.jl:147-159 (sign XOR and absolute-value byte stream)"
    ``IntegerHashSignMixing
]

/-! ## Method coverage

| Julia method | Registry property or Nothing to promise |
|---|---|
| `hash(data::Any)`@40 | Nothing to promise: selects the default seed for generic dispatch |
| `hash(w::WeakRef,h::UInt)`@41 | Nothing to promise: forwards to the referent hash |
| `_jl_type_hash(T::Type)`@44 | Nothing to promise: runtime intrinsic boundary |
| `hash(T::Type,h::UInt)`@45 | Nothing to promise: forwards the runtime type hash to UInt hashing |
| `hash(@nospecialize(data),h::UInt)`@46 | Nothing to promise: generic objectid fallback |
| `mul_parts`@48 | Nothing to promise: private multiplication primitive; consumers are covered below |
| `hash_mix`@52 | Nothing to promise: private multiplication/XOR primitive |
| `hash_mix_linear`@55 | Nothing to promise: private small-key mixer |
| `hash_finalizer`@56 | Nothing to promise: private UInt64 finalizer |
| `hash_64_64`@63 | Nothing to promise: dispatch-width adapter |
| `hash_64_32`@64 | Nothing to promise: dispatch-width adapter |
| `hash_32_32`@65 | Nothing to promise: dispatch-width adapter |
| `hash(::UInt64,::UInt)`@75 | `hashops-small-integer-hash` |
| `hash(::Int64,::UInt)`@76 | `hashops-small-integer-hash`, `promotion-float16-hash-consistent` |
| `hash(::Union{Bool,Int8,UInt8,Int16,UInt16,Int32,UInt32},::UInt)`@77 | `hashops-small-integer-hash` |
| `IntegerCodeUnits(::Integer)`@84 | `hashing-integer-codeunits` |
| `size(::IntegerCodeUnits)`@91 | `hashing-integer-codeunits` |
| `length(::IntegerCodeUnits)`@92 | `hashing-integer-codeunits` |
| `getindex(::IntegerCodeUnits,::Int)`@93 | `hashing-integer-codeunits` |
| `load_le_array(::Type{UInt64},::IntegerCodeUnits,::Int)`@94 | `hashing-integer-codeunits` |
| `load_le_array(::Type{UInt32},::IntegerCodeUnits,::Int)`@95 | `hashing-integer-codeunits` |
| `codeunits(::Integer)`@99 | `hashing-integer-codeunits` |
| `utf8units(::AbstractString)`@106 | `hashops-string-hash` |
| `iterate(::UTF8Units)`@109 | `hashops-string-hash` |
| `iterate(::UTF8Units,state)`@123 | `hashops-string-hash` |
| `hash_integer(::Integer,::UInt)`@147 | `hashing-integer-sign-mix` |
| `_hash_integer(::Integer,::UInt64,::NTuple{4,UInt64})`@148 | `hashing-integer-sign-mix` |
| `hash(::Float64,::UInt)`@165 | `promotion-float16-hash-consistent` |
| `hash(::Float32,::UInt)`@183 | `promotion-float16-hash-consistent` |
| `hash(::Float16,::UInt)`@185 | `promotion-float16-hash-consistent` |
| `_hash_shl!(x,n)`@199 | Nothing to promise: helper used by the generic Real method |
| `hash(::Real,::UInt)`@200 | `hashops-decomposed-real-hash` |
| `hash(::QuoteNode,::UInt)`@251 | `intfuncscov-hash-structural` |
| `hash(::PhiNode,::UInt)`@252 | `intfuncscov-hash-structural` |
| `hash(::PhiCNode,::UInt)`@253 | `intfuncscov-hash-structural` |
| `hash(::QuoteNode,::UInt)`@255 | `intfuncscov-hash-structural` |
| `hash(::PhiNode,::UInt)`@256 | `intfuncscov-hash-structural` |
| `hash(::PhiCNode,::UInt)`@257 | `intfuncscov-hash-structural` |
| `hash(::Expr,::UInt)`@260 | `intfuncscov-hash-structural` |
| `hash(::CodeInfo,::UInt)`@266 | `intfuncscov-hash-structural` |
| `hash(::DebugInfo,::UInt)`@274 | `intfuncscov-hash-structural` |
| `hash(::Symbol)`@282 | `intfuncscov-hash-structural` |
| `hash(::GlobalRef,::UInt)`@286 | `intfuncscov-hash-structural` |
| `hash(::PartialStruct,::UInt)`@287 | `intfuncscov-hash-structural` |
| `load_le(::Type{T},::Ptr{UInt8},i,align)`@296 | `hashing-byte-path-equivalence` |
| `hash_bytes(::Ptr{UInt8},::Int,::UInt64,::NTuple{4,UInt64})`@301 | `hashing-byte-path-equivalence` |
| `load_le_array(::Type{UInt64},::AbstractArray{UInt8},idx)`@378 | `hashing-byte-path-equivalence` |
| `load_le_array(::Type{UInt32},::AbstractArray{UInt8},idx)`@390 | `hashing-byte-path-equivalence` |
| `hash_bytes(::AbstractArray{UInt8},::UInt64,::NTuple{4,UInt64})`@399 | `hashing-byte-path-equivalence` |
| `concat_shift(::UInt64,::UInt64,::UInt8)`@479 | `hashing-byte-path-equivalence` |
| `read_uint64_from_uint8_iter(iter,state)`@484 | `hashing-byte-path-equivalence` |
| `read_uint64_from_uint8_iter(iter)`@495 | `hashing-byte-path-equivalence` |
| `hash_bytes(iter,::UInt64,::NTuple{4,UInt64})`@509 | `hashing-byte-path-equivalence` |
| `hash(::AbstractString,::UInt)`@649 | `hashops-string-hash` |
| `hash(::String,::UInt)`@652 | `hashops-string-hash` |

-/

end JuliaLean.Proofs.base.hashing
