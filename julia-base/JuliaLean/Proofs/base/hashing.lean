import JuliaLean.base.hashing
import JuliaLean.Registry.Types
import JuliaLean.base.operators
import JuliaLean.Bindings.base.hashing

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
      some (hashBytesArray arr seed secret) = hashBytesIterator iter seed secret)

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
    some (hashString pointerOps preserve pointer sizeof sizeofInt data h) =
      hashAbstractString utf8Ops codeunitIsUInt8 codeunits data h)

def AnnotatedStringHash : Prop :=
  ∀ (S A State Char : Type) (utf8Ops : UTF8Iterator S State Char)
    (codeunitIsUInt8 : S → Bool) (codeunits : S → HashByteArray)
    (parent : A → S) (annotationFree : A → Bool)
    (hashAnnotated : A → Word → Jl Word) (value : A) (h : Word),
    codeunitIsUInt8 (parent value) = false → annotationFree value = true →
    ∀ hash, hashAbstractString utf8Ops codeunitIsUInt8 codeunits (parent value) h = some hash →
      hashAnnotated value h = .ok hash

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

end JuliaLean.Proofs.base.hashing

namespace JuliaLean.Proofs.base.hashing

open JuliaLean JuliaLean.Promotion JuliaLean.base.hashing

/-!
This candidate uses the frozen source-mirrored hash definitions. The native machine
model is the 64-bit UInt model declared at JuliaLean/base/hashing.lean:5-8; both
explicit 32-bit compiler-node source arms are separately inventoried in the TSV.
No historic proposal is imported, and no frozen definition is replaced.

The closed numeric records below supply actual installed callee definitions to the
existing hashFloat64/hashFloat16 interfaces. They contain no laws, hash results,
postconditions, or copies of a hash algorithm. In particular they do not use the
incorrect cmpIF .eq slots of standardHashFloat64Ops / standardHashFloat16Ops:
Julia's isequal distinguishes the signs of zero, whereas == does not.
-/

/-- Source-selected integer/IEEE-float isequal, including the sign test.
Julia source: base/operators.jl:202; base/float.jl:636-691,702-704;
  base/int.jl:182-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Verbatim Julia subject:
```
isequal(x::Real,          y::AbstractFloat) = (isnan(x) & isnan(y)) | signequal(x, y) & (x == y)::Bool
```
Callees: base/operators.lean:214-223; base/float.lean:2189-2195,2239,2248;
  base/int.lean:1448-1467; base/float.lean:155.
-/
def integerFloatIsequal {T : JuliaLean.base.float.FTy} {t : IntTy} (n : JInt t) (x : JuliaLean.base.float.FV T) : Bool :=
  JuliaLean.base.operators.isequalRealFloat
    JuliaLean.base.float.isnan_Number
    (JuliaLean.base.float.isnan_IEEEFloat (T := T))
    JuliaLean.base.int.signbit
    (JuliaLean.base.float.signbit_float (T := T))
    (JuliaLean.base.float.eq_IF (Tf := T) (Ti := t)) n x

/-- Callee instantiation for the unchanged hash(::Float64) body.
Julia source: base/hashing.jl:165-181; base/float.jl:636-705
  @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Every field below calls its installed source-mirrored primitive or dispatch:
base/float.lean:58,81-83,155,2171-2187,2207-2213,2239,2258-2259.
-/
def float64Calls : FloatHashOps (FV .f64) where
  leIntFloat := JuliaLean.base.float.le_IF (Tf := .f64) (Ti := .i64)
  ltFloatInt := JuliaLean.base.float.lt_FI (Tf := .f64) (Ti := .i64)
  leUIntFloat := JuliaLean.base.float.le_IF (Tf := .f64) (Ti := .u64)
  ltFloatUInt := JuliaLean.base.float.lt_FI (Tf := .f64) (Ti := .u64)
  fptosi := JuliaLean.base.float.fptosi .i64 (T := .f64)
  fptoui := JuliaLean.base.float.fptoui .u64 (T := .f64)
  isequalI64 := integerFloatIsequal (T := .f64) (t := .i64)
  isequalU64 := integerFloatIsequal (T := .f64) (t := .u64)
  isnan := JuliaLean.base.float.isnan_IEEEFloat (T := .f64)
  isfinite := JuliaLean.base.float.isfinite_IEEEFloat (T := .f64)
  bitcastU64 := JuliaLean.base.float.bitcast_from_float .u64 (T := .f64)

/-- Callee instantiation for the unchanged hash(::Float16) body.
Julia source: base/hashing.jl:185-196; base/float.jl:347,681,702-705
  @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Callees: base/float.lean:58,81,1146,2189-2195,2239,2258-2259;
  base/operators.lean:214-223.
-/
def float16Calls : Float16HashOps (FV .f16) where
  isfinite := JuliaLean.base.float.isfinite_IEEEFloat (T := .f16)
  isnan := JuliaLean.base.float.isnan_IEEEFloat (T := .f16)
  fptosi := JuliaLean.base.float.fptosi .i64 (T := .f16)
  isequalI64 := integerFloatIsequal (T := .f16) (t := .i64)
  toFloat64 := JuliaLean.base.float.Float64_Float16
  bitcastFloat64U64 := JuliaLean.base.float.bitcast_from_float .u64 (T := .f64)

end JuliaLean.Proofs.base.hashing

namespace JuliaLean.Proofs.base.hashing.Round1

open JuliaLean.Proofs.base.hashing
open JuliaLean JuliaLean.Promotion JuliaLean.base.hashing

/-- Every pair of equal-valued Bool or machine integers through 64 bits has equal hashes for every UInt seed.
Julia source: base/hashing.jl:75-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/hashing.jl:11-25; base/operators.jl:134-137;
  doc/src/base/base.md:154; doc/src/manual/mathematical-operations.md:344-350
  @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
The four conjuncts cover every distinct dispatch pairing; equal same-type Int64
or UInt64 values are identical inputs. SmallInteger includes Bool and all six
signed/unsigned widths through 32. No value/range/conversion law is assumed.
-/
def NativeIntegerHashConsistency : Prop :=
  (∀ x y : SmallInteger, ∀ h : Word, x.value = y.value →
    hashSmallInteger x h = hashSmallInteger y h) ∧
  (∀ x : JInt .i64, ∀ y h : Word, x.val = y.val →
    hashInt64 x h = hashUInt64 y h) ∧
  (∀ x : SmallInteger, ∀ y : JInt .i64, ∀ h : Word, x.value = y.val →
    hashSmallInteger x h = hashInt64 y h) ∧
  (∀ x : SmallInteger, ∀ y h : Word, x.value = y.val →
    hashSmallInteger x h = hashUInt64 y h)

/-- Every Float16 hashes as its exact Float64 conversion and as every isequal Int64, for every seed.
Julia source: base/hashing.jl:165-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/hashing.jl:11-25; base/operators.jl:145-150,202;
  doc/src/manual/mathematical-operations.md:321-350
  @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
All Float16 bit patterns are included: both zeros, subnormals, infinities, and all
NaNs. Integer equality uses the actual isequal model, not an assumed hash law or
the hash method's chosen truncation as the only permitted comparison integer.
-/
def Float16HashPromotion : Prop :=
  ∀ (x : FV .f16) (h : Word),
    hashFloat16 float16Calls x h =
      hashFloat64 float64Calls (JuliaLean.base.float.Float64_Float16 x) h ∧
    (∀ n : JInt .i64, integerFloatIsequal (T := .f16) n x = true →
      hashFloat16 float16Calls x h = hashInt64 n h)

/-- Float64 hashing respects isequal for all Float64 values and both 64-bit integer types at every seed.
Julia source: base/hashing.jl:75-76,165-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/hashing.jl:11-25; base/operators.jl:145-150,201-203;
  doc/src/manual/mathematical-operations.md:321-350
  @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
No finite-only or in-range assumption excludes the exceptional IEEE values.
The native smaller-integer pairings follow together with NativeIntegerHashConsistency;
the generic Real cross-type contract remains explicitly blocked in the TSV.
-/
def Float64HashConsistency : Prop :=
  (∀ (x y : FV .f64) (h : Word),
    JuliaLean.base.float.isequal_IEEEFloat (T := .f64) x y = true →
      hashFloat64 float64Calls x h = hashFloat64 float64Calls y h) ∧
  (∀ (x : FV .f64) (n : JInt .i64) (h : Word),
    integerFloatIsequal (T := .f64) n x = true → hashFloat64 float64Calls x h = hashInt64 n h) ∧
  (∀ (x : FV .f64) (n h : Word),
    integerFloatIsequal (T := .f64) n x = true → hashFloat64 float64Calls x h = hashUInt64 n h)

/-- Hashing any String through its specialized pointer method agrees with invoking the generic AbstractString method.
Julia source: base/hashing.jl:649-654 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/hashing.jl:11-25; doc/src/base/base.md:154;
  doc/src/manual/strings.md:27-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Both subjects below are the installed source-mirrored public hash definitions.
Their callees are the installed Bindings/base/hashing.lean:34-68,112-145 adapters,
not premises saying the pointer or array has the required hash. JStr carries its
machine-realizable byte-length bound. Malformed UTF-8 is included: this property
relates the two byte routes on every String, without requiring decoding success.
The wider all-AbstractString contract keeps its own blocked existing ID.
-/
def StringSpecializedGenericAgreement : Prop :=
  ∀ (s : JuliaLean.Strings.JStr) (h : Word),
    some (hashString JuliaLean.Bindings.base.hashing.stringPointerOps
      (fun _ value => value) (fun (value : JuliaLean.Strings.JStr) => ⟨value, 0⟩)
      (fun (value : JuliaLean.Strings.JStr) => value.bytes.length) 8 s h) =
    hashAbstractString
      (JuliaLean.Bindings.base.hashing.utf8Iterator
        JuliaLean.Bindings.base.hashing.stringMethods s)
      (fun _ => true)
      (JuliaLean.Bindings.base.hashing.codeunitsArray
        JuliaLean.Bindings.base.hashing.stringMethods) s h

/-! ## Individual public forwarding/plumbing dispositions

* hash(data::Any)@40 selects HASH_SEED and forwards to the two-argument dispatch.
  The docstring's warning about optional arguments explains this selection; an
  equality with hashAny's own callback body would add no independent property.
* hash(w::WeakRef,h::UInt)@41 forwards w.value to the same hash dispatch. WeakRef
  lifetime/identity and the callee's equal-value promise are not assumed here.
* hash(T::Type,h::UInt)@45 forwards the runtime type hash to UInt hashing. The
  runtime binding remains incomplete, but this wrapper adds no independent rule.
* hash(@nospecialize(data),h::UInt)@46 forwards objectid(data) to UInt hashing.
  Native objectid DOES exist in src/builtins_identity_c.lean:852-883; the pure
  unconstrained objectid slot in hashFallback is not itself that effectful binding.
* size(units::IntegerCodeUnits)@91 directly returns the stored one-dimensional
  length tuple. Relating that stored value to the actual integer's magnitude is
  retained under hashing-integer-codeunits; a tuple-field equation is plumbing.
* length(units::IntegerCodeUnits)@92 directly returns num_bytes. The minimal-byte
  and zero-length contract remains under hashing-integer-codeunits, rather than
  a vacuous equation against the same stored field.
* hash(x::Float32,h::UInt)@183 forwards through the exact installed
  float.Float64_Float32 conversion to the Float64 method. The conversion includes
  infinities, NaNs and signed zero; no separate wrapper-body equation is registered.
* hash(x::Symbol)@282 directly forwards objectid(x). Its observable identity hash
  callee exists in native form, but this one-line forwarding wrapper adds no
  independent property. Compiler-field consistency remains a retained blocker.

Inventory: 55 explicit named methods, all six 32/64 conditional IR definitions,
and three optional-argument generated forwarders (at148,296,301): 58 rows.
There are no local runtime function definitions. The i -> forms in @nexprs at486
and500 are anonymous-function syntax consumed by the macro, not installed
anonymous methods: cartesian.jl:141-159 inlines them into 8 and 7 expression blocks.
The const hash_uint64/hash_uint assignments at67-73 do not create new methods.

The historical five-declaration iterator patch, stringIterate correction, and
single String adapter migration ARE present in the frozen input. The six-kind
Real proposal is not installed. Neither a historical acceptance nor an installed
Prop is an approved statement ID; all nine inherited IDs remain unapproved.
-/

end JuliaLean.Proofs.base.hashing.Round1

namespace JuliaLean.Proofs.base.hashing

open JuliaLean.Registry

end JuliaLean.Proofs.base.hashing

namespace JuliaLean.ChatGPT.Batch4.Group21

open JuliaLean JuliaLean.Promotion JuliaLean.base.hashing
open JuliaLean.Proofs.base.hashing

theorem hashLitSelf {t : IntTy} (x : JInt t) : JInt.lit t x.val = x := by
  apply Subtype.ext
  exact wrapInt_of_inRange t x.val x.property

theorem hashSmallIntegerRange (x : SmallInteger) :
    IntTy.i64.min ≤ x.value ∧ x.value ≤ IntTy.i64.max := by
  cases x with
  | boolean b => cases b <;> decide
  | @fixed t x width =>
      change IntTy.i64.min ≤ x.val ∧ x.val ≤ IntTy.i64.max
      have hx := x.property
      change t.min ≤ x.val ∧ x.val ≤ t.max at hx
      cases t <;>
        simp only [IntTy.bits] at width <;>
        simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hx ⊢ <;> omega

/-- hashops-small-integer-hash -/
theorem HashopsSmallIntegerHash_proven : JuliaLean.Proofs.base.hashing.SmallIntegerHashConsistency := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y h hxy
    unfold hashSmallInteger
    rw [hxy]
  · intro x y h hxy
    unfold hashInt64
    rw [hxy, hashLitSelf]
  · intro x y h hxy
    unfold hashSmallInteger
    rw [hxy, hashLitSelf]
  · intro x y h hxy
    unfold hashSmallInteger hashInt64
    have hx : (JInt.lit .i64 x.value).val = x.value :=
      wrapInt_of_inRange .i64 x.value (hashSmallIntegerRange x)
    rw [hx, hxy, hashLitSelf]

/-- hashing-integer-sign-mix -/
theorem HashingIntegerSignMix_proven : JuliaLean.Proofs.base.hashing.IntegerHashSignMixing := by
  intro x h hx
  have hneg : -x < 0 := by omega
  have hnot : ¬ x < 0 := by omega
  simp only [hashIntegerInt, hashInteger, _hashInteger, hneg, hnot,
    decide_true, decide_false, Bool.false_eq_true,
    ite_true, ite_false, intMagnitudeModel, Int.natAbs_neg]

/-- hashops-small-integer-hash-v2 -/
theorem HashopsSmallIntegerHashV2_proven : JuliaLean.Proofs.base.hashing.Round1.NativeIntegerHashConsistency :=
  HashopsSmallIntegerHash_proven


theorem hashCodeUnits_numBytes (x : Int) :
    (codeUnitsForInt x).numBytes = Int.ofNat (max 1 ((x.natAbs.log2 + 8) / 8)) := by
  change max (integerCeilDiv (integerTopSetBit (Int.ofNat x.natAbs)) 8) 1 = _
  by_cases hx : x.natAbs = 0
  · rw [hx]
    decide
  · have hzero : (Int.ofNat x.natAbs : Int) ≠ 0 := by
      simp only [Int.ofNat_eq_natCast] at *
      omega
    unfold integerTopSetBit integerCeilDiv
    rw [if_neg hzero]
    change max (((Int.ofNat (x.natAbs.log2 + 1)) / 8) +
      (if (Int.ofNat (x.natAbs.log2 + 1)) % 8 = 0 then 0 else 1)) 1 = _
    simp only [Int.ofNat_eq_natCast] at *
    split <;> omega

theorem hashCodeUnits_shiftIndex (i : Nat) :
    8 * (Int.ofNat (i + 1) - 1) = Int.ofNat (8 * i) := by
  simp only [Int.ofNat_eq_natCast]
  omega

theorem hashCodeUnits_byte (x : Int) (i : Nat) :
    getindexIntegerCodeUnits integerShiftRight integerUInt8 (codeUnitsForInt x)
      (Int.ofNat (i + 1)) = UInt8.ofNat ((x.natAbs / 2 ^ (8 * i)) % 256) := by
  unfold getindexIntegerCodeUnits integerShiftRight integerUInt8
  rw [hashCodeUnits_shiftIndex]
  change UInt8.ofNat (((Int.ofNat x.natAbs / Int.ofNat (2 ^ (8 * i))).toNat) % 256) = _
  simp only [Int.ofNat_eq_natCast]
  rw [← Int.natCast_ediv]
  rfl

theorem hashCodeUnits_word64 (x : Int) (i : Nat) :
    (loadLEArrayU64Units integerShiftRight integerUInt64 (codeUnitsForInt x)
      (Int.ofNat (i + 1))).val = Int.ofNat ((x.natAbs / 2 ^ (8 * i)) % 2 ^ 64) := by
  unfold loadLEArrayU64Units integerShiftRight integerUInt64
  rw [hashCodeUnits_shiftIndex]
  change (JInt.lit .u64 (Int.ofNat x.natAbs / Int.ofNat (2 ^ (8 * i)))).val = _
  simp only [Int.ofNat_eq_natCast]
  rw [← Int.natCast_ediv]
  change Int.ofNat (x.natAbs / 2 ^ (8 * i)) % (Int.ofNat (2 ^ 64)) = _
  simpa only [Int.ofNat_eq_natCast] using (Int.natCast_emod (x.natAbs / 2 ^ (8 * i)) (2 ^ 64)).symm

theorem hashCodeUnits_word32 (x : Int) (i : Nat) :
    (loadLEArrayU32Units integerShiftRight integerUInt32 (codeUnitsForInt x)
      (Int.ofNat (i + 1))).val = Int.ofNat ((x.natAbs / 2 ^ (8 * i)) % 2 ^ 32) := by
  unfold loadLEArrayU32Units integerShiftRight integerUInt32
  rw [hashCodeUnits_shiftIndex]
  change (JInt.lit .u32 (Int.ofNat x.natAbs / Int.ofNat (2 ^ (8 * i)))).val = _
  simp only [Int.ofNat_eq_natCast]
  rw [← Int.natCast_ediv]
  change Int.ofNat (x.natAbs / 2 ^ (8 * i)) % (Int.ofNat (2 ^ 32)) = _
  simpa only [Int.ofNat_eq_natCast] using (Int.natCast_emod (x.natAbs / 2 ^ (8 * i)) (2 ^ 32)).symm

theorem HashingIntegerCodeunits_proven : JuliaLean.Proofs.base.hashing.IntegerCodeUnitsLittleEndian := by
  intro x
  exact ⟨hashCodeUnits_numBytes x, rfl, rfl, hashCodeUnits_byte x,
    hashCodeUnits_word64 x, hashCodeUnits_word32 x⟩

/-- The sole character of the Julia witness is ASCII `a`; its Char storage is
    0x61000000 and its UInt32-codeunit string emits that Char once. -/
def hashAnnotatedUtf8Witness : UTF8Iterator Unit Nat UInt32 where
  string := ()
  defaultState := 0
  first := fun _ => some (0x61000000, 1)
  next := fun _ _ => none
  reinterpretUInt32 := fun c => JInt.lit .u32 c.toNat
  bswapUInt32 := JuliaLean.base.int.bswap

def hashAnnotatedBytesWitness : HashByteArray where
  firstIndex := 1
  length := 1
  get := fun _ => 0x61

def hashAnnotatedUnderlyingValue : Word :=
  hashBytesArray hashAnnotatedBytesWitness (JInt.lit .u64 0) hashSecret

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hashAnnotatedUnderlying_success :
    hashAbstractString hashAnnotatedUtf8Witness (fun _ => false)
      (fun _ => hashAnnotatedBytesWitness) () (JInt.lit .u64 0) =
    some hashAnnotatedUnderlyingValue := by
  simp only [hashAbstractString, utf8units, hashBytesDispatch, hashUTF8Units,
    hashBytesIterator]
  unfold hashIteratorChunks
  decide +kernel

/-- hashops-annotated-non8-hash: the public Julia witness in the accompanying
    reproducer is a one-character UInt32-codeunit AbstractString and its
    annotation-free AnnotatedString wrapper. Hashing the wrapper raises the
    recorded ArgumentError while hashing its equal underlying string succeeds. -/
theorem HashopsAnnotatedNon8Hash_refuted : ¬ JuliaLean.Proofs.base.hashing.AnnotatedStringHash := by
  intro claim
  have contradiction := claim Unit Unit Nat UInt32 hashAnnotatedUtf8Witness
    (fun _ => false) (fun _ => hashAnnotatedBytesWitness) id (fun _ => true)
    (fun _ _ => Except.error (.argumentError "Source type for reinterpret must be isbits"))
    () (JInt.lit .u64 0) rfl rfl hashAnnotatedUnderlyingValue hashAnnotatedUnderlying_success
  cases contradiction

set_option maxRecDepth 2048

theorem hashPointerLoad64_succ {Ptr : Type} {ops : HashPointerOps Ptr} {ptr : Ptr}
    {arr : HashByteArray} (hm : PointerLoadsMatchArray ops ptr arr)
    (pos align : Nat) :
    loadLE ops.convert64 ops.add64 ops.pointerref64 ptr (((pos + 1 : Nat) : Int)) align =
      loadLEArrayU64 arr (arr.firstIndex + ((pos : Nat) : Int)) := by
  simpa only [Int.ofNat_eq_natCast, Nat.add_sub_cancel] using
    hm.2.1 (pos + 1) align (by omega)

theorem hashPointerLoad64_add {Ptr : Type} {ops : HashPointerOps Ptr} {ptr : Ptr}
    {arr : HashByteArray} (hm : PointerLoadsMatchArray ops ptr arr)
    (pos delta align : Nat) :
    loadLE ops.convert64 ops.add64 ops.pointerref64 ptr (((pos + 1 + delta : Nat) : Int)) align =
      loadLEArrayU64 arr (arr.firstIndex + ((pos : Nat) : Int) + ((delta : Nat) : Int)) := by
  have hload := hm.2.1 (pos + 1 + delta) align (by omega)
  simp only [Int.ofNat_eq_natCast] at hload
  rw [hload]
  congr 1
  omega

theorem hashPointerArrayLoop {Ptr : Type} (ops : HashPointerOps Ptr) (ptr : Ptr)
    (arr : HashByteArray) (hm : PointerLoadsMatchArray ops ptr arr)
    (secret : HashSecret) (align : Nat) (i pos : Nat) (seed see1 see2 : Word) :
    ∃ (newSeed newSee1 newSee2 : Word) (newPos newI : Nat),
      hashArray48Loop arr secret i (((pos : Nat) : Int)) seed see1 see2 =
        (newSeed, newSee1, newSee2, ((newPos : Nat) : Int), newI) ∧
      hashPointer48Loop ops ptr secret align i (pos + 1) seed see1 see2 =
        (newSeed, newSee1, newSee2, newPos + 1, newI) := by
  induction i using Nat.strongRecOn generalizing pos seed see1 see2 with
  | ind i ih =>
    by_cases hi : i > 48
    · let s0 := hashMix
        (xorWord (loadLEArrayU64 arr (arr.firstIndex + ((pos : Nat) : Int))) secret.1)
        (xorWord (loadLEArrayU64 arr (arr.firstIndex + ((pos : Nat) : Int) + 8)) seed)
      let s1 := hashMix
        (xorWord (loadLEArrayU64 arr (arr.firstIndex + ((pos : Nat) : Int) + 16)) secret.2.1)
        (xorWord (loadLEArrayU64 arr (arr.firstIndex + ((pos : Nat) : Int) + 24)) see1)
      let s2 := hashMix
        (xorWord (loadLEArrayU64 arr (arr.firstIndex + ((pos : Nat) : Int) + 32)) secret.2.2.1)
        (xorWord (loadLEArrayU64 arr (arr.firstIndex + ((pos : Nat) : Int) + 40)) see2)
      obtain ⟨ns0, ns1, ns2, np, ni, ha, hp⟩ :=
        ih (i - 48) (by omega) (pos + 48) s0 s1 s2
      refine ⟨ns0, ns1, ns2, np, ni, ?_, ?_⟩
      · rw [hashArray48Loop, ite_eq_left hi]
        have hpadd : ((pos : Nat) : Int) + 48 = ((pos + 48 : Nat) : Int) := by
          omega
        rw [hpadd]
        exact ha
      · rw [hashPointer48Loop, ite_eq_left hi]
        simp only [Int.ofNat_eq_natCast]
        simp only [hashPointerLoad64_succ hm]
        simp only [Int.natCast_add, Int.cast_ofNat_Int]
        have hpadd : pos + 1 + 48 = (pos + 48) + 1 := by omega
        rw [hpadd]
        simpa only [s0, s1, s2, Int.add_assoc] using hp
    · refine ⟨seed, see1, see2, pos, i, ?_, ?_⟩
      · rw [hashArray48Loop, ite_eq_right hi]
      · rw [hashPointer48Loop, ite_eq_right hi]

theorem hashLengthWord_le (n : Nat) :
    (JInt.lit .u64 (((n : Nat) : Int))).val ≤ ((n : Nat) : Int) := by
  change ((n : Nat) : Int) % (2 ^ 64 : Int) ≤ ((n : Nat) : Int)
  omega

theorem hashPointerLoad64_tail {Ptr : Type} {ops : HashPointerOps Ptr} {ptr : Ptr}
    {arr : HashByteArray} (hm : PointerLoadsMatchArray ops ptr arr)
    (n delta align : Nat) (hdelta : delta < n) :
    loadLE ops.convert64 ops.add64 ops.pointerref64 ptr (((n - delta : Nat) : Int)) align =
      loadLEArrayU64 arr (arr.firstIndex + ((n : Nat) : Int) - ((delta + 1 : Nat) : Int)) := by
  have hload := hm.2.1 (n - delta) align (by omega)
  simp only [Int.ofNat_eq_natCast] at hload
  rw [hload]
  congr 1
  omega

theorem hashPointerLoad32_tail {Ptr : Type} {ops : HashPointerOps Ptr} {ptr : Ptr}
    {arr : HashByteArray} (hm : PointerLoadsMatchArray ops ptr arr)
    (n delta align : Nat) (hdelta : delta < n) :
    loadLE ops.convert32 ops.add32 ops.pointerref32 ptr (((n - delta : Nat) : Int)) align =
      loadLEArrayU32 arr (arr.firstIndex + ((n : Nat) : Int) - ((delta + 1 : Nat) : Int)) := by
  have hload := hm.2.2 (n - delta) align (by omega)
  simp only [Int.ofNat_eq_natCast] at hload
  rw [hload]
  congr 1
  omega

theorem hashPointerArrayAgreement {Ptr : Type} (ops : HashPointerOps Ptr) (ptr : Ptr)
    (arr : HashByteArray) (hm : PointerLoadsMatchArray ops ptr arr)
    (seed : Word) (secret : HashSecret) (alignment : Nat) :
    hashBytesArray arr seed secret = hashBytesPointer ops ptr arr.length seed secret alignment := by
  have hlen := hashLengthWord_le arr.length
  have h64first (align : Nat) :
      loadLE ops.convert64 ops.add64 ops.pointerref64 ptr ((1 : Nat) : Int) align =
        loadLEArrayU64 arr arr.firstIndex := by
    simpa only [Nat.zero_add, Int.natCast_zero, Int.add_zero] using
      hashPointerLoad64_succ hm 0 align
  have h32first (align : Nat) :
      loadLE ops.convert32 ops.add32 ops.pointerref32 ptr ((1 : Nat) : Int) align =
        loadLEArrayU32 arr arr.firstIndex := by
    simpa only [Int.ofNat_eq_natCast, Nat.sub_self, Int.natCast_zero, Int.add_zero] using
      hm.2.2 1 align (by decide)
  have h8first : ops.load8 ptr 1 = arr.get arr.firstIndex := by
    simpa only [Int.ofNat_eq_natCast, Nat.sub_self, Int.natCast_zero, Int.add_zero] using
      hm.1 1 (by decide)
  by_cases h16 : (JInt.lit .u64 (arr.length : Int)).val ≤ 16
  · by_cases h4 : (JInt.lit .u64 (arr.length : Int)).val ≥ 4
    · by_cases h8 : (JInt.lit .u64 (arr.length : Int)).val ≥ 8
      · have hn : 7 < arr.length := by omega
        have hlast := hashPointerLoad64_tail hm arr.length 7 1 hn
        simp only [hashBytesArray, hashBytesPointer, Id.run, Int.ofNat_eq_natCast,
          ite_eq_left h16, ite_eq_left h4, ite_eq_left h8]
        simp only [h64first, hlast]
        simp only [Int.natCast_add, Int.cast_ofNat_Int, Int.reduceAdd]
      · have hn : 3 < arr.length := by omega
        have hlast := hashPointerLoad32_tail hm arr.length 3 1 hn
        simp only [hashBytesArray, hashBytesPointer, Id.run, Int.ofNat_eq_natCast,
          ite_eq_left h16, ite_eq_left h4, ite_eq_right h8]
        simp only [h32first, hlast]
        simp only [Int.natCast_add, Int.cast_ofNat_Int, Int.reduceAdd]
    · by_cases h0 : (JInt.lit .u64 (arr.length : Int)).val > 0
      · have hn : 0 < arr.length := by omega
        have hlast : ops.load8 ptr arr.length =
            arr.get (arr.firstIndex + (arr.length : Int) - 1) := by
          rw [hm.1 arr.length hn]
          congr 1
          simp only [Int.ofNat_eq_natCast]
          omega
        have hmid : ops.load8 ptr (arr.length / 2 + 1) =
            arr.get (arr.firstIndex + ((arr.length / 2 : Nat) : Int)) := by
          simpa only [Int.ofNat_eq_natCast, Nat.add_sub_cancel] using
            hm.1 (arr.length / 2 + 1) (by omega)
        simp only [hashBytesArray, hashBytesPointer, Id.run, Int.ofNat_eq_natCast,
          ite_eq_left h16, ite_eq_right h4, ite_eq_left h0, h8first, hlast, hmid]
      · simp only [hashBytesArray, hashBytesPointer, Id.run, Int.ofNat_eq_natCast,
          ite_eq_left h16, ite_eq_right h4, ite_eq_right h0]
  · have hn : 16 < arr.length := by omega
    have hlast16 := hashPointerLoad64_tail hm arr.length 15 1 (by omega)
    have hlast8 := hashPointerLoad64_tail hm arr.length 7 1 (by omega)
    by_cases h48 : arr.length > 48
    · obtain ⟨ns0, ns1, ns2, np, ni, ha, hp⟩ := hashPointerArrayLoop ops ptr arr hm secret
        (min alignment 8) arr.length 0
        (xorWord seed (hashMix (xorWord seed secret.2.2.1) secret.2.1))
        (xorWord seed (hashMix (xorWord seed secret.2.2.1) secret.2.1))
        (xorWord seed (hashMix (xorWord seed secret.2.2.1) secret.2.1))
      simp only [Int.natCast_zero] at ha
      simp only [Nat.zero_add] at hp
      simp only [hashBytesArray, hashBytesPointer, Id.run, Int.ofNat_eq_natCast,
        ite_eq_right h16, ite_eq_left h48, ha, hp]
      simp only [hashPointerLoad64_succ hm, hlast16, hlast8]
      simp only [Int.natCast_add, Int.cast_ofNat_Int, Int.add_assoc, Nat.reduceAdd]
    · simp only [hashBytesArray, hashBytesPointer, Id.run, Int.ofNat_eq_natCast,
        ite_eq_right h16, ite_eq_right h48]
      simp only [hashPointerLoad64_succ hm, hlast16, hlast8]
      simp only [Int.cast_ofNat_Int, Int.add_zero, Nat.reduceAdd]

theorem hashUnsignedLit_add (t : IntTy) (hu : t.signed = false) (a b : Int) :
    JInt.lit t a + JInt.lit t b = JInt.lit t (a + b) := by
  have hw (z : Int) : wrapInt t z = z % (2 ^ t.bits : Int) := by
    unfold wrapInt
    rw [hu]
    rfl
  apply Subtype.ext
  change wrapInt t (wrapInt t a + wrapInt t b) = wrapInt t (a + b)
  simp only [hw]
  exact (Int.add_emod a b (2 ^ t.bits)).symm

theorem hashUnsignedFold (t : IntTy) (hu : t.signed = false)
    (is : List Nat) (f : Nat → Int) (z : Int) :
    is.foldl (fun value i => value + JInt.lit t (f i)) (JInt.lit t z) =
      JInt.lit t (is.foldl (fun value i => value + f i) z) := by
  induction is generalizing z with
  | nil => rfl
  | cons i is ih =>
    simp only [List.foldl_cons, hashUnsignedLit_add t hu, ih]

theorem hashStringPointerByte (s : JuliaLean.Strings.JStr) (offset i : Nat)
    (hpos : 0 < offset) :
    JuliaLean.Bindings.base.hashing.stringPtrByte
      (JuliaLean.Bindings.base.hashing.addStringPtr ⟨s, 0⟩ (((offset : Nat) : Int) - 1)) (1 + i) =
      (JuliaLean.Bindings.base.hashing.codeunitsArray
        JuliaLean.Bindings.base.hashing.stringMethods s).get
        (1 + ((offset - 1 : Nat) : Int) + ((i : Nat) : Int)) := by
  unfold JuliaLean.Bindings.base.hashing.stringPtrByte
    JuliaLean.Bindings.base.hashing.addStringPtr
    JuliaLean.Bindings.base.hashing.codeunitsArray
    JuliaLean.Bindings.base.hashing.stringMethods
  congr 2
  simp only [Int.ofNat_eq_natCast]
  omega

theorem hashStringPointerWord (t : IntTy) (hu : t.signed = false)
    (s : JuliaLean.Strings.JStr) (offset width : Nat) (hpos : 0 < offset) :
    JInt.lit t (JuliaLean.Bindings.base.hashing.stringPtrWord
      (JuliaLean.Bindings.base.hashing.addStringPtr ⟨s, 0⟩ (((offset : Nat) : Int) - 1)) 1 width) =
      (List.range width).foldl (fun value i => value + JInt.lit t
        ((((((JuliaLean.Bindings.base.hashing.codeunitsArray
          JuliaLean.Bindings.base.hashing.stringMethods s).get
          (1 + ((offset - 1 : Nat) : Int) + ((i : Nat) : Int))).toNat * 2 ^ (8 * i)) : Nat) : Int)))
        (JInt.lit t 0) := by
  rw [hashUnsignedFold t hu]
  apply congrArg (JInt.lit t)
  unfold JuliaLean.Bindings.base.hashing.stringPtrWord
  congr 1
  funext value i
  rw [hashStringPointerByte s offset i hpos]
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int]

theorem hashStringPointerLoads (s : JuliaLean.Strings.JStr) :
    PointerLoadsMatchArray JuliaLean.Bindings.base.hashing.stringPointerOps ⟨s, 0⟩
      (JuliaLean.Bindings.base.hashing.codeunitsArray
        JuliaLean.Bindings.base.hashing.stringMethods s) := by
  constructor
  · intro offset hpos
    change s.bytes.getD (0 + ((offset : Nat) : Int) - 1).toNat 0 =
      s.bytes.getD ((1 + ((offset - 1 : Nat) : Int)) - 1).toNat 0
    congr 2
    omega
  · constructor
    · intro offset align hpos
      exact hashStringPointerWord .u64 rfl s offset 8 hpos
    · intro offset align hpos
      exact hashStringPointerWord .u32 rfl s offset 4 hpos

theorem HashingStringGenericDispatch_proven :
    JuliaLean.Proofs.base.hashing.Round1.StringSpecializedGenericAgreement := by
  intro s h
  change some (hashBytesPointer JuliaLean.Bindings.base.hashing.stringPointerOps ⟨s, 0⟩
    s.bytes.length h hashSecret 8) = some (hashBytesArray
      (JuliaLean.Bindings.base.hashing.codeunitsArray
        JuliaLean.Bindings.base.hashing.stringMethods s) h hashSecret)
  apply congrArg some
  exact (hashPointerArrayAgreement JuliaLean.Bindings.base.hashing.stringPointerOps ⟨s, 0⟩
    (JuliaLean.Bindings.base.hashing.codeunitsArray
      JuliaLean.Bindings.base.hashing.stringMethods s) (hashStringPointerLoads s) h hashSecret 8).symm

inductive HashNumericRoute where
  | word (value : Word)
  | canonicalNaN
  deriving DecidableEq

def hashNumericRouteEval (route : HashNumericRoute) (h : Word) : Word :=
  match route with
  | .word value => hashUInt64 value h
  | .canonicalNaN => xorWord hashNaNSeed h

def hashFloat16Route {α : Type} (ops : Float16HashOps α) (x : α) : HashNumericRoute :=
  if ops.isfinite x then
    if ops.isequalI64 (ops.fptosi x) x then
      .word (JInt.lit .u64 (ops.fptosi x).val)
    else .word (ops.bitcastFloat64U64 (ops.toFloat64 x))
  else if ops.isnan x then .canonicalNaN
  else .word (ops.bitcastFloat64U64 (ops.toFloat64 x))

def hashFloat64Route {α : Type} (ops : FloatHashOps α) (x : α) : HashNumericRoute :=
  if ops.leIntFloat (JInt.typemin .i64) x && ops.ltFloatInt x (JInt.typemax .i64) then
    if ops.isequalI64 (ops.fptosi x) x then
      .word (JInt.lit .u64 (ops.fptosi x).val)
    else .word (ops.bitcastU64 x)
  else if ops.leUIntFloat (JInt.lit .u64 0) x && ops.ltFloatUInt x (JInt.typemax .u64) then
    if ops.isequalU64 (ops.fptoui x) x then .word (ops.fptoui x)
    else .word (ops.bitcastU64 x)
  else if ops.isnan x then .canonicalNaN
  else .word (ops.bitcastU64 x)

theorem hashFloat16_route {α : Type} (ops : Float16HashOps α) (x : α) (h : Word) :
    hashFloat16 ops x h = hashNumericRouteEval (hashFloat16Route ops x) h := by
  unfold hashFloat16 hashFloat16Route
  dsimp only
  split
  · split <;> rfl
  · split <;> rfl

theorem hashFloat64_route {α : Type} (ops : FloatHashOps α) (x : α) (h : Word) :
    hashFloat64 ops x h = hashNumericRouteEval (hashFloat64Route ops x) h := by
  unfold hashFloat64 hashFloat64Route
  dsimp only
  split
  · split <;> rfl
  · split
    · split <;> rfl
    · split <;> rfl

/-- The finite integer branch is independent of promotion between formats. -/
theorem hashFloat16_integer_branch {α : Type} (ops : Float16HashOps α)
    (x : α) (h : Word) (hf : ops.isfinite x = true)
    (he : ops.isequalI64 (ops.fptosi x) x = true) :
    hashFloat16 ops x h = hashInt64 (ops.fptosi x) h := by
  simp only [hashFloat16, hf, he, ite_true]

theorem hashFloat16_original_integer
    (x : Fl half) (h : Word) (hf : standardHashFloat16Ops.isfinite x = true)
    (he : standardHashFloat16Ops.isequalI64 (standardHashFloat16Ops.fptosi x) x = true) :
    hashFloat16 standardHashFloat16Ops x h = hashInt64 (standardHashFloat16Ops.fptosi x) h :=
  hashFloat16_integer_branch standardHashFloat16Ops x h hf he

/-- The original target is reduced entirely to equality of seed-independent routes. -/
theorem hashFloat16_original_of_routes
    (hroutes : ∀ x : Fl half, hashFloat16Route standardHashFloat16Ops x =
      hashFloat64Route standardHashFloat64Ops (standardHashFloat16Ops.toFloat64 x)) :
    Float16HashConsistent := by
  intro x h
  constructor
  · rw [hashFloat16_route, hashFloat64_route, hroutes x]
  · exact hashFloat16_original_integer x h

def hashHalfRoutesOk (x : Fl half) : Bool :=
  decide (hashFloat16Route standardHashFloat16Ops x =
    hashFloat64Route standardHashFloat64Ops (standardHashFloat16Ops.toFloat64 x))

def hashHalfRouteChunk (k : Nat) : Bool :=
  (List.range 256).all (fun i => hashHalfRoutesOk (Fl.ofBits (k * 256 + i)))

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem hashHalfRouteChunk0 : hashHalfRouteChunk 0 = true := by decide +kernel
theorem hashHalfRouteChunk1 : hashHalfRouteChunk 1 = true := by decide +kernel
theorem hashHalfRouteChunk2 : hashHalfRouteChunk 2 = true := by decide +kernel
theorem hashHalfRouteChunk3 : hashHalfRouteChunk 3 = true := by decide +kernel
theorem hashHalfRouteChunk4 : hashHalfRouteChunk 4 = true := by decide +kernel
theorem hashHalfRouteChunk5 : hashHalfRouteChunk 5 = true := by decide +kernel
theorem hashHalfRouteChunk6 : hashHalfRouteChunk 6 = true := by decide +kernel
theorem hashHalfRouteChunk7 : hashHalfRouteChunk 7 = true := by decide +kernel
theorem hashHalfRouteChunk8 : hashHalfRouteChunk 8 = true := by decide +kernel
theorem hashHalfRouteChunk9 : hashHalfRouteChunk 9 = true := by decide +kernel
theorem hashHalfRouteChunk10 : hashHalfRouteChunk 10 = true := by decide +kernel
theorem hashHalfRouteChunk11 : hashHalfRouteChunk 11 = true := by decide +kernel
theorem hashHalfRouteChunk12 : hashHalfRouteChunk 12 = true := by decide +kernel
theorem hashHalfRouteChunk13 : hashHalfRouteChunk 13 = true := by decide +kernel
theorem hashHalfRouteChunk14 : hashHalfRouteChunk 14 = true := by decide +kernel
theorem hashHalfRouteChunk15 : hashHalfRouteChunk 15 = true := by decide +kernel
theorem hashHalfRouteChunk16 : hashHalfRouteChunk 16 = true := by decide +kernel
theorem hashHalfRouteChunk17 : hashHalfRouteChunk 17 = true := by decide +kernel
theorem hashHalfRouteChunk18 : hashHalfRouteChunk 18 = true := by decide +kernel
theorem hashHalfRouteChunk19 : hashHalfRouteChunk 19 = true := by decide +kernel
theorem hashHalfRouteChunk20 : hashHalfRouteChunk 20 = true := by decide +kernel
theorem hashHalfRouteChunk21 : hashHalfRouteChunk 21 = true := by decide +kernel
theorem hashHalfRouteChunk22 : hashHalfRouteChunk 22 = true := by decide +kernel
theorem hashHalfRouteChunk23 : hashHalfRouteChunk 23 = true := by decide +kernel
theorem hashHalfRouteChunk24 : hashHalfRouteChunk 24 = true := by decide +kernel
theorem hashHalfRouteChunk25 : hashHalfRouteChunk 25 = true := by decide +kernel
theorem hashHalfRouteChunk26 : hashHalfRouteChunk 26 = true := by decide +kernel
theorem hashHalfRouteChunk27 : hashHalfRouteChunk 27 = true := by decide +kernel
theorem hashHalfRouteChunk28 : hashHalfRouteChunk 28 = true := by decide +kernel
theorem hashHalfRouteChunk29 : hashHalfRouteChunk 29 = true := by decide +kernel
theorem hashHalfRouteChunk30 : hashHalfRouteChunk 30 = true := by decide +kernel
theorem hashHalfRouteChunk31 : hashHalfRouteChunk 31 = true := by decide +kernel
theorem hashHalfRouteChunk32 : hashHalfRouteChunk 32 = true := by decide +kernel
theorem hashHalfRouteChunk33 : hashHalfRouteChunk 33 = true := by decide +kernel
theorem hashHalfRouteChunk34 : hashHalfRouteChunk 34 = true := by decide +kernel
theorem hashHalfRouteChunk35 : hashHalfRouteChunk 35 = true := by decide +kernel
theorem hashHalfRouteChunk36 : hashHalfRouteChunk 36 = true := by decide +kernel
theorem hashHalfRouteChunk37 : hashHalfRouteChunk 37 = true := by decide +kernel
theorem hashHalfRouteChunk38 : hashHalfRouteChunk 38 = true := by decide +kernel
theorem hashHalfRouteChunk39 : hashHalfRouteChunk 39 = true := by decide +kernel
theorem hashHalfRouteChunk40 : hashHalfRouteChunk 40 = true := by decide +kernel
theorem hashHalfRouteChunk41 : hashHalfRouteChunk 41 = true := by decide +kernel
theorem hashHalfRouteChunk42 : hashHalfRouteChunk 42 = true := by decide +kernel
theorem hashHalfRouteChunk43 : hashHalfRouteChunk 43 = true := by decide +kernel
theorem hashHalfRouteChunk44 : hashHalfRouteChunk 44 = true := by decide +kernel
theorem hashHalfRouteChunk45 : hashHalfRouteChunk 45 = true := by decide +kernel
theorem hashHalfRouteChunk46 : hashHalfRouteChunk 46 = true := by decide +kernel
theorem hashHalfRouteChunk47 : hashHalfRouteChunk 47 = true := by decide +kernel
theorem hashHalfRouteChunk48 : hashHalfRouteChunk 48 = true := by decide +kernel
theorem hashHalfRouteChunk49 : hashHalfRouteChunk 49 = true := by decide +kernel
theorem hashHalfRouteChunk50 : hashHalfRouteChunk 50 = true := by decide +kernel
theorem hashHalfRouteChunk51 : hashHalfRouteChunk 51 = true := by decide +kernel
theorem hashHalfRouteChunk52 : hashHalfRouteChunk 52 = true := by decide +kernel
theorem hashHalfRouteChunk53 : hashHalfRouteChunk 53 = true := by decide +kernel
theorem hashHalfRouteChunk54 : hashHalfRouteChunk 54 = true := by decide +kernel
theorem hashHalfRouteChunk55 : hashHalfRouteChunk 55 = true := by decide +kernel
theorem hashHalfRouteChunk56 : hashHalfRouteChunk 56 = true := by decide +kernel
theorem hashHalfRouteChunk57 : hashHalfRouteChunk 57 = true := by decide +kernel
theorem hashHalfRouteChunk58 : hashHalfRouteChunk 58 = true := by decide +kernel
theorem hashHalfRouteChunk59 : hashHalfRouteChunk 59 = true := by decide +kernel
theorem hashHalfRouteChunk60 : hashHalfRouteChunk 60 = true := by decide +kernel
theorem hashHalfRouteChunk61 : hashHalfRouteChunk 61 = true := by decide +kernel
theorem hashHalfRouteChunk62 : hashHalfRouteChunk 62 = true := by decide +kernel
theorem hashHalfRouteChunk63 : hashHalfRouteChunk 63 = true := by decide +kernel
theorem hashHalfRouteChunk64 : hashHalfRouteChunk 64 = true := by decide +kernel
theorem hashHalfRouteChunk65 : hashHalfRouteChunk 65 = true := by decide +kernel
theorem hashHalfRouteChunk66 : hashHalfRouteChunk 66 = true := by decide +kernel
theorem hashHalfRouteChunk67 : hashHalfRouteChunk 67 = true := by decide +kernel
theorem hashHalfRouteChunk68 : hashHalfRouteChunk 68 = true := by decide +kernel
theorem hashHalfRouteChunk69 : hashHalfRouteChunk 69 = true := by decide +kernel
theorem hashHalfRouteChunk70 : hashHalfRouteChunk 70 = true := by decide +kernel
theorem hashHalfRouteChunk71 : hashHalfRouteChunk 71 = true := by decide +kernel
theorem hashHalfRouteChunk72 : hashHalfRouteChunk 72 = true := by decide +kernel
theorem hashHalfRouteChunk73 : hashHalfRouteChunk 73 = true := by decide +kernel
theorem hashHalfRouteChunk74 : hashHalfRouteChunk 74 = true := by decide +kernel
theorem hashHalfRouteChunk75 : hashHalfRouteChunk 75 = true := by decide +kernel
theorem hashHalfRouteChunk76 : hashHalfRouteChunk 76 = true := by decide +kernel
theorem hashHalfRouteChunk77 : hashHalfRouteChunk 77 = true := by decide +kernel
theorem hashHalfRouteChunk78 : hashHalfRouteChunk 78 = true := by decide +kernel
theorem hashHalfRouteChunk79 : hashHalfRouteChunk 79 = true := by decide +kernel
theorem hashHalfRouteChunk80 : hashHalfRouteChunk 80 = true := by decide +kernel
theorem hashHalfRouteChunk81 : hashHalfRouteChunk 81 = true := by decide +kernel
theorem hashHalfRouteChunk82 : hashHalfRouteChunk 82 = true := by decide +kernel
theorem hashHalfRouteChunk83 : hashHalfRouteChunk 83 = true := by decide +kernel
theorem hashHalfRouteChunk84 : hashHalfRouteChunk 84 = true := by decide +kernel
theorem hashHalfRouteChunk85 : hashHalfRouteChunk 85 = true := by decide +kernel
theorem hashHalfRouteChunk86 : hashHalfRouteChunk 86 = true := by decide +kernel
theorem hashHalfRouteChunk87 : hashHalfRouteChunk 87 = true := by decide +kernel
theorem hashHalfRouteChunk88 : hashHalfRouteChunk 88 = true := by decide +kernel
theorem hashHalfRouteChunk89 : hashHalfRouteChunk 89 = true := by decide +kernel
theorem hashHalfRouteChunk90 : hashHalfRouteChunk 90 = true := by decide +kernel
theorem hashHalfRouteChunk91 : hashHalfRouteChunk 91 = true := by decide +kernel
theorem hashHalfRouteChunk92 : hashHalfRouteChunk 92 = true := by decide +kernel
theorem hashHalfRouteChunk93 : hashHalfRouteChunk 93 = true := by decide +kernel
theorem hashHalfRouteChunk94 : hashHalfRouteChunk 94 = true := by decide +kernel
theorem hashHalfRouteChunk95 : hashHalfRouteChunk 95 = true := by decide +kernel
theorem hashHalfRouteChunk96 : hashHalfRouteChunk 96 = true := by decide +kernel
theorem hashHalfRouteChunk97 : hashHalfRouteChunk 97 = true := by decide +kernel
theorem hashHalfRouteChunk98 : hashHalfRouteChunk 98 = true := by decide +kernel
theorem hashHalfRouteChunk99 : hashHalfRouteChunk 99 = true := by decide +kernel
theorem hashHalfRouteChunk100 : hashHalfRouteChunk 100 = true := by decide +kernel
theorem hashHalfRouteChunk101 : hashHalfRouteChunk 101 = true := by decide +kernel
theorem hashHalfRouteChunk102 : hashHalfRouteChunk 102 = true := by decide +kernel
theorem hashHalfRouteChunk103 : hashHalfRouteChunk 103 = true := by decide +kernel
theorem hashHalfRouteChunk104 : hashHalfRouteChunk 104 = true := by decide +kernel
theorem hashHalfRouteChunk105 : hashHalfRouteChunk 105 = true := by decide +kernel
theorem hashHalfRouteChunk106 : hashHalfRouteChunk 106 = true := by decide +kernel
theorem hashHalfRouteChunk107 : hashHalfRouteChunk 107 = true := by decide +kernel
theorem hashHalfRouteChunk108 : hashHalfRouteChunk 108 = true := by decide +kernel
theorem hashHalfRouteChunk109 : hashHalfRouteChunk 109 = true := by decide +kernel
theorem hashHalfRouteChunk110 : hashHalfRouteChunk 110 = true := by decide +kernel
theorem hashHalfRouteChunk111 : hashHalfRouteChunk 111 = true := by decide +kernel
theorem hashHalfRouteChunk112 : hashHalfRouteChunk 112 = true := by decide +kernel
theorem hashHalfRouteChunk113 : hashHalfRouteChunk 113 = true := by decide +kernel
theorem hashHalfRouteChunk114 : hashHalfRouteChunk 114 = true := by decide +kernel
theorem hashHalfRouteChunk115 : hashHalfRouteChunk 115 = true := by decide +kernel
theorem hashHalfRouteChunk116 : hashHalfRouteChunk 116 = true := by decide +kernel
theorem hashHalfRouteChunk117 : hashHalfRouteChunk 117 = true := by decide +kernel
theorem hashHalfRouteChunk118 : hashHalfRouteChunk 118 = true := by decide +kernel
theorem hashHalfRouteChunk119 : hashHalfRouteChunk 119 = true := by decide +kernel
theorem hashHalfRouteChunk120 : hashHalfRouteChunk 120 = true := by decide +kernel
theorem hashHalfRouteChunk121 : hashHalfRouteChunk 121 = true := by decide +kernel
theorem hashHalfRouteChunk122 : hashHalfRouteChunk 122 = true := by decide +kernel
theorem hashHalfRouteChunk123 : hashHalfRouteChunk 123 = true := by decide +kernel
theorem hashHalfRouteChunk124 : hashHalfRouteChunk 124 = true := by decide +kernel
theorem hashHalfRouteChunk125 : hashHalfRouteChunk 125 = true := by decide +kernel
theorem hashHalfRouteChunk126 : hashHalfRouteChunk 126 = true := by decide +kernel
theorem hashHalfRouteChunk127 : hashHalfRouteChunk 127 = true := by decide +kernel
theorem hashHalfRouteChunk128 : hashHalfRouteChunk 128 = true := by decide +kernel
theorem hashHalfRouteChunk129 : hashHalfRouteChunk 129 = true := by decide +kernel
theorem hashHalfRouteChunk130 : hashHalfRouteChunk 130 = true := by decide +kernel
theorem hashHalfRouteChunk131 : hashHalfRouteChunk 131 = true := by decide +kernel
theorem hashHalfRouteChunk132 : hashHalfRouteChunk 132 = true := by decide +kernel
theorem hashHalfRouteChunk133 : hashHalfRouteChunk 133 = true := by decide +kernel
theorem hashHalfRouteChunk134 : hashHalfRouteChunk 134 = true := by decide +kernel
theorem hashHalfRouteChunk135 : hashHalfRouteChunk 135 = true := by decide +kernel
theorem hashHalfRouteChunk136 : hashHalfRouteChunk 136 = true := by decide +kernel
theorem hashHalfRouteChunk137 : hashHalfRouteChunk 137 = true := by decide +kernel
theorem hashHalfRouteChunk138 : hashHalfRouteChunk 138 = true := by decide +kernel
theorem hashHalfRouteChunk139 : hashHalfRouteChunk 139 = true := by decide +kernel
theorem hashHalfRouteChunk140 : hashHalfRouteChunk 140 = true := by decide +kernel
theorem hashHalfRouteChunk141 : hashHalfRouteChunk 141 = true := by decide +kernel
theorem hashHalfRouteChunk142 : hashHalfRouteChunk 142 = true := by decide +kernel
theorem hashHalfRouteChunk143 : hashHalfRouteChunk 143 = true := by decide +kernel
theorem hashHalfRouteChunk144 : hashHalfRouteChunk 144 = true := by decide +kernel
theorem hashHalfRouteChunk145 : hashHalfRouteChunk 145 = true := by decide +kernel
theorem hashHalfRouteChunk146 : hashHalfRouteChunk 146 = true := by decide +kernel
theorem hashHalfRouteChunk147 : hashHalfRouteChunk 147 = true := by decide +kernel
theorem hashHalfRouteChunk148 : hashHalfRouteChunk 148 = true := by decide +kernel
theorem hashHalfRouteChunk149 : hashHalfRouteChunk 149 = true := by decide +kernel
theorem hashHalfRouteChunk150 : hashHalfRouteChunk 150 = true := by decide +kernel
theorem hashHalfRouteChunk151 : hashHalfRouteChunk 151 = true := by decide +kernel
theorem hashHalfRouteChunk152 : hashHalfRouteChunk 152 = true := by decide +kernel
theorem hashHalfRouteChunk153 : hashHalfRouteChunk 153 = true := by decide +kernel
theorem hashHalfRouteChunk154 : hashHalfRouteChunk 154 = true := by decide +kernel
theorem hashHalfRouteChunk155 : hashHalfRouteChunk 155 = true := by decide +kernel
theorem hashHalfRouteChunk156 : hashHalfRouteChunk 156 = true := by decide +kernel
theorem hashHalfRouteChunk157 : hashHalfRouteChunk 157 = true := by decide +kernel
theorem hashHalfRouteChunk158 : hashHalfRouteChunk 158 = true := by decide +kernel
theorem hashHalfRouteChunk159 : hashHalfRouteChunk 159 = true := by decide +kernel
theorem hashHalfRouteChunk160 : hashHalfRouteChunk 160 = true := by decide +kernel
theorem hashHalfRouteChunk161 : hashHalfRouteChunk 161 = true := by decide +kernel
theorem hashHalfRouteChunk162 : hashHalfRouteChunk 162 = true := by decide +kernel
theorem hashHalfRouteChunk163 : hashHalfRouteChunk 163 = true := by decide +kernel
theorem hashHalfRouteChunk164 : hashHalfRouteChunk 164 = true := by decide +kernel
theorem hashHalfRouteChunk165 : hashHalfRouteChunk 165 = true := by decide +kernel
theorem hashHalfRouteChunk166 : hashHalfRouteChunk 166 = true := by decide +kernel
theorem hashHalfRouteChunk167 : hashHalfRouteChunk 167 = true := by decide +kernel
theorem hashHalfRouteChunk168 : hashHalfRouteChunk 168 = true := by decide +kernel
theorem hashHalfRouteChunk169 : hashHalfRouteChunk 169 = true := by decide +kernel
theorem hashHalfRouteChunk170 : hashHalfRouteChunk 170 = true := by decide +kernel
theorem hashHalfRouteChunk171 : hashHalfRouteChunk 171 = true := by decide +kernel
theorem hashHalfRouteChunk172 : hashHalfRouteChunk 172 = true := by decide +kernel
theorem hashHalfRouteChunk173 : hashHalfRouteChunk 173 = true := by decide +kernel
theorem hashHalfRouteChunk174 : hashHalfRouteChunk 174 = true := by decide +kernel
theorem hashHalfRouteChunk175 : hashHalfRouteChunk 175 = true := by decide +kernel
theorem hashHalfRouteChunk176 : hashHalfRouteChunk 176 = true := by decide +kernel
theorem hashHalfRouteChunk177 : hashHalfRouteChunk 177 = true := by decide +kernel
theorem hashHalfRouteChunk178 : hashHalfRouteChunk 178 = true := by decide +kernel
theorem hashHalfRouteChunk179 : hashHalfRouteChunk 179 = true := by decide +kernel
theorem hashHalfRouteChunk180 : hashHalfRouteChunk 180 = true := by decide +kernel
theorem hashHalfRouteChunk181 : hashHalfRouteChunk 181 = true := by decide +kernel
theorem hashHalfRouteChunk182 : hashHalfRouteChunk 182 = true := by decide +kernel
theorem hashHalfRouteChunk183 : hashHalfRouteChunk 183 = true := by decide +kernel
theorem hashHalfRouteChunk184 : hashHalfRouteChunk 184 = true := by decide +kernel
theorem hashHalfRouteChunk185 : hashHalfRouteChunk 185 = true := by decide +kernel
theorem hashHalfRouteChunk186 : hashHalfRouteChunk 186 = true := by decide +kernel
theorem hashHalfRouteChunk187 : hashHalfRouteChunk 187 = true := by decide +kernel
theorem hashHalfRouteChunk188 : hashHalfRouteChunk 188 = true := by decide +kernel
theorem hashHalfRouteChunk189 : hashHalfRouteChunk 189 = true := by decide +kernel
theorem hashHalfRouteChunk190 : hashHalfRouteChunk 190 = true := by decide +kernel
theorem hashHalfRouteChunk191 : hashHalfRouteChunk 191 = true := by decide +kernel
theorem hashHalfRouteChunk192 : hashHalfRouteChunk 192 = true := by decide +kernel
theorem hashHalfRouteChunk193 : hashHalfRouteChunk 193 = true := by decide +kernel
theorem hashHalfRouteChunk194 : hashHalfRouteChunk 194 = true := by decide +kernel
theorem hashHalfRouteChunk195 : hashHalfRouteChunk 195 = true := by decide +kernel
theorem hashHalfRouteChunk196 : hashHalfRouteChunk 196 = true := by decide +kernel
theorem hashHalfRouteChunk197 : hashHalfRouteChunk 197 = true := by decide +kernel
theorem hashHalfRouteChunk198 : hashHalfRouteChunk 198 = true := by decide +kernel
theorem hashHalfRouteChunk199 : hashHalfRouteChunk 199 = true := by decide +kernel
theorem hashHalfRouteChunk200 : hashHalfRouteChunk 200 = true := by decide +kernel
theorem hashHalfRouteChunk201 : hashHalfRouteChunk 201 = true := by decide +kernel
theorem hashHalfRouteChunk202 : hashHalfRouteChunk 202 = true := by decide +kernel
theorem hashHalfRouteChunk203 : hashHalfRouteChunk 203 = true := by decide +kernel
theorem hashHalfRouteChunk204 : hashHalfRouteChunk 204 = true := by decide +kernel
theorem hashHalfRouteChunk205 : hashHalfRouteChunk 205 = true := by decide +kernel
theorem hashHalfRouteChunk206 : hashHalfRouteChunk 206 = true := by decide +kernel
theorem hashHalfRouteChunk207 : hashHalfRouteChunk 207 = true := by decide +kernel
theorem hashHalfRouteChunk208 : hashHalfRouteChunk 208 = true := by decide +kernel
theorem hashHalfRouteChunk209 : hashHalfRouteChunk 209 = true := by decide +kernel
theorem hashHalfRouteChunk210 : hashHalfRouteChunk 210 = true := by decide +kernel
theorem hashHalfRouteChunk211 : hashHalfRouteChunk 211 = true := by decide +kernel
theorem hashHalfRouteChunk212 : hashHalfRouteChunk 212 = true := by decide +kernel
theorem hashHalfRouteChunk213 : hashHalfRouteChunk 213 = true := by decide +kernel
theorem hashHalfRouteChunk214 : hashHalfRouteChunk 214 = true := by decide +kernel
theorem hashHalfRouteChunk215 : hashHalfRouteChunk 215 = true := by decide +kernel
theorem hashHalfRouteChunk216 : hashHalfRouteChunk 216 = true := by decide +kernel
theorem hashHalfRouteChunk217 : hashHalfRouteChunk 217 = true := by decide +kernel
theorem hashHalfRouteChunk218 : hashHalfRouteChunk 218 = true := by decide +kernel
theorem hashHalfRouteChunk219 : hashHalfRouteChunk 219 = true := by decide +kernel
theorem hashHalfRouteChunk220 : hashHalfRouteChunk 220 = true := by decide +kernel
theorem hashHalfRouteChunk221 : hashHalfRouteChunk 221 = true := by decide +kernel
theorem hashHalfRouteChunk222 : hashHalfRouteChunk 222 = true := by decide +kernel
theorem hashHalfRouteChunk223 : hashHalfRouteChunk 223 = true := by decide +kernel
theorem hashHalfRouteChunk224 : hashHalfRouteChunk 224 = true := by decide +kernel
theorem hashHalfRouteChunk225 : hashHalfRouteChunk 225 = true := by decide +kernel
theorem hashHalfRouteChunk226 : hashHalfRouteChunk 226 = true := by decide +kernel
theorem hashHalfRouteChunk227 : hashHalfRouteChunk 227 = true := by decide +kernel
theorem hashHalfRouteChunk228 : hashHalfRouteChunk 228 = true := by decide +kernel
theorem hashHalfRouteChunk229 : hashHalfRouteChunk 229 = true := by decide +kernel
theorem hashHalfRouteChunk230 : hashHalfRouteChunk 230 = true := by decide +kernel
theorem hashHalfRouteChunk231 : hashHalfRouteChunk 231 = true := by decide +kernel
theorem hashHalfRouteChunk232 : hashHalfRouteChunk 232 = true := by decide +kernel
theorem hashHalfRouteChunk233 : hashHalfRouteChunk 233 = true := by decide +kernel
theorem hashHalfRouteChunk234 : hashHalfRouteChunk 234 = true := by decide +kernel
theorem hashHalfRouteChunk235 : hashHalfRouteChunk 235 = true := by decide +kernel
theorem hashHalfRouteChunk236 : hashHalfRouteChunk 236 = true := by decide +kernel
theorem hashHalfRouteChunk237 : hashHalfRouteChunk 237 = true := by decide +kernel
theorem hashHalfRouteChunk238 : hashHalfRouteChunk 238 = true := by decide +kernel
theorem hashHalfRouteChunk239 : hashHalfRouteChunk 239 = true := by decide +kernel
theorem hashHalfRouteChunk240 : hashHalfRouteChunk 240 = true := by decide +kernel
theorem hashHalfRouteChunk241 : hashHalfRouteChunk 241 = true := by decide +kernel
theorem hashHalfRouteChunk242 : hashHalfRouteChunk 242 = true := by decide +kernel
theorem hashHalfRouteChunk243 : hashHalfRouteChunk 243 = true := by decide +kernel
theorem hashHalfRouteChunk244 : hashHalfRouteChunk 244 = true := by decide +kernel
theorem hashHalfRouteChunk245 : hashHalfRouteChunk 245 = true := by decide +kernel
theorem hashHalfRouteChunk246 : hashHalfRouteChunk 246 = true := by decide +kernel
theorem hashHalfRouteChunk247 : hashHalfRouteChunk 247 = true := by decide +kernel
theorem hashHalfRouteChunk248 : hashHalfRouteChunk 248 = true := by decide +kernel
theorem hashHalfRouteChunk249 : hashHalfRouteChunk 249 = true := by decide +kernel
theorem hashHalfRouteChunk250 : hashHalfRouteChunk 250 = true := by decide +kernel
theorem hashHalfRouteChunk251 : hashHalfRouteChunk 251 = true := by decide +kernel
theorem hashHalfRouteChunk252 : hashHalfRouteChunk 252 = true := by decide +kernel
theorem hashHalfRouteChunk253 : hashHalfRouteChunk 253 = true := by decide +kernel
theorem hashHalfRouteChunk254 : hashHalfRouteChunk 254 = true := by decide +kernel
theorem hashHalfRouteChunk255 : hashHalfRouteChunk 255 = true := by decide +kernel

theorem hashHalfRouteChunks : ∀ k, k < 256 → hashHalfRouteChunk k = true
  | 0, _ => hashHalfRouteChunk0
  | 1, _ => hashHalfRouteChunk1
  | 2, _ => hashHalfRouteChunk2
  | 3, _ => hashHalfRouteChunk3
  | 4, _ => hashHalfRouteChunk4
  | 5, _ => hashHalfRouteChunk5
  | 6, _ => hashHalfRouteChunk6
  | 7, _ => hashHalfRouteChunk7
  | 8, _ => hashHalfRouteChunk8
  | 9, _ => hashHalfRouteChunk9
  | 10, _ => hashHalfRouteChunk10
  | 11, _ => hashHalfRouteChunk11
  | 12, _ => hashHalfRouteChunk12
  | 13, _ => hashHalfRouteChunk13
  | 14, _ => hashHalfRouteChunk14
  | 15, _ => hashHalfRouteChunk15
  | 16, _ => hashHalfRouteChunk16
  | 17, _ => hashHalfRouteChunk17
  | 18, _ => hashHalfRouteChunk18
  | 19, _ => hashHalfRouteChunk19
  | 20, _ => hashHalfRouteChunk20
  | 21, _ => hashHalfRouteChunk21
  | 22, _ => hashHalfRouteChunk22
  | 23, _ => hashHalfRouteChunk23
  | 24, _ => hashHalfRouteChunk24
  | 25, _ => hashHalfRouteChunk25
  | 26, _ => hashHalfRouteChunk26
  | 27, _ => hashHalfRouteChunk27
  | 28, _ => hashHalfRouteChunk28
  | 29, _ => hashHalfRouteChunk29
  | 30, _ => hashHalfRouteChunk30
  | 31, _ => hashHalfRouteChunk31
  | 32, _ => hashHalfRouteChunk32
  | 33, _ => hashHalfRouteChunk33
  | 34, _ => hashHalfRouteChunk34
  | 35, _ => hashHalfRouteChunk35
  | 36, _ => hashHalfRouteChunk36
  | 37, _ => hashHalfRouteChunk37
  | 38, _ => hashHalfRouteChunk38
  | 39, _ => hashHalfRouteChunk39
  | 40, _ => hashHalfRouteChunk40
  | 41, _ => hashHalfRouteChunk41
  | 42, _ => hashHalfRouteChunk42
  | 43, _ => hashHalfRouteChunk43
  | 44, _ => hashHalfRouteChunk44
  | 45, _ => hashHalfRouteChunk45
  | 46, _ => hashHalfRouteChunk46
  | 47, _ => hashHalfRouteChunk47
  | 48, _ => hashHalfRouteChunk48
  | 49, _ => hashHalfRouteChunk49
  | 50, _ => hashHalfRouteChunk50
  | 51, _ => hashHalfRouteChunk51
  | 52, _ => hashHalfRouteChunk52
  | 53, _ => hashHalfRouteChunk53
  | 54, _ => hashHalfRouteChunk54
  | 55, _ => hashHalfRouteChunk55
  | 56, _ => hashHalfRouteChunk56
  | 57, _ => hashHalfRouteChunk57
  | 58, _ => hashHalfRouteChunk58
  | 59, _ => hashHalfRouteChunk59
  | 60, _ => hashHalfRouteChunk60
  | 61, _ => hashHalfRouteChunk61
  | 62, _ => hashHalfRouteChunk62
  | 63, _ => hashHalfRouteChunk63
  | 64, _ => hashHalfRouteChunk64
  | 65, _ => hashHalfRouteChunk65
  | 66, _ => hashHalfRouteChunk66
  | 67, _ => hashHalfRouteChunk67
  | 68, _ => hashHalfRouteChunk68
  | 69, _ => hashHalfRouteChunk69
  | 70, _ => hashHalfRouteChunk70
  | 71, _ => hashHalfRouteChunk71
  | 72, _ => hashHalfRouteChunk72
  | 73, _ => hashHalfRouteChunk73
  | 74, _ => hashHalfRouteChunk74
  | 75, _ => hashHalfRouteChunk75
  | 76, _ => hashHalfRouteChunk76
  | 77, _ => hashHalfRouteChunk77
  | 78, _ => hashHalfRouteChunk78
  | 79, _ => hashHalfRouteChunk79
  | 80, _ => hashHalfRouteChunk80
  | 81, _ => hashHalfRouteChunk81
  | 82, _ => hashHalfRouteChunk82
  | 83, _ => hashHalfRouteChunk83
  | 84, _ => hashHalfRouteChunk84
  | 85, _ => hashHalfRouteChunk85
  | 86, _ => hashHalfRouteChunk86
  | 87, _ => hashHalfRouteChunk87
  | 88, _ => hashHalfRouteChunk88
  | 89, _ => hashHalfRouteChunk89
  | 90, _ => hashHalfRouteChunk90
  | 91, _ => hashHalfRouteChunk91
  | 92, _ => hashHalfRouteChunk92
  | 93, _ => hashHalfRouteChunk93
  | 94, _ => hashHalfRouteChunk94
  | 95, _ => hashHalfRouteChunk95
  | 96, _ => hashHalfRouteChunk96
  | 97, _ => hashHalfRouteChunk97
  | 98, _ => hashHalfRouteChunk98
  | 99, _ => hashHalfRouteChunk99
  | 100, _ => hashHalfRouteChunk100
  | 101, _ => hashHalfRouteChunk101
  | 102, _ => hashHalfRouteChunk102
  | 103, _ => hashHalfRouteChunk103
  | 104, _ => hashHalfRouteChunk104
  | 105, _ => hashHalfRouteChunk105
  | 106, _ => hashHalfRouteChunk106
  | 107, _ => hashHalfRouteChunk107
  | 108, _ => hashHalfRouteChunk108
  | 109, _ => hashHalfRouteChunk109
  | 110, _ => hashHalfRouteChunk110
  | 111, _ => hashHalfRouteChunk111
  | 112, _ => hashHalfRouteChunk112
  | 113, _ => hashHalfRouteChunk113
  | 114, _ => hashHalfRouteChunk114
  | 115, _ => hashHalfRouteChunk115
  | 116, _ => hashHalfRouteChunk116
  | 117, _ => hashHalfRouteChunk117
  | 118, _ => hashHalfRouteChunk118
  | 119, _ => hashHalfRouteChunk119
  | 120, _ => hashHalfRouteChunk120
  | 121, _ => hashHalfRouteChunk121
  | 122, _ => hashHalfRouteChunk122
  | 123, _ => hashHalfRouteChunk123
  | 124, _ => hashHalfRouteChunk124
  | 125, _ => hashHalfRouteChunk125
  | 126, _ => hashHalfRouteChunk126
  | 127, _ => hashHalfRouteChunk127
  | 128, _ => hashHalfRouteChunk128
  | 129, _ => hashHalfRouteChunk129
  | 130, _ => hashHalfRouteChunk130
  | 131, _ => hashHalfRouteChunk131
  | 132, _ => hashHalfRouteChunk132
  | 133, _ => hashHalfRouteChunk133
  | 134, _ => hashHalfRouteChunk134
  | 135, _ => hashHalfRouteChunk135
  | 136, _ => hashHalfRouteChunk136
  | 137, _ => hashHalfRouteChunk137
  | 138, _ => hashHalfRouteChunk138
  | 139, _ => hashHalfRouteChunk139
  | 140, _ => hashHalfRouteChunk140
  | 141, _ => hashHalfRouteChunk141
  | 142, _ => hashHalfRouteChunk142
  | 143, _ => hashHalfRouteChunk143
  | 144, _ => hashHalfRouteChunk144
  | 145, _ => hashHalfRouteChunk145
  | 146, _ => hashHalfRouteChunk146
  | 147, _ => hashHalfRouteChunk147
  | 148, _ => hashHalfRouteChunk148
  | 149, _ => hashHalfRouteChunk149
  | 150, _ => hashHalfRouteChunk150
  | 151, _ => hashHalfRouteChunk151
  | 152, _ => hashHalfRouteChunk152
  | 153, _ => hashHalfRouteChunk153
  | 154, _ => hashHalfRouteChunk154
  | 155, _ => hashHalfRouteChunk155
  | 156, _ => hashHalfRouteChunk156
  | 157, _ => hashHalfRouteChunk157
  | 158, _ => hashHalfRouteChunk158
  | 159, _ => hashHalfRouteChunk159
  | 160, _ => hashHalfRouteChunk160
  | 161, _ => hashHalfRouteChunk161
  | 162, _ => hashHalfRouteChunk162
  | 163, _ => hashHalfRouteChunk163
  | 164, _ => hashHalfRouteChunk164
  | 165, _ => hashHalfRouteChunk165
  | 166, _ => hashHalfRouteChunk166
  | 167, _ => hashHalfRouteChunk167
  | 168, _ => hashHalfRouteChunk168
  | 169, _ => hashHalfRouteChunk169
  | 170, _ => hashHalfRouteChunk170
  | 171, _ => hashHalfRouteChunk171
  | 172, _ => hashHalfRouteChunk172
  | 173, _ => hashHalfRouteChunk173
  | 174, _ => hashHalfRouteChunk174
  | 175, _ => hashHalfRouteChunk175
  | 176, _ => hashHalfRouteChunk176
  | 177, _ => hashHalfRouteChunk177
  | 178, _ => hashHalfRouteChunk178
  | 179, _ => hashHalfRouteChunk179
  | 180, _ => hashHalfRouteChunk180
  | 181, _ => hashHalfRouteChunk181
  | 182, _ => hashHalfRouteChunk182
  | 183, _ => hashHalfRouteChunk183
  | 184, _ => hashHalfRouteChunk184
  | 185, _ => hashHalfRouteChunk185
  | 186, _ => hashHalfRouteChunk186
  | 187, _ => hashHalfRouteChunk187
  | 188, _ => hashHalfRouteChunk188
  | 189, _ => hashHalfRouteChunk189
  | 190, _ => hashHalfRouteChunk190
  | 191, _ => hashHalfRouteChunk191
  | 192, _ => hashHalfRouteChunk192
  | 193, _ => hashHalfRouteChunk193
  | 194, _ => hashHalfRouteChunk194
  | 195, _ => hashHalfRouteChunk195
  | 196, _ => hashHalfRouteChunk196
  | 197, _ => hashHalfRouteChunk197
  | 198, _ => hashHalfRouteChunk198
  | 199, _ => hashHalfRouteChunk199
  | 200, _ => hashHalfRouteChunk200
  | 201, _ => hashHalfRouteChunk201
  | 202, _ => hashHalfRouteChunk202
  | 203, _ => hashHalfRouteChunk203
  | 204, _ => hashHalfRouteChunk204
  | 205, _ => hashHalfRouteChunk205
  | 206, _ => hashHalfRouteChunk206
  | 207, _ => hashHalfRouteChunk207
  | 208, _ => hashHalfRouteChunk208
  | 209, _ => hashHalfRouteChunk209
  | 210, _ => hashHalfRouteChunk210
  | 211, _ => hashHalfRouteChunk211
  | 212, _ => hashHalfRouteChunk212
  | 213, _ => hashHalfRouteChunk213
  | 214, _ => hashHalfRouteChunk214
  | 215, _ => hashHalfRouteChunk215
  | 216, _ => hashHalfRouteChunk216
  | 217, _ => hashHalfRouteChunk217
  | 218, _ => hashHalfRouteChunk218
  | 219, _ => hashHalfRouteChunk219
  | 220, _ => hashHalfRouteChunk220
  | 221, _ => hashHalfRouteChunk221
  | 222, _ => hashHalfRouteChunk222
  | 223, _ => hashHalfRouteChunk223
  | 224, _ => hashHalfRouteChunk224
  | 225, _ => hashHalfRouteChunk225
  | 226, _ => hashHalfRouteChunk226
  | 227, _ => hashHalfRouteChunk227
  | 228, _ => hashHalfRouteChunk228
  | 229, _ => hashHalfRouteChunk229
  | 230, _ => hashHalfRouteChunk230
  | 231, _ => hashHalfRouteChunk231
  | 232, _ => hashHalfRouteChunk232
  | 233, _ => hashHalfRouteChunk233
  | 234, _ => hashHalfRouteChunk234
  | 235, _ => hashHalfRouteChunk235
  | 236, _ => hashHalfRouteChunk236
  | 237, _ => hashHalfRouteChunk237
  | 238, _ => hashHalfRouteChunk238
  | 239, _ => hashHalfRouteChunk239
  | 240, _ => hashHalfRouteChunk240
  | 241, _ => hashHalfRouteChunk241
  | 242, _ => hashHalfRouteChunk242
  | 243, _ => hashHalfRouteChunk243
  | 244, _ => hashHalfRouteChunk244
  | 245, _ => hashHalfRouteChunk245
  | 246, _ => hashHalfRouteChunk246
  | 247, _ => hashHalfRouteChunk247
  | 248, _ => hashHalfRouteChunk248
  | 249, _ => hashHalfRouteChunk249
  | 250, _ => hashHalfRouteChunk250
  | 251, _ => hashHalfRouteChunk251
  | 252, _ => hashHalfRouteChunk252
  | 253, _ => hashHalfRouteChunk253
  | 254, _ => hashHalfRouteChunk254
  | 255, _ => hashHalfRouteChunk255
  | _ + 256, h => False.elim (by omega)

theorem hashHalfRouteEq (x : Fl half) :
    hashFloat16Route standardHashFloat16Ops x =
      hashFloat64Route standardHashFloat64Ops (standardHashFloat16Ops.toFloat64 x) := by
  obtain ⟨⟨n, hn⟩⟩ := x
  have hn' : n < 65536 := hn
  have hchunk := hashHalfRouteChunks (n / 256) (by omega)
  unfold hashHalfRouteChunk at hchunk
  have hvalue := (List.all_eq_true.mp hchunk) (n % 256) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have hx : (Fl.ofBits (n / 256 * 256 + n % 256) : Fl half) = ⟨⟨n, hn⟩⟩ := by
    have he : n / 256 * 256 + n % 256 = n := by omega
    simp only [Fl.ofBits, he]
    apply congrArg Fl.mk
    apply Fin.ext
    exact Nat.mod_eq_of_lt hn
  rw [hx] at hvalue
  exact of_decide_eq_true hvalue

/-- promotion-float16-hash-consistent -/
theorem PromotionFloat16HashConsistent_proven : JuliaLean.Proofs.base.hashing.Float16HashConsistent := by
  intro x h
  constructor
  · rw [hashFloat16_route, hashFloat64_route, hashHalfRouteEq]
  · intro hfinite hequal
    simp only [hashFloat16, hfinite, hequal, ite_true]


end JuliaLean.ChatGPT.Batch4.Group21

/- Complete float hash dependency closure. -/
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096


/- FloatSmall.lean -/
/- Complete float hash dependency closure. -/
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096


/- FloatSmall.lean -/

namespace JuliaLean.ChatGPT.Batch8.Group14

open JuliaLean JuliaLean.Promotion JuliaLean.base.hashing

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem fhSmallFloorLog (a : Nat) (ha : a ≠ 0) :
    Fl.floorLog2Rat a 1 = (a.log2 : Int) := by
  have hp : 2 ^ a.log2 ≤ a := (Nat.le_log2 ha).mp (Nat.le_refl _)
  simp only [Fl.floorLog2Rat, show Nat.log2 1 = 0 from rfl,
    Int.natCast_zero, Int.sub_zero, show (a.log2 : Int) ≥ 0 by omega,
    ↓reduceIte, Int.toNat_natCast, Nat.one_mul,
    show ¬ a < 2 ^ a.log2 by omega, ↓reduceIte]

theorem fhSmallRoundOne (a : Nat) : Fl.roundQuotient a 1 = a := by
  simp only [Fl.roundQuotient, Nat.div_one, Nat.mod_one, Nat.mul_zero,
    show decide (0 > 1) = false from rfl, show (0 == 1) = false from rfl,
    Bool.false_and, Bool.false_or, Bool.false_eq_true, if_false]

def fhSmallEncode (s : Bool) (e q : Nat) : Fl double :=
  Fl.ofBits ((if s then 2 ^ 63 else 0) + (e + 1023) * 2 ^ 52 + (q - 2 ^ 52))

theorem fhSmallExpFromMagnitude {f : Fmt} (x : Fl f) :
    x.expField = x.magnitude / 2 ^ f.sb := by
  unfold Fl.expField Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_div_self]


theorem fhSmallFracFromMagnitude {f : Fmt} (x : Fl f) :
    x.frac = x.magnitude % 2 ^ f.sb := by
  unfold Fl.frac Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_mod]


theorem fhSmallOfBitsParts (negative : Bool) (mag : Nat) (hmag : mag < 2 ^ 63) :
    let x := Fl.ofBits (f := double) ((if negative then 2 ^ 63 else 0) + mag)
    x.magnitude = mag ∧ x.signbit = negative := by
  cases negative <;>
    simp only [Fl.ofBits, Fl.toBits, Fl.magnitude, Fl.signbit, double, Fmt.width,
      Nat.reduceAdd, Nat.reducePow, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  · have hb : mag < 18446744073709551616 := by omega
    rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega)]
    exact ⟨rfl, by simp only [show ¬ mag ≥ 9223372036854775808 by omega, decide_false]⟩
  · have hb : 9223372036854775808 + mag < 18446744073709551616 := by omega
    rw [Nat.mod_eq_of_lt hb]
    have hm : (9223372036854775808 + mag) % 9223372036854775808 = mag := by
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt hmag]
    rw [hm]
    exact ⟨rfl, by simp only [show 9223372036854775808 + mag ≥ 9223372036854775808 by omega, decide_true]⟩


theorem fhSmallEncodeParts (s : Bool) (e q : Nat) (he : e ≤ 15)
    (hlo : 2 ^ 52 ≤ q) (hhi : q < 2 ^ 53) :
    (fhSmallEncode s e q).expField = e + 1023 ∧
      (fhSmallEncode s e q).frac = q - 2 ^ 52 ∧
      (fhSmallEncode s e q).signbit = s := by
  let r := q - 2 ^ 52
  let E := e + 1023
  let mag := E * 2 ^ 52 + r
  have hr : r < 2 ^ 52 := by dsimp only [r]; omega
  have hE : E < 2048 := by dsimp only [E]; omega
  have hm : mag < 2 ^ 63 := by
    calc
      _ < E * 2 ^ 52 + 2 ^ 52 := Nat.add_lt_add_left hr _
      _ = (E + 1) * 2 ^ 52 := (Nat.succ_mul E (2 ^ 52)).symm
      _ ≤ 2048 * 2 ^ 52 := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hE)
      _ = 2 ^ 63 := by decide
  have hcode : fhSmallEncode s e q =
      Fl.ofBits (f := double) ((if s then 2 ^ 63 else 0) + mag) := by
    unfold fhSmallEncode
    dsimp only [mag, E, r]
    rw [Nat.add_assoc]
  have parts := fhSmallOfBitsParts s mag hm
  have hmag : (fhSmallEncode s e q).magnitude = mag := by
    rw [hcode]
    exact parts.1
  have hsign : (fhSmallEncode s e q).signbit = s := by
    rw [hcode]
    exact parts.2
  refine ⟨?_, ?_, hsign⟩
  · rw [fhSmallExpFromMagnitude, hmag]
    change (E * 2 ^ 52 + r) / 2 ^ 52 = E
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [fhSmallFracFromMagnitude, hmag]
    change (E * 2 ^ 52 + r) % 2 ^ 52 = r
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hr]

theorem fhSmallEncodeValue (s : Bool) (e q : Nat) (he : e ≤ 15)
    (hlo : 2 ^ 52 ≤ q) (hhi : q < 2 ^ 53) :
    (fhSmallEncode s e q).isfinite = true ∧
      (fhSmallEncode s e q).toRat =
        (if s then -(q : Int) else (q : Int), 2 ^ (52 - e)) := by
  obtain ⟨hexp, hfrac, hsign⟩ := fhSmallEncodeParts s e q he hlo hhi
  have hf : (fhSmallEncode s e q).isfinite = true := by
    unfold Fl.isfinite
    rw [hexp]
    change (e + 1023 != 2047) = true
    exact bne_iff_ne.mpr (by omega)
  refine ⟨hf, ?_⟩
  have hnonzero : (e + 1023 == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  have hq : q - 2 ^ 52 + 2 ^ 52 = q := Nat.sub_add_cancel hlo
  have hp : ((e + 1023 : Nat) : Int) - 1023 - 52 = (e : Int) - 52 := by omega
  have hneg : ¬ (e : Int) - 52 ≥ 0 := by omega
  have hden : (-((e : Int) - 52)).toNat = 52 - e := by omega
  unfold Fl.toRat
  rw [hf]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  rw [hexp, hfrac, hsign, hnonzero]
  simp only [Bool.false_eq_true, if_false]
  change (if ((e + 1023 : Nat) : Int) - 1023 - 52 ≥ 0 then
      ((if s then -((q - 2 ^ 52 + 2 ^ 52 : Nat) : Int) else
          ((q - 2 ^ 52 + 2 ^ 52 : Nat) : Int)) *
        ((2 ^ (((e + 1023 : Nat) : Int) - 1023 - 52).toNat : Nat) : Int), 1)
    else (if s then -((q - 2 ^ 52 + 2 ^ 52 : Nat) : Int) else
      ((q - 2 ^ 52 + 2 ^ 52 : Nat) : Int),
      2 ^ (-(((e + 1023 : Nat) : Int) - 1023 - 52)).toNat)) = _
  rw [hp, if_neg hneg, hden, hq]

theorem fhSmallScaledBounds (a : Nat) (ha : a ≠ 0) (hab : a < 2 ^ 16) :
    2 ^ 52 ≤ a * 2 ^ (52 - a.log2) ∧ a * 2 ^ (52 - a.log2) < 2 ^ 53 := by
  have he : a.log2 < 16 := (Nat.log2_lt ha).mpr hab
  have hlo : 2 ^ a.log2 ≤ a := (Nat.le_log2 ha).mp (Nat.le_refl _)
  have hhi : a < 2 ^ (a.log2 + 1) := (Nat.log2_lt ha).mp (Nat.lt_succ_self _)
  have hp : 2 ^ a.log2 * 2 ^ (52 - a.log2) = 2 ^ 52 := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
  have hp' : 2 ^ (a.log2 + 1) * 2 ^ (52 - a.log2) = 2 ^ 53 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  constructor
  · rw [← hp]
    exact Nat.mul_le_mul_right _ hlo
  · have hmul := Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos (52 - a.log2))
    rw [hp'] at hmul
    exact hmul

theorem fhSmallPack (s : Bool) (e q : Nat) (he : e ≤ 15)
    (hlo : 2 ^ 52 ≤ q) (hhi : q < 2 ^ 53) :
    Fl.packRounded (f := double) s q ((e : Int) - 52) = fhSmallEncode s e q := by
  have hz : (q == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  have hc : ¬ q ≥ 2 ^ (double.sb + 1) := by change ¬ q ≥ 2 ^ 53; omega
  have hs : ¬ q < 2 ^ double.sb := by change ¬ q < 2 ^ 52; omega
  have hp : (e : Int) - 52 + (double.bias : Int) + double.sb = (e : Int) + 1023 := by
    change (e : Int) - 52 + 1023 + 52 = _
    omega
  have hn : ¬ (e : Int) + 1023 ≥ (double.emax : Int) := by
    change ¬ (e : Int) + 1023 ≥ 2047
    omega
  have hnat : ((e : Int) + 1023).toNat = e + 1023 := by omega
  unfold Fl.packRounded
  simp only [hz, Bool.false_eq_true, ↓reduceIte, hc, hp, hn, hs, hnat]
  change Fl.ofBits ((if s then 2 ^ 63 else 0) +
    ((e + 1023) * 2 ^ 52 + (q - 2 ^ 52))) = _
  unfold fhSmallEncode
  rw [Nat.add_assoc]

theorem fhSmallOfIntEncode (n : Int) (hn : n ≠ 0) (hb : n.natAbs < 2 ^ 16) :
    (Fl.ofInt (f := double) n) =
      fhSmallEncode (decide (n < 0)) n.natAbs.log2
        (n.natAbs * 2 ^ (52 - n.natAbs.log2)) := by
  have ha : n.natAbs ≠ 0 := fun h => hn (Int.natAbs_eq_zero.mp h)
  have he : n.natAbs.log2 ≤ 15 := by
    have := (Nat.log2_lt ha).mpr hb
    omega
  have hlog := fhSmallFloorLog n.natAbs ha
  have hnBool : (n == 0) = false := beq_eq_false_iff_ne.mpr hn
  unfold Fl.ofInt Fl.roundRat
  simp only [show (1 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    hnBool, hlog]
  have hover : ¬ (n.natAbs.log2 : Int) ≥ (double.emax : Int) - double.bias := by
    change ¬ (n.natAbs.log2 : Int) ≥ 2047 - 1023
    omega
  have hunder : ¬ (n.natAbs.log2 : Int) < -((double.bias : Int) + double.sb) - 1 := by
    change ¬ (n.natAbs.log2 : Int) < -(1023 + 52) - 1
    omega
  rw [if_neg hover, if_neg hunder]
  have hk : max ((n.natAbs.log2 : Int) - double.sb)
      (1 - (double.bias : Int) - double.sb) = (n.natAbs.log2 : Int) - 52 := by
    change max ((n.natAbs.log2 : Int) - 52) (1 - 1023 - 52) = _
    exact Int.max_eq_left (by omega)
  rw [hk]
  have hkneg : ¬ (n.natAbs.log2 : Int) - 52 ≥ 0 := by omega
  have hkNat : (-((n.natAbs.log2 : Int) - 52)).toNat = 52 - n.natAbs.log2 := by omega
  rw [if_neg hkneg, hkNat, fhSmallRoundOne]
  obtain ⟨hlo, hhi⟩ := fhSmallScaledBounds n.natAbs ha hb
  exact fhSmallPack (decide (n < 0)) n.natAbs.log2 _ he hlo hhi

theorem fhSmallOfIntExact (n : Int) (hb : n.natAbs < 2 ^ 16) :
    (Fl.ofInt (f := double) n).isfinite = true ∧
      (Fl.ofInt (f := double) n).truncVal = n := by
  by_cases hn : n = 0
  · subst n
    decide
  · have ha : n.natAbs ≠ 0 := fun h => hn (Int.natAbs_eq_zero.mp h)
    have he : n.natAbs.log2 ≤ 15 := by
      have := (Nat.log2_lt ha).mpr hb
      omega
    obtain ⟨hlo, hhi⟩ := fhSmallScaledBounds n.natAbs ha hb
    rw [fhSmallOfIntEncode n hn hb]
    obtain ⟨hf, hr⟩ := fhSmallEncodeValue (decide (n < 0)) n.natAbs.log2 _ he hlo hhi
    refine ⟨hf, ?_⟩
    unfold Fl.truncVal
    rw [hr]
    dsimp only
    have hsign : (if decide (n < 0) then -((n.natAbs : Nat) : Int)
      else ((n.natAbs : Nat) : Int)) = n := by
      by_cases hs : n < 0
      · rw [if_pos (decide_eq_true hs), Int.ofNat_natAbs_of_nonpos (by omega)]
        omega
      · rw [if_neg (by simpa only [decide_eq_true_eq] using hs), Int.natAbs_of_nonneg (by omega)]
    have hmul : (if decide (n < 0) then -((n.natAbs * 2 ^ (52 - n.natAbs.log2) : Nat) : Int)
      else ((n.natAbs * 2 ^ (52 - n.natAbs.log2) : Nat) : Int)) =
        n * ((2 ^ (52 - n.natAbs.log2) : Nat) : Int) := by
      calc
        _ = (if decide (n < 0) then -(n.natAbs : Int) else (n.natAbs : Int)) *
            ((2 ^ (52 - n.natAbs.log2) : Nat) : Int) := by
          rw [Int.natCast_mul]
          cases decide (n < 0) <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.neg_mul]
        _ = _ := by rw [hsign]
    rw [hmul]
    exact Int.mul_tdiv_cancel n (by have := Nat.two_pow_pos (52 - n.natAbs.log2); omega)

theorem fhSmallOfIntFptosi (n : Int) (hb : n.natAbs < 2 ^ 16) :
    base.float.fptosi (T := .f64) .i64 (Fl.ofInt (f := double) n) = JInt.lit .i64 n := by
  obtain ⟨hf, ht⟩ := fhSmallOfIntExact n hb
  have hu : n ≤ (n.natAbs : Int) := Int.le_natAbs
  have hl : -n ≤ (n.natAbs : Int) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -n))
  change JInt.wrap .i64 (BitVec.ofInt 64
    (if (Fl.ofInt (f := double) n).isfinite then (Fl.ofInt (f := double) n).truncVal else 0)).toInt = _
  rw [if_pos hf, ht, BitVec.toInt_ofInt_eq_self (w := 64) (by decide) (by omega) (by omega)]
  rfl

end JuliaLean.ChatGPT.Batch8.Group14


/- FloatWork.lean -/

namespace JuliaLean.ChatGPT.Batch8.Group14

open JuliaLean JuliaLean.Promotion JuliaLean.base.hashing
open JuliaLean.Proofs.base.hashing

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem fhHashNanEqRight {f : Fmt} (x y : Fl f) (hy : y.isnan = true) :
    Fl.eq x y = false := by
  simp only [Fl.eq, hy, Bool.not_true, Bool.and_false, Bool.false_and]

theorem fhHashNanLtRight {f : Fmt} (x y : Fl f) (hy : y.isnan = true) :
    Fl.lt x y = false := by
  simp only [Fl.lt, hy, Bool.or_true, Bool.true_or, ite_true]

theorem fhHashIsnanCall {T : JuliaLean.base.float.FTy}
    (x : JuliaLean.base.float.FV T) : JuliaLean.base.float.isnan_IEEEFloat x = x.isnan := by
  change (!(Fl.eq x x)) = x.isnan
  cases hx : x.isnan <;> simp only [Fl.eq, hx, Fl.toBits, beq_self_eq_true,
    Bool.true_or, Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and]

theorem fhHashFloat64_nan (x : JuliaLean.base.float.FV .f64) (h : Word) (hx : x.isnan = true) :
    hashFloat64 float64Calls x h = xorWord hashNaNSeed h := by
  have hleI : float64Calls.leIntFloat (JInt.typemin .i64) x = false := by
    change (Fl.lt _ x || (Fl.eq _ x && _)) = false
    rw (transparency := .default) [fhHashNanLtRight _ x hx, fhHashNanEqRight _ x hx]
    rfl
  have hleU : float64Calls.leUIntFloat (JInt.lit .u64 0) x = false := by
    change (Fl.lt _ x || (Fl.eq _ x && _)) = false
    rw (transparency := .default) [fhHashNanLtRight _ x hx, fhHashNanEqRight _ x hx]
    rfl
  have hn : float64Calls.isnan x = true := by
    exact (fhHashIsnanCall (T := .f64) x).trans hx
  simp only [hashFloat64, hleI, hleU, Bool.false_and, Bool.false_eq_true,
    ite_false, hn, ite_true]

theorem fhHashFloat64_equalFloats (x y : JuliaLean.base.float.FV .f64) (h : Word)
    (heq : JuliaLean.base.float.isequal_IEEEFloat (T := .f64) x y = true) :
    hashFloat64 float64Calls x h = hashFloat64 float64Calls y h := by
  change ((x.isnan && y.isnan) || x.toBits == y.toBits) = true at heq
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at heq
  rcases heq with ⟨hx, hy⟩ | hbits
  · rw (transparency := .default) [fhHashFloat64_nan x h hx, fhHashFloat64_nan y h hy]
  · have hxy : x = y := by
      cases x with
      | mk xb =>
        cases y with
        | mk yb =>
          have hb : xb = yb := Fin.ext hbits
          cases hb
          rfl
    rw (transparency := .default) [hxy]







theorem fhHash64FlExt {f : Fmt} {x y : Fl f} (h : x.toBits = y.toBits) : x = y := by
  cases x with
  | mk xb =>
    cases y with
    | mk yb =>
      have hb : xb = yb := Fin.ext h
      cases hb
      rfl

theorem fhHash64ExpFromMagnitude {f : Fmt} (x : Fl f) :
    x.expField = x.magnitude / 2 ^ f.sb := by
  unfold Fl.expField Fl.magnitude
  rw (transparency := .default) [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_div_self]

theorem fhHash64FracFromMagnitude {f : Fmt} (x : Fl f) :
    x.frac = x.magnitude % 2 ^ f.sb := by
  unfold Fl.frac Fl.magnitude
  rw (transparency := .default) [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_mod]

theorem fhHash64TruncZero {f : Fmt} (x : Fl f) (hz : x.iszero = true) : x.truncVal = 0 := by
  have hm : x.magnitude = 0 := by simpa only [Fl.iszero, beq_iff_eq] using hz
  have he : x.expField = 0 := by rw (transparency := .default) [fhHash64ExpFromMagnitude, hm, Nat.zero_div]
  have hr : x.frac = 0 := by rw (transparency := .default) [fhHash64FracFromMagnitude, hm, Nat.zero_mod]
  by_cases hp : (f.sb : Int) ≤ 1 - (f.bias : Int)
  all_goals
    cases hf : x.isfinite <;> cases hs : x.signbit <;>
      simp [Fl.truncVal, Fl.toRat, hf, hs, he, hr, hp]

theorem fhHash64TruncCongr {f : Fmt} (x y : Fl f) (h : Fl.eq x y = true) :
    (if x.isfinite then x.truncVal else 0) = (if y.isfinite then y.truncVal else 0) := by
  simp only [Fl.eq, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  rcases h.2 with hb | ⟨hx, hy⟩
  · rw (transparency := .default) [fhHash64FlExt hb]
  · rw (transparency := .default) [fhHash64TruncZero x hx, fhHash64TruncZero y hy]
    simp only [ite_self]

theorem fhHash64FptosiCongr {T : base.float.FTy} (x y : base.float.FV T)
    (t : IntTy) (h : Fl.eq x y = true) :
    base.float.fptosi (T := T) t x = base.float.fptosi (T := T) t y := by
  unfold base.float.fptosi C.jlFptosi
  rw (transparency := .default) [fhHash64TruncCongr x y h]

theorem fhHash64FptouiCongr {T : base.float.FTy} (x y : base.float.FV T)
    (t : IntTy) (h : Fl.eq x y = true) :
    base.float.fptoui (T := T) t x = base.float.fptoui (T := T) t y := by
  unfold base.float.fptoui C.jlFptoui
  rw (transparency := .default) [fhHash64TruncCongr x y h]

theorem fhHash64LitSelf {t : IntTy} (x : JInt t) : JInt.wrap t x.val = x := by
  apply Subtype.ext
  exact wrapInt_of_inRange t x.val x.property

theorem fhHash64I64BitsValue (x : JInt .i64) :
    (BitVec.ofInt 64 x.val).toInt = x.val := by
  have hx := x.property
  change -(2 ^ 63 : Int) ≤ x.val ∧ x.val ≤ (2 ^ 63 : Int) - 1 at hx
  exact BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)

theorem fhHash64U64BitsValue (x : JInt .u64) :
    ((BitVec.ofInt 64 x.val).toNat : Int) = x.val := by
  have hx := x.property
  change 0 ≤ x.val ∧ x.val ≤ (2 ^ 64 : Int) - 1 at hx
  rw (transparency := .default) [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]
  change x.val % (2 ^ 64 : Int) = x.val
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem fhHash64EqI64 (x y : JInt .i64) (h : base.int.eq x y = true) : x = y := by
  change base.int.eq_int (JInt.wrap .i64 x.val) (JInt.wrap .i64 y.val) = true at h
  rw (transparency := .default) [fhHash64LitSelf, fhHash64LitSelf] at h
  change (BitVec.ofInt 64 x.val == BitVec.ofInt 64 y.val) = true at h
  have hb : BitVec.ofInt 64 x.val = BitVec.ofInt 64 y.val := by
    simpa only [beq_iff_eq] using h
  have hv := congrArg BitVec.toInt hb
  rw (transparency := .default) [fhHash64I64BitsValue, fhHash64I64BitsValue] at hv
  exact Subtype.ext hv

theorem fhHash64EqU64 (x y : JInt .u64) (h : base.int.eq x y = true) : x = y := by
  change base.int.eq_int (JInt.wrap .u64 x.val) (JInt.wrap .u64 y.val) = true at h
  rw (transparency := .default) [fhHash64LitSelf, fhHash64LitSelf] at h
  change (BitVec.ofInt 64 x.val == BitVec.ofInt 64 y.val) = true at h
  have hb : BitVec.ofInt 64 x.val = BitVec.ofInt 64 y.val := by
    simpa only [beq_iff_eq] using h
  have hv := congrArg (fun b : BitVec 64 => (b.toNat : Int)) hb
  rw (transparency := .default) [fhHash64U64BitsValue, fhHash64U64BitsValue] at hv
  exact Subtype.ext hv

theorem fhHash64EqI64Trunc (n : JInt .i64) (x : base.float.FV .f64)
    (h : base.float.eq_IF n x = true) : base.float.fptosi .i64 x = n := by
  change ((base.float.eq_IEEEFloat x (base.float.floatOfInt .f64 n) &&
    !(base.float.eq_IEEEFloat (base.float.floatOfInt .f64 n)
      (base.float.floatOfInt .f64 (base.int.typemax .i64)))) &&
    base.int.eq n (base.float.fptosi .i64 (base.float.floatOfInt .f64 n))) = true at h
  have hx : Fl.eq x (base.float.floatOfInt .f64 n) = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1
  have hn : n = base.float.fptosi .i64 (base.float.floatOfInt .f64 n) :=
    fhHash64EqI64 _ _ (Bool.and_eq_true_iff.mp h).2
  exact (fhHash64FptosiCongr (T := .f64) x _ .i64 hx).trans hn.symm

theorem fhHash64EqU64Trunc (n : JInt .u64) (x : base.float.FV .f64)
    (h : base.float.eq_IF n x = true) : base.float.fptoui .u64 x = n := by
  change ((base.float.eq_IEEEFloat x (base.float.floatOfInt .f64 n) &&
    !(base.float.eq_IEEEFloat (base.float.floatOfInt .f64 n)
      (base.float.floatOfInt .f64 (base.int.typemax .u64)))) &&
    base.int.eq n (base.float.fptoui .u64 (base.float.floatOfInt .f64 n))) = true at h
  have hx : Fl.eq x (base.float.floatOfInt .f64 n) = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1
  have hn : n = base.float.fptoui .u64 (base.float.floatOfInt .f64 n) :=
    fhHash64EqU64 _ _ (Bool.and_eq_true_iff.mp h).2
  exact (fhHash64FptouiCongr (T := .f64) x _ .u64 hx).trans hn.symm


/-- The source-selected integer/float equality contains ordinary equality. -/
theorem fhHash64IntegerEquality {T : base.float.FTy} {t : IntTy}
    (n : JInt t) (x : base.float.FV T)
    (h : JuliaLean.Proofs.base.hashing.integerFloatIsequal n x = true) :
    base.float.eq_IF n x = true := by
  unfold JuliaLean.Proofs.base.hashing.integerFloatIsequal at h
  simp only [base.operators.isequalRealFloat, base.float.isnan_Number,
    base.operators.bitAnd_eq, base.operators.bitOr_eq,
    Bool.false_and, Bool.false_or, Bool.and_eq_true] at h
  exact h.2

/-- The same source call also preserves the sign distinction of zero. -/
theorem fhHash64IntegerSign {T : base.float.FTy} {t : IntTy}
    (n : JInt t) (x : base.float.FV T)
    (h : JuliaLean.Proofs.base.hashing.integerFloatIsequal n x = true) :
    base.int.signbit n = base.float.signbit_float x := by
  unfold JuliaLean.Proofs.base.hashing.integerFloatIsequal at h
  simp only [base.operators.isequalRealFloat, base.float.isnan_Number,
    base.operators.bitAnd_eq, base.operators.bitOr_eq,
    Bool.false_and, Bool.false_or, Bool.and_eq_true] at h
  have hs := h.1
  change (base.int.signbit n == base.float.signbit_float x) = true at hs
  exact beq_iff_eq.mp hs

/-- Signed integer compatibility after establishing the source branch guard. -/
theorem fhHash64SignedBranch (x : base.float.FV .f64) (n : JInt .i64)
    (h : JuliaLean.base.hashing.Word)
    (he : JuliaLean.Proofs.base.hashing.integerFloatIsequal n x = true)
    (hg : (JuliaLean.Proofs.base.hashing.float64Calls.leIntFloat
        (JInt.typemin .i64) x &&
      JuliaLean.Proofs.base.hashing.float64Calls.ltFloatInt x
        (JInt.typemax .i64)) = true) :
    base.hashing.hashFloat64 JuliaLean.Proofs.base.hashing.float64Calls x h =
      base.hashing.hashInt64 n h := by
  have ht : JuliaLean.Proofs.base.hashing.float64Calls.fptosi x = n :=
    fhHash64EqI64Trunc n x (fhHash64IntegerEquality n x he)
  have hi : JuliaLean.Proofs.base.hashing.float64Calls.isequalI64 n x = true := he
  simp only [base.hashing.hashFloat64, hg, ite_true, ht, hi]

/-- Unsigned integer compatibility after establishing its two source guards. -/
theorem fhHash64UnsignedBranch (x : base.float.FV .f64) (n h : JuliaLean.base.hashing.Word)
    (he : JuliaLean.Proofs.base.hashing.integerFloatIsequal n x = true)
    (hgs : (JuliaLean.Proofs.base.hashing.float64Calls.leIntFloat
        (JInt.typemin .i64) x &&
      JuliaLean.Proofs.base.hashing.float64Calls.ltFloatInt x
        (JInt.typemax .i64)) = false)
    (hgu : (JuliaLean.Proofs.base.hashing.float64Calls.leUIntFloat
        (JInt.lit .u64 0) x &&
      JuliaLean.Proofs.base.hashing.float64Calls.ltFloatUInt x
        (JInt.typemax .u64)) = true) :
    base.hashing.hashFloat64 JuliaLean.Proofs.base.hashing.float64Calls x h =
      base.hashing.hashUInt64 n h := by
  have ht : JuliaLean.Proofs.base.hashing.float64Calls.fptoui x = n :=
    fhHash64EqU64Trunc n x (fhHash64IntegerEquality n x he)
  have hi : JuliaLean.Proofs.base.hashing.float64Calls.isequalU64 n x = true := he
  simp only [base.hashing.hashFloat64, hgs, Bool.false_eq_true, ite_false,
    hgu, ite_true, ht, hi]

namespace fhHash64Trunc

def fhMantissaNat {T : base.float.FTy} (x : base.float.FV T) : Nat :=
  x.frac + if x.expField = 0 then 0 else 2 ^ T.fmt.sb

def fhNumerator {T : base.float.FTy} (x : base.float.FV T) : Nat :=
  fhMantissaNat (T := T) x * 2 ^ (x.expField - (T.fmt.bias + T.fmt.sb))

def fhDenominator {T : base.float.FTy} (x : base.float.FV T) : Nat :=
  2 ^ (if x.expField = 0 then T.fmt.bias + T.fmt.sb - 1 else T.fmt.bias + T.fmt.sb - x.expField)

def fhQuotient {T : base.float.FTy} (x : base.float.FV T) : Nat := fhNumerator (T := T) x / fhDenominator (T := T) x

theorem fhRat_parts {T : base.float.FTy} (x : base.float.FV T) (hfin : x.isfinite = true) :
    x.toRat = (if x.signbit then -(fhNumerator (T := T) x : Int) else (fhNumerator (T := T) x : Int), fhDenominator (T := T) x) := by
  unfold Fl.toRat fhNumerator fhMantissaNat fhDenominator
  simp only [hfin, Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
  rcases Nat.eq_zero_or_pos x.expField with hz | hpos
  · rw (transparency := .default) [hz]
    simp only [↓reduceIte, Nat.add_zero]
    have hlt : (1 : Int) - (T.fmt.bias : Int) - T.fmt.sb < 0 := by cases T <;> decide
    rw (transparency := .default) [if_neg (Int.not_le.mpr hlt)]
    have hsub : 0 - (T.fmt.bias + T.fmt.sb) = 0 := Nat.zero_sub _
    have hpow : (-(1 - (T.fmt.bias : Int) - T.fmt.sb)).toNat = T.fmt.bias + T.fmt.sb - 1 := by
      cases T <;> decide
    rw (transparency := .default) [hsub, hpow, Nat.pow_zero, Nat.mul_one]
  · have hnz : x.expField ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
    simp only [hnz, ↓reduceIte]
    by_cases hge : ((x.expField : Int) - T.fmt.bias - T.fmt.sb) ≥ 0
    · rw (transparency := .default) [if_pos hge]
      have h1 : ((x.expField : Int) - T.fmt.bias - T.fmt.sb).toNat =
          x.expField - (T.fmt.bias + T.fmt.sb) := by omega
      have h2 : T.fmt.bias + T.fmt.sb - x.expField = 0 := by omega
      rw (transparency := .default) [h1, h2, Nat.pow_zero]
      refine Prod.ext ?_ rfl
      cases x.signbit <;> simp [Int.natCast_mul, Int.neg_mul]
    · rw (transparency := .default) [if_neg hge]
      have h1 : x.expField - (T.fmt.bias + T.fmt.sb) = 0 := by omega
      have h2 : (-((x.expField : Int) - T.fmt.bias - T.fmt.sb)).toNat =
          T.fmt.bias + T.fmt.sb - x.expField := by omega
      rw (transparency := .default) [h1, h2, Nat.pow_zero, Nat.mul_one]

theorem fhTruncVal_parts {T : base.float.FTy} (x : base.float.FV T) (hfin : x.isfinite = true) :
    x.truncVal = if x.signbit then -(fhQuotient (T := T) x : Int) else (fhQuotient (T := T) x : Int) := by
  unfold Fl.truncVal
  rw (transparency := .default) [fhRat_parts (T := T) x hfin]
  cases x.signbit <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Int.neg_tdiv, ← Int.ofNat_tdiv, fhQuotient]

end fhHash64Trunc


/-- Every binary64 significand contains fewer than 53 significant magnitude bits. -/
theorem fhHash64MantissaBound (x : base.float.FV .f64) :
    fhHash64Trunc.fhMantissaNat (T := .f64) x < 2 ^ 53 := by
  have hr : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  unfold fhHash64Trunc.fhMantissaNat
  change x.frac + (if x.expField = 0 then 0 else 2 ^ 52) < 2 ^ 53
  split <;> omega

/-- Below the 2^63 binade, truncation has magnitude strictly below 2^63. -/
theorem fhHash64QuotientLt63 (x : base.float.FV .f64) (he : x.expField < 1086) :
    fhHash64Trunc.fhQuotient (T := .f64) x < 2 ^ 63 := by
  have hm := fhHash64MantissaBound x
  have hk : x.expField - (base.float.FTy.f64.fmt.bias + base.float.FTy.f64.fmt.sb) ≤ 10 := by
    change x.expField - 1075 ≤ 10
    omega
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have hn : fhHash64Trunc.fhNumerator (T := .f64) x < 2 ^ 63 := by
    unfold fhHash64Trunc.fhNumerator
    calc
      _ ≤ fhHash64Trunc.fhMantissaNat (T := .f64) x * 2 ^ 10 := Nat.mul_le_mul_left _ hp
      _ < 2 ^ 53 * 2 ^ 10 := Nat.mul_lt_mul_of_pos_right hm (by decide)
      _ = 2 ^ 63 := by decide
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn

theorem fhHash64TruncSmallExponent (x : base.float.FV .f64) (he : x.expField < 1086) :
    x.isfinite = true ∧ -(2 ^ 63 : Int) < x.truncVal ∧ x.truncVal < (2 ^ 63 : Int) := by
  have hn : x.expField ≠ 2047 := by omega
  have hf : x.isfinite = true := by
    change (x.expField != 2047) = true
    exact bne_iff_ne.mpr hn
  refine ⟨hf, ?_⟩
  have hq := fhHash64QuotientLt63 x he
  rw (transparency := .default) [fhHash64Trunc.fhTruncVal_parts (T := .f64) x hf]
  cases x.signbit <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem fhHash64TruncNonnegative (x : base.float.FV .f64)
    (hf : x.isfinite = true) (hs : x.signbit = false) : 0 ≤ x.truncVal := by
  rw (transparency := .default) [fhHash64Trunc.fhTruncVal_parts (T := .f64) x hf, hs]
  simp only [Bool.false_eq_true, ite_false, Int.natCast_nonneg]

/-- A positive raw pattern below 2^63 has a nonnegative signed-64 truncation. -/
theorem fhHash64PositiveBitsTrunc (x : base.float.FV .f64)
    (hb : x.toBits < 0x43e0000000000000) :
    x.isfinite = true ∧ 0 ≤ x.truncVal ∧ x.truncVal < (2 ^ 63 : Int) := by
  have he : x.expField < 1086 := by
    change x.toBits / 4503599627370496 % 2048 < 1086
    have hq : x.toBits / 4503599627370496 < 1086 :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 4503599627370496)).mpr hb
    rw (transparency := .default) [Nat.mod_eq_of_lt (by omega)]
    exact hq
  obtain ⟨hf, _, hu⟩ := fhHash64TruncSmallExponent x he
  have hs : x.signbit = false := by
    change decide (x.toBits ≥ 9223372036854775808) = false
    apply decide_eq_false
    omega
  exact ⟨hf, fhHash64TruncNonnegative x hf hs, hu⟩


def fhHash64SignedLower : base.float.FV .f64 := Fl.ofBits 0xc3e0000000000000
def fhHash64SignedUpper : base.float.FV .f64 := Fl.ofBits 0x43e0000000000000
def fhHash64UnsignedUpper : base.float.FV .f64 := Fl.ofBits 0x43f0000000000000

theorem fhHash64FloatOfI64 (n : JInt .i64) :
    base.float.floatOfInt .f64 n = (Fl.ofInt n.val : Fl double) := by
  change Fl.ofInt (BitVec.ofInt 64 n.val).toInt = _
  rw (transparency := .default) [fhHash64I64BitsValue] <;> rfl

theorem fhHash64FloatOfU64 (n : JInt .u64) :
    base.float.floatOfInt .f64 n = (Fl.ofInt n.val : Fl double) := by
  change Fl.ofInt ((BitVec.ofInt 64 n.val).toNat : Int) = _
  rw (transparency := .default) [fhHash64U64BitsValue] <;> rfl

theorem fhHash64MinFloat : base.float.floatOfInt .f64 (JInt.typemin .i64) = fhHash64SignedLower := by decide
theorem fhHash64MaxFloat : base.float.floatOfInt .f64 (JInt.typemax .i64) = fhHash64SignedUpper := by decide
theorem fhHash64UMaxFloat : base.float.floatOfInt .f64 (JInt.typemax .u64) = fhHash64UnsignedUpper := by decide
theorem fhHash64UZeroFloat : base.float.floatOfInt .f64 (JInt.lit .u64 0) = (Fl.zero false : Fl double) := by
  change (Fl.ofInt (0 : Int) : Fl double) = Fl.zero false
  rfl

/-- The installed signed branch guard compares against the exact binary64 powers of two. -/
theorem fhHash64SignedGuardEq (x : base.float.FV .f64) :
    (JuliaLean.Proofs.base.hashing.float64Calls.leIntFloat (JInt.typemin .i64) x &&
      JuliaLean.Proofs.base.hashing.float64Calls.ltFloatInt x (JInt.typemax .i64)) =
    (Fl.le fhHash64SignedLower x && Fl.lt x fhHash64SignedUpper) := by
  change ((Fl.lt (base.float.floatOfInt .f64 (JInt.typemin .i64)) x ||
    (Fl.eq (base.float.floatOfInt .f64 (JInt.typemin .i64)) x &&
      (Fl.eq (base.float.floatOfInt .f64 (JInt.typemin .i64))
        (base.float.floatOfInt .f64 (JInt.typemax .i64)) ||
       base.int.le (JInt.typemin .i64)
        (base.float.fptosi .i64 (T := .f64)
          (base.float.floatOfInt .f64 (JInt.typemin .i64)))))) &&
    (Fl.lt x (base.float.floatOfInt .f64 (JInt.typemax .i64)) ||
      ((Fl.eq x (base.float.floatOfInt .f64 (JInt.typemax .i64)) &&
        Fl.lt (base.float.floatOfInt .f64 (JInt.typemax .i64))
          (base.float.floatOfInt .f64 (JInt.typemax .i64))) &&
       base.int.lt (base.float.fptosi .i64 (T := .f64)
         (base.float.floatOfInt .f64 (JInt.typemax .i64))) (JInt.typemax .i64)))) = _
  rw (transparency := .default) [fhHash64MinFloat, fhHash64MaxFloat]
  have hlow : base.int.le (JInt.typemin .i64)
      (base.float.fptosi .i64 (T := .f64) fhHash64SignedLower) = true := by decide
  have hself : Fl.lt fhHash64SignedUpper fhHash64SignedUpper = false := by decide
  simp only [hlow, hself, Bool.or_true, Bool.and_true, Bool.and_false,
    Bool.false_and, Bool.or_false, Fl.le]

/-- The installed unsigned branch guard uses zero and the exact 2^64 endpoint. -/
theorem fhHash64UnsignedGuardEq (x : base.float.FV .f64) :
    (JuliaLean.Proofs.base.hashing.float64Calls.leUIntFloat (JInt.lit .u64 0) x &&
      JuliaLean.Proofs.base.hashing.float64Calls.ltFloatUInt x (JInt.typemax .u64)) =
    (Fl.le (Fl.zero false) x && Fl.lt x fhHash64UnsignedUpper) := by
  change ((Fl.lt (base.float.floatOfInt .f64 (JInt.lit .u64 0)) x ||
    (Fl.eq (base.float.floatOfInt .f64 (JInt.lit .u64 0)) x &&
      (Fl.eq (base.float.floatOfInt .f64 (JInt.lit .u64 0))
        (base.float.floatOfInt .f64 (JInt.typemax .u64)) ||
       base.int.le (JInt.lit .u64 0)
        (base.float.fptoui .u64 (T := .f64)
          (base.float.floatOfInt .f64 (JInt.lit .u64 0)))))) &&
    (Fl.lt x (base.float.floatOfInt .f64 (JInt.typemax .u64)) ||
      ((Fl.eq x (base.float.floatOfInt .f64 (JInt.typemax .u64)) &&
        Fl.lt (base.float.floatOfInt .f64 (JInt.typemax .u64))
          (base.float.floatOfInt .f64 (JInt.typemax .u64))) &&
       base.int.lt (base.float.fptoui .u64 (T := .f64)
         (base.float.floatOfInt .f64 (JInt.typemax .u64))) (JInt.typemax .u64)))) = _
  rw (transparency := .default) [fhHash64UZeroFloat, fhHash64UMaxFloat]
  have hlow : base.int.le (JInt.lit .u64 0)
      (base.float.fptoui .u64 (T := .f64) (Fl.zero false)) = true := by decide
  have hself : Fl.lt fhHash64UnsignedUpper fhHash64UnsignedUpper = false := by decide
  rw (transparency := .default) [hlow, hself]
  simp only [Bool.or_true, Bool.and_true, Bool.and_false,
    Bool.false_and, Bool.or_false, Fl.le] <;> rfl

theorem fhHash64SignedValue (x : base.float.FV .f64) (hf : x.isfinite = true)
    (hl : -(2 ^ 63 : Int) ≤ x.truncVal) (hu : x.truncVal < (2 ^ 63 : Int)) :
    (base.float.fptosi .i64 x).val = x.truncVal := by
  change wrapInt .i64 (BitVec.ofInt 64 (if x.isfinite then x.truncVal else 0)).toInt = _
  rw (transparency := .default) [if_pos hf, BitVec.toInt_ofInt_eq_self (w := 64) (by decide) hl hu]
  exact wrapInt_of_inRange .i64 x.truncVal (by
    change -(2 ^ 63 : Int) ≤ x.truncVal ∧ x.truncVal ≤ (2 ^ 63 : Int) - 1
    omega)

theorem fhHash64UnsignedValue (x : base.float.FV .f64) (hf : x.isfinite = true)
    (hl : 0 ≤ x.truncVal) (hu : x.truncVal < (2 ^ 64 : Int)) :
    (base.float.fptoui .u64 x).val = x.truncVal := by
  change wrapInt .u64 ((BitVec.ofInt 64
    ((if x.isfinite then x.truncVal else 0).natAbs : Int)).toNat : Int) = _
  rw (transparency := .default) [if_pos hf, Int.natAbs_of_nonneg hl, BitVec.toNat_ofInt,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]
  change wrapInt .u64 (x.truncVal % (2 ^ 64 : Int)) = x.truncVal
  rw (transparency := .default) [Int.emod_eq_of_lt hl hu]
  exact wrapInt_of_inRange .u64 x.truncVal (by
    change 0 ≤ x.truncVal ∧ x.truncVal ≤ (2 ^ 64 : Int) - 1
    omega)


theorem fhHash64EqTrans {f : Fmt} (x y z : Fl f)
    (hxy : Fl.eq x y = true) (hyz : Fl.eq y z = true) : Fl.eq x z = true := by
  have hxy' := hxy
  simp only [Fl.eq, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hxy'
  rcases hxy'.2 with hb | ⟨hx, hy⟩
  · rw (transparency := .default) [fhHash64FlExt hb]
    exact hyz
  · have hyz' := hyz
    simp only [Fl.eq, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hyz'
    rcases hyz'.2 with hb | ⟨_, hz⟩
    · rw (transparency := .default) [← fhHash64FlExt hb]
      exact hxy
    · simp only [Fl.eq, hxy'.1.1, hyz'.1.2, hx, hz, Bool.true_and, Bool.or_true]

theorem fhHash64LtIrrefl {f : Fmt} (x : Fl f) : Fl.lt x x = false := by
  cases hn : x.isnan <;> cases hz : x.iszero <;> cases hs : x.signbit <;>
    simp [Fl.lt, hn, hz, hs]

theorem fhHash64LtNotEq {f : Fmt} (x y : Fl f) (hl : Fl.lt x y = true) : Fl.eq x y = false := by
  apply Bool.eq_false_iff.mpr
  intro he
  simp only [Fl.eq, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at he
  rcases he.2 with hb | ⟨hx, hy⟩
  · have heq := fhHash64FlExt hb
    subst y
    rw (transparency := .default) [fhHash64LtIrrefl] at hl
    contradiction
  · simp [Fl.lt, hx, hy] at hl

theorem fhHash64LtSignedUpperBits (x : base.float.FV .f64)
    (hs : x.signbit = false) (hl : Fl.lt x fhHash64SignedUpper = true) :
    x.toBits < 0x43e0000000000000 := by
  have hn : fhHash64SignedUpper.isnan = false := by decide
  have hz : fhHash64SignedUpper.iszero = false := by decide
  have hb : fhHash64SignedUpper.signbit = false := by decide
  cases hx : x.isnan with
  | true => simp only [Fl.lt, hx, Bool.true_or, ite_true, Bool.false_eq_true] at hl
  | false =>
      simp only [Fl.lt, hx, hn, hz, hs, hb, Bool.false_or, Bool.or_false,
        Bool.and_false, Bool.false_eq_true, ite_false] at hl
      change decide (x.toBits < 0x43e0000000000000) = true at hl
      exact of_decide_eq_true hl

theorem fhHash64SignedGuardNonnegativeTrunc (x : base.float.FV .f64)
    (hs : x.signbit = false)
    (hg : (JuliaLean.Proofs.base.hashing.float64Calls.leIntFloat (JInt.typemin .i64) x &&
      JuliaLean.Proofs.base.hashing.float64Calls.ltFloatInt x (JInt.typemax .i64)) = true) :
    x.isfinite = true ∧ 0 ≤ x.truncVal ∧ x.truncVal < (2 ^ 63 : Int) := by
  rw (transparency := .default) [fhHash64SignedGuardEq] at hg
  exact fhHash64PositiveBitsTrunc x (fhHash64LtSignedUpperBits x hs (Bool.and_eq_true_iff.mp hg).2)

theorem fhHash64EqI64Self (n : JInt .i64) : base.int.eq n n = true := by
  change base.int.eq_int (JInt.wrap .i64 n.val) (JInt.wrap .i64 n.val) = true
  rw (transparency := .default) [fhHash64LitSelf]
  change (BitVec.ofInt 64 n.val == BitVec.ofInt 64 n.val) = true
  exact beq_self_eq_true _

theorem fhHash64IntegerIsequalOfEqAndSign {T : base.float.FTy} {t : IntTy}
    (n : JInt t) (x : base.float.FV T) (he : base.float.eq_IF n x = true)
    (hs : base.int.signbit n = base.float.signbit_float x) :
    JuliaLean.Proofs.base.hashing.integerFloatIsequal n x = true := by
  simp only [JuliaLean.Proofs.base.hashing.integerFloatIsequal,
    base.operators.isequalRealFloat, base.float.isnan_Number,
    base.operators.bitAnd_eq, base.operators.bitOr_eq, Bool.false_and,
    Bool.false_or, he, Bool.and_true]
  change (base.int.signbit n == base.float.signbit_float x) = true
  exact beq_iff_eq.mpr hs


theorem fhHash64BitsFromSign (x : base.float.FV .f64) :
    x.toBits = (if x.signbit then 2 ^ 63 else 0) + x.magnitude := by
  have hb : x.toBits < 2 ^ 64 := x.bits.isLt
  by_cases hs : x.toBits ≥ 2 ^ 63
  · have hsign : x.signbit = true := decide_eq_true hs
    rw (transparency := .default) [hsign]
    change x.toBits = 9223372036854775808 + x.toBits % 9223372036854775808
    rw (transparency := .default) [Nat.mod_eq_sub_mod hs, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hsign : x.signbit = false := decide_eq_false hs
    rw (transparency := .default) [hsign]
    change x.toBits = 0 + x.toBits % 9223372036854775808
    rw (transparency := .default) [Nat.mod_eq_of_lt (by omega)]
    omega

theorem fhHash64NotNaNOfMagnitude (x : base.float.FV .f64)
    (hm : x.magnitude ≤ 1087 * 2 ^ 52) : x.isnan = false := by
  have he : x.expField ≤ 1087 := by
    rw (transparency := .default) [fhHash64ExpFromMagnitude]
    change x.magnitude / 4503599627370496 ≤ 1087
    have hlt : x.magnitude < 1088 * 4503599627370496 := by omega
    have hq := (Nat.div_lt_iff_lt_mul (by decide : 0 < 4503599627370496)).mpr hlt
    exact Nat.le_of_lt_succ hq
  have hn : x.expField ≠ 2047 := by omega
  change ((x.expField == 2047) && (x.frac != 0)) = false
  simp only [beq_eq_false_iff_ne.mpr hn, Bool.false_and]

/-- Magnitudes at most 2^63 satisfy the signed guard after excluding the positive endpoint. -/
theorem fhHash64SignedGuardOfMagnitude (x : base.float.FV .f64)
    (hm : x.magnitude ≤ 1086 * 2 ^ 52)
    (hne : Fl.eq x fhHash64SignedUpper = false) :
    (JuliaLean.Proofs.base.hashing.float64Calls.leIntFloat (JInt.typemin .i64) x &&
      JuliaLean.Proofs.base.hashing.float64Calls.ltFloatInt x (JInt.typemax .i64)) = true := by
  have hn := fhHash64NotNaNOfMagnitude x (by omega)
  have hln : fhHash64SignedLower.isnan = false := by decide
  have hlz : fhHash64SignedLower.iszero = false := by decide
  have hls : fhHash64SignedLower.signbit = true := by decide
  have hlb : fhHash64SignedLower.toBits = 0xc3e0000000000000 := by decide
  have hun : fhHash64SignedUpper.isnan = false := by decide
  have huz : fhHash64SignedUpper.iszero = false := by decide
  have hus : fhHash64SignedUpper.signbit = false := by decide
  have hub : fhHash64SignedUpper.toBits = 0x43e0000000000000 := by decide
  have hb := fhHash64BitsFromSign x
  have hneq : x.toBits ≠ 0x43e0000000000000 := by
    simpa [Fl.eq, hn, hun, huz, hub] using hne
  rw (transparency := .default) [fhHash64SignedGuardEq]
  cases hs : x.signbit <;>
    simp only [hs, Bool.false_eq_true, ite_false, ite_true, Nat.zero_add] at hb
  all_goals
    simp [Fl.le, Fl.lt, Fl.eq, hn, hln, hlz, hls, hlb, hun, huz, hus, hub, hs] <;> omega

/-- The unsigned guard holds for nonnegative magnitudes below its excluded endpoint. -/
theorem fhHash64UnsignedGuardOfMagnitude (x : base.float.FV .f64)
    (hm : x.magnitude ≤ 1087 * 2 ^ 52) (hs : x.signbit = false)
    (hne : Fl.eq x fhHash64UnsignedUpper = false) :
    (JuliaLean.Proofs.base.hashing.float64Calls.leUIntFloat (JInt.lit .u64 0) x &&
      JuliaLean.Proofs.base.hashing.float64Calls.ltFloatUInt x (JInt.typemax .u64)) = true := by
  have hn := fhHash64NotNaNOfMagnitude x hm
  have hzn : (Fl.zero false : base.float.FV .f64).isnan = false := by decide
  have hzz : (Fl.zero false : base.float.FV .f64).iszero = true := by decide
  have hzs : (Fl.zero false : base.float.FV .f64).signbit = false := by decide
  have hzb : (Fl.zero false : base.float.FV .f64).toBits = 0 := by decide
  have hun : fhHash64UnsignedUpper.isnan = false := by decide
  have huz : fhHash64UnsignedUpper.iszero = false := by decide
  have hus : fhHash64UnsignedUpper.signbit = false := by decide
  have hub : fhHash64UnsignedUpper.toBits = 0x43f0000000000000 := by decide
  have hb := fhHash64BitsFromSign x
  simp only [hs, Bool.false_eq_true, ite_false, Nat.zero_add] at hb
  have hneq : x.toBits ≠ 0x43f0000000000000 := by
    simpa [Fl.eq, hn, hun, huz, hub] using hne
  rw (transparency := .default) [fhHash64UnsignedGuardEq]
  cases hz : x.iszero <;>
    simp [Fl.le, Fl.lt, Fl.eq, hn, hzn, hzz, hzs, hzb, hun, huz, hus, hub, hs, hz] <;> omega

theorem fhHash64ZeroOfIsZero (x : base.float.FV .f64) (hz : x.iszero = true) :
    x = Fl.zero x.signbit := by
  have hm : x.magnitude = 0 := by simpa only [Fl.iszero, beq_iff_eq] using hz
  have hb := fhHash64BitsFromSign x
  rw (transparency := .default) [hm, Nat.add_zero] at hb
  apply fhHash64FlExt
  have hzeroBits : (Fl.zero (f := base.float.FTy.f64.fmt) x.signbit).toBits =
      (if x.signbit then 2 ^ 63 else 0) := by
    cases x.signbit <;> decide
  exact hb.trans hzeroBits.symm

theorem fhHash64ZeroSignedGuard (s : Bool) :
    (JuliaLean.Proofs.base.hashing.float64Calls.leIntFloat (JInt.typemin .i64) (Fl.zero s) &&
      JuliaLean.Proofs.base.hashing.float64Calls.ltFloatInt (Fl.zero s) (JInt.typemax .i64)) = true := by
  rw (transparency := .default) [fhHash64SignedGuardEq]
  cases s <;> decide

theorem fhHash64ZeroUnsignedGuard (s : Bool) :
    (JuliaLean.Proofs.base.hashing.float64Calls.leUIntFloat (JInt.lit .u64 0) (Fl.zero s) &&
      JuliaLean.Proofs.base.hashing.float64Calls.ltFloatUInt (Fl.zero s) (JInt.typemax .u64)) = true := by
  rw (transparency := .default) [fhHash64UnsignedGuardEq]
  cases s <;> decide

theorem fhHash64SignedGuardCongr (x y : base.float.FV .f64) (he : Fl.eq x y = true) :
    (JuliaLean.Proofs.base.hashing.float64Calls.leIntFloat (JInt.typemin .i64) x &&
      JuliaLean.Proofs.base.hashing.float64Calls.ltFloatInt x (JInt.typemax .i64)) =
    (JuliaLean.Proofs.base.hashing.float64Calls.leIntFloat (JInt.typemin .i64) y &&
      JuliaLean.Proofs.base.hashing.float64Calls.ltFloatInt y (JInt.typemax .i64)) := by
  simp only [Fl.eq, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at he
  rcases he.2 with hb | ⟨hx, hy⟩
  · rw (transparency := .default) [fhHash64FlExt hb]
  · rw (transparency := .default) [fhHash64ZeroOfIsZero x hx, fhHash64ZeroOfIsZero y hy,
      fhHash64ZeroSignedGuard, fhHash64ZeroSignedGuard]

theorem fhHash64UnsignedGuardCongr (x y : base.float.FV .f64) (he : Fl.eq x y = true) :
    (JuliaLean.Proofs.base.hashing.float64Calls.leUIntFloat (JInt.lit .u64 0) x &&
      JuliaLean.Proofs.base.hashing.float64Calls.ltFloatUInt x (JInt.typemax .u64)) =
    (JuliaLean.Proofs.base.hashing.float64Calls.leUIntFloat (JInt.lit .u64 0) y &&
      JuliaLean.Proofs.base.hashing.float64Calls.ltFloatUInt y (JInt.typemax .u64)) := by
  simp only [Fl.eq, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at he
  rcases he.2 with hb | ⟨hx, hy⟩
  · rw (transparency := .default) [fhHash64FlExt hb]
  · rw (transparency := .default) [fhHash64ZeroOfIsZero x hx, fhHash64ZeroOfIsZero y hy,
      fhHash64ZeroUnsignedGuard, fhHash64ZeroUnsignedGuard]

open JuliaLean JuliaLean.Promotion

/-- Wrapping a represented signed integer preserves its value. -/
theorem fhHashSignI64WrapSelf (n : JInt .i64) : JInt.wrap .i64 n.val = n := by
  apply Subtype.ext
  exact wrapInt_of_inRange .i64 n.val n.property

/-- The signed BitVec interpretation agrees with the represented Int64 value. -/
theorem fhHashSignI64BitsValue (n : JInt .i64) :
    (BitVec.ofInt 64 n.val).toInt = n.val := by
  have hlo := n.property.1
  have hhi := n.property.2
  change -9223372036854775808 ≤ n.val at hlo
  change n.val ≤ 9223372036854775807 at hhi
  apply BitVec.toInt_ofInt_eq_self (by decide : 0 < 64)
  · exact hlo
  · change n.val < 9223372036854775808
    omega

/-- The installed signed-integer sign test reads the mathematical sign. -/
theorem fhHashSignI64Value (n : JInt .i64) :
    JuliaLean.base.int.signbit n = decide (n.val < 0) := by
  change decide ((BitVec.ofInt 64 (JInt.wrap .i64 n.val).val).toInt < 0) =
    decide (n.val < 0)
  rw (transparency := .default) [fhHashSignI64WrapSelf, fhHashSignI64BitsValue]

/-- Every UInt64 has a false sign test. -/
theorem fhHashSignU64False (n : JInt .u64) : JuliaLean.base.int.signbit n = false := by
  rfl

/-- Reinterpreting Float64 bits as Int64 preserves their signed BitVec interpretation. -/
theorem fhHashSignReinterpretFloat64Value (x : JuliaLean.base.float.FV .f64) :
    (JuliaLean.base.float.reinterpret_Int_Float .i64 x).val =
      (BitVec.ofNat 64 x.toBits).toInt := by
  change wrapInt .i64 (BitVec.ofNat 64 x.toBits).toInt = _
  have hlo := BitVec.le_toInt (BitVec.ofNat 64 x.toBits)
  have hhi := BitVec.toInt_lt (x := BitVec.ofNat 64 x.toBits)
  change -9223372036854775808 ≤ (BitVec.ofNat 64 x.toBits).toInt at hlo
  change (BitVec.ofNat 64 x.toBits).toInt < 9223372036854775808 at hhi
  apply wrapInt_of_inRange
  change -9223372036854775808 ≤ (BitVec.ofNat 64 x.toBits).toInt ∧
    (BitVec.ofNat 64 x.toBits).toInt ≤ 9223372036854775807
  omega

/-- The installed Float64 sign test agrees with the IEEE stored sign bit. -/
theorem fhHashSignFloat64 (x : JuliaLean.base.float.FV .f64) :
    JuliaLean.base.float.signbit_float (T := .f64) x = x.signbit := by
  unfold JuliaLean.base.float.signbit_float
  change base.int.signbit (base.float.reinterpret_Int_Float .i64 x) = x.signbit
  rw (transparency := .default) [fhHashSignI64Value, fhHashSignReinterpretFloat64Value]
  change decide ((BitVec.ofNat 64 x.toBits).toInt < 0) = decide (x.toBits ≥ 2 ^ 63)
  apply decide_eq_decide.mpr
  have hbits := x.bits.isLt
  change x.toBits < 2 ^ 64 at hbits
  rw (transparency := .default) [BitVec.toInt_neg_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbits]
  omega

open JuliaLean JuliaLean.Promotion

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- Nearest rounding can increase the truncated fhQuotient by at most one. -/
theorem fhHashBtRoundQuotientUpper (a d : Nat) :
    Fl.roundQuotient a d ≤ a / d + 1 := by
  unfold Fl.roundQuotient
  dsimp only
  split <;> omega

/-- Integral scaled significands need no rounding. -/
theorem fhHashBtRoundQuotientOne (a : Nat) : Fl.roundQuotient a 1 = a := by
  simp only [Fl.roundQuotient, Nat.div_one, Nat.mod_one, Nat.mul_zero,
    show decide (0 > 1) = false from rfl, show (0 == 1) = false from rfl,
    Bool.false_and, Bool.false_or, Bool.false_eq_true, if_false]

/-- The rational log helper specializes exactly to the integer binary logarithm. -/
theorem fhHashBtFloorLogNat (a : Nat) (ha : a ≠ 0) :
    Fl.floorLog2Rat a 1 = (a.log2 : Int) := by
  have hp : 2 ^ a.log2 ≤ a := (Nat.le_log2 ha).mp (Nat.le_refl _)
  simp only [Fl.floorLog2Rat, show Nat.log2 1 = 0 from rfl,
    Int.natCast_zero, Int.sub_zero, show (a.log2 : Int) ≥ 0 by omega,
    ↓reduceIte, Int.toNat_natCast, Nat.one_mul,
    show ¬ a < 2 ^ a.log2 by omega, ↓reduceIte]

/-- The normal integer scaling produces at most the carry value 2^53. -/
theorem fhHashBtScaledRoundBound (a e : Nat) (ha : a < 2 ^ (e + 1)) :
    (let k := (e : Int) - 52
     let scaled := if k ≥ 0 then (a, 2 ^ k.toNat) else (a * 2 ^ (-k).toNat, 1)
     Fl.roundQuotient scaled.1 scaled.2) ≤ 2 ^ 53 := by
  dsimp only
  by_cases he : 52 ≤ e
  · rw (transparency := .default) [ite_eq_left (show (e : Int) - 52 ≥ 0 by omega)]
    have hk : ((e : Int) - 52).toNat = e - 52 := by omega
    rw (transparency := .default) [hk]
    dsimp only
    have hp : 2 ^ (e + 1) = 2 ^ 53 * 2 ^ (e - 52) := by
      rw (transparency := .default) [← Nat.pow_add]
      exact congrArg (fun k : Nat => 2 ^ k) (by omega)
    have hd : a / 2 ^ (e - 52) < 2 ^ 53 :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by rw (transparency := .default) [← hp]; exact ha)
    have hr := fhHashBtRoundQuotientUpper a (2 ^ (e - 52))
    omega
  · rw (transparency := .default) [ite_eq_right (show ¬ (e : Int) - 52 ≥ 0 by omega)]
    have hk : (-((e : Int) - 52)).toNat = 52 - e := by omega
    rw (transparency := .default) [hk, fhHashBtRoundQuotientOne]
    have hm := Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos (52 - e))
    have hp : 2 ^ (e + 1) * 2 ^ (52 - e) = 2 ^ 53 := by
      rw (transparency := .default) [← Nat.pow_add]
      exact congrArg (fun k : Nat => 2 ^ k) (by omega)
    rw (transparency := .default) [hp] at hm
    omega

/-- Packing an in-range magnitude preserves both the magnitude and chosen sign. -/
theorem fhHashBtOfBitsParts (negative : Bool) (mag : Nat) (hmag : mag < 2 ^ 63) :
    let x := Fl.ofBits (f := double) ((if negative then 2 ^ 63 else 0) + mag)
    x.magnitude = mag ∧ x.signbit = negative := by
  cases negative <;>
    simp only [Fl.ofBits, Fl.toBits, Fl.magnitude, Fl.signbit, double, Fmt.width,
      Nat.reduceAdd, Nat.reducePow, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  · have hb : mag < 18446744073709551616 := by omega
    rw (transparency := .default) [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega)]
    exact ⟨rfl, by simp only [show ¬ mag ≥ 9223372036854775808 by omega, decide_false]⟩
  · have hb : 9223372036854775808 + mag < 18446744073709551616 := by omega
    rw (transparency := .default) [Nat.mod_eq_of_lt hb]
    have hm : (9223372036854775808 + mag) % 9223372036854775808 = mag := by
      rw (transparency := .default) [Nat.add_mod_left, Nat.mod_eq_of_lt hmag]
    rw (transparency := .default) [hm]
    exact ⟨rfl, by simp only [show 9223372036854775808 + mag ≥ 9223372036854775808 by omega, decide_true]⟩


/-- A rounded normal significand stays below the next binary exponent endpoint. -/
theorem fhHashBtPackBounds (negative : Bool) (q e : Nat)
    (hq : q ≤ 2 ^ 53) (he : e ≤ 63) :
    let x := Fl.packRounded (f := double) negative q ((e : Int) - 52)
    x.magnitude ≤ (e + 1024) * 2 ^ 52 ∧ x.signbit = negative := by
  dsimp only
  by_cases hz : q = 0
  · subst q
    have hparts : (Fl.zero (f := double) negative).magnitude = 0 ∧
        (Fl.zero (f := double) negative).signbit = negative := by
      simpa only [Fl.zero, double, Nat.reduceAdd, Nat.add_zero] using
        (fhHashBtOfBitsParts negative 0 (by decide))
    change (Fl.zero (f := double) negative).magnitude ≤ _ ∧
      (Fl.zero (f := double) negative).signbit = negative
    exact ⟨by rw (transparency := .default) [hparts.1]; omega, hparts.2⟩
  · by_cases hc : q ≥ 2 ^ 53
    · have hqeq : q = 2 ^ 53 := by omega
      subst q
      have hpack : Fl.packRounded (f := double) negative (2 ^ 53) ((e : Int) - 52) =
          Fl.ofBits (f := double)
            ((if negative then 2 ^ 63 else 0) + (e + 1024) * 2 ^ 52) := by
        unfold Fl.packRounded
        simp only [double, Nat.reduceAdd, Nat.reducePow, Nat.reduceBEq,
          Nat.le_refl, Bool.false_eq_true, ite_false, ite_true, Nat.reduceDiv,
          Nat.reduceLT, Nat.sub_self, Nat.add_zero]
        change (if (e : Int) - 52 + 1 + 1023 + 52 ≥ 2047 then Fl.inf negative else
          Fl.ofBits ((if negative then 2 ^ 63 else 0) +
            ((e : Int) - 52 + 1 + 1023 + 52).toNat * 2 ^ 52)) = _
        rw (transparency := .default) [ite_eq_right (by omega)]
        have hp : ((e : Int) - 52 + 1 + 1023 + 52).toNat = e + 1024 := by omega
        rw (transparency := .default) [hp]
      rw (transparency := .default) [hpack]
      have hparts := fhHashBtOfBitsParts negative ((e + 1024) * 2 ^ 52) (by omega)
      exact ⟨Nat.le_of_eq hparts.1, hparts.2⟩
    · let mag := if q < 2 ^ 52 then q else (e + 1023) * 2 ^ 52 + (q - 2 ^ 52)
      have hm : mag ≤ (e + 1024) * 2 ^ 52 := by
        dsimp only [mag]
        split <;> omega
      have hpack : Fl.packRounded (f := double) negative q ((e : Int) - 52) =
          Fl.ofBits (f := double) ((if negative then 2 ^ 63 else 0) + mag) := by
        have hqtest : (q == 0) = false := by
          simpa only [beq_eq_false_iff_ne] using hz
        unfold Fl.packRounded
        simp only [hqtest, Bool.false_eq_true, ↓reduceIte,
          show ¬ q ≥ 2 ^ (double.sb + 1) from hc, ↓reduceIte]
        have hp : (e : Int) - 52 + (double.bias : Int) + double.sb = (e : Int) + 1023 := by
          change (e : Int) - 52 + 1023 + 52 = _
          omega
        have hnot : ¬ (e : Int) + 1023 ≥ (double.emax : Int) := by
          change ¬ (e : Int) + 1023 ≥ 2047
          omega
        have hnat : ((e : Int) + 1023).toNat = e + 1023 := by omega
        simp only [hp, hnot, ↓reduceIte, hnat] <;> rfl
      rw (transparency := .default) [hpack]
      have hparts := fhHashBtOfBitsParts negative mag (by omega)
      exact ⟨by rw (transparency := .default) [hparts.1]; exact hm, hparts.2⟩

/-- Integer conversion below the 64-bit magnitude limit preserves sign and an explicit endpoint bound. -/
theorem fhHashBtOfIntLogBounds (n : Int) (hn : n ≠ 0)
    (hlog : n.natAbs.log2 ≤ 63) :
    (Fl.ofInt (f := double) n).magnitude ≤ (n.natAbs.log2 + 1024) * 2 ^ 52 ∧
      (Fl.ofInt (f := double) n).signbit = decide (n < 0) := by
  have habs : n.natAbs ≠ 0 := by
    intro hzero
    exact hn (Int.natAbs_eq_zero.mp hzero)
  have hlogExact := fhHashBtFloorLogNat n.natAbs habs
  have hupper : n.natAbs < 2 ^ (n.natAbs.log2 + 1) :=
    (Nat.log2_lt habs).mp (Nat.lt_succ_self _)
  have hrounded := fhHashBtScaledRoundBound n.natAbs n.natAbs.log2 hupper
  have hnBool : (n == 0) = false := by
    simpa only [beq_eq_false_iff_ne] using hn
  unfold Fl.ofInt Fl.roundRat
  simp only [show (1 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    hnBool, hlogExact]
  have hover : ¬ (n.natAbs.log2 : Int) ≥ (double.emax : Int) - double.bias := by
    change ¬ (n.natAbs.log2 : Int) ≥ 2047 - 1023
    omega
  have hunder : ¬ (n.natAbs.log2 : Int) < -((double.bias : Int) + double.sb) - 1 := by
    change ¬ (n.natAbs.log2 : Int) < -(1023 + 52) - 1
    omega
  rw (transparency := .default) [ite_eq_right hover, ite_eq_right hunder]
  have hk : max ((n.natAbs.log2 : Int) - double.sb)
      (1 - (double.bias : Int) - double.sb) = (n.natAbs.log2 : Int) - 52 := by
    change max ((n.natAbs.log2 : Int) - 52) (1 - 1023 - 52) = _
    exact Int.max_eq_left (by omega)
  rw (transparency := .default) [hk]
  simp only [Nat.one_mul]
  exact fhHashBtPackBounds (decide (n < 0)) _ n.natAbs.log2 hrounded hlog


/-- Every nonnegative 64-bit integer converts at or below the positive 2^64 endpoint. -/
theorem fhHashBtOfIntUnsignedBounds (n : Int) (hlo : 0 ≤ n) (hhi : n < 2 ^ 64) :
    (Fl.ofInt (f := double) n).magnitude ≤ 1087 * 2 ^ 52 ∧
      (Fl.ofInt (f := double) n).signbit = false := by
  by_cases hz : n = 0
  · subst n
    decide +kernel
  · have habs : n.natAbs ≠ 0 := by
      intro hzero
      exact hz (Int.natAbs_eq_zero.mp hzero)
    have ha : n.natAbs < 2 ^ 64 := by
      have hcast := Int.natAbs_of_nonneg hlo
      omega
    have helog : n.natAbs.log2 < 64 := (Nat.log2_lt habs).mpr ha
    have hlog : n.natAbs.log2 ≤ 63 := by omega
    obtain ⟨hm, hs⟩ := fhHashBtOfIntLogBounds n hz hlog
    refine ⟨Nat.le_trans hm (Nat.mul_le_mul_right _ (Nat.add_le_add_right hlog 1024)), ?_⟩
    rw (transparency := .default) [hs]
    simp only [show ¬ n < 0 by omega, decide_false]

/-- Signed 64-bit magnitudes convert at or below the 2^63 endpoint, preserving their sign. -/
theorem fhHashBtOfIntSignedBounds (n : Int) (hn : n.natAbs ≤ 2 ^ 63) :
    (Fl.ofInt (f := double) n).magnitude ≤ 1086 * 2 ^ 52 ∧
      (Fl.ofInt (f := double) n).signbit = decide (n < 0) := by
  by_cases hz : n = 0
  · subst n
    decide +kernel
  · by_cases hstrict : n.natAbs < 2 ^ 63
    · have habs : n.natAbs ≠ 0 := by
        intro hzero
        exact hz (Int.natAbs_eq_zero.mp hzero)
      have helog : n.natAbs.log2 < 63 := (Nat.log2_lt habs).mpr hstrict
      have hlog : n.natAbs.log2 ≤ 62 := Nat.le_of_lt_succ helog
      obtain ⟨hm, hs⟩ := fhHashBtOfIntLogBounds n hz (Nat.le_trans hlog (by decide))
      exact ⟨Nat.le_trans hm (Nat.mul_le_mul_right _ (Nat.add_le_add_right hlog 1024)), hs⟩
    · have heq : n.natAbs = 2 ^ 63 := by omega
      rcases Int.natAbs_eq_iff.mp heq with hpos | hneg
      · rw (transparency := .default) [hpos]
        decide +kernel
      · rw (transparency := .default) [hneg]
        decide +kernel

theorem fhHash64SignedGuardOfIntegerEq (n : JInt .i64) (x : base.float.FV .f64)
    (he : base.float.eq_IF n x = true) :
    (JuliaLean.Proofs.base.hashing.float64Calls.leIntFloat (JInt.typemin .i64) x &&
      JuliaLean.Proofs.base.hashing.float64Calls.ltFloatInt x (JInt.typemax .i64)) = true := by
  change ((Fl.eq x (base.float.floatOfInt .f64 n) &&
    !(Fl.eq (base.float.floatOfInt .f64 n)
      (base.float.floatOfInt .f64 (JInt.typemax .i64)))) &&
    base.int.eq n (base.float.fptosi .i64 (base.float.floatOfInt .f64 n))) = true at he
  have hxy := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp he).1).1
  have hnot := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp he).1).2
  have hne : Fl.eq (base.float.floatOfInt .f64 n) fhHash64SignedUpper = false := by
    rw (transparency := .default) [fhHash64MaxFloat] at hnot
    simpa only [Bool.not_eq_true'] using hnot
  have hbounds := n.property
  have habs : n.val.natAbs ≤ 2 ^ 63 := by
    change -9223372036854775808 ≤ n.val ∧ n.val ≤ 9223372036854775807 at hbounds
    by_cases hn : 0 ≤ n.val
    · have hc := Int.natAbs_of_nonneg hn
      omega
    · have hc := Int.ofNat_natAbs_of_nonpos (by omega : n.val ≤ 0)
      omega
  have hm := (fhHashBtOfIntSignedBounds n.val habs).1
  rw (transparency := .default) [← fhHash64FloatOfI64 n] at hm
  exact (fhHash64SignedGuardCongr x _ hxy).trans (fhHash64SignedGuardOfMagnitude _ hm hne)

theorem fhHash64UnsignedGuardOfIntegerEq (n : JInt .u64) (x : base.float.FV .f64)
    (he : base.float.eq_IF n x = true) :
    (JuliaLean.Proofs.base.hashing.float64Calls.leUIntFloat (JInt.lit .u64 0) x &&
      JuliaLean.Proofs.base.hashing.float64Calls.ltFloatUInt x (JInt.typemax .u64)) = true := by
  change ((Fl.eq x (base.float.floatOfInt .f64 n) &&
    !(Fl.eq (base.float.floatOfInt .f64 n)
      (base.float.floatOfInt .f64 (JInt.typemax .u64)))) &&
    base.int.eq n (base.float.fptoui .u64 (base.float.floatOfInt .f64 n))) = true at he
  have hxy := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp he).1).1
  have hnot := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp he).1).2
  have hne : Fl.eq (base.float.floatOfInt .f64 n) fhHash64UnsignedUpper = false := by
    rw (transparency := .default) [fhHash64UMaxFloat] at hnot
    simpa only [Bool.not_eq_true'] using hnot
  have hbounds := n.property
  change 0 ≤ n.val ∧ n.val ≤ 18446744073709551615 at hbounds
  obtain ⟨hm, hs⟩ := fhHashBtOfIntUnsignedBounds n.val hbounds.1 (by omega)
  rw (transparency := .default) [← fhHash64FloatOfU64 n] at hm hs
  exact (fhHash64UnsignedGuardCongr x _ hxy).trans (fhHash64UnsignedGuardOfMagnitude _ hm hs hne)

/-- The signed-integer conjunct follows from exact equality and the derived guard. -/
theorem fhHash64SignedHash (x : base.float.FV .f64) (n : JInt .i64)
    (h : base.hashing.Word)
    (he : JuliaLean.Proofs.base.hashing.integerFloatIsequal n x = true) :
    base.hashing.hashFloat64 JuliaLean.Proofs.base.hashing.float64Calls x h =
      base.hashing.hashInt64 n h :=
  fhHash64SignedBranch x n h he
    (fhHash64SignedGuardOfIntegerEq n x (fhHash64IntegerEquality n x he))

/-- A UInt64 value using the signed branch has the same represented nonnegative integer. -/
theorem fhHash64UnsignedLowHash (x : base.float.FV .f64) (n h : base.hashing.Word)
    (he : JuliaLean.Proofs.base.hashing.integerFloatIsequal n x = true)
    (hg : (JuliaLean.Proofs.base.hashing.float64Calls.leIntFloat (JInt.typemin .i64) x &&
      JuliaLean.Proofs.base.hashing.float64Calls.ltFloatInt x (JInt.typemax .i64)) = true) :
    base.hashing.hashFloat64 JuliaLean.Proofs.base.hashing.float64Calls x h =
      base.hashing.hashUInt64 n h := by
  have hsign := fhHash64IntegerSign n x he
  rw (transparency := .default) [fhHashSignU64False, fhHashSignFloat64] at hsign
  have hs : x.signbit = false := hsign.symm
  obtain ⟨hf, hlo, hhi⟩ := fhHash64SignedGuardNonnegativeTrunc x hs hg
  let m : JInt .i64 := base.float.fptosi .i64 x
  have hmv : m.val = x.truncVal := fhHash64SignedValue x hf (by omega) hhi
  have hut := fhHash64EqU64Trunc n x (fhHash64IntegerEquality n x he)
  have hnv := congrArg (fun z : JInt .u64 => z.val) hut
  rw (transparency := .default) [fhHash64UnsignedValue x hf hlo (by omega)] at hnv
  have hmval : m.val = n.val := hmv.trans hnv
  have hcast : base.float.floatOfInt .f64 m = base.float.floatOfInt .f64 n := by
    rw (transparency := .default) [fhHash64FloatOfI64, fhHash64FloatOfU64, hmval]
  have heu := fhHash64IntegerEquality n x he
  change ((Fl.eq x (base.float.floatOfInt .f64 n) &&
    !(Fl.eq (base.float.floatOfInt .f64 n)
      (base.float.floatOfInt .f64 (JInt.typemax .u64)))) &&
    base.int.eq n (base.float.fptoui .u64 (base.float.floatOfInt .f64 n))) = true at heu
  have hxy : Fl.eq x (base.float.floatOfInt .f64 m) = true := by
    rw (transparency := .default) [hcast]
    exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp heu).1).1
  have hguard := hg
  rw (transparency := .default) [fhHash64SignedGuardEq] at hguard
  have hlt := (Bool.and_eq_true_iff.mp hguard).2
  have hneq : Fl.eq (base.float.floatOfInt .f64 m) fhHash64SignedUpper = false := by
    apply Bool.eq_false_iff.mpr
    intro heq
    have hh := fhHash64EqTrans x (base.float.floatOfInt .f64 m) fhHash64SignedUpper hxy heq
    rw (transparency := .default) [fhHash64LtNotEq x fhHash64SignedUpper hlt] at hh
    cases hh
  have hback : base.float.fptosi .i64 (base.float.floatOfInt .f64 m) = m :=
    (fhHash64FptosiCongr (T := .f64) x _ .i64 hxy).symm
  have hei : base.float.eq_IF m x = true := by
    change ((Fl.eq x (base.float.floatOfInt .f64 m) &&
      !(Fl.eq (base.float.floatOfInt .f64 m)
        (base.float.floatOfInt .f64 (JInt.typemax .i64)))) &&
      base.int.eq m (base.float.fptosi .i64 (base.float.floatOfInt .f64 m))) = true
    rw (transparency := .default) [fhHash64MaxFloat, hxy, hneq, hback, fhHash64EqI64Self] <;> rfl
  have hsm : base.int.signbit m = false := by
    rw (transparency := .default) [fhHashSignI64Value, hmv]
    exact decide_eq_false (by omega)
  have his : JuliaLean.Proofs.base.hashing.integerFloatIsequal m x = true :=
    fhHash64IntegerIsequalOfEqAndSign m x hei (by rw (transparency := .default) [hsm, fhHashSignFloat64, hs])
  rw (transparency := .default) [fhHash64SignedBranch x m h his hg]
  change base.hashing.hashUInt64 (JInt.lit .u64 m.val) h = base.hashing.hashUInt64 n h
  rw (transparency := .default) [hmval, show JInt.lit .u64 n.val = n from fhHash64LitSelf n]

/-- Both source routes for unsigned integer equality now return the same UInt64 hash. -/
theorem fhHash64UnsignedHash (x : base.float.FV .f64) (n h : base.hashing.Word)
    (he : JuliaLean.Proofs.base.hashing.integerFloatIsequal n x = true) :
    base.hashing.hashFloat64 JuliaLean.Proofs.base.hashing.float64Calls x h =
      base.hashing.hashUInt64 n h := by
  by_cases hg : (JuliaLean.Proofs.base.hashing.float64Calls.leIntFloat (JInt.typemin .i64) x &&
      JuliaLean.Proofs.base.hashing.float64Calls.ltFloatInt x (JInt.typemax .i64)) = true
  · exact fhHash64UnsignedLowHash x n h he hg
  · exact fhHash64UnsignedBranch x n h he (Bool.eq_false_iff.mpr hg)
      (fhHash64UnsignedGuardOfIntegerEq n x (fhHash64IntegerEquality n x he))

/-- Assembly from the independently checked Float64-pair conjunct. -/
theorem fhHash64Consistency
    (floatPair : ∀ (x y : base.float.FV .f64) (h : base.hashing.Word),
      base.float.isequal_IEEEFloat x y = true →
      base.hashing.hashFloat64 JuliaLean.Proofs.base.hashing.float64Calls x h =
        base.hashing.hashFloat64 JuliaLean.Proofs.base.hashing.float64Calls y h) :
    JuliaLean.Proofs.base.hashing.Round1.Float64HashConsistency :=
  ⟨floatPair, fhHash64SignedHash, fhHash64UnsignedHash⟩

theorem HashingFloat64Consistency_proven :
    JuliaLean.Proofs.base.hashing.Round1.Float64HashConsistency :=
  fhHash64Consistency fhHashFloat64_equalFloats


end JuliaLean.ChatGPT.Batch8.Group14


/- HalfArithmetic.lean -/

namespace JuliaLean.ChatGPT.Batch8.Group14
open JuliaLean JuliaLean.Promotion JuliaLean.base.hashing
open JuliaLean.Proofs.base.hashing

/-- Nearest rounding can increase the truncated quotient by at most one. -/
theorem hfRoundQuotientUpper (a d : Nat) :
    Fl.roundQuotient a d ≤ a / d + 1 := by
  unfold Fl.roundQuotient
  dsimp only
  split <;> omega

/-- Integral scaled significands need no rounding. -/
theorem hfRoundQuotientOne (a : Nat) : Fl.roundQuotient a 1 = a := by
  simp only [Fl.roundQuotient, Nat.div_one, Nat.mod_one, Nat.mul_zero,
    show decide ((0 : Nat) > 1) = false from rfl,
    show ((0 : Nat) == 1) = false from rfl,
    Bool.false_and, Bool.false_or, Bool.false_eq_true, ite_false]

/-- The rational log helper specializes exactly to the integer binary logarithm. -/
theorem hfFloorLogNat (a : Nat) (ha : a ≠ 0) :
    Fl.floorLog2Rat a 1 = (a.log2 : Int) := by
  have hp : 2 ^ a.log2 ≤ a := (Nat.le_log2 ha).mp (Nat.le_refl _)
  simp only [Fl.floorLog2Rat, show Nat.log2 1 = 0 from rfl,
    Int.natCast_zero, Int.sub_zero, show (a.log2 : Int) ≥ 0 by omega,
    ↓reduceIte, Int.toNat_natCast, Nat.one_mul,
    show ¬ a < 2 ^ a.log2 by omega, ↓reduceIte]

/-- The normal integer scaling produces at most the carry value 2^53. -/
theorem hfScaledRoundUpper (a e : Nat) (ha : a < 2 ^ (e + 1)) :
    (let k := (e : Int) - 52
     let scaled := if k ≥ 0 then (a, 2 ^ k.toNat) else (a * 2 ^ (-k).toNat, 1)
     Fl.roundQuotient scaled.1 scaled.2) ≤ 2 ^ 53 := by
  dsimp only
  by_cases he : 52 ≤ e
  · rw [ite_eq_left (show (e : Int) - 52 ≥ 0 by omega)]
    have hk : ((e : Int) - 52).toNat = e - 52 := by omega
    rw [hk]
    dsimp only
    have hp : 2 ^ (e + 1) = 2 ^ 53 * 2 ^ (e - 52) := by
      rw [← Nat.pow_add]
      exact congrArg (fun k : Nat => 2 ^ k) (by omega)
    have hd : a / 2 ^ (e - 52) < 2 ^ 53 :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by rw [← hp]; exact ha)
    have hr := hfRoundQuotientUpper a (2 ^ (e - 52))
    omega
  · rw [ite_eq_right (show ¬ (e : Int) - 52 ≥ 0 by omega)]
    have hk : (-((e : Int) - 52)).toNat = 52 - e := by omega
    rw [hk, hfRoundQuotientOne]
    have hm := Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos (52 - e))
    have hp : 2 ^ (e + 1) * 2 ^ (52 - e) = 2 ^ 53 := by
      rw [← Nat.pow_add]
      exact congrArg (fun k : Nat => 2 ^ k) (by omega)
    rw [hp] at hm
    omega

/-- Packing an in-range magnitude preserves both the magnitude and chosen sign. -/
theorem hfOfBitsParts (negative : Bool) (mag : Nat) (hmag : mag < 2 ^ 63) :
    let x := Fl.ofBits (f := double) ((if negative then 2 ^ 63 else 0) + mag)
    x.magnitude = mag ∧ x.signbit = negative := by
  cases negative <;>
    simp only [Fl.ofBits, Fl.toBits, Fl.magnitude, Fl.signbit, double, Fmt.width,
      Nat.reduceAdd, Nat.reducePow, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  · have hb : mag < 18446744073709551616 := by omega
    rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega)]
    exact ⟨rfl, by simp only [show ¬ mag ≥ 9223372036854775808 by omega, decide_false]⟩
  · have hb : 9223372036854775808 + mag < 18446744073709551616 := by omega
    rw [Nat.mod_eq_of_lt hb]
    have hm : (9223372036854775808 + mag) % 9223372036854775808 = mag := by
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt hmag]
    rw [hm]
    exact ⟨rfl, by simp only [show 9223372036854775808 + mag ≥ 9223372036854775808 by omega, decide_true]⟩



/-- Rounding to nearest never falls below the truncated quotient. -/
theorem hfRoundQuotientLower (a d : Nat) : a / d ≤ Fl.roundQuotient a d := by
  unfold Fl.roundQuotient
  dsimp only
  split <;> omega

/-- The normal integer scaling reaches the leading significand bit. -/
theorem hfScaledRoundLower (a e : Nat) (ha : 2 ^ e ≤ a) :
    2 ^ 52 ≤
      (let k := (e : Int) - 52
       let scaled := if k ≥ 0 then (a, 2 ^ k.toNat) else (a * 2 ^ (-k).toNat, 1)
       Fl.roundQuotient scaled.1 scaled.2) := by
  dsimp only
  by_cases he : 52 ≤ e
  · rw [ite_eq_left (show (e : Int) - 52 ≥ 0 by omega)]
    have hk : ((e : Int) - 52).toNat = e - 52 := by omega
    rw [hk]
    dsimp only
    have hp : 2 ^ 52 * 2 ^ (e - 52) = 2 ^ e := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hd : 2 ^ 52 ≤ a / 2 ^ (e - 52) :=
      (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by rw [hp]; exact ha)
    exact Nat.le_trans hd (hfRoundQuotientLower _ _)
  · rw [ite_eq_right (show ¬ (e : Int) - 52 ≥ 0 by omega)]
    have hk : (-((e : Int) - 52)).toNat = 52 - e := by omega
    rw [hk, hfRoundQuotientOne]
    have hm := Nat.mul_le_mul_right (2 ^ (52 - e)) ha
    have hp : 2 ^ e * 2 ^ (52 - e) = 2 ^ 52 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hp] at hm
    exact hm

/-- A normalized significand retains its binary exponent lower endpoint. -/
theorem hfPackLower (negative : Bool) (q e : Nat)
    (hlo : 2 ^ 52 ≤ q) (hhi : q ≤ 2 ^ 53) (he : e ≤ 63) :
    (e + 1023) * 2 ^ 52 ≤
      (Fl.packRounded (f := double) negative q ((e : Int) - 52)).magnitude := by
  have hz : q ≠ 0 := by omega
  by_cases hc : q ≥ 2 ^ 53
  · have hqeq : q = 2 ^ 53 := by omega
    subst q
    have hpack : Fl.packRounded (f := double) negative (2 ^ 53) ((e : Int) - 52) =
        Fl.ofBits (f := double)
          ((if negative then 2 ^ 63 else 0) + (e + 1024) * 2 ^ 52) := by
      unfold Fl.packRounded
      simp only [double, Nat.reduceAdd, Nat.reducePow, Nat.reduceBEq,
        Nat.le_refl, Bool.false_eq_true, ite_false, ite_true, Nat.reduceDiv,
        Nat.reduceLT, Nat.sub_self, Nat.add_zero]
      change (if (e : Int) - 52 + 1 + 1023 + 52 ≥ 2047 then Fl.inf negative else
        Fl.ofBits ((if negative then 2 ^ 63 else 0) +
          ((e : Int) - 52 + 1 + 1023 + 52).toNat * 2 ^ 52)) = _
      rw [ite_eq_right (by omega)]
      have hp : ((e : Int) - 52 + 1 + 1023 + 52).toNat = e + 1024 := by omega
      rw [hp]
    rw [hpack]
    have hparts := hfOfBitsParts negative ((e + 1024) * 2 ^ 52) (by omega)
    rw [hparts.1]
    omega
  · let mag := (e + 1023) * 2 ^ 52 + (q - 2 ^ 52)
    have hmag : mag < 2 ^ 63 := by dsimp only [mag]; omega
    have hpack : Fl.packRounded (f := double) negative q ((e : Int) - 52) =
        Fl.ofBits (f := double) ((if negative then 2 ^ 63 else 0) + mag) := by
      have hqtest : (q == 0) = false := beq_eq_false_iff_ne.mpr hz
      unfold Fl.packRounded
      simp only [hqtest, Bool.false_eq_true, ↓reduceIte,
        show ¬ q ≥ 2 ^ (double.sb + 1) from hc, ↓reduceIte]
      have hp : (e : Int) - 52 + (double.bias : Int) + double.sb = (e : Int) + 1023 := by
        change (e : Int) - 52 + 1023 + 52 = _
        omega
      have hnot : ¬ (e : Int) + 1023 ≥ (double.emax : Int) := by
        change ¬ (e : Int) + 1023 ≥ 2047
        omega
      have hnat : ((e : Int) + 1023).toNat = e + 1023 := by omega
      simp only [hp, hnot, ↓reduceIte, hnat,
        show ¬ q < 2 ^ double.sb from Nat.not_lt.mpr hlo, ↓reduceIte]
      rfl
    rw [hpack, (hfOfBitsParts negative mag hmag).1]
    dsimp only [mag]
    omega

/-- Converting a nonzero 64-bit magnitude cannot erase its logarithmic lower bound. -/
theorem hfOfIntLower (n : Int) (hn : n ≠ 0) (hlog : n.natAbs.log2 ≤ 63) :
    (n.natAbs.log2 + 1023) * 2 ^ 52 ≤ (Fl.ofInt (f := double) n).magnitude := by
  have habs : n.natAbs ≠ 0 := by
    intro hzero
    exact hn (Int.natAbs_eq_zero.mp hzero)
  have hlogExact := hfFloorLogNat n.natAbs habs
  have hlower : 2 ^ n.natAbs.log2 ≤ n.natAbs :=
    (Nat.le_log2 habs).mp (Nat.le_refl _)
  have hupper : n.natAbs < 2 ^ (n.natAbs.log2 + 1) :=
    (Nat.log2_lt habs).mp (Nat.lt_succ_self _)
  have hroundedlo := hfScaledRoundLower n.natAbs n.natAbs.log2 hlower
  have hroundedhi := hfScaledRoundUpper n.natAbs n.natAbs.log2 hupper
  have hnBool : (n == 0) = false := beq_eq_false_iff_ne.mpr hn
  unfold Fl.ofInt Fl.roundRat
  simp only [show (1 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    hnBool, hlogExact]
  have hover : ¬ (n.natAbs.log2 : Int) ≥ (double.emax : Int) - double.bias := by
    change ¬ (n.natAbs.log2 : Int) ≥ 2047 - 1023
    omega
  have hunder : ¬ (n.natAbs.log2 : Int) < -((double.bias : Int) + double.sb) - 1 := by
    change ¬ (n.natAbs.log2 : Int) < -(1023 + 52) - 1
    omega
  rw [ite_eq_right hover, ite_eq_right hunder]
  have hk : max ((n.natAbs.log2 : Int) - double.sb)
      (1 - (double.bias : Int) - double.sb) = (n.natAbs.log2 : Int) - 52 := by
    change max ((n.natAbs.log2 : Int) - 52) (1 - 1023 - 52) = _
    exact Int.max_eq_left (by omega)
  rw [hk]
  simp only [Nat.one_mul]
  exact hfPackLower (decide (n < 0)) _ n.natAbs.log2 hroundedlo hroundedhi hlog

/-- A double conversion in the half precision finite range came from a small integer. -/
theorem hfOfIntSmall_of_magnitude (n : Int) (hn : n.natAbs ≤ 2 ^ 63)
    (hm : (Fl.ofInt (f := double) n).magnitude < 1039 * 2 ^ 52) :
    n.natAbs < 2 ^ 16 := by
  by_cases hz : n = 0
  · subst n
    decide
  · have ha : n.natAbs ≠ 0 := by
      intro hzero
      exact hz (Int.natAbs_eq_zero.mp hzero)
    have hlog : n.natAbs.log2 ≤ 63 := by
      have hlt : n.natAbs < 2 ^ 64 := by omega
      have hh := (Nat.log2_lt ha).mpr hlt
      omega
    have hlo := hfOfIntLower n hz hlog
    have hel : n.natAbs.log2 < 16 := by omega
    exact (Nat.log2_lt ha).mp hel


/-- IEEE numerical equality identifies the unsigned magnitudes, including signed zeros. -/
theorem hfEqMagnitude {f : Fmt} (x y : Fl f) (h : Fl.eq x y = true) :
    x.magnitude = y.magnitude := by
  simp only [Fl.eq, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  rcases h.2 with hbits | ⟨hx, hy⟩
  · unfold Fl.magnitude
    rw [hbits]
  · have hx0 : x.magnitude = 0 := by simpa only [Fl.iszero, beq_iff_eq] using hx
    have hy0 : y.magnitude = 0 := by simpa only [Fl.iszero, beq_iff_eq] using hy
    exact hx0.trans hy0.symm

/-- Raw double magnitudes below the infinity encoding are finite. -/
theorem hfFiniteFromMagnitude (x : base.float.FV .f64)
    (hm : x.magnitude < 2047 * 2 ^ 52) : x.isfinite = true := by
  have he : x.expField = x.magnitude / 2 ^ 52 := by
    change x.toBits / 2 ^ 52 % 2 ^ 11 =
      (x.toBits % (2 ^ 52 * 2 ^ 11)) / 2 ^ 52
    exact (Nat.mod_mul_right_div_self x.toBits (2 ^ 52) (2 ^ 11)).symm
  have hdiv : x.magnitude / 2 ^ 52 < 2047 :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 52)).mpr hm
  change (x.expField != 2047) = true
  rw [he]
  exact bne_iff_ne.mpr (Nat.ne_of_lt hdiv)

end JuliaLean.ChatGPT.Batch8.Group14


/- FiniteHelper.lean -/

namespace JuliaLean.ChatGPT.Batch8.Group14
open JuliaLean JuliaLean.Promotion JuliaLean.C

/-- A bit decomposition independent of any theorem imported from another proof file. -/
theorem hfFiniteWidthPow (f : Fmt) : 2 ^ f.width = 2 * 2 ^ (f.eb + f.sb) := by
  rw [Fmt.width, show 1 + f.eb + f.sb = f.eb + f.sb + 1 by omega,
    Nat.pow_succ, Nat.mul_comm]

theorem hfFiniteBitsSplit {f : Fmt} (x : Fl f) :
    x.toBits = (if x.signbit then 2 ^ (f.eb + f.sb) else 0) + x.magnitude ∧
    x.magnitude < 2 ^ (f.eb + f.sb) := by
  have h : x.toBits < 2 * 2 ^ (f.eb + f.sb) := by
    have h1 := x.bits.isLt
    have h2 := hfFiniteWidthPow f
    have h3 : x.toBits = x.bits.val := rfl
    omega
  have hW := Nat.two_pow_pos (f.eb + f.sb)
  refine ⟨?_, Nat.mod_lt _ hW⟩
  unfold Fl.signbit Fl.magnitude
  by_cases hs : x.toBits ≥ 2 ^ (f.eb + f.sb)
  · rw [Nat.mod_eq_sub_mod hs, Nat.mod_eq_of_lt (by omega)]
    simp only [hs, decide_true, ite_true]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp [hs]

theorem hfFiniteExpField {f : Fmt} (x : Fl f) : x.expField = x.magnitude / 2 ^ f.sb := by
  unfold Fl.expField Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_div_self]

theorem hfFiniteFrac {f : Fmt} (x : Fl f) : x.frac = x.magnitude % 2 ^ f.sb := by
  unfold Fl.frac Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_mod]

theorem hfFiniteNegParts {f : Fmt} (x : Fl f) :
    (Fl.neg x).magnitude = x.magnitude ∧ (Fl.neg x).signbit = !x.signbit := by
  obtain ⟨hbx, hmx⟩ := hfFiniteBitsSplit x
  have h2 := hfFiniteWidthPow f
  have hpos : 0 < 2 ^ (f.eb + f.sb) := Nat.two_pow_pos _
  unfold Fl.neg
  cases hs : x.signbit
  · simp only [Bool.false_eq_true, ite_false, Bool.not_false]
    rw [hs] at hbx
    simp only [Bool.false_eq_true, ite_false, Nat.zero_add] at hbx
    have hlt : x.toBits + 2 ^ (f.eb + f.sb) < 2 ^ f.width := by omega
    unfold Fl.magnitude Fl.signbit
    change ((x.toBits + 2 ^ (f.eb + f.sb)) % 2 ^ f.width) % 2 ^ (f.eb + f.sb) = x.magnitude ∧
      decide (((x.toBits + 2 ^ (f.eb + f.sb)) % 2 ^ f.width) ≥ 2 ^ (f.eb + f.sb)) = true
    rw [Nat.mod_eq_of_lt hlt]
    refine ⟨?_, ?_⟩
    · rw [Nat.add_comm, Nat.add_mod_left]
      rfl
    · rw [decide_eq_true_iff]
      omega
  · simp only [ite_true, Bool.not_true]
    rw [hs] at hbx
    simp only [ite_true] at hbx
    have hlt : x.toBits - 2 ^ (f.eb + f.sb) < 2 ^ f.width := by omega
    have hsub : x.toBits - 2 ^ (f.eb + f.sb) = x.magnitude := by omega
    unfold Fl.magnitude Fl.signbit
    change ((x.toBits - 2 ^ (f.eb + f.sb)) % 2 ^ f.width) % 2 ^ (f.eb + f.sb) = x.magnitude ∧
      decide (((x.toBits - 2 ^ (f.eb + f.sb)) % 2 ^ f.width) ≥ 2 ^ (f.eb + f.sb)) = false
    rw [Nat.mod_eq_of_lt hlt, hsub]
    refine ⟨Nat.mod_eq_of_lt hmx, ?_⟩
    rw [decide_eq_false_iff_not]
    omega

theorem hfFiniteFiniteClassification {f : Fmt} (x : Fl f) (hf : x.isfinite = true) :
    x.isnan = false ∧ x.isinf = false := by
  by_cases he : x.expField = f.emax
  · simp [Fl.isfinite, he] at hf
  · simp [Fl.isnan, Fl.isinf, he]

theorem hfFiniteRatDenPositive {f : Fmt} (x : Fl f) (hf : x.isfinite = true) :
    0 < x.toRat.2 := by
  unfold Fl.toRat
  simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false]
  split <;> split <;> first
    | exact Nat.zero_lt_one
    | exact Nat.two_pow_pos _

theorem hfFiniteSourceIsNaN {T : JuliaLean.base.float.FTy}
    (x : JuliaLean.base.float.FV T) :
    JuliaLean.base.float.isnan_IEEEFloat x = x.isnan := by
  change (!(Fl.eq x x)) = x.isnan
  cases hx : x.isnan <;> simp only [Fl.eq, hx, Fl.toBits, beq_self_eq_true,
    Bool.true_or, Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and]

/-- Every finite source IEEEFloat is recognized by the source `isfinite` method. -/
theorem hfFiniteSourceFinite {T : JuliaLean.base.float.FTy}
    (x : JuliaLean.base.float.FV T) (hfin : x.isfinite = true) :
    JuliaLean.base.float.isfinite_IEEEFloat x = true := by
  unfold JuliaLean.base.float.isfinite_IEEEFloat JuliaLean.base.float.isfinite_AbstractFloat
    JuliaLean.base.float.sub_IEEEFloat JuliaLean.base.float.sub_float jlSubFloat
  rw [hfFiniteSourceIsNaN]
  have hb : (T.fmt == bfloat) = false := by cases T <;> decide
  simp only [finishFloat, hb, Bool.false_and, Bool.false_eq_true, ite_false]
  unfold floatSub floatAdd
  obtain ⟨hneg_mag, hneg_sign⟩ := hfFiniteNegParts x
  have hneg_exp : (Fl.neg x).expField = x.expField := by
    rw [hfFiniteExpField, hfFiniteExpField, hneg_mag]
  have hneg_frac : (Fl.neg x).frac = x.frac := by
    rw [hfFiniteFrac, hfFiniteFrac, hneg_mag]
  have hneg_nan : (Fl.neg x).isnan = x.isnan := by
    unfold Fl.isnan
    rw [hneg_exp, hneg_frac]
  have hneg_inf : (Fl.neg x).isinf = x.isinf := by
    unfold Fl.isinf
    rw [hneg_exp, hneg_frac]
  have hneg_fin : (Fl.neg x).isfinite = x.isfinite := by
    unfold Fl.isfinite
    rw [hneg_exp]
  have hneg_rat : (Fl.neg x).toRat = (-x.toRat.1, x.toRat.2) := by
    unfold Fl.toRat
    rw [hneg_fin, hneg_exp, hneg_frac, hneg_sign]
    dsimp only
    generalize x.frac + (if (x.expField == 0) = true then 0 else 2 ^ T.fmt.sb) = m
    generalize (if (x.expField == 0) = true then 1 - (T.fmt.bias : Int) - (T.fmt.sb : Int)
      else (x.expField : Int) - (T.fmt.bias : Int) - (T.fmt.sb : Int)) = p
    rw [hfin]
    cases x.signbit <;>
      simp only [Bool.false_eq_true, Bool.not_true, Bool.not_false, ite_false, ite_true] <;>
      split <;> simp [Int.neg_mul]
  rw [hneg_nan, hneg_inf, hneg_sign, hneg_rat]
  have hzero_nan : (Fl.zero false : JuliaLean.base.float.FV T).isnan = false := by
    cases T <;> decide
  obtain ⟨hnan, hinf⟩ := hfFiniteFiniteClassification x hfin
  simp only [hnan, hinf, Bool.false_eq_true, ite_false]
  have hd_pos := hfFiniteRatDenPositive x hfin
  have hd_ne : (x.toRat.2 * x.toRat.2 == 0) = false :=
    beq_eq_false_iff_ne.mpr (by have := Nat.mul_pos hd_pos hd_pos; omega)
  have h0 : x.toRat.1 * (x.toRat.2 : Int) + -x.toRat.1 * (x.toRat.2 : Int) = 0 := by
    rw [Int.neg_mul, Int.add_right_neg]
  have hs : (x.signbit && !x.signbit) = false := by cases x.signbit <;> rfl
  rw [h0, hs]
  unfold Fl.roundRat
  simp [hd_ne, hzero_nan]


/-- Setting the format's quiet bit preserves the NaN exponent and leaves a nonzero payload. -/
theorem hfFiniteQuietNaN {T : JuliaLean.base.float.FTy}
    (x : JuliaLean.base.float.FV T) (hn : x.isnan = true) :
    (quietFloat x).isnan = true := by
  have hsb : 0 < T.fmt.sb := by cases T <;> decide
  have hsm : T.fmt.sb - 1 < T.fmt.sb := by omega
  have hbit : 2 ^ (T.fmt.sb - 1) < 2 ^ T.fmt.sb :=
    Nat.pow_lt_pow_right (by decide) hsm
  have hw : T.fmt.sb - 1 < T.fmt.width := by unfold Fmt.width; omega
  have hfull : x.toBits ||| 2 ^ (T.fmt.sb - 1) < 2 ^ T.fmt.width :=
    Nat.or_lt_two_pow x.bits.isLt (Nat.pow_lt_pow_right (by decide) hw)
  have hbits : (quietFloat x).toBits = x.toBits ||| 2 ^ (T.fmt.sb - 1) := by
    change (x.toBits ||| 2 ^ (T.fmt.sb - 1)) % 2 ^ T.fmt.width = _
    exact Nat.mod_eq_of_lt hfull
  have he : (quietFloat x).expField = x.expField := by
    unfold Fl.expField
    rw [hbits, Nat.or_div_two_pow, Nat.div_eq_of_lt hbit, Nat.or_zero]
  have hq : (quietFloat x).frac ≠ 0 := by
    intro hz
    change (quietFloat x).toBits % 2 ^ T.fmt.sb = 0 at hz
    rw [hbits] at hz
    have hb := congrArg (fun n : Nat => n.testBit (T.fmt.sb - 1)) hz
    simp [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_two_pow, hsm] at hb
  have hexp : x.expField = T.fmt.emax := by
    have hh := hn
    simp only [Fl.isnan, Bool.and_eq_true, beq_iff_eq] at hh
    exact hh.1
  simp [Fl.isnan, he, hexp, hq]

/-- Source subtraction of either infinity or a NaN from itself is a NaN. -/
theorem hfFiniteSourceNonfinite {T : JuliaLean.base.float.FTy}
    (x : JuliaLean.base.float.FV T) (hfin : x.isfinite = false) :
    JuliaLean.base.float.isfinite_IEEEFloat x = false := by
  unfold JuliaLean.base.float.isfinite_IEEEFloat JuliaLean.base.float.isfinite_AbstractFloat
    JuliaLean.base.float.sub_IEEEFloat JuliaLean.base.float.sub_float jlSubFloat
  rw [hfFiniteSourceIsNaN]
  have hb : (T.fmt == bfloat) = false := by cases T <;> decide
  simp only [finishFloat, hb, Bool.false_and, Bool.false_eq_true, ite_false]
  unfold floatSub
  cases hn : x.isnan
  · simp only [hn, Bool.false_eq_true, ite_false]
    obtain ⟨hneg_mag, hneg_sign⟩ := hfFiniteNegParts x
    have hneg_exp : (Fl.neg x).expField = x.expField := by
      rw [hfFiniteExpField, hfFiniteExpField, hneg_mag]
    have hneg_frac : (Fl.neg x).frac = x.frac := by
      rw [hfFiniteFrac, hfFiniteFrac, hneg_mag]
    have hneg_nan : (Fl.neg x).isnan = false := by
      unfold Fl.isnan
      rw [hneg_exp, hneg_frac]
      exact hn
    have hi : x.isinf = true := by
      unfold Fl.isfinite at hfin
      unfold Fl.isnan at hn
      unfold Fl.isinf
      simp only [bne_eq_false_iff_eq] at hfin
      simp [hfin] at hn ⊢
      exact hn
    have hneg_inf : (Fl.neg x).isinf = true := by
      unfold Fl.isinf
      rw [hneg_exp, hneg_frac]
      exact hi
    have hs : (x.signbit != !x.signbit) = true := by cases x.signbit <;> rfl
    have hbad : (invalidFloat T.fmt).isnan = true := by cases T <;> decide
    simp [floatAdd, hn, hneg_nan, hi, hneg_inf, hneg_sign, hs, hbad]
  · simp [hfFiniteQuietNaN x hn]

/-- The source `isfinite` predicate agrees with the raw IEEE classifier in all three formats. -/
theorem hfFiniteSourceFiniteEq {T : JuliaLean.base.float.FTy}
    (x : JuliaLean.base.float.FV T) :
    JuliaLean.base.float.isfinite_IEEEFloat x = x.isfinite := by
  cases hf : x.isfinite
  · exact hfFiniteSourceNonfinite x hf
  · exact hfFiniteSourceFinite x hf

end JuliaLean.ChatGPT.Batch8.Group14


/- HalfWork.lean -/

namespace JuliaLean.ChatGPT.Batch8.Group14
open JuliaLean JuliaLean.Promotion JuliaLean.base.hashing
open JuliaLean.Proofs.base.hashing

inductive HfNumericRoute where
  | word (value : Word)
  | canonicalNaN
  deriving DecidableEq

def hfRouteEval (route : HfNumericRoute) (h : Word) : Word :=
  match route with
  | .word value => hashUInt64 value h
  | .canonicalNaN => xorWord hashNaNSeed h

def hfRoute16 {α : Type} (ops : Float16HashOps α) (x : α) : HfNumericRoute :=
  if ops.isfinite x then
    if ops.isequalI64 (ops.fptosi x) x then
      .word (JInt.lit .u64 (ops.fptosi x).val)
    else .word (ops.bitcastFloat64U64 (ops.toFloat64 x))
  else if ops.isnan x then .canonicalNaN
  else .word (ops.bitcastFloat64U64 (ops.toFloat64 x))

def hfRoute64 {α : Type} (ops : FloatHashOps α) (x : α) : HfNumericRoute :=
  if ops.leIntFloat (JInt.typemin .i64) x && ops.ltFloatInt x (JInt.typemax .i64) then
    if ops.isequalI64 (ops.fptosi x) x then
      .word (JInt.lit .u64 (ops.fptosi x).val)
    else .word (ops.bitcastU64 x)
  else if ops.leUIntFloat (JInt.lit .u64 0) x && ops.ltFloatUInt x (JInt.typemax .u64) then
    if ops.isequalU64 (ops.fptoui x) x then .word (ops.fptoui x)
    else .word (ops.bitcastU64 x)
  else if ops.isnan x then .canonicalNaN
  else .word (ops.bitcastU64 x)

theorem hfFactor16 {α : Type} (ops : Float16HashOps α) (x : α) (h : Word) :
    hashFloat16 ops x h = hfRouteEval (hfRoute16 ops x) h := by
  unfold hashFloat16 hfRoute16
  dsimp only
  split
  · split <;> rfl
  · split <;> rfl

theorem hfFactor64 {α : Type} (ops : FloatHashOps α) (x : α) (h : Word) :
    hashFloat64 ops x h = hfRouteEval (hfRoute64 ops x) h := by
  unfold hashFloat64 hfRoute64
  dsimp only
  split
  · split <;> rfl
  · split
    · split <;> rfl
    · split <;> rfl

/-- The finite integer branch is independent of promotion between formats. -/
theorem hfIntegerBranch {α : Type} (ops : Float16HashOps α)
    (x : α) (h : Word) (hf : ops.isfinite x = true)
    (he : ops.isequalI64 (ops.fptosi x) x = true) :
    hashFloat16 ops x h = hashInt64 (ops.fptosi x) h := by
  simp only [hashFloat16, hf, he, ite_true]


/-- Seed-free routes and exact source conversion data on a half precision value. -/
abbrev HfHalfFacts (x : base.float.FV .f16) : Prop :=
  let c := base.float.Float64_Float16 x
  hfRoute16 float16Calls x = hfRoute64 float64Calls c ∧
  c.isfinite = x.isfinite ∧ c.truncVal = x.truncVal ∧
  (x.isfinite = true → c.magnitude < 1039 * 2 ^ 52)


end JuliaLean.ChatGPT.Batch8.Group14


/- HalfAnalytic.lean -/

namespace JuliaLean.ChatGPT.Batch8.Group14
open JuliaLean JuliaLean.Promotion JuliaLean.Promotion.Fl JuliaLean.base.hashing
open JuliaLean.Proofs.base.hashing

/-- Numerical shape hypotheses for the dyadic rounding helper. -/
structure HaGood (f : Fmt) : Prop where
  emax_eq : f.emax = 2 * f.bias + 1
  emax_succ : f.emax + 1 = 2 ^ f.eb
  bias_pos : 1 ≤ f.bias
  sb_pos : 1 ≤ f.sb
  sb_le : f.sb ≤ f.bias

theorem haGoodDouble : HaGood double := ⟨by decide, by decide, by decide, by decide, by decide⟩

variable {f : Fmt}

def haPack (s : Bool) (B r : Nat) : Fl f :=
  Fl.ofBits ((if s then 2 ^ (f.eb + f.sb) else 0) + (B * 2 ^ f.sb + r))

theorem haPowMulEq (m a b c d : Nat) (h : a + b = c + d) : m * 2 ^ a * 2 ^ b = m * 2 ^ c * 2 ^ d := by
  rw (transparency := .default) [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add, h]

theorem haLogMulPow (c i : Nat) (hc : c ≠ 0) : (c * 2 ^ i).log2 = c.log2 + i := by
  have hne : c * 2 ^ i ≠ 0 := Nat.mul_ne_zero hc (by have := Nat.two_pow_pos i; omega)
  apply Nat.le_antisymm
  · have : c * 2 ^ i < 2 ^ (c.log2 + i + 1) := by
      rw (transparency := .default) [show c.log2 + i + 1 = (c.log2 + 1) + i by omega, Nat.pow_add]
      exact (Nat.mul_lt_mul_right (Nat.two_pow_pos i)).2 Nat.lt_log2_self
    have := (Nat.log2_lt hne).2 this
    omega
  · apply (Nat.le_log2 hne).2
    rw (transparency := .default) [Nat.pow_add]
    exact Nat.mul_le_mul_right _ (Nat.log2_self_le hc)

theorem haFloorLogPow (a j : Nat) (ha : a ≠ 0) :
    floorLog2Rat a (2 ^ j) = (a.log2 : Int) - j := by
  have h1 := Nat.log2_self_le ha
  unfold floorLog2Rat
  simp only [Nat.log2_two_pow]
  split
  · rename_i hge
    have : 2 ^ j * 2 ^ ((a.log2 : Int) - j).toNat = 2 ^ a.log2 := by
      rw (transparency := .default) [← Nat.pow_add]
      congr 1
      omega
    have hc : ¬ a < 2 ^ j * 2 ^ ((a.log2 : Int) - j).toNat := by omega
    split
    · contradiction
    · rfl
  · rename_i hlt
    have : 2 ^ a.log2 * 2 ^ (-((a.log2 : Int) - j)).toNat = 2 ^ j := by
      rw (transparency := .default) [← Nat.pow_add]
      congr 1
      omega
    have := Nat.mul_le_mul_right (2 ^ (-((a.log2 : Int) - j)).toNat) h1
    have hc : ¬ a * 2 ^ (-((a.log2 : Int) - j)).toNat < 2 ^ j := by omega
    split
    · contradiction
    · rfl

theorem haRoundExact (q d : Nat) (hd : 0 < d) : roundQuotient (q * d) d = q := by
  unfold roundQuotient
  rw (transparency := .default) [Nat.mul_div_cancel _ hd, Nat.mul_mod_left]
  dsimp only
  split
  · rename_i h
    simp at h <;> omega
  · rfl

theorem haPackNormal (neg : Bool) (q : Nat) (k : Int) (h1 : 2 ^ f.sb ≤ q)
    (h2 : q < 2 ^ (f.sb + 1)) (hk2 : k + f.bias + f.sb < f.emax) :
    (packRounded neg q k : Fl f) = haPack neg (k + f.bias + f.sb).toNat (q - 2 ^ f.sb) := by
  have hP := Nat.two_pow_pos f.sb
  have hq0 : (q == 0) = false := by simp; omega
  have hc : ¬ q ≥ 2 ^ (f.sb + 1) := by omega
  have he : ¬ k + f.bias + f.sb ≥ (f.emax : Int) := by omega
  have hm : ¬ q < 2 ^ f.sb := by omega
  unfold packRounded haPack
  simp only [hq0, hc, he, hm, Bool.false_eq_true, ↓reduceIte]

theorem haSigBounds (c : Nat) (hc : c ≠ 0) (hc1 : c < 2 ^ (f.sb + 1)) :
    c.log2 ≤ f.sb ∧ 2 ^ f.sb ≤ c * 2 ^ (f.sb - c.log2) ∧
    c * 2 ^ (f.sb - c.log2) < 2 ^ (f.sb + 1) := by
  have hlc : c.log2 ≤ f.sb := by have := (Nat.log2_lt hc).2 hc1; omega
  refine ⟨hlc, ?_, ?_⟩
  · calc 2 ^ f.sb = 2 ^ c.log2 * 2 ^ (f.sb - c.log2) := by
          rw (transparency := .default) [← Nat.pow_add]
          congr 1
          omega
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.log2_self_le hc)
  · calc c * 2 ^ (f.sb - c.log2) < 2 ^ (c.log2 + 1) * 2 ^ (f.sb - c.log2) :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 Nat.lt_log2_self
      _ = 2 ^ (f.sb + 1) := by
          rw (transparency := .default) [← Nat.pow_add]
          congr 1
          omega

theorem haRoundDyadic (hf : HaGood f) (n : Int) (c i j : Nat) (z : Bool)
    (hn : n.natAbs = c * 2 ^ i) (hc0 : 1 ≤ c) (hc1 : c < 2 ^ (f.sb + 1))
    (hlo : j + 1 ≤ c.log2 + i + f.bias) (hhi : c.log2 + i + f.bias < j + f.emax) :
    (roundRat n (2 ^ j) z : Fl f) =
      haPack (decide (n < 0)) (c.log2 + i + f.bias - j) (c * 2 ^ (f.sb - c.log2) - 2 ^ f.sb) := by
  have hc : c ≠ 0 := by omega
  obtain ⟨hlc, hq1, hq2⟩ := haSigBounds (f := f) c hc hc1
  have ha : n.natAbs ≠ 0 := by
    rw (transparency := .default) [hn]
    exact Nat.mul_ne_zero hc (by have := Nat.two_pow_pos i; omega)
  have hn0 : (n == 0) = false := by simp; omega
  have hd : (2 ^ j == 0) = false := by simp
  have hE : floorLog2Rat n.natAbs (2 ^ j) = ((c.log2 + i : Nat) : Int) - j := by
    rw (transparency := .default) [haFloorLogPow _ _ ha, hn, haLogMulPow c i hc]
  have hb := hf.bias_pos
  have hem := hf.emax_eq
  have hs := hf.sb_pos
  unfold roundRat
  simp only [hd, hn0, Bool.false_eq_true, ↓reduceIte]
  generalize floorLog2Rat n.natAbs (2 ^ j) = e at hE
  split
  · exfalso; omega
  split
  · exfalso; omega
  have hk : max (e - f.sb) (1 - (f.bias : Int) - f.sb) = e - f.sb := by omega
  rw (transparency := .default) [hk]
  have hpack : ∀ q : Nat, q = c * 2 ^ (f.sb - c.log2) →
      (packRounded (decide (n < 0)) q (e - f.sb) : Fl f) =
        haPack (decide (n < 0)) (c.log2 + i + f.bias - j) (c * 2 ^ (f.sb - c.log2) - 2 ^ f.sb) := by
    intro q hq
    subst hq
    rw (transparency := .default) [haPackNormal _ _ _ hq1 hq2 (by omega)]
    congr 1
    omega
  apply hpack
  by_cases hk0 : e - (f.sb : Int) ≥ 0
  · rw (transparency := .default) [ite_eq_left_iff.mpr fun h => absurd hk0 h]
    dsimp only
    have h1 : n.natAbs = c * 2 ^ (f.sb - c.log2) * (2 ^ j * 2 ^ (e - f.sb).toNat) := by
      rw (transparency := .default) [hn, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]
      congr 2
      omega
    rw (transparency := .default) [h1, haRoundExact _ _ (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))]
  · rw (transparency := .default) [ite_eq_right_iff.mpr fun h => absurd h hk0]
    dsimp only
    have h1 : n.natAbs * 2 ^ (-(e - f.sb)).toNat = c * 2 ^ (f.sb - c.log2) * 2 ^ j := by
      rw (transparency := .default) [hn]
      exact haPowMulEq _ _ _ _ _ (by omega)
    rw (transparency := .default) [h1, haRoundExact _ _ (Nat.two_pow_pos _)]


/-- Packed double metadata, derived with modular arithmetic. -/
theorem haPackParts (s : Bool) (B r : Nat) (hB : B < 2048) (hr : r < 2 ^ 52) :
    (haPack (f := double) s B r).signbit = s ∧
    (haPack (f := double) s B r).expField = B ∧
    (haPack (f := double) s B r).frac = r ∧
    (haPack (f := double) s B r).magnitude = B * 2 ^ 52 + r := by
  have hm : B * 2 ^ 52 + r < 2 ^ 63 := by
    calc
      _ < B * 2 ^ 52 + 2 ^ 52 := Nat.add_lt_add_left hr _
      _ = (B + 1) * 2 ^ 52 := by rw (transparency := .default) [Nat.add_mul, Nat.one_mul]
      _ ≤ 2048 * 2 ^ 52 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by decide
  have hparts := hfOfBitsParts s (B * 2 ^ 52 + r) hm
  have hmag : (haPack (f := double) s B r).magnitude = B * 2 ^ 52 + r := hparts.1
  refine ⟨hparts.2, ?_, ?_, hmag⟩
  · rw (transparency := .default) [fhHash64ExpFromMagnitude, hmag]
    change (B * 2 ^ 52 + r) / 2 ^ 52 = B
    rw (transparency := .default) [Nat.add_comm,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw (transparency := .default) [fhHash64FracFromMagnitude, hmag]
    change (B * 2 ^ 52 + r) % 2 ^ 52 = r
    rw (transparency := .default) [Nat.add_comm,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-- Normalized small dyadics preserve exact truncation in binary64. -/
theorem haPackDyadicFacts (s : Bool) (m i j : Nat) (hm : 0 < m)
    (hmhi : m < 2048) (hi : i ≤ 5) (hj : j ≤ 24) :
    let B := m.log2 + i + 1023 - j
    let q := m * 2 ^ (52 - m.log2)
    let y := haPack (f := double) s B (q - 2 ^ 52)
    y.isfinite = true ∧
      y.truncVal = (if s then -((m * 2 ^ i / 2 ^ j : Nat) : Int)
        else ((m * 2 ^ i / 2 ^ j : Nat) : Int)) ∧
      y.signbit = s ∧ y.magnitude < 1039 * 2 ^ 52 := by
  have hm0 : m ≠ 0 := by omega
  have hl : m.log2 ≤ 10 := by
    have := (Nat.log2_lt hm0).mpr (show m < 2 ^ 11 from hmhi)
    omega
  obtain ⟨-, hqlo, hqhi⟩ := haSigBounds (f := double) m hm0 (by
    change m < 2 ^ 53
    omega)
  change 2 ^ 52 ≤ m * 2 ^ (52 - m.log2) at hqlo
  change m * 2 ^ (52 - m.log2) < 2 ^ 53 at hqhi
  let B := m.log2 + i + 1023 - j
  let q := m * 2 ^ (52 - m.log2)
  let k := 52 - m.log2 - i
  have hqExp : 52 - m.log2 = i + k := by
    dsimp only [k]
    omega
  have hdExp : 1075 - B = j + k := by
    dsimp only [B, k]
    omega
  have hq : q = (m * 2 ^ i) * 2 ^ k := by
    dsimp only [q]
    rw [Nat.mul_assoc, ← Nat.pow_add]
    exact congrArg (fun t : Nat => m * 2 ^ t) hqExp
  have hd : 2 ^ (1075 - B) = 2 ^ j * 2 ^ k := by
    rw [← Nat.pow_add]
    exact congrArg (fun t : Nat => 2 ^ t) hdExp
  have hBlo : 0 < B := by dsimp only [B]; omega
  have hBhi : B ≤ 1038 := by dsimp only [B]; omega
  have hBsub : B - 1075 = 0 :=
    Nat.sub_eq_zero_of_le (Nat.le_trans hBhi (by decide : 1038 ≤ 1075))
  have hr : q - 2 ^ 52 < 2 ^ 52 := by dsimp only [q]; omega
  obtain ⟨hs, he, hf, hmag⟩ := haPackParts s B (q - 2 ^ 52) (by omega) hr
  have hfin : (haPack (f := double) s B (q - 2 ^ 52)).isfinite = true := by
    unfold Fl.isfinite
    rw (transparency := .default) [he]
    exact bne_iff_ne.mpr (show B ≠ double.emax by change B ≠ 2047; omega)
  refine ⟨hfin, ?_, hs, ?_⟩
  · change (haPack (f := double) s B (q - 2 ^ 52)).truncVal = _
    rw (transparency := .default) [fhHash64Trunc.fhTruncVal_parts (T := .f64) _ hfin, hs]
    have hquot : fhHash64Trunc.fhQuotient (T := .f64)
        (haPack (f := double) s B (q - 2 ^ 52)) = m * 2 ^ i / 2 ^ j := by
      unfold fhHash64Trunc.fhQuotient fhHash64Trunc.fhNumerator
        fhHash64Trunc.fhDenominator fhHash64Trunc.fhMantissaNat
      rw (transparency := .default) [he, hf]
      change ((q - 2 ^ 52 + if B = 0 then 0 else 2 ^ 52) *
        2 ^ (B - 1075)) / 2 ^ (if B = 0 then 1074 else 1075 - B) = _
      rw [if_neg (Nat.ne_of_gt hBlo), if_neg (Nat.ne_of_gt hBlo),
        hBsub, Nat.pow_zero, Nat.mul_one,
        Nat.sub_add_cancel (show 2 ^ 52 ≤ q from hqlo)]
      rw (transparency := .default) [hq, hd, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos k)]
    rw (transparency := .default) [hquot]
  · rw (transparency := .default) [hmag]
    calc
      _ < B * 2 ^ 52 + 2 ^ 52 := Nat.add_lt_add_left hr _
      _ = (B + 1) * 2 ^ 52 := by rw (transparency := .default) [Nat.add_mul, Nat.one_mul]
      _ ≤ 1039 * 2 ^ 52 := Nat.mul_le_mul_right _ (by omega)

/-- The source widening intrinsic specializes to raw IEEE conversion. -/
theorem haWidenRaw (x : base.float.FV .f16) :
    base.float.Float64_Float16 x = (Fl.convert (f := double) (g := half) x) := by
  rfl

/-- Exact widening metadata for every finite Float16, without finite enumeration. -/
theorem haFiniteConversion (x : base.float.FV .f16) (hx : x.isfinite = true) :
    let c := base.float.Float64_Float16 x
    c.isfinite = true ∧ c.truncVal = x.truncVal ∧
      c.signbit = x.signbit ∧ c.magnitude < 1039 * 2 ^ 52 := by
  let m := fhHash64Trunc.fhMantissaNat (T := .f16) x
  let i := x.expField - 25
  let j := if x.expField = 0 then 24 else 25 - x.expField
  have hexp : x.expField < 32 := Nat.mod_lt _ (by decide)
  have hfrac : x.frac < 1024 := Nat.mod_lt _ (by decide)
  have hne : x.expField ≠ 31 := by
    change (x.expField != 31) = true at hx
    exact bne_iff_ne.mp hx
  have he : x.expField ≤ 30 := by omega
  have hmhi : m < 2048 := by
    dsimp only [m, fhHash64Trunc.fhMantissaNat]
    change x.frac + (if x.expField = 0 then 0 else 1024) < 2048
    split <;> omega
  have hi : i ≤ 5 := by dsimp only [i]; omega
  have hj : j ≤ 24 := by dsimp only [j]; split <;> omega
  have hnan : x.isnan = false := by
    unfold Fl.isnan
    change ((x.expField == 31) && (x.frac != 0)) = false
    rw (transparency := .default) [beq_eq_false_iff_ne.mpr hne, Bool.false_and]
  have hinf : x.isinf = false := by
    unfold Fl.isinf
    change ((x.expField == 31) && (x.frac == 0)) = false
    rw (transparency := .default) [beq_eq_false_iff_ne.mpr hne, Bool.false_and]
  have hrat : x.toRat =
      (if x.signbit then -((m * 2 ^ i : Nat) : Int) else ((m * 2 ^ i : Nat) : Int),
        2 ^ j) := fhHash64Trunc.fhRat_parts x hx
  have hconv : base.float.Float64_Float16 x =
      Fl.roundRat (f := double)
        (if x.signbit then -((m * 2 ^ i : Nat) : Int) else ((m * 2 ^ i : Nat) : Int))
        (2 ^ j) x.signbit := by
    rw (transparency := .default) [haWidenRaw]
    unfold Fl.convert
    rw (transparency := .default) [show (double == half) = false from rfl,
      hnan, hinf, hrat] <;> rfl
  have htrunc : x.truncVal =
      (if x.signbit then -((m * 2 ^ i / 2 ^ j : Nat) : Int)
        else ((m * 2 ^ i / 2 ^ j : Nat) : Int)) :=
    fhHash64Trunc.fhTruncVal_parts x hx
  rw (transparency := .default) [hconv, htrunc]
  by_cases hm : m = 0
  · rw (transparency := .default) [hm]
    have hz : (Fl.roundRat (f := double)
        (if x.signbit then -((0 * 2 ^ i : Nat) : Int) else ((0 * 2 ^ i : Nat) : Int))
        (2 ^ j) x.signbit) = Fl.zero x.signbit := by
      have hd : (2 ^ j == 0) = false := by
        exact beq_eq_false_iff_ne.mpr (Nat.ne_of_gt (Nat.two_pow_pos _))
      simp only [Nat.zero_mul, Int.natCast_zero, Int.neg_zero, ite_self,
        Fl.roundRat, hd, Bool.false_eq_true, if_false, beq_self_eq_true, if_true]
    rw (transparency := .default) [hz]
    simp only [Nat.zero_mul, Nat.zero_div, Int.natCast_zero, Int.neg_zero, ite_self]
    cases x.signbit <;> decide
  · have hmpos : 0 < m := by omega
    have hval : (if x.signbit then -((m * 2 ^ i : Nat) : Int)
        else ((m * 2 ^ i : Nat) : Int)).natAbs = m * 2 ^ i := by
      cases x.signbit <;> simp only [Bool.false_eq_true, if_false, if_true,
        Int.natAbs_neg, Int.natAbs_natCast]
    have hsign : decide ((if x.signbit then -((m * 2 ^ i : Nat) : Int)
        else ((m * 2 ^ i : Nat) : Int)) < 0) = x.signbit := by
      have hp := Nat.mul_pos hmpos (Nat.two_pow_pos i)
      cases x.signbit <;> simp only [Bool.false_eq_true, if_false, if_true]
      · exact decide_eq_false (by omega)
      · exact decide_eq_true (by omega)
    rw (transparency := .default) [haRoundDyadic haGoodDouble _ m i j x.signbit hval (by omega)
      (by change m < 2 ^ 53; omega)
      (by change j + 1 ≤ m.log2 + i + 1023; omega)
      (by change m.log2 + i + 1023 < j + 2047
          have hl := (Nat.log2_lt hm).mpr (show m < 2 ^ 11 from hmhi)
          omega), hsign]
    exact haPackDyadicFacts x.signbit m i j hmpos hmhi hi hj

/-- Widening a half precision NaN retains a NaN classification. -/
theorem haConvertNaN (x : base.float.FV .f16) (hx : x.isnan = true) :
    (base.float.Float64_Float16 x).isnan = true := by
  have hfr : x.frac < 2 ^ 10 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hpay : x.frac * 2 ^ 42 < 2 ^ 52 := by
    calc
      _ < 2 ^ 10 * 2 ^ 42 := Nat.mul_lt_mul_of_pos_right hfr (Nat.two_pow_pos _)
      _ = _ := by decide
  have hquiet : 2 ^ 51 < 2 ^ 52 := by decide
  have hlor := Nat.or_lt_two_pow hpay hquiet
  obtain ⟨-, he, hr, -⟩ := haPackParts x.signbit 2047
    (Nat.lor (x.frac * 2 ^ 42) (2 ^ 51)) (by decide) hlor
  have hconv : base.float.Float64_Float16 x =
      haPack (f := double) x.signbit 2047
        (Nat.lor (x.frac * 2 ^ 42) (2 ^ 51)) := by
    rw (transparency := .default) [haWidenRaw]
    unfold Fl.convert
    rw (transparency := .default) [show (double == half) = false from rfl, hx]
    simp only [Bool.false_eq_true, if_false, if_true,
      show double.sb ≥ half.sb by decide]
    unfold haPack
    change Fl.ofBits ((if x.signbit then 2 ^ 63 else 0) + 2047 * 2 ^ 52 +
        Nat.lor (x.frac * 2 ^ 42) (2 ^ 51)) =
      Fl.ofBits ((if x.signbit then 2 ^ 63 else 0) +
        (2047 * 2 ^ 52 + Nat.lor (x.frac * 2 ^ 42) (2 ^ 51)))
    rw (transparency := .default) [Nat.add_assoc]
  rw (transparency := .default) [hconv]
  change (((haPack (f := double) x.signbit 2047
      (Nat.lor (x.frac * 2 ^ 42) (2 ^ 51))).expField == 2047) &&
    ((haPack (f := double) x.signbit 2047
      (Nat.lor (x.frac * 2 ^ 42) (2 ^ 51))).frac != 0)) = true
  rw (transparency := .default) [he, hr]
  simp

/-- Infinity conversion chooses the infinity with the stored sign. -/
theorem haConvertInf (x : base.float.FV .f16)
    (hn : x.isnan = false) (hi : x.isinf = true) :
    base.float.Float64_Float16 x = Fl.inf x.signbit := by
  rw (transparency := .default) [haWidenRaw]
  unfold Fl.convert
  rw (transparency := .default) [show (double == half) = false from rfl, hn, hi] <;> rfl

/-- Raw nonfinite classification is preserved by half precision widening. -/
theorem haNonfiniteConversion (x : base.float.FV .f16) (hx : x.isfinite = false) :
    let c := base.float.Float64_Float16 x
    c.isfinite = false ∧ c.truncVal = x.truncVal := by
  have hxexp : x.expField = 31 := by
    change (x.expField != 31) = false at hx
    simpa only [bne_eq_false_iff_eq] using hx
  have hc : (base.float.Float64_Float16 x).isfinite = false := by
    by_cases hn : x.isnan = true
    · have hnan := haConvertNaN x hn
      unfold Fl.isnan at hnan
      have he := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hnan).1
      simp only [Fl.isfinite, he, bne_self_eq_false]
    · have hnan : x.isnan = false := Bool.eq_false_iff.mpr hn
      have hfrac : x.frac = 0 := by
        change ((x.expField == 31) && (x.frac != 0)) = false at hnan
        simp only [hxexp, beq_self_eq_true, Bool.true_and] at hnan
        simpa only [bne_eq_false_iff_eq] using hnan
      have hinf : x.isinf = true := by
        change ((x.expField == 31) && (x.frac == 0)) = true
        rw (transparency := .default) [hxexp, hfrac] <;> rfl
      rw (transparency := .default) [haConvertInf x hnan hinf]
      cases x.signbit <;> decide
  refine ⟨hc, ?_⟩
  simp only [Fl.truncVal, Fl.toRat, hx, hc, Bool.not_false, if_true]

/-- Int16 sign testing uses its represented integer value. -/
theorem haSignI16 (n : JInt .i16) :
    base.int.signbit n = decide (n.val < 0) := by
  change decide ((BitVec.ofInt 64 (JInt.wrap .i64 n.val).val).toInt < 0) = _
  have hp := n.property
  change -32768 ≤ n.val ∧ n.val ≤ 32767 at hp
  have hw : wrapInt .i64 n.val = n.val := wrapInt_of_inRange .i64 n.val (by
    change -9223372036854775808 ≤ n.val ∧ n.val ≤ 9223372036854775807
    omega)
  change decide ((BitVec.ofInt 64 (wrapInt .i64 n.val)).toInt < 0) = _
  rw (transparency := .default) [hw, BitVec.toInt_ofInt_eq_self (w := 64) (by decide) (by omega) (by omega)]

/-- The source half precision sign test is the stored IEEE sign. -/
theorem haSignFloat16 (x : base.float.FV .f16) :
    base.float.signbit_float x = x.signbit := by
  have hv : (base.float.reinterpret_Int_Float .i16 x).val =
      (BitVec.ofNat 16 x.toBits).toInt := by
    change wrapInt .i16 (BitVec.ofNat 16 x.toBits).toInt = _
    have hlo := BitVec.le_toInt (BitVec.ofNat 16 x.toBits)
    have hhi := BitVec.toInt_lt (x := BitVec.ofNat 16 x.toBits)
    apply wrapInt_of_inRange
    change -32768 ≤ (BitVec.ofNat 16 x.toBits).toInt ∧
      (BitVec.ofNat 16 x.toBits).toInt ≤ 32767
    change -32768 ≤ (BitVec.ofNat 16 x.toBits).toInt at hlo
    change (BitVec.ofNat 16 x.toBits).toInt < 32768 at hhi
    omega
  unfold base.float.signbit_float
  change base.int.signbit (base.float.reinterpret_Int_Float .i16 x) = x.signbit
  rw (transparency := .default) [haSignI16, hv]
  change decide ((BitVec.ofNat 16 x.toBits).toInt < 0) = decide (x.toBits ≥ 2 ^ 15)
  apply decide_eq_decide.mpr
  have hb : x.toBits < 2 ^ 16 := x.bits.isLt
  rw (transparency := .default) [BitVec.toInt_neg_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  omega

/-- IEEE numerical equality is symmetric, including signed zeros and NaNs. -/
theorem haEqSymm {f : Fmt} (x y : Fl f) : Fl.eq x y = Fl.eq y x := by
  unfold Fl.eq
  cases x.isnan <;> cases y.isnan <;> cases x.iszero <;> cases y.iszero <;> simp [BEq.comm]

theorem haI64Abs (n : JInt .i64) : n.val.natAbs ≤ 2 ^ 63 := by
  have hp := n.property
  change -9223372036854775808 ≤ n.val ∧ n.val ≤ 9223372036854775807 at hp
  by_cases hs : 0 ≤ n.val
  · have hc := Int.natAbs_of_nonneg hs
    omega
  · have hc := Int.ofNat_natAbs_of_nonpos (by omega : n.val ≤ 0)
    omega

/-- The signed upper endpoint is outside every finite half precision magnitude. -/
theorem haNeSignedUpper (c : base.float.FV .f64)
    (hc : c.magnitude < 1039 * 2 ^ 52) : Fl.eq c fhHash64SignedUpper = false := by
  apply Bool.eq_false_iff.mpr
  intro he
  have hm := hfEqMagnitude c fhHash64SignedUpper he
  have hb : fhHash64SignedUpper.magnitude = 1086 * 2 ^ 52 := by decide
  rw (transparency := .default) [hb] at hm
  omega

/-- Mixed equality agrees across exact widening on every finite half precision value. -/
theorem haIntegerEqFinite (x : base.float.FV .f16) (hx : x.isfinite = true)
    (n : JInt .i64) :
    integerFloatIsequal (T := .f16) n x =
      integerFloatIsequal (T := .f64) n (base.float.Float64_Float16 x) := by
  let c := base.float.Float64_Float16 x
  obtain ⟨hcfin, ht, hsign, hbound⟩ := haFiniteConversion x hx
  change c.magnitude < 1039 * 2 ^ 52 at hbound
  have hsourceSign : base.float.signbit_float c = base.float.signbit_float x := by
    rw (transparency := .default) [fhHashSignFloat64, haSignFloat16]
    exact hsign
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hvalue := fhHash64IntegerEquality n x h
    change Fl.eq (base.float.floatOfInt .f64 n) c = true at hvalue
    rw (transparency := .default) [fhHash64FloatOfI64 n] at hvalue
    have hmag := hfEqMagnitude (Fl.ofInt (f := double) n.val) c hvalue
    have hsmall : n.val.natAbs < 2 ^ 16 := by
      apply hfOfIntSmall_of_magnitude n.val (haI64Abs n)
      rw (transparency := .default) [hmag]
      exact hbound
    have hupper : Fl.eq (Fl.ofInt (f := double) n.val) fhHash64SignedUpper = false :=
      haNeSignedUpper _ (by rw (transparency := .default) [hmag]; exact hbound)
    have hcast : JInt.lit .i64 n.val = n := by
      apply Subtype.ext
      exact wrapInt_of_inRange .i64 n.val n.property
    have htrunc : base.float.fptosi (T := .f64) .i64 (Fl.ofInt n.val) = n :=
      (fhSmallOfIntFptosi n.val hsmall).trans hcast
    apply fhHash64IntegerIsequalOfEqAndSign
    · change ((Fl.eq c (base.float.floatOfInt .f64 n) &&
        !(Fl.eq (base.float.floatOfInt .f64 n)
          (base.float.floatOfInt .f64 (JInt.typemax .i64)))) &&
        base.int.eq n (base.float.fptosi .i64 (base.float.floatOfInt .f64 n))) = true
      rw (transparency := .default) [fhHash64FloatOfI64 n, fhHash64MaxFloat, hupper, htrunc,
        haEqSymm c, hvalue, fhHash64EqI64Self]
      rfl
    · rw (transparency := .default) [hsourceSign]
      exact fhHash64IntegerSign n x h
  · intro h
    have hvalue := fhHash64IntegerEquality n c h
    change ((Fl.eq c (base.float.floatOfInt .f64 n) &&
        !(Fl.eq (base.float.floatOfInt .f64 n)
          (base.float.floatOfInt .f64 (JInt.typemax .i64)))) &&
        base.int.eq n (base.float.fptosi .i64 (base.float.floatOfInt .f64 n))) = true at hvalue
    have hv := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hvalue).1).1
    apply fhHash64IntegerIsequalOfEqAndSign
    · change Fl.eq (base.float.floatOfInt .f64 n) c = true
      rw (transparency := .default) [haEqSymm]
      exact hv
    · rw (transparency := .default) [← hsourceSign]
      exact fhHash64IntegerSign n c h

/-- Source finite promotion preserves the exact seed-independent hash branch. -/
theorem haFiniteRoute (x : base.float.FV .f16) (hx : x.isfinite = true) :
    hfRoute16 float16Calls x =
      hfRoute64 float64Calls (base.float.Float64_Float16 x) := by
  let c := base.float.Float64_Float16 x
  obtain ⟨hcfin, ht, hs, hb⟩ := haFiniteConversion x hx
  change c.magnitude < 1039 * 2 ^ 52 at hb
  have hsource : float16Calls.isfinite x = true := hfFiniteSourceFinite x hx
  have hguard : (float64Calls.leIntFloat (JInt.typemin .i64) c &&
      float64Calls.ltFloatInt c (JInt.typemax .i64)) = true :=
    fhHash64SignedGuardOfMagnitude c (by omega) (haNeSignedUpper c hb)
  have htrunc : float16Calls.fptosi x = float64Calls.fptosi c := by
    change base.float.fptosi .i64 x = base.float.fptosi .i64 c
    unfold base.float.fptosi C.jlFptosi
    rw (transparency := .default) [hx, hcfin, ht]
  have heq : float16Calls.isequalI64 (float16Calls.fptosi x) x =
      float64Calls.isequalI64 (float64Calls.fptosi c) c := by
    change integerFloatIsequal (T := .f16) (float16Calls.fptosi x) x =
      integerFloatIsequal (T := .f64) (float64Calls.fptosi c) c
    rw (transparency := .default) [haIntegerEqFinite x hx, htrunc]
  unfold hfRoute16 hfRoute64
  rw (transparency := .default) [hsource, hguard]
  simp only [if_true]
  rw (transparency := .default) [heq, htrunc]
  rfl

/-- A double NaN takes the canonical NaN hash route. -/
theorem haNaNRoute (x : base.float.FV .f64) (hx : x.isnan = true) :
    hfRoute64 float64Calls x = .canonicalNaN := by
  have hleI : float64Calls.leIntFloat (JInt.typemin .i64) x = false := by
    change (Fl.lt _ x || (Fl.eq _ x && _)) = false
    rw (transparency := .default) [fhHashNanLtRight _ x hx, fhHashNanEqRight _ x hx]
    rfl
  have hleU : float64Calls.leUIntFloat (JInt.lit .u64 0) x = false := by
    change (Fl.lt _ x || (Fl.eq _ x && _)) = false
    rw (transparency := .default) [fhHashNanLtRight _ x hx, fhHashNanEqRight _ x hx]
    rfl
  have hn : float64Calls.isnan x = true := (fhHashIsnanCall x).trans hx
  simp only [hfRoute64, hleI, hleU, Bool.false_and, Bool.false_eq_true,
    if_false, hn, if_true]

/-- The two infinite doubles take their bit-pattern route. -/
theorem haInfRoute (s : Bool) :
    hfRoute64 float64Calls (Fl.inf s) =
      .word (float64Calls.bitcastU64 (Fl.inf s)) := by
  cases s <;> decide +kernel

/-- Source nonfinite promotion preserves the exact seed-independent hash branch. -/
theorem haNonfiniteRoute (x : base.float.FV .f16) (hx : x.isfinite = false) :
    hfRoute16 float16Calls x =
      hfRoute64 float64Calls (base.float.Float64_Float16 x) := by
  have hsource : float16Calls.isfinite x = false := (hfFiniteSourceFiniteEq x).trans hx
  have hsourceNan : float16Calls.isnan x = x.isnan := fhHashIsnanCall x
  by_cases hn : x.isnan = true
  · have hcNan := haConvertNaN x hn
    calc
      hfRoute16 float16Calls x = HfNumericRoute.canonicalNaN := by
        simp only [hfRoute16, hsource, hsourceNan, hn,
          Bool.false_eq_true, ite_false, ite_true]
      _ = hfRoute64 float64Calls (base.float.Float64_Float16 x) :=
        (haNaNRoute _ hcNan).symm
  · have hnfalse : x.isnan = false := Bool.eq_false_iff.mpr hn
    have he : x.expField = 31 := by
      change (x.expField != 31) = false at hx
      simpa only [bne_eq_false_iff_eq] using hx
    have hf : x.frac = 0 := by
      change ((x.expField == 31) && (x.frac != 0)) = false at hnfalse
      simp only [he, beq_self_eq_true, Bool.true_and] at hnfalse
      simpa only [bne_eq_false_iff_eq] using hnfalse
    have hinf : x.isinf = true := by
      change ((x.expField == 31) && (x.frac == 0)) = true
      rw (transparency := .default) [he, hf] <;> rfl
    have hc := haConvertInf x (Bool.eq_false_iff.mpr hn) hinf
    have hleft : hfRoute16 float16Calls x =
        HfNumericRoute.word (float64Calls.bitcastU64 (base.float.Float64_Float16 x)) := by
      simp only [hfRoute16, hsource, hsourceNan, Bool.eq_false_iff.mpr hn,
        Bool.false_eq_true, ite_false] <;> rfl
    have hright : hfRoute64 float64Calls (base.float.Float64_Float16 x) =
        HfNumericRoute.word (float64Calls.bitcastU64 (base.float.Float64_Float16 x)) := by
      exact Eq.mpr (congrArg (fun y : base.float.FV .f64 =>
        hfRoute64 float64Calls y = HfNumericRoute.word (float64Calls.bitcastU64 y)) hc)
        (haInfRoute x.signbit)
    exact hleft.trans hright.symm

/-- All half precision bit patterns satisfy the source hash and conversion facts analytically. -/
theorem haHalfFacts (x : base.float.FV .f16) : HfHalfFacts x := by
  cases hx : x.isfinite
  · obtain ⟨hc, ht⟩ := haNonfiniteConversion x hx
    exact ⟨haNonfiniteRoute x hx, hc.trans hx.symm, ht, by simp only [hx, Bool.false_eq_true, false_implies]⟩
  · obtain ⟨hc, ht, hs, hb⟩ := haFiniteConversion x hx
    exact ⟨haFiniteRoute x hx, hc.trans hx.symm, ht, fun _ => hb⟩

end JuliaLean.ChatGPT.Batch8.Group14


/- HalfConclusion.lean -/

namespace JuliaLean.ChatGPT.Batch8.Group14
open JuliaLean JuliaLean.Promotion JuliaLean.base.hashing
open JuliaLean.Proofs.base.hashing

/-- Exact source mixed equality forces the half precision input to be finite and its truncation to recover the integer. -/
theorem hfIntegerExactOfFacts
    (hdata : ∀ x : base.float.FV .f16, HfHalfFacts x)
    (x : base.float.FV .f16) (n : JInt .i64)
    (h : integerFloatIsequal (T := .f16) n x = true) :
    float16Calls.isfinite x = true ∧ float16Calls.fptosi x = n := by
  let c := base.float.Float64_Float16 x
  have hvalue := fhHash64IntegerEquality n x h
  change Fl.eq (base.float.floatOfInt .f64 n) c = true at hvalue
  rw (transparency := .default) [fhHash64FloatOfI64 n] at hvalue
  have hmag := hfEqMagnitude (Fl.ofInt (f := double) n.val) c hvalue
  have hp := n.property
  change -9223372036854775808 ≤ n.val ∧ n.val ≤ 9223372036854775807 at hp
  have habs : n.val.natAbs ≤ 2 ^ 63 := by
    by_cases hs : 0 ≤ n.val
    · have hc := Int.natAbs_of_nonneg hs
      omega
    · have hc := Int.ofNat_natAbs_of_nonpos (by omega : n.val ≤ 0)
      omega
  have hu := (fhHashBtOfIntSignedBounds n.val habs).1
  have hcfin : c.isfinite = true := by
    apply hfFiniteFromMagnitude
    rw (transparency := .default) [← hmag]
    omega
  have hfacts := hdata x
  have hxfin : x.isfinite = true := hfacts.2.1.symm.trans hcfin
  have hsmall : n.val.natAbs < 2 ^ 16 := by
    apply hfOfIntSmall_of_magnitude n.val habs
    rw (transparency := .default) [hmag]
    exact hfacts.2.2.2 hxfin
  have hfn := fhSmallOfIntFptosi n.val hsmall
  have hcast : JInt.lit .i64 n.val = n := by
    apply Subtype.ext
    exact wrapInt_of_inRange .i64 n.val n.property
  have htrunc : base.float.fptosi .i64 c = n := by
    rw (transparency := .default) [← fhHash64FptosiCongr (T := .f64) (Fl.ofInt n.val) c .i64 hvalue]
    exact hfn.trans hcast
  refine ⟨hfFiniteSourceFinite x hxfin, ?_⟩
  change base.float.fptosi .i64 x = n
  rw (transparency := .default) [← htrunc]
  unfold base.float.fptosi C.jlFptosi
  rw (transparency := .default) [hxfin, hcfin, hfacts.2.2.1]

/-- The installed Float16 hash commutes with source widening and agrees with every source-equal Int64. -/
theorem PromotionFloat16HashConsistentV2_proven :
    JuliaLean.Proofs.base.hashing.Round1.Float16HashPromotion := by
  intro x h
  refine ⟨?_, ?_⟩
  · exact (hfFactor16 float16Calls x h).trans
      ((congrArg (fun route => hfRouteEval route h) (haHalfFacts x).1).trans
        (hfFactor64 float64Calls (base.float.Float64_Float16 x) h).symm)
  · intro n he
    obtain ⟨hf, ht⟩ := hfIntegerExactOfFacts haHalfFacts x n he
    have hc : float16Calls.isequalI64 (float16Calls.fptosi x) x = true := by
      exact (congrArg (fun value => float16Calls.isequalI64 value x) ht).trans he
    exact (hfIntegerBranch float16Calls x h hf hc).trans
      (congrArg (fun value => hashInt64 value h) ht)

end JuliaLean.ChatGPT.Batch8.Group14

namespace JuliaLean.Proofs.base.hashing

open JuliaLean.Registry

def entries : List Entry := [
  { (entry "hashops-small-integer-hash"
    ["hash(::UInt64,::UInt)", "hash(::Int64,::UInt)",
     "hash(::Union{Bool,Int8,UInt8,Int16,UInt16,Int32,UInt32},::UInt)"]
    "For every seed, machine integers of widths through 64 bits with equal numeric values have equal hashes."
    "hash docstring base/hashing.jl:12-20; integer methods base/hashing.jl:75-77"
    ``SmallIntegerHashConsistency) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group21.HashopsSmallIntegerHash_proven },
  { (entry "promotion-float16-hash-consistent"
    ["hash(::Float16,::UInt)", "hash(::Float64,::UInt)", "hash(::Int64,::UInt)"]
    "For every Float16 value and seed, its hash equals the hash of its Float64 conversion, and equals the Int64 hash whenever the value is an exactly equal finite Int64."
    "isequal hash contract; base/hashing.jl:165-196"
    ``Float16HashConsistent) with thm := none, notes := "Installed callbacks use numeric equality for integer/float isequal, incorrectly treating integer zero and negative floating zero as isequal." },
  { (entry "hashops-decomposed-real-hash"
    ["hash(::Real,::UInt)", "hash_integer", "decompose"]
    "Equal Real values with the same normalized decomposition have equal hashes for every seed, including zero, infinity, and NaN cases."
    "hash docstring base/hashing.jl:12-20; generic Real method base/hashing.jl:200-245"
    ``RealHashIsequal) with notes := "Prop permits arbitrary decomposition/equality callbacks without the source laws." },
  { (entry "hashops-string-hash"
    ["hash(::AbstractString,::UInt)", "hash(::String,::UInt)", "utf8units", "iterate(::UTF8Units)", "codeunits"]
    "Valid byte-backed and character-iterated strings with the same UTF-8 byte sequence hash equally for every seed."
    "hash docstring base/hashing.jl:12-20; byte and string methods base/hashing.jl:101-145,378-473,509-654"
    ``StringHashConsistency) with notes := "Prop includes unrestricted HashBytePathAgreement with unconstructible byte-array lengths." },
  { id := "hashops-annotated-non8-hash", juliaFile := "base/hashing.jl",
    juliaFns := ["hash(::AbstractString,::UInt)", "iterate(::UTF8Units)", "hash(::AnnotatedString,::UInt)"],
    statement := "An annotation-free AnnotatedString over a non-UInt8 AbstractString hashes successfully and equals the hash of its isequal underlying string.",
    source := "hash docstring base/hashing.jl:12-20; AnnotatedString equality base/strings/annotated.jl:232-233",
    status := .todo, prop := ``AnnotatedStringHash,
    notes := "Existing reproducer: repro/hashops-annotated-non8-hash.jl. Prop universally quantifies an unrestricted wrapper-hash callback rather than the source hash method. Existing model certificate: JuliaLean.ChatGPT.Batch4.Group21.HashopsAnnotatedNon8Hash_refuted.", thm := none, issue := "bugs/hashops-annotated-non8-hash.yaml" },
  { (entry "intfuncscov-hash-structural"
    ["hash(::QuoteNode,::UInt)", "hash(::PhiNode,::UInt)", "hash(::PhiCNode,::UInt)",
     "hash(::Expr,::UInt)", "hash(::CodeInfo,::UInt)", "hash(::DebugInfo,::UInt)",
     "hash(::Symbol)", "hash(::GlobalRef,::UInt)", "hash(::PartialStruct,::UInt)"]
    "Equal compiler-IR values hash equally for each seed when their field hash functions respect equality."
    "hash docstring base/hashing.jl:12-20; structural methods base/hashing.jl:251-293"
    ``StructuralHashIsequal) with notes := "FieldHashEquivalent constrains defined fields only; DebugInfo hashing reads all getfield results." },
  { (entry "hashing-integer-codeunits"
    ["IntegerCodeUnits(::Integer)", "size(::IntegerCodeUnits)", "length(::IntegerCodeUnits)",
     "getindex(::IntegerCodeUnits,::Int)", "load_le_array(::Type{UInt64},::IntegerCodeUnits,::Int)",
     "load_le_array(::Type{UInt32},::IntegerCodeUnits,::Int)", "codeunits(::Integer)"]
    "Integer code units contain the minimal whole-byte magnitude in little-endian order, including zero as one byte."
    "Integer code-unit comment and methods base/hashing.jl:79-99"
    ``IntegerCodeUnitsLittleEndian) with thm := none, notes := "Prop uses unbounded Nat indices while source arithmetic wraps machine Int indices." },
  { (entry "hashing-byte-path-equivalence"
    ["hash_bytes(::Ptr{UInt8},::Int,::UInt64,::NTuple{4,UInt64})",
     "hash_bytes(::AbstractArray{UInt8},::UInt64,::NTuple{4,UInt64})",
     "hash_bytes(iter,::UInt64,::NTuple{4,UInt64})", "load_le", "load_le_array",
     "concat_shift", "read_uint64_from_uint8_iter"]
    "Pointer, array, and iterator hashing return the same value for the same finite byte sequence and seed."
    "base/hashing.jl:296-647; 48-byte chunking and tail branches"
    ``HashBytePathAgreement) with notes := "Prop permits unconstructible byte arrays beyond native length limits." },
  { (entry "hashing-integer-sign-mix"
    ["hash_integer", "_hash_integer"]
    "Hashing a positive integer's negative toggles the seed's low sign bit while preserving its magnitude-byte stream."
    "base/hashing.jl:147-159 (sign XOR and absolute-value byte stream)"
    ``IntegerHashSignMixing) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group21.HashingIntegerSignMix_proven },
  { id := "hashops-small-integer-hash-v2", juliaFile := "base/hashing.jl",
    juliaFns := ["hash(::UInt64,::UInt)", "hash(::Int64,::UInt)", "hash(::SmallInteger,::UInt)"],
    statement := "All equal-valued Bool and machine integers through 64 bits have equal hashes at every seed.",
    source := "base/hashing.jl:11-25,75-77; base/operators.jl:134-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.hashing.Round1.NativeIntegerHashConsistency, thm := some ``JuliaLean.ChatGPT.Batch4.Group21.HashopsSmallIntegerHashV2_proven },
  { id := "promotion-float16-hash-consistent-v2", juliaFile := "base/hashing.jl",
    juliaFns := ["hash(::Float16,::UInt)", "hash(::Float64,::UInt)", "hash(::Int64,::UInt)"],
    statement := "Every Float16 hashes as its exact Float64 conversion and as every isequal Int64, at every seed.",
    source := "base/hashing.jl:11-25,165-196; base/operators.jl:145-150,202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.hashing.Round1.Float16HashPromotion, thm := some ``JuliaLean.ChatGPT.Batch8.Group14.PromotionFloat16HashConsistentV2_proven },
  { id := "hashing-float64-consistency", juliaFile := "base/hashing.jl",
    juliaFns := ["hash(::Float64,::UInt)", "hash(::Int64,::UInt)", "hash(::UInt64,::UInt)"],
    statement := "Float64 hashes respect isequal with Float64 and both 64-bit integer types for every seed, including exceptional IEEE values.",
    source := "base/hashing.jl:11-25,75-76,165-181; base/operators.jl:145-150,201-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.hashing.Round1.Float64HashConsistency, thm := some ``JuliaLean.ChatGPT.Batch8.Group14.HashingFloat64Consistency_proven },
  { id := "hashing-string-generic-dispatch", juliaFile := "base/hashing.jl",
    juliaFns := ["hash(::String,::UInt)", "hash(::AbstractString,::UInt)"],
    statement := "For every String and seed, specialized pointer hashing agrees with generic AbstractString hashing, including malformed UTF-8.",
    source := "base/hashing.jl:11-25,649-654; doc/src/manual/strings.md:27-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.hashing.Round1.StringSpecializedGenericAgreement, thm := some ``JuliaLean.ChatGPT.Batch4.Group21.HashingStringGenericDispatch_proven }
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
