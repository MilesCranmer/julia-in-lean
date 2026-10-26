import JuliaLean.Core

/-! Models for the uncovered methods in `base/strings/cstring.jl` at Julia `bbfa0ce4150`. -/

namespace JuliaLean.StringsCovA.CStrings

inductive PtrTag where
  | int8 | uint8 | wchar | void
  deriving DecidableEq

structure PtrValue where
  tag : PtrTag
  address : Nat
  deriving DecidableEq

abbrev Cstring := PtrValue
abbrev Cwstring := PtrValue

/-- `Cstring(p)`; `base/strings/cstring.jl:31`. -/
def cstring (p : PtrValue) : Cstring := ⟨.int8, p.address⟩

/-- `Cwstring(p)`; `base/strings/cstring.jl:32`. -/
def cwstring (p : PtrValue) : Cwstring := ⟨.wchar, p.address⟩

/-- `Ptr{T}(p::Cstring)` correctly uses `T`; line 33. -/
def ptrFromCstring (target : PtrTag) (p : Cstring) : PtrValue := ⟨target, p.address⟩

/-- `Ptr{T}(p::Cwstring)` ignores `T` and bitcasts to `Ptr{Cwchar_t}`; line 34. -/
def ptrFromCwstring (_target : PtrTag) (p : Cwstring) : PtrValue := ⟨.wchar, p.address⟩

/-- The four `convert` wrappers; `base/strings/cstring.jl:36-39`. -/
def convertCstring (p : PtrValue) := cstring p
def convertCwstring (p : PtrValue) := cwstring p
def convertPtrCstring (target : PtrTag) (p : Cstring) := ptrFromCstring target p
def convertPtrCwstring (target : PtrTag) (p : Cwstring) := ptrFromCwstring target p

/-- `pointer` methods; `base/strings/cstring.jl:55-56`. -/
def pointerCstring (p : Cstring) : PtrValue := ptrFromCstring .int8 p
def pointerCwstring (p : Cwstring) : PtrValue := ptrFromCwstring .wchar p

/-- Pointer comparisons; `base/strings/cstring.jl:59-60`. -/
def eqCptr (x : Cstring) (y : PtrValue) : Bool := x.address == y.address
def eqPtrC (x : PtrValue) (y : Cstring) : Bool := x.address == y.address

/-- `unsafe_string(::Cstring)` reads through the first NUL; line 62. -/
def unsafeStringC (memory : List UInt8) : List UInt8 := memory.takeWhile (· != 0)

/-- `cconvert(Cstring, ::String/::AbstractString)`; lines 65-67. -/
def cconvertString (s : List UInt8) : List UInt8 := s
def cconvertAbstract (toString : α → List UInt8) (s : α) : List UInt8 := cconvertString (toString s)

/-- `eltype(Cstring/Cwstring)`; lines 75-76. -/
def eltypeCstring : PtrTag := .int8
def eltypeCwstring : PtrTag := .wchar

/-- `containsnul(p, len)`; lines 78-79. -/
def containsnulPtr (memory : List UInt8) (len : Nat) : Bool := (memory.take len).contains 0

/-- Raw-memory and wide-pointer conversion wrappers; lines 90,101-102. -/
def unsafeConvertMemory (address : Nat) : Cstring := ⟨.int8, address⟩
def unsafeConvertWide (address : Nat) : Cwstring := ⟨.wchar, address⟩
def unsafeConvertWideIdentity (s : Cwstring) : Cwstring := s

/-- Symbol conversion wrappers; lines 105-106. -/
def cconvertSymbol (address : Nat) : Nat := address
def unsafeConvertSymbol (address : Nat) : Cstring := ⟨.int8, address⟩

/-- Identity `transcode(T, ::AbstractVector{T})`; line 163. -/
def transcodeIdentity (src : List α) : List α := src

/-- UTF-8 to UTF-32/Int32 comprehensions and their byte wrappers; lines 164-168. -/
def transcodeString32 (decode : List UInt8 → List UInt32) (src : List UInt8) : List UInt32 := decode src
def transcodeBytes32 (decode : List UInt8 → List UInt32) (src : List UInt8) : List UInt32 :=
  transcodeString32 decode src
def transcodeCodeUnits32 (decode : List UInt8 → List UInt32) (src : List UInt8) : List UInt32 :=
  transcodeString32 decode src

/-- UTF-32/Int32 to UInt8 prints each Char; lines 170-176. -/
def transcode32Bytes (encode : UInt32 → List UInt8) (src : List UInt32) : List UInt8 :=
  (src.map encode).flatten

/-- String conversion wrappers; lines 177-183. -/
def transcodeStringIdentity (src : List UInt8) : List UInt8 := src
def transcodeStringViaCodeunits (transcode : List UInt8 → α) (src : List UInt8) : α := transcode src
def transcodeVectorString (src : List UInt8) : List UInt8 := src
def transcodeToString (transcode : α → List UInt8) (src : α) : List UInt8 := transcode src

/-- `unsafe_string(p, length)` for wide code units; lines 321-323. -/
def unsafeStringWideLength (transcode : List α → List UInt8)
    (memory : List α) (length : Nat) : List UInt8 := transcode (memory.take length)

/-- NUL-terminated `unsafe_string(p)`; lines 324-330. -/
def unsafeStringWide (zero : α) [BEq α] (transcode : List α → List UInt8)
    (memory : List α) : List UInt8 := transcode (memory.takeWhile (· != zero))

/-- `unsafe_string(::Cwstring)`; line 331. -/
def unsafeStringCwstring (zero : α) [BEq α] (transcode : List α → List UInt8)
    (memory : List α) : List UInt8 := unsafeStringWide zero transcode memory

def PointerConversions : Prop :=
  (∀ p, cstring p = ⟨.int8, p.address⟩) ∧
  (∀ p, cwstring p = ⟨.wchar, p.address⟩) ∧
  (∀ target p, ptrFromCstring target p = ⟨target, p.address⟩) ∧
  (∀ p, convertCstring p = cstring p) ∧ (∀ p, convertCwstring p = cwstring p) ∧
  (∀ target p, convertPtrCstring target p = ptrFromCstring target p)

theorem pointerConversions : PointerConversions := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def CwstringPointerType : Prop :=
  ∀ p : Cwstring, (ptrFromCwstring .void p).tag = .void ∧
    (convertPtrCwstring .void p).tag = .void

theorem cwstringPointerType_refuted : ¬ CwstringPointerType := by
  intro h
  have hp := (h ⟨.wchar, 0⟩).1
  change PtrTag.wchar = PtrTag.void at hp
  cases hp

def PointerOperations : Prop :=
  (∀ p, pointerCstring p = ⟨.int8, p.address⟩) ∧
  (∀ p, pointerCwstring p = ⟨.wchar, p.address⟩) ∧
  (∀ x y, eqCptr x y = (x.address == y.address)) ∧
  (∀ x y, eqPtrC x y = (x.address == y.address)) ∧
  (∀ memory, unsafeStringC memory = memory.takeWhile (· != 0))

theorem pointerOperations : PointerOperations := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def ConversionOperations : Prop :=
  (∀ s, cconvertString s = s) ∧
  (∀ (α : Type) (toString : α → List UInt8) s,
    cconvertAbstract toString s = toString s) ∧
  eltypeCstring = .int8 ∧ eltypeCwstring = .wchar ∧
  (∀ memory len, containsnulPtr memory len = (memory.take len).contains 0) ∧
  (∀ address, unsafeConvertMemory address = ⟨.int8, address⟩) ∧
  (∀ address, unsafeConvertWide address = ⟨.wchar, address⟩) ∧
  (∀ s, unsafeConvertWideIdentity s = s) ∧
  (∀ address, cconvertSymbol address = address) ∧
  (∀ address, unsafeConvertSymbol address = ⟨.int8, address⟩)

theorem conversionOperations : ConversionOperations := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def TranscodeWrappers : Prop :=
  (∀ (α : Type) (src : List α), transcodeIdentity src = src) ∧
  (∀ decode src, transcodeString32 decode src = decode src) ∧
  (∀ decode src, transcodeBytes32 decode src = decode src) ∧
  (∀ decode src, transcodeCodeUnits32 decode src = decode src) ∧
  (∀ encode src, transcode32Bytes encode src = (src.map encode).flatten) ∧
  (∀ src, transcodeStringIdentity src = src) ∧
  (∀ (α : Type) (transcode : List UInt8 → α) src,
    transcodeStringViaCodeunits transcode src = transcode src) ∧
  (∀ src, transcodeVectorString src = src) ∧
  (∀ (α : Type) (transcode : α → List UInt8) src,
    transcodeToString transcode src = transcode src)

theorem transcodeWrappers : TranscodeWrappers := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def UnsafeWideStrings : Prop :=
  (∀ (α : Type) (transcode : List α → List UInt8) memory length,
    unsafeStringWideLength transcode memory length = transcode (memory.take length)) ∧
  (∀ (α : Type) (zero : α) (_ : BEq α) (transcode : List α → List UInt8) memory,
    unsafeStringWide zero transcode memory = transcode (memory.takeWhile (· != zero))) ∧
  (∀ (α : Type) (zero : α) (_ : BEq α) (transcode : List α → List UInt8) memory,
    unsafeStringCwstring zero transcode memory = unsafeStringWide zero transcode memory)

theorem unsafeWideStrings : UnsafeWideStrings := by
  repeat' apply And.intro
  all_goals intros <;> rfl

end JuliaLean.StringsCovA.CStrings
