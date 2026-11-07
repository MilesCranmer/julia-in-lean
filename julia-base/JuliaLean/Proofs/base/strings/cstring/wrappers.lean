import JuliaLean.Registry.Types
import JuliaLean.base.strings.cstring

namespace JuliaLean.Proofs.base.strings.cstring
open JuliaLean.Registry
open JuliaLean.base.strings.cstring

/-- Pointer wrappers and conversions retain the native address. -/
def PointerAddressSpec : Prop :=
  (∀ {T : Type} [CstringTarget T] (p : Ptr T),
    (cstringCtor p).address = p.address ∧ (convertCstring p).address = p.address) ∧
  (∀ {T : Type} [CwstringTarget T] (p : Ptr T),
    (cwstringCtor p).address = p.address ∧ (convertCwstring p).address = p.address) ∧
  (∀ {T : Type} [CstringTarget T] (p : Cstring),
    (ptrCstring (T := T) p).address = p.address ∧
    (convertPtrCstring (T := T) p).address = p.address) ∧
  (∀ {T : Type} [CwstringTarget T] (p : Cwstring),
    (ptrCwstring (T := T) p).address = p.address ∧
    (convertPtrCwstring (T := T) p).address = p.address) ∧
  (∀ p : Cstring, (pointerCstring p).address = p.address) ∧
  (∀ p : Cwstring, (pointerCwstring p).address = p.address) ∧
  (∀ {T : Type} [CstringMemoryTarget T] (convert : Memory T → Ptr Cvoid) (s : Memory T),
    (unsafeConvertCstringMemory convert s).address = (convert s).address) ∧
  (∀ (convert : Symbol → Ptr Int8) (s : Symbol),
    (unsafeConvertCstringSymbol convert s).address = (convert s).address) ∧
  (∀ {S : Type} (convert : S → StringResult (Ptr Cwchar_t)) (s : S)
      (p : Ptr Cwchar_t), convert s = .ok p →
    ∃ out, unsafeConvertCwstring convert s = .ok out ∧ out.address = p.address)

theorem pointerAddress_proven : PointerAddressSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; exact ⟨rfl, rfl⟩
  · intros; exact ⟨rfl, rfl⟩
  · intros; exact ⟨rfl, rfl⟩
  · intros; exact ⟨rfl, rfl⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro S convert s p h
    exact ⟨cwstringCtor p, by simp [unsafeConvertCwstring, h, Functor.map, Except.map], rfl⟩

/-- Identity conversions preserve their argument, including invalid string bytes. -/
def IdentityConversionSpec : Prop :=
  (∀ s : JString, cconvertCstringString s = s) ∧
  (∀ s : Cwstring, unsafeConvertCwstringIdentity s = s) ∧
  (∀ s : Symbol, cconvertCstringSymbol s = s) ∧
  (∀ {T V : Type} [TranscodeCodeUnit T] [AbstractVectorValue V T] (src : V),
    transcodeIdentity (T := T) src = src) ∧
  (∀ s : JString, transcodeStringIdentity s = .ok s)

theorem identityConversion_proven : IdentityConversionSpec := by
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The two C string types expose the platform's native code-unit types. -/
def ElementTypeSpec : Prop := eltypeCstring = Int8 ∧ eltypeCwstring = Cwchar_t

theorem elementType_proven : ElementTypeSpec := ⟨rfl, rfl⟩

/-- Constructing the concrete C-call argument preserves conversion results and errors. -/
def AbstractCStringSpec : Prop :=
  ∀ {S : Type} (convert : S → StringResult JString) (s : S)
    (result : StringResult JString), convert s = result →
    cconvertCstringAbstract convert s = result

theorem abstractCString_proven : AbstractCStringSpec := by
  intro S convert s result h
  cases result <;> simp [cconvertCstringAbstract, h, cconvertCstringString]

/-- UTF-32 forwarding preserves the converted character sequence and conversion errors. -/
def Utf32ForwardingSpec : Prop :=
  (∀ {V T : Type} [Utf32CodeUnit T] [AbstractVectorValue V UInt8]
    (copy : V → List UInt8) (string : List UInt8 → StringResult JString)
    (convert : UInt32 → StringResult T) (src : V) (text : JString)
    (result : StringResult (List T)),
    string (copy src) = .ok text → transcodeString32 convert text = result →
    transcodeBytes32 copy string convert src = result) ∧
  (∀ {T : Type} [Utf32CodeUnit T]
    (string : CodeUnits → StringResult JString) (convert : UInt32 → StringResult T)
    (src : CodeUnits) (text : JString) (result : StringResult (List T)),
    string src = .ok text → transcodeString32 convert text = result →
    transcodeCodeUnits32 string convert src = result)

theorem utf32Forwarding_proven : Utf32ForwardingSpec := by
  constructor
  · intro V T inst instV copy string convert src text result hs ht
    simpa only [transcodeBytes32, hs, bind, Except.bind] using ht
  · intro T inst string convert src text result hs ht
    simpa only [transcodeCodeUnits32, hs, bind, Except.bind] using ht

/-- Generic transcoding keeps the target encoding's output and the String constructor's bytes. -/
def TranscodeForwardingSpec : Prop :=
  (∀ {T R A : Type} [TranscodeOverload T R A] (units : JString → R)
    (src : JString) (result : StringResult A),
    transcode (T := T) (units src) = result →
    transcodeStringCodeUnits (T := T) units src = result) ∧
  (∀ {S : Type} [TranscodeOverload UInt8 S (List UInt8)]
    (string : List UInt8 → StringResult JString) (src : S) (bytes : List UInt8)
    (out : JString),
    transcode (T := UInt8) src = .ok bytes → string bytes = .ok out →
    transcodeToString string src = .ok out)

theorem transcodeForwarding_proven : TranscodeForwardingSpec := by
  constructor
  · intro T R A inst units src result h; exact h
  · intro S inst string src bytes out ht hs
    simp only [transcodeToString, ht, bind, Except.bind, hs]

/-- Cwstring's unsafe string conversion preserves the wide-pointer reader's result. -/
def UnsafeCwstringForwardingSpec : Prop :=
  ∀ (pointer : PointerAccess Cwchar_t) (zero : Cwchar_t)
    (eq : Cwchar_t → Cwchar_t → Bool)
    [CwcharPlatform] [Utf16ToUtf8Runtime] [Char32ToUtf8Runtime Int32]
    (string : List UInt8 → StringResult JString) (cw : Cwstring)
    (result : StringResult JString),
    unsafeStringWide pointer zero eq string cw = result →
    unsafeStringCwstring pointer zero eq string cw = result

theorem unsafeCwstringForwarding_proven : UnsafeCwstringForwardingSpec := by
  intro pointer zero eq platform utf16 utf32 string cw result h
  exact h

/-- Abstract-string NUL detection uses character membership for any string encoding. -/
def AbstractContainsNulSpec : Prop :=
  ∀ {S : Type} (member : S → StringResult Bool) (characters : S → List UInt32) (s : S),
    (∀ text, member text = .ok ((characters text).contains 0)) →
    containsnulAbstract member s = .ok ((characters s).contains 0)

theorem abstractContainsNul_proven : AbstractContainsNulSpec := by
  intro S member characters s law
  exact law s

end JuliaLean.Proofs.base.strings.cstring

namespace JuliaLean.Proofs.base.strings.cstring

def wrapperEntries : List JuliaLean.Registry.Entry := [
  { id := "cstring-pointer-address", juliaFile := "base/strings/cstring.jl"
    juliaFns := ["Cstring(p::Union{Ptr{Int8},Ptr{UInt8},Ptr{Cvoid}})", "Cwstring(p::Union{Ptr{Cwchar_t},Ptr{Cvoid}})", "Ptr{T}(p::Cstring) where {T<:Union{Int8,UInt8,Cvoid}}", "convert(::Type{Cstring}, p::Union{Ptr{Int8},Ptr{UInt8},Ptr{Cvoid}})", "convert(::Type{Cwstring}, p::Union{Ptr{Cwchar_t},Ptr{Cvoid}})", "convert(::Type{Ptr{T}}, p::Cstring) where {T<:Union{Int8,UInt8,Cvoid}}", "convert(::Type{Ptr{T}}, p::Cwstring) where {T<:Union{Cwchar_t,Cvoid}}", "pointer(p::Cstring)", "pointer(p::Cwstring)", "unsafe_convert(::Type{Cstring}, s::Union{Memory{UInt8},Memory{Int8}})", "unsafe_convert(::Type{Cwstring}, s)", "unsafe_convert(::Type{Cstring}, s::Symbol)"]
    statement := "C string constructors, pointer conversions, Memory and Symbol conversions preserve their native addresses."
    source := "base/strings/cstring.jl:31,32,33,36,37,38,39,55,56,90,101,106", status := .proven, prop := ``PointerAddressSpec, thm := some ``pointerAddress_proven },
  { id := "cstring-identity-conversions", juliaFile := "base/strings/cstring.jl"
    juliaFns := ["cconvert(::Type{Cstring}, s::String)", "unsafe_convert(::Type{Cwstring}, s::Cwstring)", "cconvert(::Type{Cstring}, s::Symbol)", "transcode(::Type{T}, src::AbstractVector{T}) where {T<:Union{UInt8,UInt16,UInt32,Int32}}", "transcode(::Type{String}, src::String)"]
    statement := "Identity C-call and same-encoding conversions preserve their string, symbol or vector argument."
    source := "base/strings/cstring.jl:65,102,105,163,177", status := .proven, prop := ``IdentityConversionSpec, thm := some ``identityConversion_proven },
  { id := "cstring-element-types", juliaFile := "base/strings/cstring.jl"
    juliaFns := ["eltype(::Type{Cstring})", "eltype(::Type{Cwstring})"]
    statement := "Cstring and Cwstring expose their native character code-unit types."
    source := "base/strings/cstring.jl:75,76", status := .proven, prop := ``ElementTypeSpec, thm := some ``elementType_proven },
  { id := "cstring-abstract-argument", juliaFile := "base/strings/cstring.jl"
    juliaFns := ["cconvert(::Type{Cstring}, s::AbstractString)"]
    statement := "Abstract-string C-call conversion preserves the String conversion result, including errors."
    source := "base/strings/cstring.jl:66", status := .proven, prop := ``AbstractCStringSpec, thm := some ``abstractCString_proven },
  { id := "cstring-utf32-forwarding", juliaFile := "base/strings/cstring.jl"
    juliaFns := ["transcode(::Type{T}, src::AbstractVector{UInt8}) where {T<:Union{Int32,UInt32}}", "transcode(::Type{T}, src::CodeUnits{UInt8,String}) where {T<:Union{Int32,UInt32}}"]
    statement := "UTF-32 forwarding wrappers preserve the converted character sequence and conversion errors."
    source := "base/strings/cstring.jl:165,167", status := .proven, prop := ``Utf32ForwardingSpec, thm := some ``utf32Forwarding_proven },
  { id := "cstring-transcode-forwarding", juliaFile := "base/strings/cstring.jl"
    juliaFns := ["transcode(T, src::String)", "transcode(::Type{String}, src)"]
    statement := "Generic transcode wrappers preserve the selected target output and the constructed String bytes."
    source := "base/strings/cstring.jl:178,183", status := .proven, prop := ``TranscodeForwardingSpec, thm := some ``transcodeForwarding_proven },
  { id := "cstring-unsafe-wide-forwarding", juliaFile := "base/strings/cstring.jl"
    juliaFns := ["unsafe_string(cw::Cwstring)"]
    statement := "Cwstring unsafe_string returns the same decoded bytes or error as the wide-pointer reader."
    source := "base/strings/cstring.jl:331", status := .proven, prop := ``UnsafeCwstringForwardingSpec, thm := some ``unsafeCwstringForwarding_proven },
  { id := "cstring-abstract-nul-membership", juliaFile := "base/strings/cstring.jl"
    juliaFns := ["containsnul(s::AbstractString)"]
    statement := "Abstract-string NUL detection agrees with character membership for every string encoding."
    source := "base/strings/cstring.jl:81", status := .proven, prop := ``AbstractContainsNulSpec, thm := some ``abstractContainsNul_proven },
]

end JuliaLean.Proofs.base.strings.cstring
