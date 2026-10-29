import JuliaLean.Core
import JuliaLean.Strings.Basic
import JuliaLean.base.strings.string

/-!
# Model of `base/strings/cstring.jl`

Julia revision `f755f49a9e41380d7da126b3c1db9fe7f83dd027`. Pointers keep their
pointee type. `PointerAccess.load` is the typed one-based `unsafe_load` interface;
`loadLaw` relates it to the addressed cells, and `wrapLaw` describes a valid
length-qualified pointer wrap. Calls into other Base files and runtime services
remain typed parameters.
-/

namespace JuliaLean.base.strings.cstring

open JuliaLean JuliaLean.Strings

abbrev JString := JuliaLean.Strings.JStr
abbrev StringResult (α : Type) := JuliaLean.Strings.SJl α
abbrev Index := JuliaLean.JInt64
abbrev ix (n : Int) : Index := JuliaLean.Strings.ix n

/-- Typed dispatch for Julia's overloaded `transcode` methods. Instances select the local
source-mirrored overload; runtime and other-file operations remain typed interfaces. -/
class TranscodeOverload (T S Output : Type) where
  run : S → StringResult Output

def transcode {T S Output : Type} [overload : TranscodeOverload T S Output]
    (src : S) : StringResult Output :=
  overload.run src

inductive Cvoid where
  | token
  deriving Repr, DecidableEq

opaque Cwchar_t : Type

inductive CwcharEncoding where
  | utf16
  | utf32
  deriving Repr, DecidableEq

/-- `Cwchar_t` is `UInt16` on Windows and a 32-bit character type on Unix systems. -/
class CwcharPlatform where
  encoding : CwcharEncoding
  fromUInt16 : UInt16 → Cwchar_t
  fromChar32 : UInt32 → StringResult Cwchar_t
  toUInt16 : Cwchar_t → UInt16
  toInt32 : Cwchar_t → Int32

structure Ptr (α : Type) where
  address : Nat
  deriving Repr, DecidableEq

abbrev Cstring := Ptr Int8
abbrev Cwstring := Ptr Cwchar_t
inductive CstringOrCwstring where
  | cstring (value : Cstring)
  | cwstring (value : Cwstring)

class CstringTarget (T : Type) : Prop where
  supported : True

class CwstringTarget (T : Type) : Prop where
  supported : True

instance : CstringTarget Int8 := ⟨True.intro⟩
instance : CstringTarget UInt8 := ⟨True.intro⟩
instance : CstringTarget Cvoid := ⟨True.intro⟩
instance : CwstringTarget Cwchar_t := ⟨True.intro⟩
instance : CwstringTarget Cvoid := ⟨True.intro⟩

class CstringMemoryTarget (T : Type) : Prop where
  supported : True

instance : CstringMemoryTarget UInt8 := ⟨True.intro⟩
instance : CstringMemoryTarget Int8 := ⟨True.intro⟩

class WideCodeUnit (T : Type) : Prop where
  supported : True

instance : WideCodeUnit UInt16 := ⟨True.intro⟩
instance : WideCodeUnit UInt32 := ⟨True.intro⟩
instance : WideCodeUnit Cwchar_t := ⟨True.intro⟩

class JuliaIntegerArgument (N : Type) where
  toInt : N → Int

instance : JuliaIntegerArgument Int := ⟨id⟩
instance : JuliaIntegerArgument Nat := ⟨Int.ofNat⟩
instance (t : IntTy) : JuliaIntegerArgument (JInt t) := ⟨fun n => n.val⟩
class AbstractVectorValue (V : Type) (T : Type) : Prop where
  supported : True

instance (T : Type) : AbstractVectorValue (List T) T := ⟨True.intro⟩

structure Memory (α : Type) where
  address : Nat
  deriving Repr, DecidableEq

structure Symbol where
  address : Nat
  deriving Repr, DecidableEq

structure CodeUnits where
  parent : JString
  bytes : List UInt8
  deriving Repr
instance : AbstractVectorValue CodeUnits UInt8 := ⟨True.intro⟩

def codeunitsString (src : JString) : CodeUnits := ⟨src, src.bytes⟩

structure StringVector where
  capacity : Index
  written : List UInt8
  deriving Repr

/-- Pointer reads use one-based indices and expose the valid cells they address. -/
structure PointerAccess (α : Type) where
  cells : Ptr α → List α
  load : Ptr α → Nat → α
  loadLaw : ∀ p i, 1 ≤ i → i ≤ (cells p).length →
    ∃ before after, cells p = before ++ load p i :: after ∧ before.length + 1 = i
  unsafeWrap : Ptr α → Int → StringResult (List α)
  wrapLaw : ∀ p n, 0 ≤ n → n.toNat ≤ (cells p).length →
    unsafeWrap p n = .ok ((cells p).take n.toNat)

/-- The signed interpretation used by `b % Int8` in the UTF-8 decoder. -/
def signedByte (b : UInt8) : Int :=
  if b.toNat < 128 then (b.toNat : Int) else (b.toNat : Int) - 256

def utf8Lead (a : UInt8) : Bool :=
  decide (-64 ≤ signedByte a) && decide (signedByte a ≤ -12)

def utf8Two (a b : UInt8) : UInt16 :=
  (0x3080 : UInt16) ^^^ (a.toUInt16 <<< 6) ^^^ b.toUInt16

def utf8Three (a b c : UInt8) : UInt16 :=
  (0x2080 : UInt16) ^^^ (a.toUInt16 <<< 12) ^^^ (b.toUInt16 <<< 6) ^^^ c.toUInt16

def utf8FourHigh (a b c : UInt8) : UInt16 :=
  (0xe5b8 : UInt16) + (a.toUInt16 <<< 8) + (b.toUInt16 <<< 2) + (c >>> 4).toUInt16

def utf8FourLow (c d : UInt8) : UInt16 :=
  (0xdc80 : UInt16) ^^^ ((c &&& 0xf).toUInt16 <<< 6) ^^^ d.toUInt16

/-- The `while true` decoder over the unconsumed bytes of `src`. -/
def utf8ToUtf16Loop {V : Type}
    (read : V → Index → StringResult UInt8)
    (push : List UInt16 → List UInt16 → StringResult (List UInt16))
    (src : V) (n : Index) : Nat → Index → UInt8 → List UInt16 → StringResult (List UInt16)
  | 0, _, _, _ => .error .assertion
  | fuel + 1, i, a, dst => do
      if decide (i < n) && utf8Lead a then
        let b ← read src (i + ix 1)
        let i := i + ix 1
        if decide (-64 ≤ signedByte b) || (a == 0xf4 && 0x8f < b) then
          utf8ToUtf16Loop read push src n fuel i b (← push dst [a.toUInt16])
        else if a < 0xe0 then
          let dst ← push dst [utf8Two a b]
          if i < n then
            let next ← read src (i + ix 1)
            utf8ToUtf16Loop read push src n fuel (i + ix 1) next dst
          else pure dst
        else if i < n then
          let c ← read src (i + ix 1)
          let i := i + ix 1
          if decide (-64 ≤ signedByte c) then
            utf8ToUtf16Loop read push src n fuel i c (← push dst [a.toUInt16, b.toUInt16])
          else if a < 0xf0 then
            let dst ← push dst [utf8Three a b c]
            if i < n then
              let next ← read src (i + ix 1)
              utf8ToUtf16Loop read push src n fuel (i + ix 1) next dst
            else pure dst
          else if i < n then
            let d ← read src (i + ix 1)
            let i := i + ix 1
            if decide (-64 ≤ signedByte d) then
              utf8ToUtf16Loop read push src n fuel i d
                (← push dst [a.toUInt16, b.toUInt16, c.toUInt16])
            else if a == 0xf0 && b < 0x90 then
              let dst ← push dst [utf8Three b c d]
              if i < n then
                let next ← read src (i + ix 1)
                utf8ToUtf16Loop read push src n fuel (i + ix 1) next dst
              else pure dst
            else
              let dst ← push dst [utf8FourHigh a b c, utf8FourLow c d]
              if i < n then
                let next ← read src (i + ix 1)
                utf8ToUtf16Loop read push src n fuel (i + ix 1) next dst
              else pure dst
          else
            push dst [a.toUInt16, b.toUInt16, c.toUInt16]
        else
          push dst [a.toUInt16, b.toUInt16]
      else
        let dst ← push dst [a.toUInt16]
        if i < n then
          let next ← read src (i + ix 1)
          utf8ToUtf16Loop read push src n fuel (i + ix 1) next dst
        else pure dst

def u16CountContinue {V : Type} (read : V → Index → StringResult UInt16)
    (src : V) (n i m : Index) : StringResult (Option (Index × UInt16 × Index)) :=
  if i < n then do
    let a ← read src (i + ix 1)
    pure (some (i + ix 1, a, m))
  else pure none

def utf16CountLoop {V : Type} (read : V → Index → StringResult UInt16)
    (length : V → Index) (src : V) (n : Index) :
      Nat → Index → UInt16 → Index → StringResult Index
  | 0, _, _, _ => .error .assertion
  | fuel + 1, i, a, m => do
      if a < 0x80 then
        let m := m + ix 1
        match ← u16CountContinue read src n i m with
        | none => pure m
        | some (nextI, nextA, nextM) =>
            utf16CountLoop read length src n fuel nextI nextA nextM
      else if a < 0x800 then
        let m := m + ix 2
        match ← u16CountContinue read src n i m with
        | none => pure m
        | some (nextI, nextA, nextM) =>
            utf16CountLoop read length src n fuel nextI nextA nextM
      else if (a &&& 0xfc00) == 0xd800 && decide (i < length src) then
        let b ← read src (i + ix 1)
        if (b &&& 0xfc00) == 0xdc00 then
          let m := m + ix 4
          match ← u16CountContinue read src n (i + ix 1) m with
          | none => pure m
          | some (nextI, nextA, nextM) =>
              utf16CountLoop read length src n fuel nextI nextA nextM
        else
          utf16CountLoop read length src n fuel (i + ix 1) b (m + ix 3)
      else
        let m := m + ix 3
        match ← u16CountContinue read src n i m with
        | none => pure m
        | some (nextI, nextA, nextM) =>
            utf16CountLoop read length src n fuel nextI nextA nextM

def putStringBytes (setByte : StringVector → Index → UInt8 → StringResult StringVector)
    (dst : StringVector) (j : Index) (bytes : List UInt8) :
      StringResult (StringVector × Index) :=
  bytes.foldlM (fun (state : StringVector × Index) b => do
    let j := state.2 + ix 1
    let dst ← setByte state.1 j b
    pure (dst, j)) (dst, j)

def u16WriteContinue {V : Type} (read : V → Index → StringResult UInt16)
    (src : V) (n i j : Index) (dst : StringVector) :
      StringResult (Option (Index × UInt16 × Index × StringVector)) :=
  if i < n then do
    let a ← read src (i + ix 1)
    pure (some (i + ix 1, a, j, dst))
  else pure none

def utf16ToUtf8WriteLoop {V : Type}
    (read : V → Index → StringResult UInt16)
    (setByte : StringVector → Index → UInt8 → StringResult StringVector)
    (src : V) (n : Index) :
      Nat → Index → UInt16 → Index → StringVector → StringResult StringVector
  | 0, _, _, _, _ => .error .assertion
  | fuel + 1, i, a, j, dst => do
      if a < 0x80 then
        let (dst, j) ← putStringBytes setByte dst j [a.toUInt8]
        match ← u16WriteContinue read src n i j dst with
        | none => pure dst
        | some (nextI, nextA, nextJ, nextDst) =>
            utf16ToUtf8WriteLoop read setByte src n fuel nextI nextA nextJ nextDst
      else if a < 0x800 then
        let bytes := [(0xc0 : UInt8) ||| (a >>> 6).toUInt8,
          (0x80 : UInt8) ||| (a.toUInt8 &&& (0x3f : UInt8))]
        let (dst, j) ← putStringBytes setByte dst j bytes
        match ← u16WriteContinue read src n i j dst with
        | none => pure dst
        | some (nextI, nextA, nextJ, nextDst) =>
            utf16ToUtf8WriteLoop read setByte src n fuel nextI nextA nextJ nextDst
      else if (a &&& 0xfc00) == 0xd800 && decide (i < n) then
        let b ← read src (i + ix 1)
        if (b &&& 0xfc00) == 0xdc00 then
          let a := a + 0x2840
          let bytes := [
            (0xf0 : UInt8) ||| (a >>> 8).toUInt8,
            (0x80 : UInt8) ||| (a.toUInt8 >>> 2),
            (0xf0 : UInt8) ^^^ ((a.toUInt8 <<< 4) &&& (0x3f : UInt8)) ^^^ (b >>> 6).toUInt8,
            (0x80 : UInt8) ||| (b.toUInt8 &&& (0x3f : UInt8))]
          let (dst, j) ← putStringBytes setByte dst j bytes
          match ← u16WriteContinue read src n (i + ix 1) j dst with
          | none => pure dst
          | some (nextI, nextA, nextJ, nextDst) =>
              utf16ToUtf8WriteLoop read setByte src n fuel nextI nextA nextJ nextDst
        else
          let bytes := [
            (0xe0 : UInt8) ||| (a >>> 12).toUInt8,
            (0x80 : UInt8) ||| ((a >>> 6).toUInt8 &&& (0x3f : UInt8)),
            (0x80 : UInt8) ||| (a.toUInt8 &&& (0x3f : UInt8))]
          let (dst, j) ← putStringBytes setByte dst j bytes
          utf16ToUtf8WriteLoop read setByte src n fuel (i + ix 1) b j dst
      else
        let bytes := [
          (0xe0 : UInt8) ||| (a >>> 12).toUInt8,
          (0x80 : UInt8) ||| ((a >>> 6).toUInt8 &&& (0x3f : UInt8)),
          (0x80 : UInt8) ||| (a.toUInt8 &&& (0x3f : UInt8))]
        let (dst, j) ← putStringBytes setByte dst j bytes
        match ← u16WriteContinue read src n i j dst with
        | none => pure dst
        | some (nextI, nextA, nextJ, nextDst) =>
            utf16ToUtf8WriteLoop read setByte src n fuel nextI nextA nextJ nextDst

/--
Julia source: base/strings/cstring.jl:31-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Cstring(p::Union{Ptr{Int8},Ptr{UInt8},Ptr{Cvoid}}) = bitcast(Cstring, p)
```
-/
def cstringCtor {T : Type} [CstringTarget T] (p : Ptr T) : Cstring := ⟨p.address⟩

/--
Julia source: base/strings/cstring.jl:32-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Cwstring(p::Union{Ptr{Cwchar_t},Ptr{Cvoid}})       = bitcast(Cwstring, p)
```
-/
def cwstringCtor {T : Type} [CwstringTarget T] (p : Ptr T) : Cwstring := ⟨p.address⟩

/--
Julia source: base/strings/cstring.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Ptr{T}(p::Cstring) where {T<:Union{Int8,UInt8,Cvoid}} = bitcast(Ptr{T}, p)
```
-/
def ptrCstring {T : Type} [CstringTarget T] (p : Cstring) : Ptr T := ⟨p.address⟩

/--
Julia source: base/strings/cstring.jl:34-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Ptr{T}(p::Cwstring) where {T<:Union{Cwchar_t,Cvoid}}  = bitcast(Ptr{Cwchar_t}, p)
```
-/
def ptrCwstring {T : Type} [CwstringTarget T] (p : Cwstring) : Ptr Cwchar_t :=
  ⟨p.address⟩

/--
Julia source: base/strings/cstring.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Cstring}, p::Union{Ptr{Int8},Ptr{UInt8},Ptr{Cvoid}}) = Cstring(p)
```
-/
def convertCstring {T : Type} [CstringTarget T] (p : Ptr T) : Cstring := cstringCtor p

/--
Julia source: base/strings/cstring.jl:37-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Cwstring}, p::Union{Ptr{Cwchar_t},Ptr{Cvoid}}) = Cwstring(p)
```
-/
def convertCwstring {T : Type} [CwstringTarget T] (p : Ptr T) : Cwstring := cwstringCtor p

/--
Julia source: base/strings/cstring.jl:38-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Ptr{T}}, p::Cstring) where {T<:Union{Int8,UInt8,Cvoid}} = Ptr{T}(p)
```
-/
def convertPtrCstring {T : Type} [CstringTarget T] (p : Cstring) : Ptr T := ptrCstring p

/--
Julia source: base/strings/cstring.jl:39-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Ptr{T}}, p::Cwstring) where {T<:Union{Cwchar_t,Cvoid}} = Ptr{T}(p)
```
-/
def convertPtrCwstring {T : Type} [CwstringTarget T] (p : Cwstring) : Ptr Cwchar_t :=
  ptrCwstring (T := T) p

/--
Julia source: base/strings/cstring.jl:55-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pointer(p::Cstring) = convert(Ptr{Cchar}, p)
```
-/
def pointerCstring (p : Cstring) : Ptr Int8 := convertPtrCstring (T := Int8) p

/--
Julia source: base/strings/cstring.jl:56-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pointer(p::Cwstring) = convert(Ptr{Cwchar_t}, p)
```
-/
def pointerCwstring (p : Cwstring) : Ptr Cwchar_t :=
  convertPtrCwstring (T := Cwchar_t) p

inductive CStringPointerValue where
  | cstring (value : Ptr Int8)
  | cwstring (value : Ptr Cwchar_t)

def pointerCstringOrCwstring (value : CstringOrCwstring) : CStringPointerValue :=
  match value with
  | .cstring pointer => .cstring (pointerCstring pointer)
  | .cwstring pointer => .cwstring (pointerCwstring pointer)

/--
Julia source: base/strings/cstring.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::Union{Cstring,Cwstring}, y::Ptr) = pointer(x) == y
```
-/
def eqCptr {U : Type}
    (ptrEq : ∀ {α β : Type}, Ptr α → Ptr β → Bool)
    (x : CstringOrCwstring) (y : Ptr U) : Bool :=
  match pointerCstringOrCwstring x with
  | .cstring value => ptrEq value y
  | .cwstring value => ptrEq value y

/--
Julia source: base/strings/cstring.jl:60-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::Ptr, y::Union{Cstring,Cwstring}) = x == pointer(y)
```
-/
def eqPtrC {T : Type}
    (ptrEq : ∀ {α β : Type}, Ptr α → Ptr β → Bool)
    (x : Ptr T) (y : CstringOrCwstring) : Bool :=
  match pointerCstringOrCwstring y with
  | .cstring value => ptrEq x value
  | .cwstring value => ptrEq x value

/--
Julia source: base/strings/cstring.jl:62-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_string(s::Cstring) = unsafe_string(convert(Ptr{UInt8}, s))
```
-/
def unsafeStringCstring (unsafeString : Ptr UInt8 → StringResult JString)
    (s : Cstring) : StringResult JString :=
  unsafeString (convertPtrCstring (T := UInt8) s)

/--
Julia source: base/strings/cstring.jl:65-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Cstring}, s::String) = s
```
-/
def cconvertCstringString (s : JString) : JString := s

/--
Julia source: base/strings/cstring.jl:66-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Cstring}, s::AbstractString) =
    cconvert(Cstring, String(s)::String)
```
-/
def cconvertCstringAbstract {S : Type} (toString : S → StringResult JString)
    (s : S) : StringResult JString := do
  let concrete ← toString s
  pure (cconvertCstringString concrete)


/--
Julia source: base/strings/cstring.jl:75-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{Cstring}) = Cchar
```
-/
def eltypeCstring : Type := Int8

/--
Julia source: base/strings/cstring.jl:76-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{Cwstring}) = Cwchar_t
```
-/
def eltypeCwstring : Type := Cwchar_t

/--
Julia source: base/strings/cstring.jl:78-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
containsnul(p::Ptr, len) =
    C_NULL != ccall(:memchr, Ptr{Cchar}, (Ptr{Cchar}, Cint, Csize_t), p, 0, len)
```
-/
def containsnulPtr {T : Type} (cast : Ptr T → Ptr Int8)
    (memchrZero : Ptr Int8 → Nat → Bool) (p : Ptr T) (len : Nat) : Bool :=
  memchrZero (cast p) len

/--
Julia source: base/strings/cstring.jl:80-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
containsnul(s::String) = containsnul(unsafe_convert(Ptr{Cchar}, s), sizeof(s))
```
-/
def containsnulString (unsafeConvert : JString → Ptr Int8) (sizeof : JString → Nat)
    (memchrZero : Ptr Int8 → Nat → Bool) (s : JString) : Bool :=
  containsnulPtr (fun p => p) memchrZero (unsafeConvert s) (sizeof s)

/--
Julia source: base/strings/cstring.jl:81-81 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
containsnul(s::AbstractString) = '\0' in s
```
-/
def containsnulAbstract {S : Type}
    (containsNulChar : S → StringResult Bool) (s : S) : StringResult Bool :=
  containsNulChar s

/--
Julia source: base/strings/cstring.jl:83-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_convert(::Type{Cstring}, s::String)
    p = unsafe_convert(Ptr{Cchar}, s)
    containsnul(p, sizeof(s)) &&
        throw(ArgumentError("embedded NULs are not allowed in C strings: $(repr(s))"))
    return Cstring(p)
end
```
-/
def unsafeConvertCstring (unsafeConvert : JString → Ptr Int8)
    (memchrZero : Ptr Int8 → Nat → Bool) (sizeof : JString → Nat)
    (repr : JString → String) (s : JString) : StringResult Cstring := do
  let p := unsafeConvert s
  if containsnulPtr (fun p => p) memchrZero p (sizeof s) then
    .error (.jl (.argumentError s!"embedded NULs are not allowed in C strings: {repr s}"))
  else
    pure (cstringCtor p)

/--
Julia source: base/strings/cstring.jl:90-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Cstring}, s::Union{Memory{UInt8},Memory{Int8}}) = Cstring(unsafe_convert(Ptr{Cvoid}, s))
```
-/
def unsafeConvertCstringMemory {T : Type} [CstringMemoryTarget T]
    (unsafeConvertVoid : Memory T → Ptr Cvoid) (memory : Memory T) : Cstring :=
  cstringCtor (unsafeConvertVoid memory)

/--
Julia source: base/strings/cstring.jl:92-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cconvert(::Type{Cwstring}, v::Vector{Cwchar_t})
    for i = 1:length(v)-1
        v[i] == 0 &&
            throw(ArgumentError("embedded NULs are not allowed in C strings: $(repr(v))"))
    end
    v[end] == 0 ||
        throw(ArgumentError("C string data must be NUL terminated: $(repr(v))"))
    return cconvert(Ptr{Cwchar_t}, v)
end
```
-/
def cconvertCwstringVector (zero : Cwchar_t) (eq : Cwchar_t → Cwchar_t → Bool)
    (repr : List Cwchar_t → String)
    (cconvertPtr : List Cwchar_t → StringResult (Ptr Cwchar_t))
    (v : List Cwchar_t) : StringResult (Ptr Cwchar_t) := do
  for x in v.dropLast do
    if eq x zero then
      throw (.jl (.argumentError s!"embedded NULs are not allowed in C strings: {repr v}"))
  match v.getLast? with
  | none => throw boundsErr
  | some last =>
      if eq last zero then
        cconvertPtr v
      else
        throw (.jl (.argumentError s!"C string data must be NUL terminated: {repr v}"))

/--
Julia source: base/strings/cstring.jl:69-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cconvert(::Type{Cwstring}, s::AbstractString)
    v = transcode(Cwchar_t, String(s))
    push!(v, 0)
    return cconvert(Cwstring, v)
end
```
-/
def cconvertCwstringAbstract {S : Type}
    [TranscodeOverload Cwchar_t JString (List Cwchar_t)]
    (toString : S → StringResult JString)
    (zero : Cwchar_t) (eq : Cwchar_t → Cwchar_t → Bool)
    (repr : List Cwchar_t → String)
    (cconvertPtr : List Cwchar_t → StringResult (Ptr Cwchar_t))
    (s : S) : StringResult (Ptr Cwchar_t) := do
  let concrete ← toString s
  let v ← transcode (T := Cwchar_t) concrete
  let v := v ++ [zero]
  cconvertCwstringVector zero eq repr cconvertPtr v
/--
Julia source: base/strings/cstring.jl:101-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Cwstring}, s) = Cwstring(unsafe_convert(Ptr{Cwchar_t}, s))
```
-/
def unsafeConvertCwstring {S : Type} (unsafeConvert : S → StringResult (Ptr Cwchar_t))
    (s : S) : StringResult Cwstring := do
  pure (cwstringCtor (T := Cwchar_t) (← unsafeConvert s))

/--
Julia source: base/strings/cstring.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Cwstring}, s::Cwstring) = s
```
-/
def unsafeConvertCwstringIdentity (s : Cwstring) : Cwstring := s

/--
Julia source: base/strings/cstring.jl:105-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Cstring}, s::Symbol) = s
```
-/
def cconvertCstringSymbol (s : Symbol) : Symbol := s

/--
Julia source: base/strings/cstring.jl:106-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Cstring}, s::Symbol) = Cstring(unsafe_convert(Ptr{Cchar}, s))
```
-/
def unsafeConvertCstringSymbol (unsafeConvert : Symbol → Ptr Int8) (s : Symbol) : Cstring :=
  cstringCtor (unsafeConvert s)

/--
Julia source: base/strings/cstring.jl:119-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cwstring(s::AbstractString)
    bytes = codeunits(String(s))
    0 in bytes && throw(ArgumentError("embedded NULs are not allowed in C strings: $(repr(s))"))
    return push!(transcode(UInt16, bytes), 0)
end
```
-/
def cwstringWindows {S : Type}
    [TranscodeOverload UInt16 (List UInt8) (List UInt16)]
    (toString : S → StringResult JString)
    (codeunits : JString → List UInt8)
    (repr : JString → String) (s : S) : StringResult (List UInt16) := do
  let concrete ← toString s
  let bytes := codeunits concrete
  if bytes.contains 0 then
    throw (.jl (.argumentError s!"embedded NULs are not allowed in C strings: {repr concrete}"))
  let wide ← transcode (T := UInt16) bytes
  pure (wide ++ [0])
def iterateCstringString (s : JString) (i : Index) : Option (UInt32 × Index) :=
  JuliaLean.base.strings.string.iterateString
    (fun _ => ix 1)
    (fun text => ix text.bytes.length)
    (fun text index => text.bytes.getD (index.val.toNat - 1) 0)
    (fun byte lo hi => decide (lo ≤ byte) && decide (byte ≤ hi))
    s i

def transcodeString32Loop {T : Type} (convertChar : UInt32 → StringResult T)
    (src : JString) : Nat → Index → List T → StringResult (List T)
  | 0, _, _ => .error .assertion
  | fuel + 1, i, outputRev =>
      match iterateCstringString src i with
      | none => .ok outputRev.reverse
      | some (character, next) => do
          let value ← convertChar character
          transcodeString32Loop convertChar src fuel next (value :: outputRev)

class TranscodeCodeUnit (T : Type) : Prop where
  valid : True

instance : TranscodeCodeUnit UInt8 := ⟨True.intro⟩
instance : TranscodeCodeUnit UInt16 := ⟨True.intro⟩
instance : TranscodeCodeUnit UInt32 := ⟨True.intro⟩
instance : TranscodeCodeUnit Int32 := ⟨True.intro⟩
/--
Julia source: base/strings/cstring.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
transcode(::Type{T}, src::AbstractVector{T}) where {T<:Union{UInt8,UInt16,UInt32,Int32}} = src
```
-/

def transcodeIdentity {T V : Type} [TranscodeCodeUnit T]
    [AbstractVectorValue V T] (src : V) : V := src

instance {T V : Type} [TranscodeCodeUnit T] [AbstractVectorValue V T] :
    TranscodeOverload T V V where
  run src := .ok (transcodeIdentity (T := T) (V := V) src)

class Utf32CodeUnit (T : Type) : Prop where
  valid : True

instance : Utf32CodeUnit Int32 := ⟨True.intro⟩
instance : Utf32CodeUnit UInt32 := ⟨True.intro⟩

instance : Utf32CodeUnit Cwchar_t := ⟨True.intro⟩
/--
Julia source: base/strings/cstring.jl:164-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
transcode(::Type{T}, src::String) where {T<:Union{Int32,UInt32}} = T[T(c) for c in src]
```
-/

def transcodeString32 {T : Type} [Utf32CodeUnit T]
    (convertChar : UInt32 → StringResult T) (src : JString) : StringResult (List T) :=
  transcodeString32Loop convertChar src (src.bytes.length + 1) (ix 1) []

class Utf32CharacterConversion (T : Type) where
  convertChar : UInt32 → StringResult T

instance {T : Type} [Utf32CodeUnit T] [conversion : Utf32CharacterConversion T] :
    TranscodeOverload T JString (List T) where
  run := transcodeString32 conversion.convertChar

/--
Julia source: base/strings/cstring.jl:165-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
transcode(::Type{T}, src::AbstractVector{UInt8}) where {T<:Union{Int32,UInt32}} =
    transcode(T, String(Vector(src)))
```
-/
def transcodeBytes32 {V T : Type} [Utf32CodeUnit T]
    [AbstractVectorValue V UInt8]
    (copyVector : V → List UInt8) (stringFromVector : List UInt8 → StringResult JString)
    (convertChar : UInt32 → StringResult T) (src : V) : StringResult (List T) := do
  let concrete ← stringFromVector (copyVector src)
  transcodeString32 convertChar concrete

class Utf8VectorRuntime (V : Type) where
  copyVector : V → List UInt8
  stringFromVector : List UInt8 → StringResult JString

instance (priority := low) {V T : Type}
    [Utf32CodeUnit T] [conversion : Utf32CharacterConversion T]
    [AbstractVectorValue V UInt8] [runtime : Utf8VectorRuntime V] :
    TranscodeOverload T V (List T) where
  run src :=
    transcodeBytes32 runtime.copyVector runtime.stringFromVector
      conversion.convertChar src

/--
Julia source: base/strings/cstring.jl:167-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
transcode(::Type{T}, src::CodeUnits{UInt8,String}) where {T<:Union{Int32,UInt32}} =
    transcode(T, String(src))
```
-/

def transcodeCodeUnits32 {T : Type} [Utf32CodeUnit T]
    (stringFromCodeUnits : CodeUnits → StringResult JString)
    (convertChar : UInt32 → StringResult T)
    (src : CodeUnits) : StringResult (List T) := do
  let concrete ← stringFromCodeUnits src
  transcodeString32 convertChar concrete
instance {T : Type} [Utf32CodeUnit T]
    [conversion : Utf32CharacterConversion T] :
    TranscodeOverload T CodeUnits (List T) where
  run src :=
    transcodeCodeUnits32 (fun units => .ok units.parent) conversion.convertChar src

class Char32Value (T : Type) : Prop where
  valid : True

instance : Char32Value Int32 := ⟨True.intro⟩
instance : Char32Value UInt32 := ⟨True.intro⟩

instance : Char32Value Cwchar_t := ⟨True.intro⟩

structure JuliaChar where
  bits : UInt32
  deriving Repr, DecidableEq
/--
Julia source: base/strings/cstring.jl:170-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function transcode(::Type{UInt8}, src::Vector{<:Union{Int32,UInt32}})
    buf = IOBuffer()
    for c in src
        print(buf, Char(c))
    end
    take!(buf)
end
```
-/

def transcode32To8 {T B : Type} [Char32Value T]
    (ioBuffer : B) (toChar : T → StringResult JuliaChar)
    (printChar : B → JuliaChar → B) (takeBuffer : B → List UInt8)
    (src : List T) : StringResult (List UInt8) := do
  let buf ← src.foldlM (fun buf c => do
    let ch ← toChar c
    pure (printChar buf ch)) ioBuffer
  pure (takeBuffer buf)

class Char32ToUtf8Runtime (T : Type) where
  Buffer : Type
  initialBuffer : Buffer
  toChar : T → StringResult JuliaChar
  printChar : Buffer → JuliaChar → Buffer
  takeBuffer : Buffer → List UInt8

instance {T : Type} [Char32Value T] [runtime : Char32ToUtf8Runtime T] :
    TranscodeOverload UInt8 (List T) (List UInt8) where
  run src :=
    transcode32To8 runtime.initialBuffer runtime.toChar runtime.printChar
      runtime.takeBuffer src

/--
Julia source: base/strings/cstring.jl:177-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
transcode(::Type{String}, src::String) = src
```
-/
def transcodeStringIdentity (src : JString) : StringResult JString := .ok src

instance : TranscodeOverload JString JString JString where
  run := transcodeStringIdentity

/--
Julia source: base/strings/cstring.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
transcode(T, src::String) = transcode(T, codeunits(src))
```
-/
def transcodeStringCodeUnits {T R α : Type}
    [TranscodeOverload T R α] (codeunits : JString → R) (src : JString) :
    StringResult α :=
  transcode (T := T) (Output := α) (codeunits src)

instance (priority := low) {T α : Type}
    [TranscodeOverload T CodeUnits α] : TranscodeOverload T JString α where
  run src :=
    transcodeStringCodeUnits (T := T) (R := CodeUnits) (α := α) codeunitsString src

/--
Julia source: base/strings/cstring.jl:182-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
transcode(::Type{String}, src::Vector{UInt8}) = String(view(src, :))
```
-/
def transcodeVectorString {W : Type} (viewAll : List UInt8 → W)
    (stringFromView : W → StringResult JString) (src : List UInt8) : StringResult JString :=
  stringFromView (viewAll src)

/--
Julia source: base/strings/cstring.jl:183-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
transcode(::Type{String}, src) = String(transcode(UInt8, src))
```
-/
def transcodeToString {S : Type} [TranscodeOverload UInt8 S (List UInt8)]
    (stringFromBytes : List UInt8 → StringResult JString)
    (src : S) : StringResult JString := do
  let bytes ← transcode (T := UInt8) src
  stringFromBytes bytes

class StringViewRuntime where
  View : Type
  viewAll : List UInt8 → View
  stringFromView : View → StringResult JString
  viewBytes : View → List UInt8

instance [runtime : StringViewRuntime] :
    TranscodeOverload JString (List UInt8) JString where
  run src := transcodeVectorString runtime.viewAll runtime.stringFromView src

class StringFromBytesRuntime where
  fromBytes : List UInt8 → StringResult JString

instance (priority := low) {S : Type}
    [TranscodeOverload UInt8 S (List UInt8)]
    [runtime : StringFromBytesRuntime] :
    TranscodeOverload JString S JString where
  run src := transcodeToString runtime.fromBytes src

/--
Julia source: base/strings/cstring.jl:185-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function transcode(::Type{UInt16}, src::AbstractVector{UInt8})
    require_one_based_indexing(src)
    dst = UInt16[]
    i, n = 1, length(src)
    n > 0 || return dst
    sizehint!(dst, 2n)
    a = src[1]
    while true
        if i < n && -64 <= a % Int8 <= -12 # multi-byte character
            b = src[i += 1]
            if -64 <= (b % Int8) || a == 0xf4 && 0x8f < b
                # invalid UTF-8 (non-continuation or too-high code point)
                push!(dst, a)
                a = b; continue
            elseif a < 0xe0 # 2-byte UTF-8
                push!(dst, xor(0x3080, UInt16(a) << 6, b))
            elseif i < n # 3/4-byte character
                c = src[i += 1]
                if -64 <= (c % Int8) # invalid UTF-8 (non-continuation)
                    push!(dst, a, b)
                    a = c; continue
                elseif a < 0xf0 # 3-byte UTF-8
                    push!(dst, xor(0x2080, UInt16(a) << 12, UInt16(b) << 6, c))
                elseif i < n
                    d = src[i += 1]
                    if -64 <= (d % Int8) # invalid UTF-8 (non-continuation)
                        push!(dst, a, b, c)
                        a = d; continue
                    elseif a == 0xf0 && b < 0x90 # overlong encoding
                        push!(dst, xor(0x2080, UInt16(b) << 12, UInt16(c) << 6, d))
                    else # 4-byte UTF-8
                        push!(dst, 0xe5b8 +% (UInt16(a) << 8) +% (UInt16(b) << 2) +% UInt16(c >> 4),
                                   xor(0xdc80, UInt16(c & 0xf) << 6, d))
                    end
                else # too short
                    push!(dst, a, b, c)
                    break
                end
            else # too short
                push!(dst, a, b)
                break
            end
        else # ASCII or invalid UTF-8 (continuation byte or too-high code point)
            push!(dst, a)
        end
        i < n || break
        a = src[i += 1]
    end
    return dst
end
```
-/
def transcodeUtf8ToUtf16 {V : Type} [AbstractVectorValue V UInt8]
    (requireOneBased : V → StringResult Unit) (length : V → Index)
    (read : V → Index → StringResult UInt8)
    (sizehint : List UInt16 → Index → StringResult (List UInt16))
    (push : List UInt16 → List UInt16 → StringResult (List UInt16))
    (src : V) : StringResult (List UInt16) := do
  let _ ← requireOneBased src
  let dst := ([] : List UInt16)
  let i := ix 1
  let n := length src
  if 0 < n.val then
    let dst ← sizehint dst (ix 2 * n)
    let a ← read src i
    utf8ToUtf16Loop read push src n n.val.toNat i a dst
  else pure dst


def transcodeUtf8ToUtf16List (src : List UInt8) : StringResult (List UInt16) :=
  transcodeUtf8ToUtf16 (V := List UInt8)
    (fun _ => .ok ())
    (fun bytes => ix bytes.length)
    (fun bytes index =>
      match bytes[(index.val - 1).toNat]? with
      | some byte => .ok byte
      | none => .error JuliaLean.Strings.boundsErr)
    (fun dst _ => .ok dst)
    (fun dst more => .ok (dst ++ more))
    src

instance : TranscodeOverload UInt16 (List UInt8) (List UInt16) where
  run := transcodeUtf8ToUtf16List

instance : TranscodeOverload UInt16 CodeUnits (List UInt16) where
  run src := transcodeUtf8ToUtf16List src.bytes

instance [platform : CwcharPlatform] :
    TranscodeOverload Cwchar_t CodeUnits (List Cwchar_t) where
  run src :=
    match platform.encoding with
    | .utf16 => do
        let units ← transcodeUtf8ToUtf16List src.bytes
        pure (units.map platform.fromUInt16)
    | .utf32 => transcodeString32 platform.fromChar32 src.parent
/--
Julia source: base/strings/cstring.jl:236-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function transcode(::Type{UInt8}, src::AbstractVector{UInt16})
    require_one_based_indexing(src)
    n = length(src)
    n == 0 && return UInt8[]

    # Precompute m = sizeof(dst).   This involves annoying duplication
    # of the loop over the src array.   However, this is not just an
    # optimization: it is problematic for security reasons to grow
    # dst dynamically, because Base.winprompt uses this function to
    # convert passwords to UTF-8 and we don't want to make unintentional
    # copies of the password data.
    a = src[1]
    i, m = 1, 0
    while true
        if a < 0x80
            m += 1
        elseif a < 0x800 # 2-byte UTF-8
            m += 2
        elseif a & 0xfc00 == 0xd800 && i < length(src)
            b = src[i += 1]
            if (b & 0xfc00) == 0xdc00 # 2-unit UTF-16 sequence => 4-byte UTF-8
                m += 4
            else
                m += 3
                a = b; continue
            end
        else
            # 1-unit high UTF-16 or unpaired high surrogate
            # either way, encode as 3-byte UTF-8 code point
            m += 3
        end
        i < n || break
        a = src[i += 1]
    end

    dst = StringVector(m)
    a = src[1]
    i, j = 1, 0
    while true
        if a < 0x80 # ASCII
            dst[j += 1] = a % UInt8
        elseif a < 0x800 # 2-byte UTF-8
            dst[j += 1] = 0xc0 | ((a >> 6) % UInt8)
            dst[j += 1] = 0x80 | ((a % UInt8) & 0x3f)
        elseif a & 0xfc00 == 0xd800 && i < n
            b = src[i += 1]
            if (b & 0xfc00) == 0xdc00
                # 2-unit UTF-16 sequence => 4-byte UTF-8
                a +%= 0x2840
                dst[j += 1] = 0xf0 | ((a >> 8) % UInt8)
                dst[j += 1] = 0x80 | ((a % UInt8) >> 2)
                dst[j += 1] = xor(0xf0, ((a % UInt8) << 4) & 0x3f, (b >> 6) % UInt8)
                dst[j += 1] = 0x80 | ((b % UInt8) & 0x3f)
            else
                dst[j += 1] = 0xe0 | ((a >> 12) % UInt8)
                dst[j += 1] = 0x80 | (((a >> 6) % UInt8) & 0x3f)
                dst[j += 1] = 0x80 | ((a % UInt8) & 0x3f)
                a = b; continue
            end
        else
            # 1-unit high UTF-16 or unpaired high surrogate
            # either way, encode as 3-byte UTF-8 code point
            dst[j += 1] = 0xe0 | ((a >> 12) % UInt8)
            dst[j += 1] = 0x80 | (((a >> 6) % UInt8) & 0x3f)
            dst[j += 1] = 0x80 | ((a % UInt8) & 0x3f)
        end
        i < n || break
        a = src[i += 1]
    end
    return dst
end
```
-/
def transcodeUtf16ToUtf8 {V : Type} [AbstractVectorValue V UInt16]
    (requireOneBased : V → StringResult Unit) (length : V → Index)
    (read : V → Index → StringResult UInt16) (empty : StringVector)
    (allocate : Index → StringResult StringVector)
    (setByte : StringVector → Index → UInt8 → StringResult StringVector)
    (src : V) : StringResult StringVector := do
  let _ ← requireOneBased src
  let n := length src
  if n.val == 0 then pure empty else do
    let a ← read src (ix 1)
    let m ← utf16CountLoop read length src n n.val.toNat (ix 1) a (ix 0)
    let dst ← allocate m
    let a ← read src (ix 1)
    utf16ToUtf8WriteLoop read setByte src n n.val.toNat (ix 1) a (ix 0) dst

class Utf16ToUtf8Runtime where
  requireOneBased : List UInt16 → StringResult Unit
  length : List UInt16 → Index
  read : List UInt16 → Index → StringResult UInt16
  empty : StringVector
  allocate : Index → StringResult StringVector
  setByte : StringVector → Index → UInt8 → StringResult StringVector

instance [runtime : Utf16ToUtf8Runtime] :
    TranscodeOverload UInt8 (List UInt16) (List UInt8) where
  run src := do
    let result ← transcodeUtf16ToUtf8 runtime.requireOneBased runtime.length
      runtime.read runtime.empty runtime.allocate runtime.setByte src
    pure result.written

instance [platform : CwcharPlatform] [Utf16ToUtf8Runtime]
    [Char32ToUtf8Runtime Int32] :
    TranscodeOverload UInt8 (List Cwchar_t) (List UInt8) where
  run units :=
    match platform.encoding with
    | .utf16 => transcode (T := UInt8) (units.map platform.toUInt16)
    | .utf32 => transcode (T := UInt8) (units.map platform.toInt32)

/--
Julia source: base/strings/cstring.jl:321-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_string(p::Ptr{T}, length::Integer) where {T<:Union{UInt16,UInt32,Cwchar_t}}
    transcode(String, unsafe_wrap(Array, p, length; own=false))
end
```
-/
def unsafeStringWideLength {T N : Type} [WideCodeUnit T] [JuliaIntegerArgument N]
    [TranscodeOverload UInt8 (List T) (List UInt8)]
    (pointer : PointerAccess T) (stringFromBytes : List UInt8 → StringResult JString)
    (p : Ptr T) (length : N) : StringResult JString := do
  let units ← pointer.unsafeWrap p (JuliaIntegerArgument.toInt length)
  transcodeToString stringFromBytes units

/--
Julia source: base/strings/cstring.jl:324-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_string(p::Ptr{T}) where {T<:Union{UInt16,UInt32,Cwchar_t}}
    n = 1
    while unsafe_load(p, n) != 0
        n += 1
    end
    return unsafe_string(p, n - 1)
end
```
-/
def unsafeStringWide {T : Type} [WideCodeUnit T]
    [TranscodeOverload UInt8 (List T) (List UInt8)] (pointer : PointerAccess T)
    (zero : T) (eq : T → T → Bool)
    (stringFromBytes : List UInt8 → StringResult JString)
    (p : Ptr T) : StringResult JString :=
  let rec scan : Nat → Nat → StringResult JString
    | 0, _ => .error JuliaLean.Strings.boundsErr
    | fuel + 1, n =>
        if eq (pointer.load p n) zero then
          unsafeStringWideLength pointer stringFromBytes p (Int.ofNat (n - 1))
        else scan fuel (n + 1)
  scan (pointer.cells p).length 1

/--
Julia source: base/strings/cstring.jl:331-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_string(cw::Cwstring) = unsafe_string(convert(Ptr{Cwchar_t}, cw))
```
-/
def unsafeStringCwstring (pointer : PointerAccess Cwchar_t)
    (zero : Cwchar_t) (eq : Cwchar_t → Cwchar_t → Bool)
    [CwcharPlatform] [Utf16ToUtf8Runtime] [Char32ToUtf8Runtime Int32]
    (stringFromBytes : List UInt8 → StringResult JString)
    (cw : Cwstring) : StringResult JString :=
  unsafeStringWide pointer zero eq stringFromBytes
    (convertPtrCwstring (T := Cwchar_t) cw)

end JuliaLean.base.strings.cstring
