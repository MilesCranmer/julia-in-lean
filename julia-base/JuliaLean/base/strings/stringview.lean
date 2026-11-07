import JuliaLean.base.char
import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.strings.basic
import JuliaLean.base.strings.string
import JuliaLean.base.strings.substring

/-!
# Model of `base/strings/stringview.jl`

Typed source models for `StringView` and `SubString{<:StringView}` over an `AbstractVector{UInt8}`
at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
-/

namespace JuliaLean.base.strings.stringview

open JuliaLean
open JuliaLean.base.strings.basic
open JuliaLean.base.strings.string (StringResult thisindStr nextindStr)
open JuliaLean.base.strings.substring (SubString)

structure StringView (V : Type) where
  data : V
  deriving Repr, DecidableEq

/--
Julia source: base/strings/stringview.jl:8-8 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StringView(v::AbstractVector{UInt8}) = StringView{typeof(v)}(v)
```
-/
def stringView {V : Type} (v : V) : StringView V := ⟨v⟩

/--
Julia source: base/strings/stringview.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pointer(s::DenseStringView) = pointer(s.data)
```
-/
def pointerStringView {V Ptr : Type} (pointerData : V → Ptr) (s : StringView V) : Ptr :=
  pointerData s.data

/--
Julia source: base/strings/stringview.jl:19-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pointer(s::DenseStringView, i::Integer) = pointer(s.data, i)
```
-/
def pointerStringViewAt {V I Ptr : Type} (pointerDataAt : V → I → Ptr)
    (s : StringView V) (i : I) : Ptr :=
  pointerDataAt s.data i

/--
Julia source: base/strings/stringview.jl:20-20 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pointer(x::SubString{<:DenseStringView}) = pointer(x.string) + x.offset
```
-/
def pointerSubStringView {V Ptr : Type} (pointerData : V → Ptr)
    (addPtr : Ptr → Index → Ptr) (x : SubString (StringView V)) : Ptr :=
  addPtr (pointerStringView pointerData x.string) x.offset

/--
Julia source: base/strings/stringview.jl:21-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pointer(x::SubString{<:DenseStringView}, i::Integer) = pointer(x.string) + x.offset + (i - 1)
```
-/
def pointerSubStringViewAt {V I J Ptr R : Type} (pointerData : V → Ptr)
    (addOffset : Ptr → Index → Ptr) (subOne : I → J) (addIndex : Ptr → J → R)
    (x : SubString (StringView V)) (i : I) : R :=
  addIndex (addOffset (pointerStringView pointerData x.string) x.offset) (subOne i)

/--
Julia source: base/strings/stringview.jl:85-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sizeof(s::StringView) = length(s.data)
```
-/
def sizeofStringView {V R : Type} (length : V → R) (s : StringView V) : R :=
  length s.data

/--
Julia source: base/strings/stringview.jl:86-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ncodeunits(s::StringView) = length(s.data)
```
-/
def ncodeunitsStringView {V R : Type} (length : V → R) (s : StringView V) : R :=
  length s.data

/--
Julia source: base/strings/stringview.jl:87-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
codeunit(::StringView) = UInt8
```
-/
def codeunitTypeStringView {V : Type} (_ : StringView V) : Type := UInt8

/--
Julia source: base/strings/stringview.jl:88-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds codeunit(s::StringView, i::Integer) = s.data[i]::UInt8
```
-/
def codeunitStringView {V I R : Type} (getindex : V → I → R)
    (s : StringView V) (i : I) : R :=
  getindex s.data i

/--
Julia source: base/strings/stringview.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
codeunits(s::StringView) = s.data
```
-/
def codeunitsStringView {V : Type} (s : StringView V) : V := s.data

/--
Julia source: base/strings/stringview.jl:90-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
codeunits(s::SubString{<:StringView}) = @view s.string.data[(1 + s.offset):(s.offset + s.ncodeunits)]
```
-/
def codeunitsSubStringView {V R : Type} (view : V → Index → Index → R)
    (s : SubString (StringView V)) : R :=
  view s.string.data (int 1 + s.offset) (s.offset + s.ncodeunits)

/--
Julia source: base/strings/stringview.jl:116-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds thisind(s::StringViewAndSub, i::Integer) = _thisind_str(s, Int(i)::Int)
```
-/
def thisindStringViewInteger {S I : Type} (toInt : I → StringResult Index)
    (ncodeunits : S → Index) (betweenI : Index → Index → Index → Bool)
    (betweenByte : UInt8 → UInt8 → UInt8 → Bool)
    (codeunit : Bool → S → Index → StringResult UInt8) (s : S) (i : I) : StringResult Index := do
  thisindStr ncodeunits betweenI betweenByte codeunit s (← toInt i)

/--
Julia source: base/strings/stringview.jl:117-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds thisind(s::StringViewAndSub, i::Int) = _thisind_str(s, i)
```
-/
def thisindStringView {S : Type} (ncodeunits : S → Index)
    (betweenI : Index → Index → Index → Bool) (betweenByte : UInt8 → UInt8 → UInt8 → Bool)
    (codeunit : Bool → S → Index → StringResult UInt8) (s : S) (i : Index) : StringResult Index :=
  thisindStr ncodeunits betweenI betweenByte codeunit s i

/--
Julia source: base/strings/stringview.jl:119-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds nextind(s::StringViewAndSub, i::Integer) = _nextind_str(s, Int(i)::Int)
```
-/
def nextindStringViewInteger {S I : Type} (toInt : I → StringResult Index)
    (ncodeunits : S → Index) (betweenI : Index → Index → Index → Bool)
    (betweenByte : UInt8 → UInt8 → UInt8 → Bool)
    (codeunit : Bool → S → Index → StringResult UInt8) (s : S) (i : I) : StringResult Index := do
  nextindStr ncodeunits betweenI betweenByte codeunit s (← toInt i)

/--
Julia source: base/strings/stringview.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds nextind(s::StringViewAndSub, i::Int) = _nextind_str(s, i)
```
-/
def nextindStringView {S : Type} (ncodeunits : S → Index)
    (betweenI : Index → Index → Index → Bool) (betweenByte : UInt8 → UInt8 → UInt8 → Bool)
    (codeunit : Bool → S → Index → StringResult UInt8) (s : S) (i : Index) : StringResult Index :=
  nextindStr ncodeunits betweenI betweenByte codeunit s i

/--
Julia source: base/strings/stringview.jl:122-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isvalid(s::StringViewAndSub, i::Int) = checkbounds(Bool, s, i) && thisind(s, i) == i
```
-/
def isvalidStringViewAt {S : Type} (checkboundsBool : S → Index → StringResult Bool)
    (thisind : S → Index → StringResult Index) (s : S) (i : Index) : StringResult Bool := do
  if !(← checkboundsBool s i) then return false
  return (← thisind s i).val == i.val

end JuliaLean.base.strings.stringview


/-! Models for `base/strings/stringview.jl` at Julia `bbfa0ce4150`. -/

namespace JuliaLean.Strings

/-- `reverse(s::UTF8String)`, `base/strings/stringview.jl:67-83`: read chars
forwards and store each one ending at the current offset. -/
def reverse (s : JStr) : JStr :=
  let n := s.bytes.length
  let step : List UInt8 × Int → UInt32 → List UInt8 × Int := fun (buf, offs) c =>
    let offs := offs - ncodeunitsChar c
    (writeAt buf (offs - 1).toNat (charBytes c), offs)
  let out := ((chars s).foldl step (List.replicate n 0, n + 1)).1
  if h : out.length < 2 ^ 62 then ⟨out, h⟩ else JStr.empty

end JuliaLean.Strings

namespace JuliaLean.StringsCovA.StringView

structure View where
  bytes : List UInt8
  address : Nat := 0
  deriving DecidableEq

structure SubView where
  parent : View
  offset : Nat
  ncodeunits : Nat
  deriving DecidableEq

/-- `StringView(v)`; `base/strings/stringview.jl:8`. -/
def ctor (v : List UInt8) (address : Nat := 0) : View := ⟨v, address⟩

/-- `Vector{UInt8}(s)` and `Array{UInt8}(s)`; `base/strings/stringview.jl:9-10`. -/
def toVector (s : View) : List UInt8 := s.bytes
def toArray (s : View) : List UInt8 := toVector s

/-- Both `String` conversion methods; `base/strings/stringview.jl:11,26`. -/
def toString (s : View) : List UInt8 := s.bytes

/-- `copy(s::StringView)`; `base/strings/stringview.jl:12`. -/
def copy (s : View) : View := ⟨s.bytes, s.address⟩

/-- `Symbol(s::DenseStringViewAndSub)`; `base/strings/stringview.jl:14-16`. -/
def toSymbol (intern : List UInt8 → Nat) (s : View) : Nat := intern s.bytes

/-- Pointer methods; `base/strings/stringview.jl:18-21`. -/
def pointer (s : View) : Nat := s.address
def pointerAt (s : View) (i : Int) : Int := s.address + i - 1
def subPointer (s : SubView) : Nat := s.parent.address + s.offset
def subPointerAt (s : SubView) (i : Int) : Int := s.parent.address + s.offset + i - 1

/-- `unsafe_convert` methods; `base/strings/stringview.jl:23-24`. -/
def unsafeConvertU8 (s : View) : Nat := pointer s
def unsafeConvertI8 (s : View) : Nat := pointer s

/-- `cconvert` methods; `base/strings/stringview.jl:28-29`. -/
def cconvertU8 (s : View) : View := s
def cconvertI8 (s : View) : View := s

/-- `sizeof` and `ncodeunits`; `base/strings/stringview.jl:85-86`. -/
def sizeof (s : View) : Nat := s.bytes.length
def ncodeunits (s : View) : Nat := s.bytes.length

/-- `codeunit(::StringView)` and indexed `codeunit`; `base/strings/stringview.jl:87-88`. -/
def codeunitType (_s : View) : Nat := 8
def codeunit (s : View) (i : Int) : Jl UInt8 :=
  if 1 ≤ i ∧ i ≤ s.bytes.length then .ok (s.bytes.getD (i.toNat - 1) 0)
  else .error .boundsError

/-- `codeunits` for a view and subview; `base/strings/stringview.jl:89-90`. -/
def codeunits (s : View) : List UInt8 := s.bytes
def subCodeunits (s : SubView) : List UInt8 := (s.parent.bytes.drop s.offset).take s.ncodeunits

/-- UTF-8 `cmp` and `==` operate on code units; `base/strings/stringview.jl:94-95`. -/
def cmp (cmpBytes : List UInt8 → List UInt8 → Int) (a b : View) : Int := cmpBytes a.bytes b.bytes
def eq (a b : View) : Bool := a.bytes == b.bytes

inductive BackingKind where
  | codeUnits | vector | subarray
  deriving DecidableEq

/-- Whether the backing type supports the source's `V()` expression. -/
def emptyBacking : BackingKind → Jl (List UInt8)
  | .codeUnits | .vector => .ok []
  | .subarray => .error (.methodError "SubArray()")

/-- `typemin(::Type{StringView{CodeUnits{UInt8,String}}})`; line 98. -/
def typeminCodeUnits : View := ⟨[], 0⟩

/-- Generic `typemin(::Type{StringView{V}})`; line 99. -/
def typeminType (kind : BackingKind) : Jl View := do
  let bytes ← emptyBacking kind
  .ok ⟨bytes, 0⟩

/-- Value `typemin`, `one`, and `oneunit`; lines 100-102. -/
def typeminValue (kind : BackingKind) : Jl View := typeminType kind
def one (kind : BackingKind) : Jl View := typeminType kind
def oneunit (kind : BackingKind) : Jl View := typeminType kind

/-- `isascii(s)`; `base/strings/stringview.jl:105`. -/
def isascii (s : View) : Bool := s.bytes.all (· < 0x80)

/-- `hash`; `base/strings/stringview.jl:108-110`. -/
def hash (hashBytes : List UInt8 → UInt64 → UInt64) (s : View) (h : UInt64) : UInt64 :=
  hashBytes s.bytes h

/-- `write` and `print`; `base/strings/stringview.jl:113-114`. -/
def write (emit : List UInt8 → Nat) (s : View) : Nat := emit s.bytes
def print (emit : List UInt8 → Nat) (s : View) : Unit := let _ := write emit s; ()

/-- `thisind` and `nextind` forward to the UTF-8 helpers; lines 116-120. -/
def thisind (f : List UInt8 → Int → Jl Int) (s : View) (i : Int) := f s.bytes i
def nextind (f : List UInt8 → Int → Jl Int) (s : View) (i : Int) := f s.bytes i

/-- `isvalid`; `base/strings/stringview.jl:122`. -/
def isvalid (this : List UInt8 → Int → Int) (s : View) (i : Int) : Bool :=
  decide (1 ≤ i ∧ i ≤ s.bytes.length) && decide (this s.bytes i = i)

/-- `getindex(s::StringView, r::UnitRange{Int})`; lines 126-137. -/
def getindexRange (valid : List UInt8 → Int → Bool) (next : List UInt8 → Int → Int)
    (s : View) (i j : Int) : Jl View :=
  if j < i then .ok ⟨[], s.address⟩
  else if !(1 ≤ i ∧ j ≤ s.bytes.length) then .error .boundsError
  else if !valid s.bytes i || !valid s.bytes j then .error (.argumentError "StringIndexError")
  else
    let stop := next s.bytes j - 1
    .ok ⟨(s.bytes.drop (i.toNat - 1)).take (stop - i + 1).toNat, s.address + i.toNat - 1⟩

/-- `chomp`; `base/strings/stringview.jl:139-151`. -/
def chomp (s : View) : View :=
  let bytes := match s.bytes.reverse with
    | 0x0a :: 0x0d :: rest => rest.reverse
    | 0x0a :: rest => rest.reverse
    | _ => s.bytes
  ⟨bytes, s.address⟩

/-- `replace(io, s, pairs...; count)`; `base/strings/stringview.jl:153-155`. -/
def replace {α : Type} (replaceImpl : View → List α → Int → α)
    (s : View) (pairs : List α) (count : Int) : α := replaceImpl s pairs count

end JuliaLean.StringsCovA.StringView


namespace JuliaLean.StringsCovA.StringViewFaithful

open JuliaLean
open JuliaLean.StringsCovA.StringView

abbrev Bytes := List UInt8

def ctor (typedCtor : Bytes → View) (v : Bytes) := typedCtor v

def toVector (codeunits : View → Bytes) (s : View) := codeunits s

def toArray (toVec : View → Bytes) (s : View) := toVec s

def toStringGeneric (ncodeunits : View → Nat) (codeunits : View → Bytes)
    (stringVector : Nat → Bytes) (copyto : Bytes → Bytes → Bytes) (stringCtor : Bytes → Bytes)
    (s : View) : Bytes :=
  let out := stringVector (ncodeunits s)
  stringCtor (copyto out (codeunits s))

def copyView (copyData : Bytes → Bytes) (s : View) : View := ⟨copyData s.bytes, s.address⟩

def symbol (ccall : Nat → Nat → Nat) (s : View) (ncodeunits : View → Nat) := ccall s.address (ncodeunits s)

def pointer (s : View) : Nat := s.address

def pointerAt (s : View) (i : Int) : Int := s.address + i - 1

def subPointer (s : SubView) : Nat := s.parent.address + s.offset

def subPointerAt (s : SubView) (i : Int) : Int := s.parent.address + s.offset + i - 1

def unsafeConvertU8 (s : View) := pointer s

def unsafeConvertI8 (convert : Nat → Nat) (s : View) := convert (pointer s)

def toStringDense (unsafeString : Nat → Nat → Bytes) (ncodeunits : View → Nat) (s : View) :=
  unsafeString (pointer s) (ncodeunits s)

def cconvertU8 (s : View) := s

def cconvertI8 (s : View) := s

def sizeof (s : View) : Nat := s.bytes.length

def ncodeunits (s : View) : Nat := s.bytes.length

def codeunitType (_s : View) : Nat := 8

def codeunit (s : View) (i : Int) : Jl UInt8 :=
  if 1 ≤ i ∧ i ≤ s.bytes.length then .ok (s.bytes.getD (i.toNat - 1) 0) else .error .boundsError

def codeunits (s : View) : Bytes := s.bytes

def subCodeunits (s : SubView) : Bytes := (s.parent.bytes.drop s.offset).take s.ncodeunits

def cmp (cmpBytes : Bytes → Bytes → Int) (a b : View) := cmpBytes (codeunits a) (codeunits b)

def eq (a b : View) : Bool := codeunits a == codeunits b

def typeminCodeunits : View := ⟨[], 0⟩

def typeminType (kind : BackingKind) : Jl View := StringView.typeminType kind

def typeminValue (typeminType : BackingKind → Jl View) (kind : BackingKind) := typeminType kind

def one (typeminType : BackingKind → Jl View) (kind : BackingKind) := typeminType kind

def oneunit (typeminType : BackingKind → Jl View) (kind : BackingKind) := typeminType kind

def isascii (codeunits : View → Bytes) (asciiBytes : Bytes → Bool) (s : View) := asciiBytes (codeunits s)

def hash (hashBytes : Nat → Nat → UInt64 → UInt64 → UInt64) (s : View) (h secret : UInt64) :=
  hashBytes s.address s.bytes.length h secret

def write (writeBytes : Bytes → Nat) (s : View) := writeBytes (codeunits s)

def print (writeView : View → Nat) (s : View) : Unit := let _ := writeView s; ()

def thisindInteger (helper : View → Int → Jl Int) (s : View) (i : Int) := helper s i

def thisindInt (helper : View → Int → Jl Int) (s : View) (i : Int) := helper s i

def nextindInteger (helper : View → Int → Jl Int) (s : View) (i : Int) := helper s i

def nextindInt (helper : View → Int → Jl Int) (s : View) (i : Int) := helper s i

def isvalid (checkbounds : View → Int → Bool) (thisind : View → Int → Int) (s : View) (i : Int) :=
  checkbounds s i && thisind s i == i

def getindexRange (valid : Bytes → Int → Bool) (next : Bytes → Int → Int)
    (s : View) (i j : Int) : Jl View :=
  if j < i then .ok ⟨[], s.address⟩
  else if !(1 ≤ i ∧ j ≤ s.bytes.length) then .error .boundsError
  else if !valid s.bytes i || !valid s.bytes j then .error (.argumentError "StringIndexError")
  else
    let stop := next s.bytes j - 1
    .ok ⟨(s.bytes.drop (i.toNat - 1)).take (stop - i + 1).toNat, s.address + i.toNat - 1⟩

def chomp (s : View) : View :=
  let ncu := s.bytes.length
  let len := if ncu = 0 then 0 else
    let hasLf := s.bytes.getD (ncu - 1) 0 == 0x0a
    let twoBytes := ncu > 1
    let hasCr := hasLf && twoBytes && s.bytes.getD (ncu - (if twoBytes then 1 else 0) - 1) 0 == 0x0d
    ncu - (if hasLf then 1 else 0) - (if hasCr then 1 else 0)
  ⟨s.bytes.take len, s.address⟩

def replace (replaceImpl : View → List α → Int → β) (s : View) (pairs : List α) (count : Int) :=
  replaceImpl s pairs count

end JuliaLean.StringsCovA.StringViewFaithful


namespace JuliaLean.StringsCovA.StringViewRebuilt

open JuliaLean JuliaLean.Strings

structure Storage where
  identity : Nat
  bytes : List UInt8
  deriving DecidableEq

structure View where
  storage : Storage
  start : Nat := 0
  count : Nat := storage.bytes.length
  valid : start + count ≤ storage.bytes.length

def View.bytes (view : View) : List UInt8 := (view.storage.bytes.drop view.start).take view.count

def stringView (storage : Storage) : View := ⟨storage, 0, storage.bytes.length, by omega⟩

def vectorUInt8 (view : View) : List UInt8 := view.bytes

def arrayUInt8 (view : View) : List UInt8 := vectorUInt8 view

def stringCopy (view : View) (allocate : Nat → SJl Storage)
    (copy : Storage → List UInt8 → SJl Storage) : SJl JStr := do
  let output ← allocate view.count
  let output ← copy output view.bytes
  if h : output.bytes.length < 2 ^ 62 then .ok ⟨output.bytes, h⟩ else .error .outOfMemory

def copyView (view : View) (copyData : Storage → Storage) : View := stringView (copyData view.storage)

def symbolView (view : View) (intern : List UInt8 → Nat → SJl Sym) : SJl Sym :=
  intern view.bytes view.count

structure Pointer where address : Nat deriving DecidableEq
def pointerView (view : View) : Pointer := ⟨view.storage.identity + view.start⟩
def pointerViewAt (view : View) (index : I) (pointerData : Storage → I → SJl Pointer) : SJl Pointer :=
  pointerData view.storage index

def pointerSub (parent : View) (offset : JInt64) : Pointer :=
  ⟨(pointerView parent).address + offset.val.toNat⟩

def pointerSubAt (parent : View) (offset : JInt64) (indexMinusOne : SJl Int) : SJl Pointer := do
  let delta ← indexMinusOne
  return ⟨(pointerView parent).address + offset.val.toNat + delta.toNat⟩

def unsafeConvertInt8 (pointer : SJl Pointer) (convert : Pointer → SJl Pointer) : SJl Pointer := do
  let source ← pointer
  convert source

def denseString (view : View) : SJl JStr :=
  if h : view.bytes.length < 2 ^ 62 then .ok ⟨view.bytes, h⟩ else .error .outOfMemory

def reverseUtf8 (s : JStr) : JStr := Strings.reverse s

inductive CodeunitType where | uint8 deriving DecidableEq
def codeunitType : CodeunitType := .uint8

def codeunitAt (view : View) (index : I) (getindex : Storage → I → SJl UInt8) : SJl UInt8 :=
  getindex view.storage index

def codeunits (view : View) : View := view

def codeunitsSub (parent : View) (offset count : Nat) : Storage × Nat × Nat :=
  (parent.storage, parent.start + offset, count)

def lexBytes : List UInt8 → List UInt8 → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs => if a = b then lexBytes as bs else if a < b then -1 else 1
def cmpView (a b : View) : Int := lexBytes a.bytes b.bytes

def eqView (a b : View) : Bool := a.bytes == b.bytes

structure BackingType (V : Type) where empty : SJl V
def typeminView (backing : BackingType V) : SJl V := backing.empty

def typeminValue (typeMin : SJl V) : SJl V := typeMin
def oneView (typeMin : SJl V) : SJl V := typeMin
def oneunitView (typeMin : SJl V) : SJl V := typeMin

def isasciiView (view : View) : Bool := view.bytes.all (fun byte => byte < 0x80)

structure HashInput where
  view : View
  seed : UInt64
  secret : UInt64
  hashBytes : Pointer → Nat → UInt64 → UInt64 → SJl UInt64
  toUInt : UInt64 → UInt64
def hashView (input : HashInput) : SJl UInt64 := do
  let hash ← input.hashBytes (pointerView input.view) input.view.count input.seed input.secret
  return input.toUInt hash

def writeView (io : IOType) (view : View) (write : IOType → View → SJl JInt64) : SJl JInt64 :=
  write io view

def printView (io : IOType) (view : View) (write : IOType → View → SJl JInt64) : SJl Unit := do
  let _ ← write io view
  return ()

structure IntegerInput (I : Type) where
  value : I
  toInt : SJl JInt64
def thisindInteger (view : View) (index : IntegerInput I) : SJl JInt64 := do
  let converted ← index.toInt
  if h : view.bytes.length < 2 ^ 62 then Strings.thisind ⟨view.bytes, h⟩ converted else .error .outOfMemory

def thisindInt (view : View) (index : JInt64) : SJl JInt64 :=
  if h : view.bytes.length < 2 ^ 62 then Strings.thisind ⟨view.bytes, h⟩ index else .error .outOfMemory

def nextindInteger (view : View) (index : IntegerInput I) : SJl JInt64 := do
  let converted ← index.toInt
  if h : view.bytes.length < 2 ^ 62 then Strings.nextind ⟨view.bytes, h⟩ converted else .error .outOfMemory

def nextindInt (view : View) (index : JInt64) : SJl JInt64 :=
  if h : view.bytes.length < 2 ^ 62 then Strings.nextind ⟨view.bytes, h⟩ index else .error .outOfMemory

def isvalidView (view : View) (index : JInt64) : Bool :=
  decide (1 ≤ index.val ∧ index.val ≤ view.bytes.length) &&
    match thisindInt view index with | .ok actual => actual.val == index.val | .error _ => false

structure RangeInput where
  first : JInt64
  last : JInt64
  empty : Bool
def getindexRange (view : View) (range : RangeInput) : SJl (Storage × Nat × Nat) :=
  if range.empty then .ok (view.storage, view.start, 0)
  else if !(1 ≤ range.first.val ∧ range.last.val ≤ view.count) then .error boundsErr
  else if !isvalidView view range.first then .error (.stringIndexError range.first.val)
  else if !isvalidView view range.last then .error (.stringIndexError range.last.val)
  else do
    let after ← nextindInt view range.last
    let count := (after - range.first).val.toNat
    if h : range.first.val.toNat - 1 + count ≤ view.count then
      .ok (view.storage, view.start + range.first.val.toNat - 1, count)
    else .error boundsErr

def chompLength (view : View) : Nat :=
  let count := view.bytes.length
  let hasLf := count > 0 && view.bytes.getD (count - 1) 0 = 0x0a
  let hasCr := hasLf && count > 1 && view.bytes.getD (count - 2) 0 = 0x0d
  count - (if hasLf then 1 else 0) - (if hasCr then 1 else 0)
def chompView (view : View) : List UInt8 := view.bytes.take (chompLength view)

def replaceView (io : IOType) (view : View) (pairs : Pairs) (count : IntegerInput I)
    (replace : IOType → View → Pairs → JInt64 → SJl R) : SJl R := do
  let converted ← count.toInt
  replace io view pairs converted

end JuliaLean.StringsCovA.StringViewRebuilt
