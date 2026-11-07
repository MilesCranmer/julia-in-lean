import JuliaLean.base.char
import JuliaLean.base.expr
import JuliaLean.Core
import JuliaLean.base.pointer
import JuliaLean.Runtime.Strings


section

/-!
# The TOML lexer with comment capture (`base/toml/parser.jl`)

Model, at master `bbfa0ce4150`, of the parser state and the character-level utilities of
`base/toml/parser.jl` including line/column bookkeeping and comment capture
(`comments !== nothing`), which `JuliaLean.Toml` leaves out; the comment containers
`CommentBlock` and `Comments`; the `Parser` constructors, `startup` and `reinit!`; the
`@try` macro; and `ParserError` with its formatting (`format_error_message_for_err_type`,
`point_to_line`, `showerror`).

Strings are their bytes and characters their raw `UInt32` values, as in `JuliaLean.Toml`
(`Toml.iterate` decodes UTF-8 as `base/strings/string.jl`). The parsed document, needed by
`path_traverses_array`, is a tree of tables, arrays and leaves. Every `while` loop consumes
one unit of fuel per iteration (each iteration eats at least one byte).
-/

namespace JuliaLean.DocsSyntaxCov.TomlLex

open JuliaLean JuliaLean.DocsSyntaxCov

/-- `thisind(s::String, i)`, `base/strings/string.jl`. -/
def thisind (s : List Nat) (i : Int) : DJ Int :=
  let n : Int := s.length
  let cu (j : Int) : Nat := s.getD (j - 1).toNat 0
  let cont (b : Nat) : Bool := b / 64 == 2
  if i == 0 then pure 0
  else if i == n + 1 then pure i
  else if !(1 ≤ i && i ≤ n) then .error .boundsError
  else if !(cont (cu i) && i - 1 > 0) then pure i
  else if 0xc0 ≤ cu (i - 1) && cu (i - 1) ≤ 0xf7 then pure (i - 1)
  else if !(cont (cu (i - 1)) && i - 2 > 0) then pure i
  else if 0xe0 ≤ cu (i - 2) && cu (i - 2) ≤ 0xf7 then pure (i - 2)
  else if !(cont (cu (i - 2)) && i - 3 > 0) then pure i
  else if 0xf0 ≤ cu (i - 3) && cu (i - 3) ≤ 0xf7 then pure (i - 3)
  else pure i

end JuliaLean.DocsSyntaxCov.TomlLex

end


open JuliaLean

/-!
# Model of `base/strings/string.jl`

Julia's dispatch is represented by typed overload-specific definitions. String bytes use the
existing `JStr` representation; operations supplied by other Base files or the runtime remain
explicit typed parameters.
-/

namespace JuliaLean.base.strings.string

abbrev JString := JuliaLean.Strings.JStr
abbrev StringError := JuliaLean.Strings.SErr
abbrev StringResult (α : Type) := JuliaLean.Strings.SJl α
abbrev Index := JuliaLean.JInt64

class StringNullPointer (P : Type) where
  isNull : P → P → Bool

instance : StringNullPointer Int where
  isNull null pointer := pointer == null

instance {T : Type} : StringNullPointer (JuliaLean.base.pointer.Ptr T) where
  isNull null pointer := pointer.address.val == null.address.val

inductive CStringOutcome (α : Type) where
  | success (bytes : α)
  | juliaError (error : StringError)
  | undefinedMemory
  deriving DecidableEq, Repr
def CStringOutcome.ofStringResult {α : Type} : StringResult α → CStringOutcome α
  | .ok bytes => .success bytes
  | .error error => .juliaError error

class StringNulCall (P : Type) where
  Call : Type
  Result : Type
  lift : Call → Result
  nullError : Result

instance : StringNulCall Int where
  Call := JString
  Result := StringResult JString
  lift := .ok
  nullError := .error (.jl (.argumentError "cannot convert NULL to string"))

instance : StringNulCall (JuliaLean.base.pointer.Ptr (JInt .u8)) where
  Call := CStringOutcome (List UInt8)
  Result := CStringOutcome (List UInt8)
  lift := id
  nullError := .juliaError (.jl (.argumentError "cannot convert NULL to string"))

instance : StringNulCall (JuliaLean.base.pointer.Ptr (JInt .i8)) where
  Call := CStringOutcome (List UInt8)
  Result := CStringOutcome (List UInt8)
  lift := id
  nullError := .juliaError (.jl (.argumentError "cannot convert NULL to string"))

/-- A successful `strlen` result contains the readable prefix through its first NUL byte. -/
structure CStringPrefix (heap : JuliaLean.base.pointer.ByteHeap)
    (pointer : JuliaLean.base.pointer.Ptr (JInt .u8)) where
  length : Nat
  length_lt_size_t : length < 2 ^ 64
  readable : heap.validRange pointer.address.val.toNat (length + 1)
  noEarlierNul : ∀ offset, offset < length →
    (heap.readByte (pointer.address.val.toNat + offset)).val.toNat ≠ 0
  nul : (heap.readByte (pointer.address.val.toNat + length)).val.toNat = 0

/-- The libc `strlen` boundary: it returns the first-NUL length for readable memory;
invalid C reads have undefined behavior, represented separately from Julia errors. -/
inductive CStringScanResult (heap : JuliaLean.base.pointer.ByteHeap)
    (pointer : JuliaLean.base.pointer.Ptr (JInt .u8)) where
  | terminated (region : CStringPrefix heap pointer)
  | undefinedMemory

inductive StringAllocationOutcome where
  | allocated
  | outOfMemory
  deriving DecidableEq, Repr
/-- Runtime boundaries used by `jl_cstr_to_string`. `strlen` returns the exact
first-NUL length only for a readable region, and is defined for every such
region. `allocateString` models `jl_gc_alloc` after the exact size check. -/
structure StringPointerPrimitive where
  heap : JuliaLean.base.pointer.ByteHeap
  strlen : (pointer : JuliaLean.base.pointer.Ptr (JInt .u8)) →
    CStringScanResult heap pointer
  strlen_complete : ∀ pointer (region : CStringPrefix heap pointer),
    ∃ result, strlen pointer = .terminated result ∧ result.length = region.length
  allocateString : Nat → StringAllocationOutcome

/-- On 64-bit Julia, `jl_alloc_string` checks `sizeof(size_t) + len + 1` for
unsigned overflow before calling `jl_gc_alloc` (`src/array.c:283-297`). -/
def jlAllocString (allocateString : Nat → StringAllocationOutcome) (len : Nat)
    (_length_lt_size_t : len < 2 ^ 64) : StringResult Unit :=
  if len == 0 then .ok ()
  else if 2 ^ 64 - 10 < len then .error .outOfMemory
  else
    match allocateString len with
    | .allocated => .ok ()
    | .outOfMemory => .error .outOfMemory

/-- `jl_pchar_to_string` allocates `len` bytes, then copies exactly that readable
prefix from the source heap (`src/array.c:300-305`). -/
def jlPcharToString (ops : StringPointerPrimitive)
    (pointer : JuliaLean.base.pointer.Ptr (JInt .u8))
    (region : CStringPrefix ops.heap pointer) : StringResult (List UInt8) := do
  jlAllocString ops.allocateString region.length region.length_lt_size_t
  pure ((ops.heap.readBytes pointer.address.val.toNat region.length).map
    (fun byte => UInt8.ofNat byte.val.toNat))

/-- `jl_cstr_to_string` obtains the `strlen` result, then calls
`jl_pchar_to_string` with that length (`src/array.c:308-310`). -/
def StringPointerPrimitive.jlCstrToString (ops : StringPointerPrimitive)
    (pointer : JuliaLean.base.pointer.Ptr (JInt .u8)) : CStringOutcome (List UInt8) :=
  match ops.strlen pointer with
  | .terminated region => CStringOutcome.ofStringResult (jlPcharToString ops pointer region)
  | .undefinedMemory => .undefinedMemory


structure StringView (α : Type) where
  data : α
  deriving Repr

structure Memory where
  pointer : Int
  length : Nat
  empty : Bool
  bytes : List UInt8
  deriving Repr

structure VectorRef where
  ptrOrOffset : Int
  mem : Memory
  deriving Repr

structure ByteVector where
  length : Nat
  ref : VectorRef
  bytes : List UInt8
  deriving Repr
structure StringVectorResult where
  string : JString
  vector : ByteVector
  sharedStorage : Option Memory
  deriving Repr

/-! ## Construction and storage -/

/--
Julia source: base/strings/string.jl:35-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function StringView{T}(data::T) where {T <: AbstractVector{UInt8}}
        # For now, StringViews code assumes one-based indexing
        require_one_based_indexing(data)

        # Prevent someone constructing e.g. a `StringView{AbstractVector{UInt8}}`,
        # the existence of which will complicate the implementation and provide
        # no usability benefit.
        if !isconcretetype(T)
            throw(ArgumentError("StringView must be parameterized with a concrete type"))
        end

        new{T}(data)
    end
```
-/
def stringViewCtor {α : Type} (requireOneBased : α → StringResult Unit)
    (concreteType : Bool) (data : α) : StringResult (StringView α) := do
  let _ ← requireOneBased data
  if !concreteType then
    .error (.jl (.argumentError "StringView must be parameterized with a concrete type"))
  else
    pure ⟨data⟩

/--
Julia source: base/strings/string.jl:60-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline string_index_err((@nospecialize s::AbstractString), i::Integer) =
    throw(StringIndexError(s, Int(i)))
```
-/
def stringIndexErr {α I : Type} (toInt : I → Index) (_s : α) (i : I) : StringResult Unit :=
  .error (.stringIndexError (toInt i).val)

/--
Julia source: base/strings/string.jl:62-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, exc::StringIndexError)
    s = exc.string
    print(io, "StringIndexError: ", "invalid index [$(exc.index)]")
    if firstindex(s) <= exc.index <= ncodeunits(s)
        iprev = thisind(s, exc.index)
        inext = nextind(s, iprev)
        escprev = escape_string(s[iprev:iprev])
        if inext <= ncodeunits(s)
            escnext = escape_string(s[inext:inext])
            print(io, ", valid nearby indices [$iprev]=>'$escprev', [$inext]=>'$escnext'")
        else
            print(io, ", valid nearby index [$iprev]=>'$escprev'")
        end
    end
end
```
-/
def showStringIndexError {α : Type} (print : List String → List String → List String)
    (firstindex ncodeunits : α → Index) (thisind nextind : α → Index → StringResult Index)
    (getindexRange : α → Index → Index → StringResult JString)
    (escapeString : JString → String) (toString : Index → String)
    (io : List String) (s : α) (index : Index) : StringResult (List String) := do
  let io := print io ["StringIndexError: ", "invalid index [", toString index, "]"]
  if firstindex s ≤ index && index ≤ ncodeunits s then
    let iprev ← thisind s index
    let inext ← nextind s iprev
    let escprev := escapeString (← getindexRange s iprev iprev)
    if inext ≤ ncodeunits s then
      let escnext := escapeString (← getindexRange s inext inext)
      return print io [", valid nearby indices [", toString iprev, "]=>'", escprev, "', [",
        toString inext, "]=>'", escnext, "'"]
    else
      return print io [", valid nearby index [", toString iprev, "]=>'", escprev, "'"]
  else
    return io

/--
Julia source: base/strings/string.jl:78-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline between(b::T, lo::T, hi::T) where {T<:Integer} = (lo ≤ b) & (b ≤ hi)
```
-/
def between {α : Type} (le : α → α → Bool) (b lo hi : α) : Bool := le lo b && le b hi

/--
Julia source: base/strings/string.jl:136-138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_takestring(m::Memory{UInt8})
    isempty(m) ? "" : ccall(:jl_genericmemory_to_string, Ref{String}, (Any, Int), m, length(m))
end
```
-/
def unsafeTakestring (empty : Memory → Bool) (memoryLength : Memory → Nat)
    (memoryToString : Memory → Nat → JString) (m : Memory) : JString :=
  if empty m then JuliaLean.Strings.JStr.empty else memoryToString m (memoryLength m)
/--
Julia source: base/strings/string.jl:112-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
String(v::AbstractVector{UInt8}) = unsafe_takestring(copyto!(StringMemory(length(v)), v))
```
-/
def stringAbstractVector {V : Type} (length : V → Nat) (allocate : Nat → Memory)
    (copyTo : Memory → V → Memory) (empty : Memory → Bool) (memoryLength : Memory → Nat)
    (memoryToString : Memory → Nat → JString) (v : V) : JString :=
  unsafeTakestring empty memoryLength memoryToString (copyTo (allocate (length v)) v)

/--
Julia source: base/strings/string.jl:114-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function String(v::Vector{UInt8})
    len = length(v)
    len == 0 && return ""
    ref = v.ref
    if ref.ptr_or_offset == ref.mem.ptr
        str = ccall(:jl_genericmemory_to_string, Ref{String}, (Any, Int), ref.mem, len)
    else
        str = ccall(:jl_pchar_to_string, Ref{String}, (Ptr{UInt8}, Int), ref, len)
    end
    # optimized empty!(v); sizehint!(v, 0) calls
    setfield!(v, :size, (0,))
    setfield!(v, :ref, memoryref(Memory{UInt8}()))
    return str
end
```
-/
def stringVector (genericMemoryToString : Memory → Nat → JString)
    (pointerToString : VectorRef → Nat → JString) (emptyMemoryRef : VectorRef)
    (v : ByteVector) : StringVectorResult := Id.run do
  let len := v.length
  if len == 0 then
    return ⟨JuliaLean.Strings.JStr.empty, v, none⟩
  let ref := v.ref
  let (str, sharedStorage) := if ref.ptrOrOffset == ref.mem.pointer then
      (genericMemoryToString ref.mem len, some ref.mem)
    else
      (pointerToString ref len, none)
  let v := { v with length := 0 }
  let v := { v with ref := emptyMemoryRef }
  return ⟨str, v, sharedStorage⟩



/--
Julia source: base/strings/string.jl:159-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
takestring!(v::Vector{UInt8}) = String(v)
```
-/
def takeString (genericMemoryToString : Memory → Nat → JString)
    (pointerToString : VectorRef → Nat → JString) (emptyMemoryRef : VectorRef)
    (v : ByteVector) : StringVectorResult :=
  stringVector genericMemoryToString pointerToString emptyMemoryRef v

/--
Julia source: base/strings/string.jl:172-175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_string(p::Union{Ptr{UInt8},Ptr{Int8}}, len::Integer)
    p == C_NULL && throw(ArgumentError("cannot convert NULL to string"))
    ccall(:jl_pchar_to_string, Ref{String}, (Ptr{UInt8}, Int), p, len)
end
```
-/
def unsafeStringLength {I : Type} (toInt : I → Index) (null : Int)
    (pointerToString : Int → Index → JString) (p : Int) (len : I) : StringResult JString :=
  if p == null then .error (.jl (.argumentError "cannot convert NULL to string"))
  else .ok (pointerToString p (toInt len))

/--
Julia source: base/strings/string.jl:176-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_string(p::Union{Ptr{UInt8},Ptr{Int8}})
    p == C_NULL && throw(ArgumentError("cannot convert NULL to string"))
    ccall(:jl_cstr_to_string, Ref{String}, (Ptr{UInt8},), p)
end
```
-/
def unsafeStringNul {P : Type} [StringNullPointer P] [StringNulCall P]
    (null : P) (pointerToCString : P → StringNulCall.Call P) (p : P) :
    StringNulCall.Result P :=
  if StringNullPointer.isNull null p then StringNulCall.nullError (P := P)
  else StringNulCall.lift (P := P) (pointerToCString p)
/--
Julia source: base/strings/string.jl:184-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval _string_n(n::Integer) = $(Expr(:foreigncall, QuoteNode(:jl_alloc_string), Ref{String},
    :(Core.svec(Csize_t)), 1, QuoteNode((:ccall, _string_n_override, false)), :(convert(Csize_t, n))))
```
-/
def stringN {m : Type → Type} [Monad m] {I CSize S : Type} (toCsize : I → m CSize)
    (allocateString : CSize → m S) (n : I) : m S := do
  let size ← toCsize n
  allocateString size

/--
Julia source: base/strings/string.jl:192-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
String(s::AbstractString) = print_to_string(s)
```
-/
def stringAbstractString {α : Type} (printToString : α → JString) (s : α) : JString :=
  printToString s

/--
Julia source: base/strings/string.jl:193-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :total String(s::Symbol) = unsafe_string(unsafe_convert(Ptr{UInt8}, s))
```
-/
def stringSymbol {α P : Type} [StringNullPointer P] [StringNulCall P]
    (unsafeConvert : α → P) (null : P)
    (pointerToCString : P → StringNulCall.Call P) (s : α) :
    StringNulCall.Result P :=
  unsafeStringNul null pointerToCString (unsafeConvert s)

/--
Julia source: base/strings/string.jl:195-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_wrap(::Type{Memory{UInt8}}, s::String) = ccall(:jl_string_to_genericmemory, Ref{Memory{UInt8}}, (Any,), s)
```
-/
def unsafeWrapMemory {S Memory : Type} (stringToMemory : S → Memory) (s : S) : Memory :=
  stringToMemory s

/--
Julia source: base/strings/string.jl:196-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_wrap(::Type{Vector{UInt8}}, s::String) = wrap(Array, unsafe_wrap(Memory{UInt8}, s))
```
-/
def unsafeWrapVector (stringToMemory : JString → Memory) (wrapArray : Memory → ByteVector)
    (s : JString) : ByteVector :=
  wrapArray (unsafeWrapMemory stringToMemory s)

/--
Julia source: base/strings/string.jl:198-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Vector{UInt8}(s::CodeUnits{UInt8,String}) = copyto!(Vector{UInt8}(undef, length(s)), s)
```
-/
def vectorCodeUnits {C : Type} (length : C → Nat) (allocate : Nat → ByteVector)
    (copyTo : ByteVector → C → ByteVector) (s : C) : ByteVector :=
  copyTo (allocate (length s)) s

/--
Julia source: base/strings/string.jl:199-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Vector{UInt8}(s::String) = Vector{UInt8}(codeunits(s))
```
-/
def vectorString (codeunits : JString → List UInt8) (length : List UInt8 → Nat)
    (allocate : Nat → ByteVector) (copyTo : ByteVector → List UInt8 → ByteVector)
    (s : JString) : ByteVector :=
  vectorCodeUnits length allocate copyTo (codeunits s)

/--
Julia source: base/strings/string.jl:200-200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Array{UInt8}(s::String)  = Vector{UInt8}(codeunits(s))
```
-/
def arrayString (vectorString : JString → ByteVector) (s : JString) : ByteVector :=
  vectorString s

/--
Julia source: base/strings/string.jl:202-202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
String(s::CodeUnits{UInt8,String}) = s.s
```
-/
def stringCodeUnits {C : Type} (parent : C → JString) (s : C) : JString := parent s

/--
Julia source: base/strings/string.jl:206-206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pointer(s::String) = unsafe_convert(Ptr{UInt8}, s)
```
-/
def pointerString (unsafeConvert : JString → Int) (s : JString) : Int := unsafeConvert s

/--
Julia source: base/strings/string.jl:207-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pointer(s::String, i::Integer) = pointer(s) + Int(i)::Int - 1
```
-/
def pointerAt {I : Type} (unsafeConvertString : JString → Int) (toInt : I → Int)
    (s : JString) (i : I) : Int :=
  pointerString unsafeConvertString s + toInt i - 1

/--
Julia source: base/strings/string.jl:209-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ncodeunits(s::String) = Core.sizeof(s)
```
-/
def ncodeunits (coreSizeof : JString → Index) (s : JString) : Index := coreSizeof s

/--
Julia source: base/strings/string.jl:210-210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
codeunit(s::String) = UInt8
```
-/
def codeunitType : Type := UInt8

/--
Julia source: base/strings/string.jl:213-217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :foldable @inline function codeunit(s::String, i::Int)
    @boundscheck checkbounds(s, i)
    b = GC.@preserve s unsafe_load(pointer(s, i))
    return b
end
```
-/
def codeunitInt (boundsChecking : Bool) (s : JString) (i : Index)
    (checkbounds : JString → Index → StringResult Unit)
    (unsafeConvertString : JString → Int) (preserve : JString → (Unit → UInt8) → UInt8)
    (unsafeLoad : JString → Int → UInt8) : StringResult UInt8 := do
  if boundsChecking then
    let _ ← checkbounds s i
    pure ()
  let b := preserve s (fun _ =>
    unsafeLoad s (pointerAt unsafeConvertString (fun x => x.val) s i))
  pure b
/--
Julia source: base/strings/string.jl:212-212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
codeunit(s::String, i::Integer) = codeunit(s, Int(i)::Int)
```
-/
def codeunitInteger {I : Type} (toInt : I → Index)
    (checkbounds : JString → Index → StringResult Unit)
    (unsafeConvertString : JString → Int) (preserve : JString → (Unit → UInt8) → UInt8)
    (unsafeLoad : JString → Int → UInt8) (s : JString) (i : I) : StringResult UInt8 :=
  codeunitInt true s (toInt i) checkbounds unsafeConvertString preserve unsafeLoad


/-! ## Comparison and UTF-8 indexing -/


/--
Julia source: base/strings/string.jl:224-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _memcmp(a::Union{Ptr{UInt8},AbstractString}, b::Union{Ptr{UInt8},AbstractString}, len::Int)
    GC.@preserve a b begin
        pa = unsafe_convert(Ptr{UInt8}, a)
        pb = unsafe_convert(Ptr{UInt8}, b)
        memcmp(pa, pb, len % Csize_t) % Int
    end
end
```
-/
def memcmpLength {α : Type} (unsafeConvert : α → Int) (toCsize : Index → Nat)
    (preserve : α → α → (Unit → Int) → Int)
    (memcmp : Int → Int → Nat → Int) (a b : α) (len : Index) : Int :=
  preserve a b (fun _ => memcmp (unsafeConvert a) (unsafeConvert b) (toCsize len))
/--
Julia source: base/strings/string.jl:223-223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_memcmp(a::Union{Ptr{UInt8},AbstractString}, b::Union{Ptr{UInt8},AbstractString}) = _memcmp(a, b, min(sizeof(a), sizeof(b)))
```
-/
def memcmpUnion {α : Type} (sizeof : α → Index) (memcmpLength : α → α → Index → Int)
    (a b : α) : Int :=
  memcmpLength a b (if (sizeof a).val ≤ (sizeof b).val then sizeof a else sizeof b)


/--
Julia source: base/strings/string.jl:221-221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :total _memcmp(a::String, b::String) = @invoke _memcmp(a::Union{Ptr{UInt8},AbstractString},b::Union{Ptr{UInt8},AbstractString})
```
-/
def memcmpString (sizeof : JString → Index)
    (memcmpLength : JString → JString → Index → Int) (a b : JString) : Int :=
  memcmpUnion sizeof memcmpLength a b
/--
Julia source: base/strings/string.jl:232-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cmp(a::String, b::String)
    al, bl = sizeof(a), sizeof(b)
    c = _memcmp(a, b)
    return c < 0 ? -1 : c > 0 ? +1 : cmp(al,bl)
end
```
-/
def cmpString (sizeof : JString → Index)
    (memcmpLength : JString → JString → Index → Int)
    (cmpLength : Index → Index → Int) (a b : JString) : Int := Id.run do
  let al := sizeof a
  let bl := sizeof b
  let c := memcmpString sizeof memcmpLength a b
  return if c < 0 then -1 else if c > 0 then 1 else cmpLength al bl

/--
Julia source: base/strings/string.jl:238-238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(a::String, b::String) = a===b
```
-/
def eqString (identical : JString → JString → Bool) (a b : JString) : Bool := identical a b

/--
Julia source: base/strings/string.jl:240-240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemin(::Type{String}) = ""
```
-/
def typeminStringType : JString := JuliaLean.Strings.JStr.empty

/--
Julia source: base/strings/string.jl:241-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemin(::String) = typemin(String)
```
-/
def typeminString (typeminType : JString) (_s : JString) : JString := typeminType

/--
Julia source: base/strings/string.jl:252-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _thisind_str(s, i::Int)
    i == 0 && return 0
    n = ncodeunits(s)
    i == n + 1 && return i
    @boundscheck between(i, 1, n) || throw(BoundsError(s, i))
    @inbounds b = codeunit(s, i)
    (b & 0xc0 == 0x80) & (i-1 > 0) || return i
    (@noinline function _thisind_continued(s, i) # mark the rest of the function as a slow-path
        local b
        @inbounds b = codeunit(s, i-1)
        between(b, 0b11000000, 0b11110111) && return i-1
        (b & 0xc0 == 0x80) & (i-2 > 0) || return i
        @inbounds b = codeunit(s, i-2)
        between(b, 0b11100000, 0b11110111) && return i-2
        (b & 0xc0 == 0x80) & (i-3 > 0) || return i
        @inbounds b = codeunit(s, i-3)
        between(b, 0b11110000, 0b11110111) && return i-3
        return i
    end)(s, i)
end
```
-/
def thisindStr {S : Type} (ncodeunits : S → Index) (betweenI : Index → Index → Index → Bool)
    (betweenByte : UInt8 → UInt8 → UInt8 → Bool)
    (codeunit : Bool → S → Index → StringResult UInt8) (s : S) (i : Index) : StringResult Index := do
  if i.val == 0 then
    return JuliaLean.Strings.ix 0
  let n := ncodeunits s
  if i.val == (n + JuliaLean.Strings.ix 1).val then
    return i
  if !(betweenI i (JuliaLean.Strings.ix 1) n) then
    throw (.jl .boundsError)
  let b ← codeunit false s i
  if !((b &&& 0xc0 == 0x80) && (i - JuliaLean.Strings.ix 1).val > 0) then
    return i
  let mut b ← codeunit false s (i - JuliaLean.Strings.ix 1)
  if betweenByte b 0b11000000 0b11110111 then
    return i - JuliaLean.Strings.ix 1
  if !((b &&& 0xc0 == 0x80) && (i - JuliaLean.Strings.ix 2).val > 0) then
    return i
  b ← codeunit false s (i - JuliaLean.Strings.ix 2)
  if betweenByte b 0b11100000 0b11110111 then
    return i - JuliaLean.Strings.ix 2
  if !((b &&& 0xc0 == 0x80) && (i - JuliaLean.Strings.ix 3).val > 0) then
    return i
  b ← codeunit false s (i - JuliaLean.Strings.ix 3)
  if betweenByte b 0b11110000 0b11110111 then
    return i - JuliaLean.Strings.ix 3
  return i
/--
Julia source: base/strings/string.jl:245-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds thisind(s::String, i::Int) = _thisind_str(s, i)
```
-/
def thisindString {S : Type} (ncodeunits : S → Index)
    (betweenI : Index → Index → Index → Bool) (betweenByte : UInt8 → UInt8 → UInt8 → Bool)
    (codeunit : Bool → S → Index → StringResult UInt8) (s : S) (i : Index) : StringResult Index :=
  thisindStr ncodeunits betweenI betweenByte codeunit s i

/--
Julia source: base/strings/string.jl:249-249 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :nothrow lastindex(s::String) = thisind(s, ncodeunits(s)::Int)
```
-/
def lastindexString (ncodeunits : JString → Index)
    (betweenI : Index → Index → Index → Bool) (betweenByte : UInt8 → UInt8 → UInt8 → Bool)
    (codeunit : Bool → JString → Index → StringResult UInt8) (s : JString) : StringResult Index :=
  thisindString ncodeunits betweenI betweenByte codeunit s (ncodeunits s)


/--
Julia source: base/strings/string.jl:276-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _nextind_str(s, i::Int)
    i == 0 && return 1
    n = ncodeunits(s)
    @boundscheck between(i, 1, n) || throw(BoundsError(s, i))
    @inbounds l = codeunit(s, i)
    between(l, 0x80, 0xf7) || return i+1
    (@noinline function _nextind_continued(s, i, n, l) # mark the rest of the function as a slow-path
        if l < 0xc0
            # handle invalid codeunit index by scanning back to the start of this index
            # (which may be the same as this index)
            i′ = @inbounds thisind(s, i)
            i′ >= i && return i+1
            i = i′
            @inbounds l = codeunit(s, i)
            (l < 0x80) | (0xf8 ≤ l) && return i+1
            @assert l >= 0xc0 "invalid codeunit"
        end
        # first continuation byte
        (i += 1) > n && return i
        @inbounds b = codeunit(s, i)
        b & 0xc0 ≠ 0x80 && return i
        ((i += 1) > n) | (l < 0xe0) && return i
        # second continuation byte
        @inbounds b = codeunit(s, i)
        b & 0xc0 ≠ 0x80 && return i
        ((i += 1) > n) | (l < 0xf0) && return i
        # third continuation byte
        @inbounds b = codeunit(s, i)
        return ifelse(b & 0xc0 ≠ 0x80, i, i+1)
    end)(s, i, n, l)
end
```
-/
def nextindStr {S : Type} (ncodeunits : S → Index)
    (betweenI : Index → Index → Index → Bool) (betweenByte : UInt8 → UInt8 → UInt8 → Bool)
    (codeunit : Bool → S → Index → StringResult UInt8) (s : S) (i : Index) : StringResult Index := do
  if i.val == 0 then
    return JuliaLean.Strings.ix 1
  let n := ncodeunits s
  if !(betweenI i (JuliaLean.Strings.ix 1) n) then
    throw (.jl .boundsError)
  let l ← codeunit false s i
  if !(betweenByte l 0x80 0xf7) then
    return i + JuliaLean.Strings.ix 1
  let state : Sum Index (Index × UInt8) ←
    if l < 0xc0 then do
      let iprev ← thisindString ncodeunits betweenI betweenByte codeunit s i
      if iprev.val ≥ i.val then
        pure (Sum.inl (i + JuliaLean.Strings.ix 1))
      else
        let lead ← codeunit false s iprev
        if lead < 0x80 || 0xf8 ≤ lead then
          pure (Sum.inl (iprev + JuliaLean.Strings.ix 1))
        else if !(lead ≥ 0xc0) then
          throw .assertion
        else
          pure (Sum.inr (iprev, lead))
    else
      pure (Sum.inr (i, l))
  match state with
  | Sum.inl result => return result
  | Sum.inr (i, l) =>
    let mut i := i + JuliaLean.Strings.ix 1
    if i.val > n.val then return i
    let mut b ← codeunit false s i
    if (b &&& 0xc0) != 0x80 then return i
    i := i + JuliaLean.Strings.ix 1
    if i.val > n.val || l < 0xe0 then return i
    b ← codeunit false s i
    if (b &&& 0xc0) != 0x80 then return i
    i := i + JuliaLean.Strings.ix 1
    if i.val > n.val || l < 0xf0 then return i
    b ← codeunit false s i
    return if (b &&& 0xc0) != 0x80 then i else i + JuliaLean.Strings.ix 1
/--
Julia source: base/strings/string.jl:273-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds nextind(s::String, i::Int) = _nextind_str(s, i)
```
-/
def nextindString {S : Type} (ncodeunits : S → Index)
    (betweenI : Index → Index → Index → Bool) (betweenByte : UInt8 → UInt8 → UInt8 → Bool)
    (codeunit : Bool → S → Index → StringResult UInt8) (s : S) (i : Index) : StringResult Index :=
  nextindStr ncodeunits betweenI betweenByte codeunit s i


/-- The transition rows used to build Julia's 12-class UTF-8 DFA table. -/
def utf8DfaShifts : List Nat := [0, 4, 10, 14, 18, 24, 8, 20, 12, 26]

def utf8DfaRows : List (List Nat) := [
  [0, 1, 2, 2, 2, 2, 2, 2, 2, 2],
  [2, 2, 2, 1, 3, 2, 3, 2, 4, 4],
  [3, 3, 2, 2, 2, 2, 2, 2, 2, 2],
  [4, 4, 2, 2, 2, 2, 2, 2, 2, 2],
  [6, 6, 2, 2, 2, 2, 2, 2, 2, 2],
  [9, 9, 2, 2, 2, 2, 2, 2, 2, 2],
  [8, 8, 2, 2, 2, 2, 2, 2, 2, 2],
  [2, 2, 2, 1, 3, 3, 2, 4, 4, 2],
  [2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
  [2, 2, 2, 1, 3, 2, 3, 4, 4, 2],
  [5, 5, 2, 2, 2, 2, 2, 2, 2, 2],
  [7, 7, 2, 2, 2, 2, 2, 2, 2, 2]
]

def utf8DfaClass (byte : UInt8) : Nat :=
  let b := byte.toNat
  if b < 128 then 0
  else if b < 144 then 1
  else if b < 160 then 9
  else if b < 192 then 7
  else if b < 194 then 8
  else if b < 224 then 2
  else if b == 224 then 10
  else if b < 237 then 3
  else if b == 237 then 4
  else if b < 240 then 3
  else if b == 240 then 11
  else if b < 244 then 6
  else if b == 244 then 5
  else 8

def utf8DfaClassRow (classId : Nat) : UInt32 :=
  (List.range 10).foldl (fun row state =>
    let next := (utf8DfaRows.getD classId []).getD state 0
    row ||| (UInt32.ofNat (utf8DfaShifts.getD next 0) <<< UInt32.ofNat (utf8DfaShifts.getD state 0))) 0

def utf8DfaTable : List UInt32 :=
  (List.range 256).map (fun byte => utf8DfaClassRow (utf8DfaClass (UInt8.ofNat byte)))

def utf8DfaAscii : UInt32 := 0
def utf8DfaAccept : UInt32 := 4
def utf8DfaInvalid : UInt32 := 10

/--
Julia source: base/strings/string.jl:433-433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _utf_dfa_step(state::_UTF8DFAState, byte::UInt8) = @inbounds (_UTF8_DFA_TABLE[byte+1] >> state) & _UTF8DFAState(0x0000001E)
```
-/
def utfDfaStep (state : UInt32) (byte : UInt8) : UInt32 :=
  ((utf8DfaTable.getD byte.toNat 0) >>> state) &&& 0x0000001E

private def utfDfaRunLoop {V : Type} (getByte : V → Int → UInt8) (bytes : V) (last : Int) :
    Nat → Int → UInt32 → UInt32
  | 0, _, state => state
  | fuel + 1, i, state =>
      if i ≤ last then
        utfDfaRunLoop getByte bytes last fuel (i + 1) (utfDfaStep state (getByte bytes i))
      else state

/--
Julia source: base/strings/string.jl:435-440 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _isvalid_utf8_dfa(state::_UTF8DFAState, bytes::AbstractVector{UInt8}, first::Int = firstindex(bytes), last::Int = lastindex(bytes))
    for i = first:last
       @inbounds state = _utf_dfa_step(state, bytes[i])
    end
    return (state)
end
```
-/
def isvalidUtf8Dfa {V : Type} (getByte : V → Int → UInt8)
    (firstindex lastindex : V → Int) (state : UInt32) (bytes : V)
    (first : Int := firstindex bytes) (last : Int := lastindex bytes) : UInt32 :=
  let fuel := if first ≤ last then (last - first + 1).toNat else 0
  utfDfaRunLoop getByte bytes last fuel first state

private def findNonasciiLoop {V : Type} (isAscii : V → Int → Int → Bool)
    (bytes : V) (last chunkSize : Int) : Nat → Int → Option Int
  | 0, _ => none
  | fuel + 1, i =>
      if i ≤ last - chunkSize then
        if !isAscii bytes i (i + chunkSize - 1) then some i
        else findNonasciiLoop isAscii bytes last chunkSize fuel (i + chunkSize)
      else none

/--
Julia source: base/strings/string.jl:442-451 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function  _find_nonascii_chunk(chunk_size,cu::AbstractVector{CU}, first,last) where {CU}
    n=first
    while n <= last - chunk_size
        _isascii(cu,n,n+chunk_size-1) || return n
        n += chunk_size
    end
    n= last-chunk_size+1
    _isascii(cu,n,last) || return n
    return nothing
end
```
-/
def findNonasciiChunk {V : Type} (isAscii : V → Int → Int → Bool)
    (chunkSize : Int) (bytes : V) (first last : Int) : Option Int :=
  let fuel := if first ≤ last then (last - first + 1).toNat + 1 else 1
  match findNonasciiLoop isAscii bytes last chunkSize fuel first with
  | some i => some i
  | none =>
      let i := last - chunkSize + 1
      if !isAscii bytes i last then some i else none

private def skipAsciiChunks {V : Type} (isAscii : V → Int → Int → Bool)
    (bytes : V) (chunkSize last : Int) :
    Nat → Int → Int → UInt32 → Int × Int × UInt32
  | 0, first, stop, state => (first, stop, state)
  | fuel + 1, first, stop, state =>
      if state == utf8DfaAccept && isAscii bytes first stop then
        let next := first + chunkSize
        if next ≤ last then
          skipAsciiChunks isAscii bytes chunkSize last fuel next (min last (stop + chunkSize)) state
        else (first, stop, state)
      else (first, stop, state)

private def classifyNonasciiLoop {V : Type} (getByte : V → Int → UInt8)
    (firstindex lastindex : V → Int) (isAscii : V → Int → Int → Bool)
    (bytes : V) (chunkSize last : Int) : Nat → Int → Int → UInt32 → Nat
  | 0, first, _, state =>
      if first ≤ last then 0 else if state == utf8DfaAccept then 2 else 0
  | fuel + 1, first, stop, state =>
      if first ≤ last then
        let (first, stop, state) :=
          skipAsciiChunks isAscii bytes chunkSize last fuel first stop state
        let state := isvalidUtf8Dfa getByte firstindex lastindex state bytes first stop
        if state == utf8DfaInvalid then 0
        else
          classifyNonasciiLoop getByte firstindex lastindex isAscii bytes chunkSize last fuel
            (first + chunkSize) (min last (stop + chunkSize)) state
      else if state == utf8DfaAccept then 2 else 0

/--
Julia source: base/strings/string.jl:476-497 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _byte_string_classify_nonascii(bytes::AbstractVector{UInt8}, first::Int, last::Int)
    chunk_size = 256

    start = first
    stop = min(last,first + chunk_size - 1)
    state = _UTF8_DFA_ACCEPT
    while start <= last
        # try to process ascii chunks
        while state == _UTF8_DFA_ACCEPT
            _isascii(bytes,start,stop) || break
            (start = start + chunk_size) <= last || break
            stop = min(last,stop + chunk_size)
        end
        # Process non ascii chunk
        state = _isvalid_utf8_dfa(state,bytes,start,stop)
        state == _UTF8_DFA_INVALID && return 0

        start = start + chunk_size
        stop = min(last,stop + chunk_size)
    end
    return ifelse(state == _UTF8_DFA_ACCEPT,2,0)
end
```
-/
def byteStringClassifyNonascii {V : Type} (getByte : V → Int → UInt8)
    (firstindex lastindex : V → Int) (isAscii : V → Int → Int → Bool)
    (bytes : V) (first last : Int) : Nat :=
  let chunkSize := 256
  let stop := min last (first + chunkSize - 1)
  let fuel := if first ≤ last then (last - first + 1).toNat + 1 else 1
  classifyNonasciiLoop getByte firstindex lastindex isAscii bytes chunkSize last fuel first stop
    utf8DfaAccept

/--
Julia source: base/strings/string.jl:462-474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function byte_string_classify(bytes::AbstractVector{UInt8})
    chunk_size = 1024
    chunk_threshold =  chunk_size + (chunk_size ÷ 2)
    n = length(bytes)
    if n > chunk_threshold
        start = _find_nonascii_chunk(chunk_size,bytes,1,n)
        isnothing(start) && return 1
    else
        _isascii(bytes,1,n) && return 1
        start = 1
    end
    return _byte_string_classify_nonascii(bytes,start,n)
end
```
-/
def byteStringClassifyVector {V : Type} (length : V → Int)
    (getByte : V → Int → UInt8) (firstindex lastindex : V → Int)
    (isAscii : V → Int → Int → Bool) (bytes : V) : Nat := Id.run do
  let chunkSize := 1024
  let chunkThreshold := chunkSize + chunkSize / 2
  let n := length bytes
  if n > chunkThreshold then
    match findNonasciiChunk isAscii chunkSize bytes 1 n with
    | none => return 1
    | some start =>
        return byteStringClassifyNonascii getByte firstindex lastindex isAscii bytes start n
  else
    if isAscii bytes 1 n then return 1
    return byteStringClassifyNonascii getByte firstindex lastindex isAscii bytes 1 n

/--
Julia source: base/strings/string.jl:459-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
 byte_string_classify(s::AbstractString) = byte_string_classify(codeunits(s))
```
-/
def byteStringClassifyAbstract {S V : Type} (codeunits : S → V)
    (length : V → Int) (getByte : V → Int → UInt8)
    (firstindex lastindex : V → Int) (isAscii : V → Int → Int → Bool)
    (s : S) : Nat :=
  byteStringClassifyVector length getByte firstindex lastindex isAscii (codeunits s)

/--
Julia source: base/strings/string.jl:499-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isvalid(::Type{String}, bytes::AbstractVector{UInt8}) = (@inline byte_string_classify(bytes)) ≠ 0
```
-/
def isvalidStringBytes {V : Type} (length : V → Int) (getByte : V → Int → UInt8)
    (firstindex lastindex : V → Int) (isAscii : V → Int → Int → Bool)
    (bytes : V) : Bool :=
  byteStringClassifyVector length getByte firstindex lastindex isAscii bytes != 0

/--
Julia source: base/strings/string.jl:500-500 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isvalid(::Type{String}, s::AbstractString) =  (@inline byte_string_classify(s)) ≠ 0
```
-/
def isvalidStringAbstract {S V : Type} (codeunits : S → V) (length : V → Int)
    (getByte : V → Int → UInt8) (firstindex lastindex : V → Int)
    (isAscii : V → Int → Int → Bool) (s : S) : Bool :=
  byteStringClassifyAbstract codeunits length getByte firstindex lastindex isAscii s != 0

/--
Julia source: base/strings/string.jl:502-502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline isvalid(s::AbstractString) = @inline isvalid(String, codeunits(s))
```
-/
def isvalidAbstractString {S V : Type} (codeunits : S → V) (length : V → Int)
    (getByte : V → Int → UInt8) (firstindex lastindex : V → Int)
    (isAscii : V → Int → Int → Bool) (s : S) : Bool :=
  isvalidStringAbstract codeunits length getByte firstindex lastindex isAscii s

/--
Julia source: base/strings/string.jl:504-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_valid_continuation(c) = c & 0xc0 == 0x80
```
-/
def isValidContinuation (c : UInt8) : Bool := (c &&& 0xc0) == 0x80

/--
Julia source: base/strings/string.jl:517-538 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate_continued(s, i::Int, u::UInt32)
    @label begin
        u < 0xc0000000 && (i += 1; break)
        n = ncodeunits(s)
        # first continuation byte
        (i += 1) > n && break
        @inbounds b = codeunit(s, i)
        b & 0xc0 == 0x80 || break
        u |= UInt32(b) << 16
        # second continuation byte
        ((i += 1) > n) | (u < 0xe0000000) && break
        @inbounds b = codeunit(s, i)
        b & 0xc0 == 0x80 || break
        u |= UInt32(b) << 8
        # third continuation byte
        ((i += 1) > n) | (u < 0xf0000000) && break
        @inbounds b = codeunit(s, i)
        b & 0xc0 == 0x80 || break
        u |= UInt32(b); i += 1
    end
    return reinterpret(Char, u), i
end
```
-/
def iterateContinued {S : Type} (ncodeunits : S → Index)
    (codeunit : S → Index → UInt8) (s : S) (i : Index) (u : UInt32) :
    UInt32 × Index := Id.run do
  let mut u := u
  if u < 0xc0000000 then
    return (u, i + JuliaLean.Strings.ix 1)
  let n := ncodeunits s
  let mut i := i + JuliaLean.Strings.ix 1
  if i.val > n.val then return (u, i)
  let mut b := codeunit s i
  if (b &&& 0xc0) != 0x80 then return (u, i)
  u := u ||| (b.toUInt32 <<< 16)
  i := i + JuliaLean.Strings.ix 1
  if i.val > n.val || u < 0xe0000000 then return (u, i)
  b := codeunit s i
  if (b &&& 0xc0) != 0x80 then return (u, i)
  u := u ||| (b.toUInt32 <<< 8)
  i := i + JuliaLean.Strings.ix 1
  if i.val > n.val || u < 0xf0000000 then return (u, i)
  b := codeunit s i
  if (b &&& 0xc0) != 0x80 then return (u, i)
  return (u ||| b.toUInt32, i + JuliaLean.Strings.ix 1)

/--
Julia source: base/strings/string.jl:508-514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function iterate(s::Union{String, StringView}, i::Int=firstindex(s))
    (i % UInt) - 1 < ncodeunits(s) || return nothing
    b = @inbounds codeunit(s, i)
    u = UInt32(b) << 24
    between(b, 0x80, 0xf7) || return reinterpret(Char, u), i+1
    return @noinline iterate_continued(s, i, u)
end
```
-/
def iterateString {S : Type} (firstindex ncodeunits : S → Index)
    (codeunit : S → Index → UInt8) (betweenByte : UInt8 → UInt8 → UInt8 → Bool)
    (s : S) (i : Index := firstindex s) : Option (UInt32 × Index) :=
  if !decide ((JInt.rem .u64 i - JInt.lit .u64 1).val < (ncodeunits s).val) then none
  else
    let b := codeunit s i
    let u := b.toUInt32 <<< 24
    if !betweenByte b 0x80 0xf7 then some (u, i + JuliaLean.Strings.ix 1)
    else some (iterateContinued ncodeunits codeunit s i u)
/--
Julia source: base/strings/string.jl:548-573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex_continued(s, i::Int, u::UInt32)
    @label begin
        if u < 0xc0000000
            # called from `getindex` which checks bounds
            @inbounds isvalid(s, i) && break
            string_index_err(s, i)
        end
        n = ncodeunits(s)

        (i += 1) > n && break
        @inbounds b = codeunit(s, i) # cont byte 1
        b & 0xc0 == 0x80 || break
        u |= UInt32(b) << 16

        ((i += 1) > n) | (u < 0xe0000000) && break
        @inbounds b = codeunit(s, i) # cont byte 2
        b & 0xc0 == 0x80 || break
        u |= UInt32(b) << 8

        ((i += 1) > n) | (u < 0xf0000000) && break
        @inbounds b = codeunit(s, i) # cont byte 3
        b & 0xc0 == 0x80 || break
        u |= UInt32(b)
    end
    return reinterpret(Char, u)
end
```
-/
def getindexContinued {S : Type} (isvalid : S → Index → Bool) (ncodeunits : S → Index)
    (codeunit : S → Index → UInt8) (s : S) (i : Index) (u : UInt32) :
    StringResult UInt32 := do
  let mut u := u
  if u < 0xc0000000 then
    if isvalid s i then
      return u
    else
      let _ ← stringIndexErr (fun x => x) s i
      pure ()
  let n := ncodeunits s
  let mut i := i + JuliaLean.Strings.ix 1
  if i.val > n.val then return u
  let mut b := codeunit s i
  if (b &&& 0xc0) != 0x80 then return u
  u := u ||| (b.toUInt32 <<< 16)
  i := i + JuliaLean.Strings.ix 1
  if i.val > n.val || u < 0xe0000000 then return u
  b := codeunit s i
  if (b &&& 0xc0) != 0x80 then return u
  u := u ||| (b.toUInt32 <<< 8)
  i := i + JuliaLean.Strings.ix 1
  if i.val > n.val || u < 0xf0000000 then return u
  b := codeunit s i
  if (b &&& 0xc0) != 0x80 then return u
  return u ||| b.toUInt32

/--
Julia source: base/strings/string.jl:540-545 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function getindex(s::Union{String, StringView}, i::Int)
    b = codeunit(s, i)
    u = UInt32(b) << 24
    between(b, 0x80, 0xf7) || return reinterpret(Char, u)
    return getindex_continued(s, i, u)
end
```
-/
def getindexString {S : Type} (isvalid : S → Index → Bool) (ncodeunits : S → Index)
    (codeunit : S → Index → UInt8) (checkedCodeunit : S → Index → StringResult UInt8)
    (betweenByte : UInt8 → UInt8 → UInt8 → Bool) (s : S) (i : Index) : StringResult UInt32 := do
  let b ← checkedCodeunit s i
  let u := b.toUInt32 <<< 24
  if !betweenByte b 0x80 0xf7 then
    return u
  getindexContinued isvalid ncodeunits codeunit s i u

/--
Julia source: base/strings/string.jl:575-578 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(s::Union{String, StringView}, r::AbstractUnitRange{<:Integer})
    span = (Int(first(r))::Int):(Int(last(r)))::Int
    return s[span]
end
```
-/
def getindexAbstractRange {S I : Type} (toInt : I → Index)
    (getindexUnitRange : S → Index → Index → StringResult JString)
    (s : S) (first last : I) : StringResult JString :=
  getindexUnitRange s (toInt first) (toInt last)

/--
Julia source: base/strings/string.jl:580-595 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function getindex(s::String, r::UnitRange{Int})
    isempty(r) && return ""
    i, j = first(r), last(r)
    @boundscheck begin
        checkbounds(s, r)
        @inbounds isvalid(s, i) || string_index_err(s, i)
        @inbounds isvalid(s, j) || string_index_err(s, j)
    end
    # Safety: The boundscheck checked r is inbounds in s,
    # and since we also checked r is not empty, j must be inbounds in s
    j = @inbounds nextind(s, j) - 1
    n = (j - i + 1) % UInt
    ss = _string_n(n)
    GC.@preserve s ss unsafe_copyto!(pointer(ss), pointer(s, i), n)
    return ss
end
```
-/
def getindexStringRange (boundsChecking : Bool) (isEmptyRange : Index → Index → Bool)
    (checkbounds : JString → Index → Index → StringResult Unit)
    (isvalid : JString → Index → Bool) (ncodeunits : JString → Index)
    (betweenI : Index → Index → Index → Bool) (betweenByte : UInt8 → UInt8 → UInt8 → Bool)
    (codeunit : Bool → JString → Index → StringResult UInt8)
    (toCsize : JInt .u64 → StringResult Nat) (allocateString : Nat → StringResult JString)
    (unsafeConvertString : JString → Int) (toInt : Index → Int)
    (preserve : JString → JString → (Unit → JString) → JString)
    (unsafeCopyTo : Int → Int → Nat → JString → JString)
    (s : JString) (i j : Index) : StringResult JString := do
  if isEmptyRange i j then
    return JuliaLean.Strings.JStr.empty
  if boundsChecking then
    let _ ← checkbounds s i j
    if !isvalid s i then
      let _ ← stringIndexErr (fun x => x) s i
      pure ()
    if !isvalid s j then
      let _ ← stringIndexErr (fun x => x) s j
      pure ()
  let j' ← nextindString ncodeunits betweenI betweenByte codeunit s j
  let j := j' - JuliaLean.Strings.ix 1
  let n := JInt.rem .u64 (j - i + JuliaLean.Strings.ix 1)
  let ss ← stringN toCsize allocateString n
  let destination := pointerString unsafeConvertString ss
  let source := pointerAt unsafeConvertString toInt s i
  let result := preserve s ss (fun _ => unsafeCopyTo destination source n.val.toNat ss)
  return result
/-- Convert a Bool to Julia `Int`, as the byte-counting loop does. -/
def stringIndexBool (b : Bool) : Index := JuliaLean.Strings.ix (if b then 1 else 0)

private def lengthSeekLead {S : Type} (codeunit : S → Index → UInt8)
    (s : S) (n : Index) : Nat → Index → UInt8 → Option (Index × UInt8)
  | 0, _, _ => none
  | fuel + 1, i, b =>
      let i := i + JuliaLean.Strings.ix 1
      if i.val > n.val then none
      else if 0xc0 ≤ b && b ≤ 0xf7 then some (i, b)
      else lengthSeekLead codeunit s n fuel i (codeunit s i)

private def lengthCountLoop {S : Type} (codeunit : S → Index → UInt8)
    (s : S) (n : Index) : Nat → Index → UInt8 → Index → Index
  | 0, _, _, count => count
  | fuel + 1, i, b, count =>
      match lengthSeekLead codeunit s n fuel i b with
      | none => count
      | some (i, lead) =>
          let b := codeunit s i
          let firstIsContinuation := isValidContinuation b
          let count := count - stringIndexBool firstIsContinuation
          if !(firstIsContinuation && lead ≥ 0xe0) then
            lengthCountLoop codeunit s n fuel i b count
          else
            let i := i + JuliaLean.Strings.ix 1
            if i.val > n.val then count
            else
              let b := codeunit s i
              let secondIsContinuation := isValidContinuation b
              let count := count - stringIndexBool secondIsContinuation
              if !(secondIsContinuation && lead ≥ 0xf0) then
                lengthCountLoop codeunit s n fuel i b count
              else
                let i := i + JuliaLean.Strings.ix 1
                if i.val > n.val then count
                else
                  let b := codeunit s i
                  lengthCountLoop codeunit s n fuel i b
                    (count - stringIndexBool (isValidContinuation b))

/--
Julia source: base/strings/string.jl:635-658 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function _length_continued(s::Union{String, StringView}, i::Int, n::Int, c::Int)
    i < n || return c
    b = codeunit(s, i)
    while true
        while true
            (i += 1) ≤ n || return c
            0xc0 ≤ b ≤ 0xf7 && break
            b = codeunit(s, i)
        end
        l = b
        b = codeunit(s, i) # cont byte 1
        c -= (x = b & 0xc0 == 0x80)
        x & (l ≥ 0xe0) || continue

        (i += 1) ≤ n || return c
        b = codeunit(s, i) # cont byte 2
        c -= (x = b & 0xc0 == 0x80)
        x & (l ≥ 0xf0) || continue

        (i += 1) ≤ n || return c
        b = codeunit(s, i) # cont byte 3
        c -= (b & 0xc0 == 0x80)
    end
end
```
-/
def lengthContinuedInternal {S : Type} (codeunit : S → Index → UInt8)
    (s : S) (i n c : Index) : Index :=
  if !(i.val < n.val) then c
  else lengthCountLoop codeunit s n (n.val - i.val + 1).toNat i (codeunit s i) c

/--
Julia source: base/strings/string.jl:626-628 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :terminates_globally @propagate_inbounds function length_continued(s::String, i::Int, n::Int, c::Int)
    _length_continued(s, i, n, c)
end
```
-/
def lengthContinuedString (codeunit : JString → Index → UInt8)
    (s : JString) (i n c : Index) : Index :=
  lengthContinuedInternal codeunit s i n c

/--
Julia source: base/strings/string.jl:630-632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function length_continued(s::StringView, i::Int, n::Int, c::Int)
    _length_continued(s, i, n, c)
end
```
-/
def lengthContinuedView {S : Type} (codeunit : S → Index → UInt8)
    (s : S) (i n c : Index) : Index :=
  lengthContinuedInternal codeunit s i n c

/--
Julia source: base/strings/string.jl:615-624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _length(s::Union{String, StringView}, i::Int, j::Int)
    @boundscheck begin
        0 < i ≤ ncodeunits(s)+1 || throw(BoundsError(s, i))
        0 ≤ j < ncodeunits(s)+1 || throw(BoundsError(s, j))
    end
    j < i && return 0
    @inbounds i, k = thisind(s, i), i
    c = j - i + (i == k)
    @inbounds length_continued(s, i, j, c)
end
```
-/
def lengthRange {S : Type} (ncodeunits : S → Index)
    (thisind : S → Index → StringResult Index)
    (lengthContinued : S → Index → Index → Index → Index)
    (s : S) (i j : Index) : StringResult Index := do
  let n := ncodeunits s
  if !(0 < i.val && i.val ≤ (n + JuliaLean.Strings.ix 1).val) then
    throw (.jl .boundsError)
  if !(0 ≤ j.val && j.val < (n + JuliaLean.Strings.ix 1).val) then
    throw (.jl .boundsError)
  if j.val < i.val then
    return JuliaLean.Strings.ix 0
  let k := i
  let i ← thisind s i
  let c := j - i + stringIndexBool (i.val == k.val)
  return lengthContinued s i j c

/--
Julia source: base/strings/string.jl:607-609 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :consistent :effect_free @inline function length(s::String, i::Int, j::Int)
    _length(s, i, j)
end
```
-/
def lengthStringRange (ncodeunits : JString → Index)
    (thisind : JString → Index → StringResult Index)
    (lengthContinued : JString → Index → Index → Index → Index)
    (s : JString) (i j : Index) : StringResult Index :=
  lengthRange ncodeunits thisind lengthContinued s i j

/--
Julia source: base/strings/string.jl:611-613 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function length(s::StringView, i::Int, j::Int)
    _length(s, i, j)
end
```
-/
def lengthViewRange {S : Type} (ncodeunits : S → Index)
    (thisind : S → Index → StringResult Index)
    (lengthContinued : S → Index → Index → Index → Index)
    (s : S) (i j : Index) : StringResult Index :=
  lengthRange ncodeunits thisind lengthContinued s i j

/--
Julia source: base/strings/string.jl:598-600 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :nothrow function length(s::String)
    return length_continued(s, 1, ncodeunits(s), ncodeunits(s))
end
```
-/
def lengthString (ncodeunits : JString → Index) (codeunit : JString → Index → UInt8)
    (s : JString) : Index :=
  lengthContinuedString codeunit s (JuliaLean.Strings.ix 1) (ncodeunits s) (ncodeunits s)

/--
Julia source: base/strings/string.jl:602-604 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function length(s::StringView)
    return length_continued(s, 1, ncodeunits(s), ncodeunits(s))
end
```
-/
def lengthView {S : Type} (ncodeunits : S → Index) (codeunit : S → Index → UInt8)
    (s : S) : Index :=
  lengthContinuedView codeunit s (JuliaLean.Strings.ix 1) (ncodeunits s) (ncodeunits s)
/--
Julia source: base/strings/string.jl:662-662 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isvalid(s::String, i::Int) = checkbounds(Bool, s, i) && thisind(s, i) == i
```
-/
def isvalidStringIndex (checkbounds : JString → Index → Bool)
    (ncodeunits : JString → Index) (betweenI : Index → Index → Index → Bool)
    (betweenByte : UInt8 → UInt8 → UInt8 → Bool)
    (codeunit : Bool → JString → Index → StringResult UInt8) (s : JString) (i : Index) : Bool :=
  checkbounds s i &&
    match thisindString ncodeunits betweenI betweenByte codeunit s i with
    | .ok index => index.val == i.val
    | .error _ => false

/--
Julia source: base/strings/string.jl:665-665 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isascii(s::String) = @assume_effects :nothrow :foldable isascii(codeunits(s))
```
-/
def isasciiString {V : Type} (codeunits : JString → V) (isascii : V → Bool)
    (s : JString) : Bool :=
  isascii (codeunits s)

private def repeatStore16Loop (store16 : JString → Int → UInt16 → Nat → JString)
    (pointer : Int) (value : UInt16) : Nat → Nat → JString → JString
  | 0, _, s => s
  | fuel + 1, i, s =>
      repeatStore16Loop store16 pointer value fuel (i + 1) (store16 s pointer value i)

private def repeatStore32Loop (store32 : JString → Int → UInt32 → Nat → JString)
    (pointer : Int) (value : UInt32) : Nat → Nat → JString → JString
  | 0, _, s => s
  | fuel + 1, i, s =>
      repeatStore32Loop store32 pointer value fuel (i + 1) (store32 s pointer value i)

private def repeatStoreThreeLoop (store8 : JString → Int → UInt8 → Nat → JString)
    (pointer : Int) (b1 b2 b3 : UInt8) : Nat → Nat → JString → JString
  | 0, _, s => s
  | fuel + 1, i, s =>
      let s := store8 s pointer b1 (3 * i + 1)
      let s := store8 s pointer b2 (3 * i + 2)
      let s := store8 s pointer b3 (3 * i + 3)
      repeatStoreThreeLoop store8 pointer b1 b2 b3 fuel (i + 1) s

/--
Julia source: base/strings/string.jl:682-715 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function repeat(c::AbstractChar, r::Integer)
    r < 0 && throw(ArgumentError("can't repeat a character $r times"))
    r = UInt(r)::UInt
    c = Char(c)::Char
    r == 0 && return ""
    u = bswap(reinterpret(UInt32, c))
    n = 4 - (leading_zeros(u | 0xff) >> 3)
    r > typemax(UInt) ÷ UInt(n) && throw(OutOfMemoryError())
    s = _string_n(n*r)
    p = pointer(s)
    GC.@preserve s if n == 1
        memset(p, u % UInt8, r)
    elseif n == 2
        p16 = reinterpret(Ptr{UInt16}, p)
        for i = 1:r
            unsafe_store!(p16, u % UInt16, i)
        end
    elseif n == 3
        b1 = (u >> 0) % UInt8
        b2 = (u >> 8) % UInt8
        b3 = (u >> 16) % UInt8
        for i = 0:r-1
            unsafe_store!(p, b1, 3i + 1)
            unsafe_store!(p, b2, 3i + 2)
            unsafe_store!(p, b3, 3i + 3)
        end
    elseif n == 4
        p32 = reinterpret(Ptr{UInt32}, p)
        for i = 1:r
            unsafe_store!(p32, u, i)
        end
    end
    return s
end
```
-/
def repeatChar {C I : Type} (isNegative : I → Bool) (showInteger : I → String)
    (toUInt : I → StringResult (JInt .u64)) (charBits : C → StringResult UInt32)
    (bswap : UInt32 → UInt32) (leadingZeros : UInt32 → Nat) (maxUInt : Nat)
    (toCsize : Nat → StringResult Nat) (allocateString : Nat → StringResult JString)
    (unsafeConvertString : JString → Int) (withPreserve : JString → (Unit → JString) → JString)
    (memset : JString → Int → UInt8 → Nat → JString)
    (reinterpretPtr16 : Int → Int) (store16 : JString → Int → UInt16 → Nat → JString)
    (reinterpretPtr32 : Int → Int) (store32 : JString → Int → UInt32 → Nat → JString)
    (store8 : JString → Int → UInt8 → Nat → JString) (toUInt8 : UInt32 → UInt8)
    (toUInt16 : UInt32 → UInt16) (c : C) (r : I) : StringResult JString := do
  if isNegative r then
    throw (.jl (.argumentError ("can't repeat a character " ++ showInteger r ++ " times")))
  let r ← toUInt r
  let c ← charBits c
  if r.val == 0 then
    return JuliaLean.Strings.JStr.empty
  let u := bswap c
  let n := 4 - leadingZeros (u ||| 0xff) / 8
  if r.val.toNat > maxUInt / n then
    throw .outOfMemory
  let s ← stringN toCsize allocateString (n * r.val.toNat)
  let pointer := pointerString unsafeConvertString s
  let result := withPreserve s (fun _ =>
    if n == 1 then
      memset s pointer (toUInt8 u) r.val.toNat
    else if n == 2 then
      let pointer := reinterpretPtr16 pointer
      repeatStore16Loop store16 pointer (toUInt16 u) r.val.toNat 1 s
    else if n == 3 then
      let b1 := toUInt8 u
      let b2 := toUInt8 (u >>> 0x8)
      let b3 := toUInt8 (u >>> 0x10)
      repeatStoreThreeLoop store8 pointer b1 b2 b3 r.val.toNat 0 s
    else if n == 4 then
      let pointer := reinterpretPtr32 pointer
      repeatStore32Loop store32 pointer u r.val.toNat 1 s
    else
      s)
  return result
/--
Julia source: base/strings/string.jl:668-668 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :foldable repeat(c::Char, r::BitInteger) = @invoke repeat(c::Char, r::Integer)
```
-/
def repeatCharBit {t : IntTy} (isNegative : JInt t → Bool) (showInteger : JInt t → String)
    (toUInt : JInt t → StringResult (JInt .u64)) (charBits : UInt32 → StringResult UInt32)
    (bswap : UInt32 → UInt32) (leadingZeros : UInt32 → Nat) (maxUInt : Nat)
    (toCsize : Nat → StringResult Nat) (allocateString : Nat → StringResult JString)
    (unsafeConvertString : JString → Int) (withPreserve : JString → (Unit → JString) → JString)
    (memset : JString → Int → UInt8 → Nat → JString)
    (reinterpretPtr16 : Int → Int) (store16 : JString → Int → UInt16 → Nat → JString)
    (reinterpretPtr32 : Int → Int) (store32 : JString → Int → UInt32 → Nat → JString)
    (store8 : JString → Int → UInt8 → Nat → JString) (toUInt8 : UInt32 → UInt8)
    (toUInt16 : UInt32 → UInt16) (c : UInt32) (r : JInt t) : StringResult JString :=
  repeatChar isNegative showInteger toUInt charBits bswap leadingZeros maxUInt
    toCsize allocateString unsafeConvertString withPreserve memset reinterpretPtr16 store16
    reinterpretPtr32 store32 store8 toUInt8 toUInt16 c r


/-- One-based byte access used to instantiate the string memory interface. -/
def stringByteAt (s : JString) (i : Index) : UInt8 :=
  s.bytes.getD (i.val.toNat - 1) 0

def stringCoreSizeof (s : JString) : Index :=
  JuliaLean.Strings.ix s.bytes.length

def stringCheckbounds (s : JString) (i : Index) : StringResult Unit :=
  if 1 ≤ i.val && i.val ≤ s.bytes.length then .ok ()
  else .error (.jl .boundsError)

def stringCheckboundsBool (s : JString) (i : Index) : Bool :=
  1 ≤ i.val && i.val ≤ s.bytes.length

def stringUnsafeConvert (_s : JString) : Int := 0

def stringUnsafeLoad (s : JString) (pointer : Int) : UInt8 :=
  s.bytes.getD pointer.toNat 0

def stringPreserveByte (_s : JString) (readByte : Unit → UInt8) : UInt8 :=
  readByte ()

def stringCodeunitAt (boundsChecking : Bool) (s : JString) (i : Index) :
    StringResult UInt8 :=
  codeunitInt boundsChecking s i stringCheckbounds
    stringUnsafeConvert stringPreserveByte stringUnsafeLoad

def stringCodeunit (s : JString) (i : Index) : StringResult UInt8 :=
  codeunitInteger (fun x => x) stringCheckbounds stringUnsafeConvert
    stringPreserveByte stringUnsafeLoad s i

def stringNcodeunits (s : JString) : Index :=
  ncodeunits stringCoreSizeof s

def stringBetweenIndex (i lo hi : Index) : Bool :=
  between (fun a b => decide (a.val ≤ b.val)) i lo hi

def stringBetweenByte (b lo hi : UInt8) : Bool :=
  between (fun a b => decide (a ≤ b)) b lo hi

def stringThisind (s : JString) (i : Index) : StringResult Index :=
  thisindString stringNcodeunits stringBetweenIndex stringBetweenByte stringCodeunitAt s i

def stringNextind (s : JString) (i : Index) : StringResult Index :=
  nextindString stringNcodeunits stringBetweenIndex stringBetweenByte stringCodeunitAt s i

def stringIsvalidIndex (s : JString) (i : Index) : Bool :=
  isvalidStringIndex stringCheckboundsBool stringNcodeunits stringBetweenIndex
    stringBetweenByte stringCodeunitAt s i

def stringFirstindex (_s : JString) : Index := JuliaLean.Strings.ix 1

def stringIterate (s : JString) (i : Index) : Option (UInt32 × Index) :=
  iterateString stringFirstindex stringNcodeunits stringByteAt stringBetweenByte s i

def stringLength (s : JString) : Index :=
  lengthString stringNcodeunits stringByteAt s

def byteListLength (bytes : List UInt8) : Int := Int.ofNat bytes.length

def byteListGet (bytes : List UInt8) (i : Int) : UInt8 :=
  bytes.getD (i.toNat - 1) 0

def byteListIsAscii (bytes : List UInt8) (first last : Int) : Bool :=
  if first > last then true
  else
    (List.range (last - first + 1).toNat).all
      (fun offset => (byteListGet bytes (first + Int.ofNat offset)).toNat < 0x80)

def byteListFirstindex (_bytes : List UInt8) : Int := 1

def byteListLastindex (bytes : List UInt8) : Int := Int.ofNat bytes.length

def stringBytesAreValidUtf8 (bytes : List UInt8) : Bool :=
  isvalidStringBytes byteListLength byteListGet byteListFirstindex byteListLastindex
    byteListIsAscii bytes
def stringGetindex (s : JString) (i : Index) : StringResult UInt32 :=
  getindexString stringIsvalidIndex stringNcodeunits stringByteAt stringCodeunit
    stringBetweenByte s i

def stringLengthContinued (s : JString) (i n c : Index) : Index :=
  lengthContinuedString stringByteAt s i n c

def stringIsascii (s : JString) : Bool :=
  isasciiString (fun string => string.bytes)
    (fun bytes => byteListIsAscii bytes 1 (Int.ofNat bytes.length)) s

def byteListLengthIndex (bytes : List UInt8) : Index :=
  JuliaLean.Strings.ix (Int.ofNat bytes.length)

def stringViewLength (view : StringView (List UInt8)) : Index :=
  lengthView byteListLengthIndex (fun bytes i => byteListGet bytes i.val) view.data

def stringLengthRange (s : JString) (i j : Index) : StringResult Index :=
  lengthStringRange stringNcodeunits stringThisind stringLengthContinued s i j

def stringViewNcodeunits (view : StringView (List UInt8)) : Index :=
  byteListLengthIndex view.data

def stringViewByteAt (view : StringView (List UInt8)) (i : Index) : UInt8 :=
  byteListGet view.data i.val

def stringViewFirstindex (_view : StringView (List UInt8)) : Index :=
  JuliaLean.Strings.ix 1

def stringViewIterate (view : StringView (List UInt8)) (i : Index) :
    Option (UInt32 × Index) :=
  iterateString stringViewFirstindex stringViewNcodeunits stringViewByteAt stringBetweenByte view i

def stringViewCodeunitAt (_boundsChecking : Bool) (view : StringView (List UInt8))
    (i : Index) : StringResult UInt8 :=
  if 1 ≤ i.val && i.val ≤ Int.ofNat view.data.length then
    .ok (stringViewByteAt view i)
  else .error (.jl .boundsError)

def stringViewThisind (view : StringView (List UInt8)) (i : Index) : StringResult Index :=
  thisindString stringViewNcodeunits stringBetweenIndex stringBetweenByte
    stringViewCodeunitAt view i

def stringViewLengthContinued (view : StringView (List UInt8)) (i n c : Index) : Index :=
  lengthContinuedView stringViewByteAt view i n c

def stringViewLengthRange (view : StringView (List UInt8)) (i j : Index) : StringResult Index :=
  lengthViewRange stringViewNcodeunits stringViewThisind stringViewLengthContinued view i j

def stringGetindexRange (isEmptyRange : Index → Index → Bool)
    (checkbounds : JString → Index → Index → StringResult Unit)
    (toCsize : JInt .u64 → StringResult Nat)
    (allocateString : Nat → StringResult JString) (toInt : Index → Int)
    (preserve : JString → JString → (Unit → JString) → JString)
    (unsafeCopyTo : Int → Int → Nat → JString → JString)
    (s : JString) (i j : Index) : StringResult JString :=
  getindexStringRange true isEmptyRange checkbounds stringIsvalidIndex stringNcodeunits
    stringBetweenIndex stringBetweenByte stringCodeunitAt toCsize allocateString
    stringUnsafeConvert toInt preserve unsafeCopyTo s i j

end JuliaLean.base.strings.string


/-!
# Strings as UTF-8 code units

Model of `String` from `base/strings/string.jl` and the generic index
functions of `base/strings/basic.jl` (master `bbfa0ce4150`).

* A `String` is its byte sequence (`JStr.bytes`), with no validity
  requirement: overlong forms, surrogates, truncated sequences and stray
  continuation bytes are all representable, exactly as in Julia
  (`base/strings/string.jl:80-90`).
* A `Char` is its 32-bit encoded bit pattern (`base/char.jl:39-52`): the
  UTF-8 bytes of the character, left-aligned, padded with zero bytes.
  Bit patterns are Lean `UInt8`/`UInt32`, whose operators are the
  fixed-width wrapping operators Julia uses on those types.
* Indices and counts are `Int` (`JInt64`) and use the wrapping `JInt`
  operators, so overflow happens exactly where Julia overflows.
* Julia's `while` loops are written as structural recursion on an explicit
  bound on the number of remaining iterations (for example `n - i` when `i`
  increases towards `n`). Each docstring states the bound; when it reaches
  zero the loop condition is false, so the bound never truncates a run.
-/

namespace JuliaLean.Strings

-- placed here to break an import cycle with strings/stringview
/-- Store `bs` at zero-based offset `p` of `buf`. -/
def writeAt (buf : List UInt8) (p : Nat) (bs : List UInt8) : List UInt8 :=
  buf.take p ++ bs ++ buf.drop (p + bs.length)

/-- `ncodeunits(s::String) = Core.sizeof(s)`, `base/strings/string.jl:209`. -/
def ncodeunits (s : JStr) : JInt64 := ix s.bytes.length

/-- `@inbounds codeunit(s, i)` (`base/strings/string.jl:213-217`): the byte at
one-based index `i`. Only called at indices the caller has checked. -/
def cu (s : JStr) (i : JInt64) : UInt8 := s.bytes.getD (i.val.toNat - 1) 0

/-- `codeunit(s::String, i::Int)` with its bounds check, `base/strings/string.jl:213-217`. -/
def codeunit (s : JStr) (i : JInt64) : SJl UInt8 :=
  if 1 ≤ i.val ∧ i.val ≤ (ncodeunits s).val then .ok (cu s i) else .error boundsErr

/-- `b & 0xc0 == 0x80`: `b` is a continuation byte. -/
abbrev isCont (b : UInt8) : Bool := (b &&& 0xc0) == 0x80

/-- `between(b, lo, hi) = (lo ≤ b) & (b ≤ hi)`, `base/strings/string.jl:78`. -/
abbrev between (b lo hi : UInt8) : Bool := decide (lo ≤ b) && decide (b ≤ hi)

/-- `between` on `Int` indices. -/
abbrev betweenI (i lo hi : JInt64) : Bool := decide (lo.val ≤ i.val) && decide (i.val ≤ hi.val)

/-- The slow path `_thisind_continued`, `base/strings/string.jl:259-270`.
Precondition (from the caller): `b(i)` is a continuation byte and `i > 1`. -/
def thisindContinued (s : JStr) (i : JInt64) : JInt64 :=
  let b := cu s (i - ix 1)
  if between b 0xc0 0xf7 then i - ix 1
  else if !(isCont b && decide ((i - ix 2).val > 0)) then i
  else
    let b := cu s (i - ix 2)
    if between b 0xe0 0xf7 then i - ix 2
    else if !(isCont b && decide ((i - ix 3).val > 0)) then i
    else
      let b := cu s (i - ix 3)
      if between b 0xf0 0xf7 then i - ix 3 else i

/-- `_thisind_str(s, i::Int)`, `base/strings/string.jl:252-271`; this is
`thisind(s::String, i::Int)` (`:245`). -/
def thisind (s : JStr) (i : JInt64) : SJl JInt64 :=
  if i.val = 0 then .ok (ix 0)
  else
    let n := ncodeunits s
    if i.val = (n + ix 1).val then .ok i
    else if !betweenI i (ix 1) n then .error boundsErr
    else
      let b := cu s i
      if !(isCont b && decide ((i - ix 1).val > 0)) then .ok i
      else .ok (thisindContinued s i)

/-- `isvalid(s::String, i::Int) = checkbounds(Bool, s, i) && thisind(s, i) == i`,
`base/strings/string.jl:662`, with `checkbounds(Bool, s, i) = 1 ≤ i ≤ ncodeunits(s)`
(`base/strings/basic.jl:204-205`). -/
def isvalidAt (s : JStr) (i : JInt64) : Bool :=
  decide (1 ≤ i.val ∧ i.val ≤ (ncodeunits s).val) &&
    (match thisind s i with
     | .ok j => decide (j.val = i.val)
     | .error _ => false)

/-- The lead-byte part of `_nextind_continued`, `base/strings/string.jl:293-304`:
skip up to three continuation bytes after the lead byte `l` at `i`. -/
def nextindFromLead (s : JStr) (i n : JInt64) (l : UInt8) : JInt64 :=
  let i := i + ix 1
  if i.val > n.val then i
  else if !isCont (cu s i) then i
  else
    let i := i + ix 1
    if decide (i.val > n.val) || decide (l < 0xe0) then i
    else if !isCont (cu s i) then i
    else
      let i := i + ix 1
      if decide (i.val > n.val) || decide (l < 0xf0) then i
      else if !isCont (cu s i) then i else i + ix 1

/-- `_nextind_continued(s, i, n, l)`, `base/strings/string.jl:282-305`. -/
def nextindContinued (s : JStr) (i n : JInt64) (l : UInt8) : SJl JInt64 :=
  if l < 0xc0 then
    match thisind s i with
    | .error e => .error e
    | .ok i' =>
      if i'.val ≥ i.val then .ok (i + ix 1)
      else
        let l := cu s i'
        if decide (l < 0x80) || decide (0xf8 ≤ l) then .ok (i' + ix 1)
        else if !decide (l ≥ 0xc0) then .error .assertion
        else .ok (nextindFromLead s i' n l)
  else .ok (nextindFromLead s i n l)

/-- `_nextind_str(s, i::Int)`, `base/strings/string.jl:276-306`; this is
`nextind(s::String, i::Int)` (`:273`). -/
def nextind (s : JStr) (i : JInt64) : SJl JInt64 :=
  if i.val = 0 then .ok (ix 1)
  else
    let n := ncodeunits s
    if !betweenI i (ix 1) n then .error boundsErr
    else
      let l := cu s i
      if !between l 0x80 0xf7 then .ok (i + ix 1)
      else nextindContinued s i n l

/-- `lastindex(s::String) = thisind(s, ncodeunits(s))`, `base/strings/string.jl:249`.
It cannot throw: `thisind(s, n)` is in bounds or `n = 0`. -/
def lastindex (s : JStr) : JInt64 :=
  match thisind s (ncodeunits s) with
  | .ok j => j
  | .error _ => ix 0

/-- `iterate_continued(s, i, u)`, `base/strings/string.jl:517-538`. -/
def iterateContinued (s : JStr) (i : JInt64) (u : UInt32) : UInt32 × JInt64 :=
  if u < 0xc0000000 then (u, i + ix 1)
  else
    let n := ncodeunits s
    let i := i + ix 1
    if i.val > n.val then (u, i)
    else
      let b := cu s i
      if !isCont b then (u, i)
      else
        let u := u ||| (b.toUInt32 <<< 16)
        let i := i + ix 1
        if decide (i.val > n.val) || decide (u < 0xe0000000) then (u, i)
        else
          let b := cu s i
          if !isCont b then (u, i)
          else
            let u := u ||| (b.toUInt32 <<< 8)
            let i := i + ix 1
            if decide (i.val > n.val) || decide (u < 0xf0000000) then (u, i)
            else
              let b := cu s i
              if !isCont b then (u, i)
              else (u ||| b.toUInt32, i + ix 1)

/-- `iterate(s::String, i::Int)`, `base/strings/string.jl:508-514`.
`(i % UInt) - 1 < ncodeunits(s)` is a wrapping UInt64 subtraction followed by
Julia's exact mixed signed/unsigned comparison. -/
def iterate (s : JStr) (i : JInt64) : Option (UInt32 × JInt64) :=
  if !decide ((JInt.rem .u64 i - JInt.lit .u64 1).val < (ncodeunits s).val) then none
  else
    let b := cu s i
    let u := b.toUInt32 <<< 24
    if !between b 0x80 0xf7 then some (u, i + ix 1)
    else some (iterateContinued s i u)

/-- `getindex_continued(s, i, u)`, `base/strings/string.jl:548-573`. -/
def getindexContinued (s : JStr) (i : JInt64) (u : UInt32) : SJl UInt32 :=
  if u < 0xc0000000 then
    if isvalidAt s i then .ok u else .error (.stringIndexError i.val)
  else .ok (iterateContinued s i u).1

/-- `getindex(s::String, i::Int)`, `base/strings/string.jl:540-545`. -/
def getindex (s : JStr) (i : JInt64) : SJl UInt32 := do
  let b ← codeunit s i
  let u := b.toUInt32 <<< 24
  if !between b 0x80 0xf7 then pure u else getindexContinued s i u


/-- `getindex(s::String, r::UnitRange{Int})`, `base/strings/string.jl:580-595`, for
`r = i:j`. `checked = false` models a call under `@inbounds`, which skips the
`@boundscheck` block. `isempty(r)` is `j < i`. -/
def getindexRange (s : JStr) (i j : JInt64) (checked : Bool := true) : SJl JStr :=
  if j.val < i.val then .ok JStr.empty
  else
    let chk : SJl Unit :=
      if !checked then .ok ()
      else if !(decide (1 ≤ i.val) && decide (j.val ≤ (ncodeunits s).val)) then .error boundsErr
      else if !isvalidAt s i then .error (.stringIndexError i.val)
      else if !isvalidAt s j then .error (.stringIndexError j.val)
      else .ok ()
    match chk with
    | .error e => .error e
    | .ok () =>
      match nextind s j with
      | .error e => .error e
      | .ok j' =>
        let j := j' - ix 1
        let n := JInt.rem .u64 (j - i + ix 1)
        .ok (s.slice (i.val - 1).toNat n.val.toNat)

/-- The loops of `_length_continued`, `base/strings/string.jl:635-658`. The state
is the head of the inner `while` loop, before `(i += 1) ≤ n`; `b` is the byte
read last. The first argument is `n - i`; every path back to the head passes
through the increment, and at `0` the test `(i += 1) ≤ n` fails. -/
def lenLoop (s : JStr) (n : JInt64) : Nat → JInt64 → UInt8 → JInt64 → JInt64
  | 0, _, _, c => c
  | k + 1, i, b, c =>
    let i := i + ix 1
    if !(decide (0xc0 ≤ b) && decide (b ≤ 0xf7)) then lenLoop s n k i (cu s i) c
    else
      let l := b
      let b := cu s i
      let x := isCont b
      let c := c - bInt x
      if !(x && decide (l ≥ 0xe0)) then lenLoop s n k i b c
      else
        match k with
        | 0 => c
        | k + 1 =>
          let i := i + ix 1
          let b := cu s i
          let x := isCont b
          let c := c - bInt x
          if !(x && decide (l ≥ 0xf0)) then lenLoop s n k i b c
          else
            match k with
            | 0 => c
            | k + 1 =>
              let i := i + ix 1
              let b := cu s i
              let c := c - bInt (isCont b)
              lenLoop s n k i b c

/-- `_length_continued(s, i, n, c)`, `base/strings/string.jl:635-658`. -/
def lengthContinued (s : JStr) (i n c : JInt64) : JInt64 :=
  if !decide (i.val < n.val) then c
  else lenLoop s n (n.val - i.val).toNat i (cu s i) c

/-- `length(s::String)`, `base/strings/string.jl:598-600`. -/
def length (s : JStr) : JInt64 :=
  lengthContinued s (ix 1) (ncodeunits s) (ncodeunits s)

/-- `length(s::String, i::Int, j::Int)` = `_length(s, i, j)`,
`base/strings/string.jl:607-624`. -/
def lengthRange (s : JStr) (i j : JInt64) : SJl JInt64 :=
  let n := ncodeunits s
  if !(decide (0 < i.val) && decide (i.val ≤ (n + ix 1).val)) then .error boundsErr
  else if !(decide (0 ≤ j.val) && decide (j.val < (n + ix 1).val)) then .error boundsErr
  else if j.val < i.val then .ok (ix 0)
  else
    match thisind s i with
    | .error e => .error e
    | .ok i' =>
      let c := j - i' + bInt (decide (i'.val = i.val))
      .ok (lengthContinued s i' j c)

/-- `collect(s)` by repeated `iterate`, starting at `firstindex(s) = 1`. The bound
is `n + 1`: every step increases the state by at least one and `iterate`
returns `nothing` once the state exceeds `n` (see `iterTrace_collect`). -/
def collectFrom (s : JStr) : Nat → JInt64 → List (UInt32 × JInt64)
  | 0, _ => []
  | k + 1, i =>
    match iterate s i with
    | none => []
    | some (c, j) => (c, i) :: collectFrom s k j

def collectPairs (s : JStr) : List (UInt32 × JInt64) :=
  collectFrom s (s.bytes.length + 1) (ix 1)

/-- `collect(s)`: the characters. -/
def chars (s : JStr) : List UInt32 := (collectPairs s).map (·.1)

/-- `[i for i in a:ncodeunits(s) if isvalid(s, i)]`; the first argument counts the
remaining positions. -/
def validFrom (s : JStr) : Nat → JInt64 → List Int
  | 0, _ => []
  | k + 1, i => if isvalidAt s i then i.val :: validFrom s k (i + ix 1) else validFrom s k (i + ix 1)

/-- The valid indices `1 ≤ i ≤ ncodeunits(s)` in increasing order. -/
def validIndices (s : JStr) : List Int := validFrom s s.bytes.length (ix 1)

end JuliaLean.Strings

namespace JuliaLean.Strings

class AsciiCodeUnitOps where
  range : List UInt8 → Int → Int → Bool
  chunks : Int → List UInt8 → Int → Nat → Int → Bool

section
variable [AsciiCodeUnitOps]
local notation "isasciiRange" => AsciiCodeUnitOps.range
local notation "isasciiChunksLoop" => AsciiCodeUnitOps.chunks

/-- `memcmp` sign over the first `len` bytes. -/
def memcmpSign : List UInt8 → List UInt8 → Nat → Int
  | _, _, 0 => 0
  | a :: as, b :: bs, k + 1 => if a < b then -1 else if b < a then 1 else memcmpSign as bs k
  | _, _, _ => 0

/-- `cmp(a::String, b::String)`, `base/strings/string.jl:232-236`. -/
def cmp (a b : JStr) : Int :=
  let c := memcmpSign a.bytes b.bytes (min a.bytes.length b.bytes.length)
  if c < 0 then -1 else if c > 0 then 1
  else if a.bytes.length < b.bytes.length then -1
  else if b.bytes.length < a.bytes.length then 1 else 0

/-- `_string_n(n)`: a fresh String of `n` bytes (`jl_alloc_string`) filled by
the caller with the bytes `fill ()`. The model machine allocates any size below
`2^62` bytes and throws `OutOfMemoryError` otherwise. -/
def stringN (n : Nat) (fill : Unit → List UInt8) : SJl JStr :=
  if n < 2 ^ 62 then
    let bs := fill ()
    if h : bs.length < 2 ^ 62 then .ok ⟨bs, h⟩ else .error .outOfMemory
  else .error .outOfMemory

-- placed here to break an import cycle with strings/substring
/-- `repeat(s::Union{String, SubString{String}}, r::Integer)`,
`base/strings/substring.jl:289-307`, for `r::Int`. `typemax(UInt) ÷ UInt(n)` and
`n*r` are UInt64 operations; the copy loop stores copy `i` at offset `i*n`. -/
def repeatStr (s : JStr) (r : JInt64) : SJl JStr :=
  if r.val < 0 then .error (.jl (.argumentError "can't repeat a string r times"))
  else
    let r := JInt.rem .u64 r
    if r.val = 0 then .ok JStr.empty
    else if r.val = 1 then .ok s
    else
      let n := s.bytes.length
      if n = 0 then .ok JStr.empty
      else if r.val > (JInt.typemax .u64).val / n then .error .outOfMemory
      else
        let size := (r * JInt.lit .u64 n).val.toNat
        stringN size fun _ => (List.replicate r.val.toNat s.bytes).flatten

/-- `repeat(c::AbstractChar, r::Integer)`, `base/strings/string.jl:682-715`,
for `c::Char`, `r::Int`. -/
def repeatChar (c : UInt32) (r : JInt64) : SJl JStr :=
  if r.val < 0 then .error (.jl (.argumentError "can't repeat a character r times"))
  else
    let r := JInt.rem .u64 r
    if r.val = 0 then .ok JStr.empty
    else
      let u := bswap32 c
      let n := 4 - clz32 (u ||| 0xff) / 8
      if r.val > (JInt.typemax .u64).val / n then .error .outOfMemory
      else
        let size := (r * JInt.lit .u64 n).val.toNat
        let unit := [u.toUInt8, (u >>> 8).toUInt8, (u >>> 16).toUInt8, (u >>> 24).toUInt8].take n
        stringN size fun _ => (List.replicate r.val.toNat unit).flatten

/-- `isascii(s::String) = isascii(codeunits(s))`, `base/strings/string.jl:665`,
`base/strings/basic.jl:645-653`. -/
def isascii (s : JStr) : Bool :=
  let l : Int := s.bytes.length
  if l < 1536 then isasciiRange s.bytes 1 l
  else isasciiChunksLoop 1024 s.bytes l (s.bytes.length / 1024 + 1) 1

/-- `state_shifts`, `base/strings/string.jl:377`. -/
def dfaShifts : List Nat := [0, 4, 10, 14, 18, 24, 8, 20, 12, 26]

/-- `character_classes`, `base/strings/string.jl:379-394`, by byte value. -/
def dfaClass (b : UInt8) : Nat :=
  let x := b.toNat
  if x < 0x80 then 0 else if x < 0x90 then 1 else if x < 0xa0 then 9
  else if x < 0xc0 then 7 else if x < 0xc2 then 8 else if x < 0xe0 then 2
  else if x = 0xe0 then 10 else if x = 0xed then 4 else if x < 0xf0 then 3
  else if x = 0xf0 then 11 else if x < 0xf4 then 6 else if x = 0xf4 then 5 else 8

/-- `state_arrays`, `base/strings/string.jl:397-408`, row = class, column = state. -/
def dfaStates : List (List Nat) :=
  [[0, 1, 2, 2, 2, 2, 2, 2, 2, 2],
   [2, 2, 2, 1, 3, 2, 3, 2, 4, 4],
   [3, 3, 2, 2, 2, 2, 2, 2, 2, 2],
   [4, 4, 2, 2, 2, 2, 2, 2, 2, 2],
   [6, 6, 2, 2, 2, 2, 2, 2, 2, 2],
   [9, 9, 2, 2, 2, 2, 2, 2, 2, 2],
   [8, 8, 2, 2, 2, 2, 2, 2, 2, 2],
   [2, 2, 2, 1, 3, 3, 2, 4, 4, 2],
   [2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
   [2, 2, 2, 1, 3, 2, 3, 4, 4, 2],
   [5, 5, 2, 2, 2, 2, 2, 2, 2, 2],
   [7, 7, 2, 2, 2, 2, 2, 2, 2, 2]]

/-- `class_row[i]`, `base/strings/string.jl:411-422`: OR of
`UInt32(state_shifts[next+1]) << state_shifts[j]` over the ten states. -/
def dfaRow (cls : Nat) : UInt32 :=
  ((List.range 10).map fun j =>
    (UInt32.ofNat (dfaShifts.getD ((dfaStates.getD cls []).getD j 0) 0)) <<<
      (UInt32.ofNat (dfaShifts.getD j 0))).foldl (· ||| ·) 0

/-- `_utf_dfa_step(state, byte)`, `base/strings/string.jl:433`, with
`_UTF8_DFA_TABLE[byte+1] = class_row[class(byte)+1]` (`:424`). -/
def dfaStep (state : UInt32) (b : UInt8) : UInt32 := (dfaRow (dfaClass b) >>> state) &&& 0x1e

/-- `_isvalid_utf8_dfa(state, bytes, first, last)`, `base/strings/string.jl:435-440`. -/
def dfaRun (state : UInt32) (bs : List UInt8) (a b : Int) : UInt32 :=
  ((bs.drop (a - 1).toNat).take (b - a + 1).toNat).foldl dfaStep state

/-- `_find_nonascii_chunk`, `base/strings/string.jl:442-451`. Bound as for `isascii`. -/
def findNonasciiLoop (cs : Int) (bs : List UInt8) (last : Int) : Nat → Int → Option Int
  | 0, _ =>
    let n := last - cs + 1
    if !isasciiRange bs n last then some n else none
  | k + 1, n =>
    if n ≤ last - cs then
      if !isasciiRange bs n (n + cs - 1) then some n else findNonasciiLoop cs bs last k (n + cs)
    else
      let n := last - cs + 1
      if !isasciiRange bs n last then some n else none

/-- The inner ASCII-skipping loop of `_byte_string_classify_nonascii`,
`base/strings/string.jl:484-488`. Bound: remaining chunks. -/
def classifySkip (bs : List UInt8) (last : Int) (state : UInt32) : Nat → Int → Int → Int × Int
  | 0, start, stop => (start, stop)
  | k + 1, start, stop =>
    if state == 0x4 then
      if !isasciiRange bs start stop then (start, stop)
      else
        let start := start + 256
        if !(start ≤ last) then (start, stop)
        else classifySkip bs last state k start (min last (stop + 256))
    else (start, stop)

/-- `_byte_string_classify_nonascii(bytes, first, last)`, `base/strings/string.jl:476-497`.
Each outer iteration advances `start` by at least 256, bounding the loop. -/
def classifyLoop (bs : List UInt8) (last : Int) : Nat → Int → Int → UInt32 → Nat
  | 0, _, _, state => if state == 0x4 then 2 else 0
  | k + 1, start, stop, state =>
    if start ≤ last then
      let (start, stop) := classifySkip bs last state (bs.length / 256 + 2) start stop
      let state := dfaRun state bs start stop
      if state == 10 then 0
      else classifyLoop bs last k (start + 256) (min last (stop + 256)) state
    else if state == 0x4 then 2 else 0

def classifyNonascii (bs : List UInt8) (first last : Int) : Nat :=
  classifyLoop bs last (bs.length / 256 + 2) first (min last (first + 255)) 0x4

/-- `byte_string_classify(bytes)`, `base/strings/string.jl:462-474`. -/
def byteStringClassify (bs : List UInt8) : Nat :=
  let n : Int := bs.length
  if n > 1536 then
    match findNonasciiLoop 1024 bs n (bs.length / 1024 + 1) 1 with
    | none => 1
    | some start => classifyNonascii bs start n
  else if isasciiRange bs 1 n then 1
  else classifyNonascii bs 1 n

/-- `isvalid(s::String) = isvalid(String, codeunits(s))`, `base/strings/string.jl:499-502`. -/
def isvalidStr (s : JStr) : Bool := byteStringClassify s.bytes != 0

end
end JuliaLean.Strings


/-!
# `String(v::Vector{UInt8})` and arrays that share memory

A small heap model of `Memory{UInt8}` objects, `Vector{UInt8}` arrays and
`String` objects, enough to follow `String(v::Vector{UInt8})`
(`base/strings/string.jl:114-127`) and `jl_genericmemory_to_string`
(`src/genericmemory.c:189-215`) on master `bbfa0ce4150`.

* A `Memory` whose `how` is `JL_GENERICMEMORY_STRINGOWNED` stores the bytes of a
  `String` object (`owner`); this is what `Base.StringMemory(n) =
  unsafe_wrap(Memory{UInt8}, _string_n(n))` creates (`base/iobuffer.jl:167`),
  and what `StringVector(n)` and `take!(::IOBuffer)` return vectors over.
* A `String` object either lives in such a memory (its first `len` bytes) or
  owns a copy of its bytes.
* An operation that would throw (an out-of-bounds index) leaves the heap
  unchanged; the property below is about operations that succeed.
-/

namespace JuliaLean.Transcode

/-- `GC_MAX_SZCLASS = 2032 - sizeof(void*)` on 64-bit platforms (`src/julia_internal.h:675`). -/
def gcMaxSzclass : Nat := 2032 - 8

structure Mem where
  data : List UInt8
  /-- The owning String object when `how == JL_GENERICMEMORY_STRINGOWNED`. -/
  owner : Option Nat
  deriving DecidableEq, Repr

/-- A String object: its length, and the memory holding its bytes or its own copy. -/
structure Str where
  len : Nat
  mem : Option Nat
  own : List UInt8
  deriving DecidableEq, Repr

/-- A `Vector{UInt8}`: its memory, the offset of its first element in that memory, its length. -/
structure Vec where
  mem : Nat
  off : Nat
  len : Nat
  deriving DecidableEq, Repr

structure Heap where
  mems : List Mem
  strs : List Str
  vecs : List Vec
  /-- The Strings returned to the program by `String(v)`. -/
  visible : List Nat
  deriving DecidableEq, Repr

def Heap.empty : Heap := ⟨[], [], [], []⟩

/-- The bytes of String object `i`. -/
def Heap.content (h : Heap) (i : Nat) : Option (List UInt8) := do
  let s ← h.strs[i]?
  match s.mem with
  | none => pure s.own
  | some m => do let mm ← h.mems[m]?; pure (mm.data.take s.len)

inductive Op where
  /-- `v = Base.StringVector(n)`: a vector over a fresh string-owned memory. -/
  | stringVector (n : Nat)
  /-- `w = vec(reshape(v, 1, :))`: a new vector over the same memory as `v`. -/
  | share (v : Nat)
  /-- `v[i] = x`. -/
  | setindex (v i : Nat) (x : UInt8)
  /-- `resize!(v, n)` with `n ≤ length(v)`. -/
  | shrink (v n : Nat)
  /-- `String(v)`. -/
  | string (v : Nat)
  deriving DecidableEq, Repr

/-- A new String object owning a copy of `bs`, made visible. -/
def Heap.copyStr (h : Heap) (bs : List UInt8) : Heap × Nat :=
  ({ h with strs := h.strs ++ [⟨bs.length, none, bs⟩] }, h.strs.length)

/-- `jl_genericmemory_to_string(m, len)` for `len > 0`, `src/genericmemory.c:189-215`. -/
def Heap.memToString (h : Heap) (m len : Nat) : Heap × Nat :=
  match h.mems[m]? with
  | none => h.copyStr []
  | some mm =>
    let mlength := mm.data.length
    match mm.owner with
    | some o =>
      if decide (mlength + 8 + 1 ≤ gcMaxSzclass) = decide (len + 8 + 1 ≤ gcMaxSzclass) then
        -- `jl_string_data(o)[len] = '\0'; *(size_t*)o = len; return o;`
        let data := if len < mlength then mm.data.set len 0 else mm.data
        ({ h with mems := h.mems.set m { mm with data := data },
                  strs := h.strs.modify o fun s => { s with len := len } }, o)
      else h.copyStr (mm.data.take len)
    | none => h.copyStr (mm.data.take len)

/-- One operation; one that would throw changes nothing. -/
def Heap.step (h : Heap) : Op → Heap
  | .stringVector n =>
    let s := h.strs.length
    let m := h.mems.length
    { h with strs := h.strs ++ [⟨n, some m, []⟩], mems := h.mems ++ [⟨List.replicate n 0, some s⟩],
             vecs := h.vecs ++ [⟨m, 0, n⟩] }
  | .share v =>
    match h.vecs[v]? with
    | none => h
    | some vv => { h with vecs := h.vecs ++ [vv] }
  | .setindex v i x =>
    match h.vecs[v]? with
    | none => h
    | some vv =>
      if 1 ≤ i ∧ i ≤ vv.len then
        match h.mems[vv.mem]? with
        | none => h
        | some mm => { h with mems := h.mems.set vv.mem { mm with data := mm.data.set (vv.off + i - 1) x } }
      else h
  | .shrink v n =>
    match h.vecs[v]? with
    | none => h
    | some vv => if n ≤ vv.len then { h with vecs := h.vecs.set v { vv with len := n } } else h
  | .string v =>
    match h.vecs[v]? with
    | none => h
    | some vv =>
      -- `base/strings/string.jl:115-122`
      let (h', i) :=
        if vv.len = 0 then h.copyStr []
        else if vv.off = 0 then h.memToString vv.mem vv.len
        else match h.mems[vv.mem]? with
          | none => h.copyStr []
          | some mm => h.copyStr ((mm.data.drop vv.off).take vv.len)
      -- `setfield!(v, :size, (0,)); setfield!(v, :ref, memoryref(Memory{UInt8}()))`
      { h' with mems := h'.mems ++ [⟨[], none⟩],
                vecs := h'.vecs.set v ⟨h'.mems.length, 0, 0⟩,
                visible := h'.visible ++ [i] }

def Heap.run (h : Heap) (ops : List Op) : Heap := ops.foldl Heap.step h


end JuliaLean.Transcode

section
variable [JuliaLean.Strings.AsciiCodeUnitOps]

/-! Coverage models for `base/strings/string.jl` at Julia `bbfa0ce4150`. -/

namespace JuliaLean.StringsCovA.String

open JuliaLean JuliaLean.Strings

structure View where bytes : List UInt8

def stringViewCtor (oneBased concrete : Bool) (bytes : List UInt8) : Jl View :=
  if !oneBased then .error (.argumentError "one-based indexing required")
  else if !concrete then .error (.argumentError "concrete type required") else .ok ⟨bytes⟩
def stringIndexErr (i : Int) : SJl Unit := .error (.stringIndexError i)
def showStringIndexError (i : Int) : String := "StringIndexError: invalid index [" ++ toString i ++ "]"
def between (b lo hi : Int) : Bool := decide (lo ≤ b) && decide (b ≤ hi)

def stringAbstractVector (v : List UInt8) := v
def unsafeTakeString (m : List UInt8) := m
def takeString (v : List UInt8) : List UInt8 × List UInt8 := (v, [])
def unsafeStringLength (memory : List UInt8) (len : Nat) : List UInt8 := memory.take len
def unsafeStringNul (memory : List UInt8) : List UInt8 := memory.takeWhile (· != 0)
def stringN (n : Nat) : List UInt8 := List.replicate n 0
def stringAbstract (render : α → List UInt8) (s : α) := render s
def stringSymbol (memory : List UInt8) := unsafeStringNul memory
def unsafeWrapMemory (s : List UInt8) := s
def unsafeWrapVector (s : List UInt8) := s
def vectorCodeUnits (s : List UInt8) := s
def vectorString (s : List UInt8) := s
def arrayString (s : List UInt8) := s
def stringCodeUnits (s : List UInt8) := s
def pointer (address : Nat) := address
def pointerAt (address : Nat) (i : Int) : Int := address + i - 1
def ncodeunits (s : List UInt8) := s.length
def codeunitType : Nat := 8
def codeunit (s : List UInt8) (i : Int) : Jl UInt8 :=
  if 1 ≤ i ∧ i ≤ s.length then .ok (s.getD (i.toNat - 1) 0) else .error .boundsError

def memcmp (a b : List UInt8) (len : Nat) : Int :=
  Strings.memcmpSign a b len
def memcmpMin (a b : List UInt8) := memcmp a b (min a.length b.length)
def eqString (a b : List UInt8) := a == b
def typeminType : List UInt8 := []
def typeminValue : List UInt8 := typeminType
def thisind (s : JStr) (i : JInt64) := Strings.thisind s i
def thisindContinued (s : JStr) (i : JInt64) := Strings.thisindContinued s i
def nextind (s : JStr) (i : JInt64) := Strings.nextind s i
def nextindContinued (s : JStr) (i n : JInt64) (l : UInt8) := Strings.nextindContinued s i n l

def utfDfaStep := Strings.dfaStep
def isvalidUtf8Dfa := Strings.dfaRun
def findNonascii (chunk : Int) (bytes : List UInt8) (last : Int) :=
  Strings.findNonasciiLoop chunk bytes last bytes.length 1
def byteClassifyString (s : JStr) := Strings.byteStringClassify s.bytes
def byteClassifyVector (bytes : List UInt8) := Strings.byteStringClassify bytes
def byteClassifyNonascii (bytes : List UInt8) (first last : Int) := Strings.classifyNonascii bytes first last
def isvalidBytes (bytes : List UInt8) := Strings.byteStringClassify bytes != 0
def isvalidString (s : JStr) := Strings.isvalidStr s
def isvalidAbstract (s : JStr) := Strings.isvalidStr s
def isValidContinuation (c : UInt8) := Strings.isCont c

def iterateContinued := Strings.iterateContinued
def getindex (s : JStr) (i : JInt64) := Strings.getindex s i
def getindexContinued := Strings.getindexContinued
def getindexAbstractRange (s : JStr) (i j : JInt64) := Strings.getindexRange s i j
def getindexUnitRange (s : JStr) (i j : JInt64) := Strings.getindexRange s i j
def lengthView (s : JStr) := Strings.length s
def lengthStringRange (s : JStr) (i j : JInt64) := Strings.lengthRange s i j
def lengthViewRange (s : JStr) (i j : JInt64) := Strings.lengthRange s i j
def lengthInternal (s : JStr) (i j : JInt64) := Strings.lengthRange s i j
def lengthContinued (s : JStr) (i n c : JInt64) := Strings.lengthContinued s i n c
def isasciiString (s : JStr) := Strings.isascii s
def repeatCharBit (c : UInt32) (r : JInt64) := Strings.repeatChar c r
def repeatCharInteger (c : UInt32) (r : JInt64) := Strings.repeatChar c r

end JuliaLean.StringsCovA.String

end

section
variable [JuliaLean.Strings.AsciiCodeUnitOps]

namespace JuliaLean.StringsCovA.StringFaithful

open JuliaLean JuliaLean.Strings
def lastindexM (s : JStr) := Strings.lastindex s

end JuliaLean.StringsCovA.StringFaithful

end

section
variable [JuliaLean.Strings.AsciiCodeUnitOps]

namespace JuliaLean.StringsCovA.StringRebuilt

open JuliaLean JuliaLean.Strings

inductive StorageCall where
  | requireOneBased | isConcrete | allocate | copyTo | unsafeTake
  | isEmpty | genericMemoryToString | stringVector | convertInt | nullCheck
  | pcharToString | cstrToString | allocString | printToString | unsafeConvert
  | stringToMemory | wrapArray | codeunits | copyVector | readParent
  | pointer | preserve | unsafeLoad | invokeMemcmp | memcmp | delegate
  deriving Repr, DecidableEq

structure StorageRun where
  bytes : List UInt8
  calls : List StorageCall
  sourceEmptied : Bool := false
  deriving Repr, DecidableEq

def abstractVectorRun (bytes : List UInt8) : StorageRun :=
  ⟨bytes, [.allocate, .copyTo, .unsafeTake], false⟩
def unsafeTakeRun (bytes : List UInt8) : StorageRun :=
  if bytes.isEmpty then ⟨[], [.isEmpty], false⟩ else ⟨bytes, [.isEmpty, .genericMemoryToString], false⟩
def takeStringRun (bytes : List UInt8) : StorageRun :=
  ⟨bytes, [.stringVector], true⟩
def unsafeLengthRun (isNull : Bool) (convertOk : Bool) (bytes : List UInt8) (count : Nat) :
    Except StorageCall StorageRun :=
  if isNull then .error .nullCheck else if !convertOk then .error .convertInt
  else .ok ⟨bytes.take count, [.nullCheck, .convertInt, .pcharToString], false⟩
def unsafeNulRun (isNull : Bool) (bytes : List UInt8) : Except StorageCall StorageRun :=
  if isNull then .error .nullCheck
  else .ok ⟨bytes.takeWhile (· != 0), [.nullCheck, .cstrToString], false⟩
def allocRun (convertOk : Bool) (count : Nat) : Except StorageCall StorageRun :=
  if !convertOk then .error .convertInt else .ok ⟨List.replicate count 0, [.convertInt, .allocString], false⟩
def copyRun (calls : List StorageCall) (bytes : List UInt8) : StorageRun := ⟨bytes, calls, false⟩
inductive CodeunitType where | uint8

def lastindexModel (string : JStr) := Strings.lastindex string

def findNonasciiFrom (chunk : Int) (bytes : List UInt8) (first last : Int) :=
  Strings.findNonasciiLoop chunk bytes last (bytes.length + 1) first

def convertIndex {indexType : IntTy} (index : JInt indexType) : SJl JInt64 :=
  match JInt.convert (IntTy.i64.name) .i64 index.val with
  | .ok converted => .ok converted
  | .error error => .error (.jl error)

def getindexAbstractRangeRun {firstType lastType : IntTy}
    (string : JStr) (first : JInt firstType) (last : JInt lastType) : SJl JStr := do
  let first ← convertIndex first
  let last ← convertIndex last
  String.getindexUnitRange string first last
end JuliaLean.StringsCovA.StringRebuilt

end

namespace JuliaLean.ParsePrint.IntParse

open JuliaLean JuliaLean.ParsePrint

abbrev Byte := JInt .u8
abbrev Bytes := List Byte

/-- `codeunit(s, i)` for an in-bounds one-based index. -/
def cu (s : Bytes) (i : Int) : Byte := s.getD (i - 1).toNat (JInt.lit .u8 0)

/-- The code unit as a natural number. -/
def cuN (s : Bytes) (i : Int) : Nat := (cu s i).val.toNat

/-- `ncodeunits(s)`. -/
def ncu (s : Bytes) : Int := s.length

/-- A byte literal. -/
def byte (n : Nat) : Byte := JInt.lit .u8 n
/-- `iterate(s::String, i)`, `base/strings/string.jl:504-538`: the raw `Char`
starting at `i` and the index after it. -/
def iterate (s : Bytes) (i : Int) : Nat × Int :=
  let n := ncu s
  let b := cuN s i
  let u := b * 2 ^ 24
  if ¬ (0x80 ≤ b ∧ b ≤ 0xf7) then (u, i + 1)
  else if u < 0xc0000000 then (u, i + 1)
  else
    let i := i + 1
    if i > n then (u, i) else
    let b := cuN s i
    if Nat.land b 0xc0 != 0x80 then (u, i) else
    let u := Nat.lor u (b * 2 ^ 16)
    let i := i + 1
    if i > n ∨ u < 0xe0000000 then (u, i) else
    let b := cuN s i
    if Nat.land b 0xc0 != 0x80 then (u, i) else
    let u := Nat.lor u (b * 2 ^ 8)
    let i := i + 1
    if i > n ∨ u < 0xf0000000 then (u, i) else
    let b := cuN s i
    if Nat.land b 0xc0 != 0x80 then (u, i) else
    (Nat.lor u b, i + 1)

/-- `s[i]` for a valid in-bounds index: the same decoding as `iterate`,
`base/strings/string.jl:540-560`. -/
def getChar (s : Bytes) (i : Int) : Nat := (iterate s i).1

/-- `thisind(s, i)` for `1 ≤ i ≤ ncodeunits(s)`, `base/strings/string.jl:252-271`. -/
def thisind (s : Bytes) (i : Int) : Int :=
  let isCont (k : Int) := Nat.land (cuN s k) 0xc0 == 0x80
  if ¬ (isCont i ∧ i - 1 > 0) then i
  else if 0xc0 ≤ cuN s (i - 1) ∧ cuN s (i - 1) ≤ 0xf7 then i - 1
  else if ¬ (isCont (i - 1) ∧ i - 2 > 0) then i
  else if 0xe0 ≤ cuN s (i - 2) ∧ cuN s (i - 2) ≤ 0xf7 then i - 2
  else if ¬ (isCont (i - 2) ∧ i - 3 > 0) then i
  else if 0xf0 ≤ cuN s (i - 3) ∧ cuN s (i - 3) ≤ 0xf7 then i - 3
  else i

end JuliaLean.ParsePrint.IntParse

namespace JuliaLean.ShellCmd

open JuliaLean

/-- `ncodeunits(s)`: the byte length. -/
def ncu (s : JS) : Nat := (s.map ncuC).sum

/-- `pairs(s)` of a string whose first character is at byte index `p`:
each character with its byte index. -/
def pairsFrom : Nat → JS → List (Nat × JC)
  | _, [] => []
  | p, c :: cs => (p, c) :: pairsFrom (p + ncuC c) cs

/-- `isvalid(s, i)`: `i` is the index of a character of `s`. -/
def isStart (s : JS) (i : Int) : Bool := (pairsFrom 1 s).any (fun q => (q.1 : Int) == i)

/-- `lastindex(s)`: the index of the last character, `0` for `""`. -/
def lastindex (s : JS) : Int := ((pairsFrom 1 s).getLast?.map (fun q => (q.1 : Int))).getD 0

end JuliaLean.ShellCmd
