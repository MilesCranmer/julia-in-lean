import JuliaLean.Core
import JuliaLean.Strings.Basic

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
def unsafeStringNul (null : Int) (pointerToCString : Int → JString)
    (p : Int) : StringResult JString :=
  if p == null then .error (.jl (.argumentError "cannot convert NULL to string"))
  else .ok (pointerToCString p)

/--
Julia source: base/strings/string.jl:184-185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval _string_n(n::Integer) = $(Expr(:foreigncall, QuoteNode(:jl_alloc_string), Ref{String},
    :(Core.svec(Csize_t)), 1, QuoteNode((:ccall, _string_n_override, false)), :(convert(Csize_t, n))))
```
-/
def stringN {I : Type} (toCsize : I → StringResult Nat)
    (allocateString : Nat → StringResult JString) (n : I) : StringResult JString := do
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
def stringSymbol {α : Type} (unsafeConvert : α → Int) (null : Int)
    (pointerToCString : Int → JString) (s : α) : StringResult JString :=
  unsafeStringNul null pointerToCString (unsafeConvert s)

/--
Julia source: base/strings/string.jl:195-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_wrap(::Type{Memory{UInt8}}, s::String) = ccall(:jl_string_to_genericmemory, Ref{Memory{UInt8}}, (Any,), s)
```
-/
def unsafeWrapMemory (stringToMemory : JString → Memory) (s : JString) : Memory :=
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
      pure ()
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
  else lengthCountLoop codeunit s n (n.val - i.val).toNat i (codeunit s i) c

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
