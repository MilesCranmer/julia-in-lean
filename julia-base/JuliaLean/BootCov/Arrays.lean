import JuliaLean.BootCov.IntConv
import JuliaLean.ReinterpretArrays.Reshape

/-!
Memory, `MemoryRef`, `Array`, `SimpleVector` and `Symbol` primitives of
`base/boot.jl` and `base/essentials.jl` (master `bbfa0ce4150`).

A memory is its list of slots (`none` is an undefined slot); a reference is a
memory and a 0-based element offset; an array is a reference and its
dimensions. `maxLen` is the largest element count the runtime can allocate for
the element type (`jl_alloc_genericmemory` rejects counts with
`nel >= MAXINTVAL-1` or a byte size that overflows).
-/

namespace JuliaLean.BootCov.Arrays

open JuliaLean
open JuliaLean.BootCov
open JuliaLean.BootCov.IntConv

abbrev Mem := List (Option JVal)

structure MRef where
  mem : Mem
  /-- 0-based offset of the referenced element. -/
  off : Nat

structure Arr where
  ref : MRef
  dims : List JInt64

/-- `memorynew(self, m)` (`jl_alloc_genericmemory`): `m` is read as `size_t`. -/
def memorynew (maxLen : Nat) (m : JInt64) : R Mem :=
  let nel := wrapInt .u64 m.val
  if nel > maxLen then .error (.argument "invalid GenericMemory size")
  else .ok (List.replicate nel.toNat none)

/-- `GenericMemory{kind,T,addrspace}(undef, m)`, `(undef, (m,))` and `()`,
`base/boot.jl:762-765`. -/
def memoryUndef (maxLen : Nat) (m : JInt64) : R Mem := memorynew maxLen m
def memoryUndefTuple (maxLen : Nat) (d : JInt64) : R Mem := memoryUndef maxLen d
def memoryEmpty (maxLen : Nat) : R Mem := memoryUndef maxLen (JInt.lit .i64 0)

/-- `memoryrefnew(mem)`: a reference to the first slot. -/
def memoryrefnew1 (mem : Mem) : MRef := ⟨mem, 0⟩

/-- `memoryrefnew(mem, i, true)`, `src/builtins.c`: `i - 1` read as `size_t` must be
below the length. -/
def memoryrefnewMem (mem : Mem) (i : JInt64) : R MRef :=
  let k := wrapInt .u64 (i.val - 1)
  if k ≥ mem.length then .error .bounds else .ok ⟨mem, k.toNat⟩

/-- `memoryrefnew(ref, i, true)`: the shifted offset, computed modulo `2^64`, must be
below the length. -/
def memoryrefnewRef (r : MRef) (i : JInt64) : R MRef :=
  let k := wrapInt .u64 (r.off + wrapInt .u64 (i.val - 1))
  if k ≥ r.mem.length then .error .bounds else .ok ⟨r.mem, k.toNat⟩

/-- `memoryref(mem)`, `memoryref(mem, i::Integer)`, `memoryref(ref, i::Integer)` and the
`GenericMemoryRef` aliases, `base/boot.jl:768-773`: `Int(i)` converts first. -/
def memoryref1 (mem : Mem) : MRef := memoryrefnew1 mem
def memoryref2 (mem : Mem) (i : BuiltinInt) : R MRef := do
  let i ← ctor .i64 i
  memoryrefnewMem mem i
def memoryrefRef (r : MRef) (i : BuiltinInt) : R MRef := do
  let i ← ctor .i64 i
  memoryrefnewRef r i
def genericMemoryRef1 (mem : Mem) : MRef := memoryref1 mem
def genericMemoryRef2 (mem : Mem) (i : BuiltinInt) : R MRef := memoryref2 mem i
def genericMemoryRefRef (r : MRef) (i : BuiltinInt) : R MRef := memoryrefRef r i

/-- `new_as_memoryref(self, m) = memoryref(Memory(undef, m))`, `base/boot.jl:779`. -/
def newAsMemoryref (maxLen : Nat) (m : JInt64) : R MRef := do
  let mem ← memoryUndef maxLen m
  pure (memoryref1 mem)

/-! `Core.checked_dims` and `_checked_mul_dims` (`base/boot.jl:782-818`) are
`JuliaLean.ReinterpretArrays.checkedDims` and `checkedMulDims`. -/
open JuliaLean.ReinterpretArrays (checkedDims checkedMulDims)

/-- Read a shared-model result as a result of this area (`ArgumentError` stays one). -/
def ofJl {α : Type} : Jl α → R α
  | .ok a => .ok a
  | .error (.argumentError m) => .error (.argument m)
  | .error _ => .error (.error "unexpected exception")

/-- `Array{T,1}(undef, m)`, `base/boot.jl:821-824`. -/
def array1 (maxLen : Nat) (m : JInt64) : R Arr := do
  let mem ← memoryUndef maxLen m
  pure ⟨memoryref1 mem, [m]⟩
/-- `Array{T,2}(undef, m, n)`, `base/boot.jl:825-827`. -/
def array2 (maxLen : Nat) (m n : JInt64) : R Arr := do
  let p ← ofJl (checkedDims [m, n])
  let r ← newAsMemoryref maxLen p
  pure ⟨r, [m, n]⟩
/-- `Array{T,3}(undef, m, n, o)`, `base/boot.jl:828-830`. -/
def array3 (maxLen : Nat) (m n o : JInt64) : R Arr := do
  let p ← ofJl (checkedDims [m, n, o])
  let r ← newAsMemoryref maxLen p
  pure ⟨r, [m, n, o]⟩
/-- `Array{T,N}(undef, d::Vararg{Int,N})`, `base/boot.jl:831-833`. -/
def arrayN (maxLen : Nat) (d : List JInt64) : R Arr := do
  let p ← ofJl (checkedDims d)
  let r ← newAsMemoryref maxLen p
  pure ⟨r, d⟩

/-- Method selection among the four `Array{T,N}(undef, dims...)` methods. -/
def arrayUndef (maxLen : Nat) : List JInt64 → R Arr
  | [m] => array1 maxLen m
  | [m, n] => array2 maxLen m n
  | [m, n, o] => array3 maxLen m n o
  | d => arrayN maxLen d

/-- `Array{T,N}(undef, d::NTuple{N,Int})`, `base/boot.jl:835-838`: splat the tuple. -/
def arrayUndefTuple (maxLen : Nat) (d : List JInt64) : R Arr := arrayUndef maxLen d
/-- `Array{T}(undef, dims...)` and `Array{T}(undef, d::Tuple)`, `base/boot.jl:840-845`:
`N` is the number of dimensions. -/
def arrayTUndef (maxLen : Nat) (d : List JInt64) : R Arr := arrayUndef maxLen d
def arrayTUndefTuple (maxLen : Nat) (d : List JInt64) : R Arr := arrayUndefTuple maxLen d
/-- `Vector{T}() = Vector{T}(undef, 0)`, `base/boot.jl:847`. -/
def vectorEmpty (maxLen : Nat) : R Arr := array1 maxLen (JInt.lit .i64 0)

/-- The converting constructors `Array{T,N} where T`, `Array(A)`, `Array{T}(A)` and
`AbstractArray{T}(A)`, `base/boot.jl:849-854`: each calls the constructor with element
type `elt` and the source dimensionality `N`. `conv elt N` is that constructor. -/
def arrayFromAbstract {A B : Type} (conv : String → Nat → A → B) (eltS : String) (N : Nat)
    (x : A) : B := conv eltS N x
def arrayOf {A B : Type} (conv : String → Nat → A → B) (eltT : String) (N : Nat) (x : A) : B :=
  conv eltT N x
def arrayTOf {A B : Type} (conv : String → Nat → A → B) (T : String) (N : Nat) (x : A) : B :=
  conv T N x
def abstractArrayTOf {A B : Type} (conv : String → Nat → A → B) (T : String) (N : Nat)
    (x : A) : B := conv T N x

/-- `checkbounds(::Type{Bool}, A::Union{Array,Memory}, i::Int)`, `base/essentials.jl:385-388`:
`ult_int(bitcast(UInt, i - 1), bitcast(UInt, length(A)))`. -/
def checkboundsBool (len i : JInt64) : Bool :=
  decide ((JInt.rem .u64 (i - JInt.lit .i64 1)).val < (JInt.rem .u64 len).val)

/-- `checkbounds(A, I...)`, `base/essentials.jl:389-393`. -/
def checkbounds {α : Type} (check : α → Bool) (I : α) : R Unit :=
  if check I then .ok () else .error .bounds

/-- `default_access_order`, `base/essentials.jl:395-398`. -/
def defaultAccessOrder (atomic : Bool) : String := if atomic then "monotonic" else "not_atomic"

/-- `memoryrefget(r, order, boundscheck)` of a slot. -/
def memoryrefget (r : MRef) : R JVal :=
  match r.mem[r.off]? with
  | some (some v) => .ok v
  | some none => .error .undefRef
  | none => .error .bounds

/-- `memoryrefset!(r, x, order, boundscheck)`. -/
def memoryrefset (r : MRef) (x : JVal) : R MRef :=
  if r.off < r.mem.length then .ok ⟨r.mem.set r.off (some x), r.off⟩ else .error .bounds

/-- `getindex(A::GenericMemory, i::Int)`, `base/essentials.jl:400-404`. -/
def getindexMem (mem : Mem) (i : JInt64) : R JVal := do
  checkbounds (checkboundsBool (JInt.lit .i64 mem.length)) i
  memoryrefget ⟨mem, (i.val - 1).toNat⟩

/-- `getindex(A::GenericMemoryRef)`, `base/essentials.jl:406`. -/
def getindexRef (r : MRef) : R JVal := memoryrefget r

/-- `length(a::Array{T,1}) = size[1]` (`base/essentials.jl:1286`) and `size(a::Array)`
(line 12). -/
def lengthVec (a : Arr) : R JInt64 :=
  match a.dims with
  | m :: _ => .ok m
  | [] => .error .bounds
def sizeArr (a : Arr) : List JInt64 := a.dims

/-- `size(a::GenericMemory) = (getfield(a, :length),)`, `base/essentials.jl:14`. -/
def sizeMem (mem : Mem) : List Nat := [mem.length]

/-- `getindex(A::Array, i::Int)`, `base/essentials.jl:1063-1067`; `len = length(A)`. -/
def getindexArr (len : JInt64) (a : Arr) (i : JInt64) : R JVal := do
  checkbounds (checkboundsBool len) i
  memoryrefget ⟨a.ref.mem, a.ref.off + (i.val - 1).toNat⟩

/-- `setindex!(A::Array{Any}, x, i::Int)`, `base/essentials.jl:1069-1074`. -/
def setindexArr (len : JInt64) (a : Arr) (x : JVal) (i : JInt64) : R Arr := do
  checkbounds (checkboundsBool len) i
  let r ← memoryrefset ⟨a.ref.mem, a.ref.off + (i.val - 1).toNat⟩ x
  pure ⟨⟨r.mem, a.ref.off⟩, a.dims⟩

/-- `setindex!(A::Memory{Any}, x, i::Int)`, `base/essentials.jl:1075-1080`. -/
def setindexMem (mem : Mem) (x : JVal) (i : JInt64) : R Mem := do
  checkbounds (checkboundsBool (JInt.lit .i64 mem.length)) i
  let r ← memoryrefset ⟨mem, (i.val - 1).toNat⟩ x
  pure r.mem

/-- `setindex!(A::MemoryRef{T}, x)` (converting with `conv = convert(T, _)`) and
`setindex!(A::MemoryRef{Any}, x)`, `base/essentials.jl:1081-1082`. -/
def setindexRefT (conv : JVal → R JVal) (r : MRef) (x : JVal) : R MRef := do
  let x ← conv x
  memoryrefset r x
def setindexRefAny (r : MRef) (x : JVal) : R MRef := memoryrefset r x

/-! ## `SimpleVector`, `base/essentials.jl:1086-1144` -/

abbrev SVec := List (Option JVal)

/-- `getindex(v, i) = Core._svec_ref(v, i)`: `BoundsError` outside `1:length(v)`; an
undefined slot comes back as a null reference (`none`). -/
def svecRef (v : SVec) (i : Int) : R (Option JVal) :=
  if i < 1 ∨ i > v.length then .error .bounds else .ok (v[(i - 1).toNat]?.join)

def svecLength (v : SVec) : Nat := v.length
def svecFirstindex (_ : SVec) : Nat := 1
def svecLastindex (v : SVec) : Nat := svecLength v
/-- `iterate(v::SimpleVector, i=1) = (length(v) < i ? nothing : (v[i], i + 1))`. -/
def svecIterate (v : SVec) (i : Int := 1) : R (Option (Option JVal × Int)) :=
  if (svecLength v : Int) < i then .ok none
  else do
    let x ← svecRef v i
    pure (some (x, i + 1))
def svecEltype : String := "Any"
/-- `keys(v) = OneTo(length(v))`, `axes(v) = (OneTo(length(v)),)`; `OneTo(n)` is `n`. -/
def svecKeys (v : SVec) : Nat := svecLength v
def svecIsempty (v : SVec) : Bool := svecLength v == 0
def svecAxes (v : SVec) : List Nat := [svecLength v]
/-- `axes(v, d) = d <= 1 ? axes(v)[d] : OneTo(1)`. -/
def svecAxesD (v : SVec) (d : Int) : R Nat :=
  if d ≤ 1 then (if d = 1 then .ok (svecLength v) else .error .bounds) else .ok 1

/-- `==(v1::SimpleVector, v2::SimpleVector)` with element comparison `eq`. -/
def svecEqLoop (eq : Option JVal → Option JVal → Bool) : SVec → SVec → Bool
  | a :: as, b :: bs => eq a b && svecEqLoop eq as bs
  | _, _ => true
def svecEq (eq : Option JVal → Option JVal → Bool) (v1 v2 : SVec) : Bool :=
  if svecLength v1 != svecLength v2 then false else svecEqLoop eq v1 v2

/-- `map(f, v::SimpleVector) = Any[f(v[i]) for i = 1:length(v)]`. -/
def svecMap {β : Type} (f : Option JVal → β) (v : SVec) : List β := v.map f

/-- `getindex(v::SimpleVector, I::AbstractArray) = Core.svec(Any[v[i] for i in I]...)`. -/
def svecGetindexArray (v : SVec) : List Int → R SVec
  | [] => .ok []
  | i :: is => do
    let x ← svecRef v i
    let rest ← svecGetindexArray v is
    pure (x :: rest)

/-- `unsafe_convert(Ptr{Any}, sv) = convert(Ptr{Any}, pointer_from_objref(sv)) + sizeof(Ptr)`:
the address of the first element, one word past the length header. -/
def svecUnsafeConvert (addr : Nat) : Nat := addr + 8

/-- `isassigned(v::SimpleVector, i::Int)`, `base/essentials.jl:1141-1144`. -/
def svecIsassigned (v : SVec) (i : Int) : Bool := decide (1 ≤ i ∧ i ≤ (svecLength v : Int))

/-! ## `Symbol` constructors, `base/boot.jl:858-873` -/

/-- `_Symbol(ptr, sz, root)` (`jl_symbol_n`): a symbol is its byte string; a NUL byte
throws `ArgumentError`. -/
def symbolN (bytes : List Nat) : R (List Nat) :=
  if bytes.contains 0 then .error (.argument "Symbol name may not contain \\0") else .ok bytes

/-- `Symbol(s::String)`: the bytes of `s` (`sizeof(s)` of them). -/
def symbolOfString (s : List Nat) : R (List Nat) := symbolN (s.take s.length)
/-- `Symbol(a::Array{UInt8,1})`: `size(a)[1]` bytes starting at the array's reference. -/
def symbolOfVector (a : List Nat) (off len : Nat) : R (List Nat) := symbolN ((a.drop off).take len)
/-- `Symbol(s::Symbol) = s`. -/
def symbolOfSymbol (s : List Nat) : List Nat := s

end JuliaLean.BootCov.Arrays
