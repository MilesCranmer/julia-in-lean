import JuliaLean.base.range
import JuliaLean.base.boot
import JuliaLean.base.expr
import JuliaLean.src.runtime_intrinsics_c
import JuliaLean.Core
import JuliaLean.base.int


section

/-!
Type-object functions of `base/boot.jl` and `base/essentials.jl` (master
`bbfa0ce4150`): `Typeof`, `TypeVar`, `UnionAll`, `typename`, the
`unwrap_unionall` family, `Vararg` helpers, `datatype_min_ninitialized`,
`has_typevar` and the `TypeApp` machinery.
-/

namespace JuliaLean.BootCov.Types

open JuliaLean
open JuliaLean.BootCov

/-- `unwrap_unionall(a)`, `base/essentials.jl:544-550`. -/
def unwrapUnionall : JType → JType
  | .unionAll _ b => unwrapUnionall b
  | t => t

/-- `rewrap_unionall(t, u)`, `base/essentials.jl:552-558`. -/
def rewrapUnionall (t : JType) : JType → R JType
  | .unionAll v b => do
    let inner ← rewrapUnionall t b
    unionAllCtor v inner
  | _ => .ok t

/-- `!isdefined(t, :N) || t.N === u.var` for a `Vararg` length `N`. -/
def lengthIsVar : Option JType → JType → Bool
  | none, _ => true
  | some (.tvar i _ _ _), v => i == varId v
  | some _, _ => false

/-- `rewrap_unionall(t::Core.TypeofVararg, u)`, `base/essentials.jl:560-571`. -/
def rewrapUnionallVararg (T N : Option JType) (u : JType) : R JType :=
  match T, u with
  | none, _ => .ok (.vararg T N)
  | some t, .unionAll v b =>
    match rewrapUnionall t (.unionAll v b) with
    | .error e => .error e
    | .ok T' => if lengthIsVar N v then .ok (.vararg (some T') none) else .ok (.vararg (some T') N)
  | some _, _ => .ok (.vararg T N)

mutual
/-- Substitute typevar `id` by `r` (the instantiation `u{r}`). -/
def subst (id : Nat) (r : JType) : JType → JType
  | .dt n a ps => .dt n a (substList id r ps)
  | .union a b => .union (subst id r a) (subst id r b)
  | .bottom => .bottom
  | .tvar i n lb ub => if i = id then r else .tvar i n (subst id r lb) (subst id r ub)
  | .unionAll v b => .unionAll (subst id r v) (subst id r b)
  | .vararg T N => .vararg (substOpt id r T) (substOpt id r N)
  | .typeApp h p => .typeApp (subst id r h) (subst id r p)
  | .intParam n => .intParam n
  | .names s => .names s
  | .other s => .other s
def substList (id : Nat) (r : JType) : List JType → List JType
  | [] => []
  | t :: ts => subst id r t :: substList id r ts
def substOpt (id : Nat) (r : JType) : Option JType → Option JType
  | none => none
  | some t => some (subst id r t)
end

/-- `body{nv}`: instantiate the outermost variable of a `UnionAll`. -/
def instantiate (u r : JType) : R JType :=
  match u with
  | .unionAll v b => .ok (subst (varId v) r b)
  | _ => .error (.typeError "Type{...} expression")

/-- `rename_unionall(u)`, `base/essentials.jl:574-582`; fresh typevar ids start at `next`. -/
def renameUnionall (next : Nat) : JType → R (JType × Nat)
  | .unionAll v b => do
    match v with
    | .tvar _ name lb ub =>
      let (b', next') ← renameUnionall next b
      let body ← unionAllCtor v b'
      let nv := JType.tvar next' name lb ub
      let inst ← instantiate body nv
      let r ← unionAllCtor nv inst
      pure (r, next' + 1)
    | _ => .error (.typeError "typeassert")
  | u => .ok (u, next)

/-- `widen_diagonal(t, troot)` (`jl_widen_diagonal`), `base/essentials.jl:585-587`. -/
def widenDiagonal (widen : JType → JType → JType) (t troot : JType) : JType := widen t troot

/-- `isvarargtype(t)`, `base/essentials.jl:589-591`. -/
def isvarargtype : JType → Bool
  | .vararg _ _ => true
  | _ => false

/-- `isvatuple(t)`, `base/essentials.jl:593-601`. -/
def isvatuple (t : JType) : Bool :=
  match unwrapUnionall t with
  | .dt _ _ ps => decide (ps.length > 0) && (match ps.getLast? with
      | some p => isvarargtype p | none => false)
  | _ => false

/-- `unwrapva(t)`, `base/essentials.jl:603-606`. -/
def unwrapva : JType → JType
  | .vararg (some T) _ => T
  | .vararg none _ => .dt "Any" true []
  | t => t

/-- `unconstrain_vararg_length(va) = Vararg{unwrapva(va)}`, `base/essentials.jl:608-613`. -/
def unconstrainVarargLength (va : JType) : JType := .vararg (some (unwrapva va)) none

/-- The `Tuple` branch of `datatype_min_ninitialized`, `base/essentials.jl:630-644`. -/
def tupleMinFields (ps : List JType) : Int :=
  let n : Int := ps.length
  if n = 0 then 0
  else match ps.getLast? with
    | some (.vararg _ N) =>
      let n := n - 1
      match N with
      | some (.intParam k) => n + k
      | _ => n
    | _ => n

/-- `datatype_min_ninitialized(t0)`, `base/essentials.jl:617-646`; `nfields name` is
`length(t.name.names)` and `nuninit name` is `t.name.n_uninitialized`. -/
def datatypeMinNinitialized (nfields nuninit : String → Nat) (t0 : JType) : Int :=
  match unwrapUnionall t0 with
  | .dt name abs ps =>
    if abs then 0
    else if name = "NamedTuple" then
      match ps with
      | .names syms :: _ => syms.length
      | _ :: types :: _ =>
        match unwrapUnionall types with
        | .dt "Tuple" _ tps => tupleMinFields tps
        | _ => 0
      | _ => 0
    else if name = "Tuple" then tupleMinFields ps
    else (nfields name : Int) - nuninit name
  | _ => 0

end JuliaLean.BootCov.Types

end

section

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

end JuliaLean.BootCov.Arrays

end

section

/-!
Macros of `base/boot.jl` and `base/essentials.jl` (master `bbfa0ce4150`) as
functions from their arguments (and `__module__`, `__source__`) to the `Expr`
they return, plus the small doc-system helpers of `Core`.
-/

namespace JuliaLean.BootCov.Macros

open JuliaLean
open JuliaLean.BootCov
/-- `@_total_meta()`, `base/essentials.jl:196-209`. -/
def baseTotalMeta : EffectFlags := ⟨true, true, true, true, false, true, true, true, false, false, true⟩
/-- `@_foldable_meta()`, `base/essentials.jl:211-224`. -/
def baseFoldableMeta : EffectFlags := ⟨true, true, false, true, false, true, true, true, false, false, true⟩
/-- `@_terminates_locally_meta()`, `base/essentials.jl:226-239`. -/
def baseTerminatesLocallyMeta : EffectFlags := ⟨false, false, false, false, true, false, false, false, false, false, false⟩
/-- `@_terminates_globally_meta()`, `base/essentials.jl:241-254`. -/
def baseTerminatesGloballyMeta : EffectFlags := ⟨false, false, false, true, true, false, false, false, false, false, false⟩
/-- `@_terminates_globally_notaskstate_meta()`, `base/essentials.jl:256-269`. -/
def baseTerminatesGloballyNotaskstateMeta : EffectFlags := ⟨false, false, false, true, true, true, false, false, false, false, false⟩
/-- `@_terminates_globally_noub_meta()`, `base/essentials.jl:271-284`. -/
def baseTerminatesGloballyNoubMeta : EffectFlags := ⟨false, false, false, true, true, false, false, true, false, false, false⟩
/-- `@_effect_free_terminates_locally_meta()`, `base/essentials.jl:286-299`. -/
def baseEffectFreeTerminatesLocallyMeta : EffectFlags := ⟨false, true, false, false, true, false, false, false, false, false, false⟩
/-- `@_nothrow_noub_meta()`, `base/essentials.jl:301-314`. -/
def baseNothrowNoubMeta : EffectFlags := ⟨false, false, true, false, false, false, false, true, false, false, false⟩
/-- `@_nothrow_meta()`, `base/essentials.jl:316-329`. -/
def baseNothrowMeta : EffectFlags := ⟨false, false, true, false, false, false, false, false, false, false, false⟩
/-- `@_noub_meta()`, `base/essentials.jl:331-344`. -/
def baseNoubMeta : EffectFlags := ⟨false, false, false, false, false, false, false, true, false, false, false⟩
/-- `@_notaskstate_meta()`, `base/essentials.jl:346-359`. -/
def baseNotaskstateMeta : EffectFlags := ⟨false, false, false, false, false, true, false, false, false, false, false⟩
/-- `@_noub_if_noinbounds_meta()`, `base/essentials.jl:361-374`. -/
def baseNoubIfNoinboundsMeta : EffectFlags := ⟨false, false, false, false, false, false, false, false, true, false, false⟩

/-- `Base._nameof(m)` (`jl_module_name`), `base/essentials.jl:188`, and `Base.nameof(m::Module)`
(line 419); a module is identified by its name here. -/
def nameofModule (m : String) : String := m

/-- `Base._is_internal(m)`, `base/essentials.jl:190-193`; `baseRelative m` is
`jl_base_relative_to(m)`. -/
def baseIsInternal (baseRelative : String → String) (m : String) : Bool :=
  nameofModule m == "Base" || nameofModule (baseRelative m) == "Compiler"

/-- `@nospecialize(vars...)` and `@specialize(vars...)`, `base/essentials.jl:125-151`:
a single `x = v` argument becomes `Expr(:kw, x, v)`. -/
def kwOf : JVal → JVal
  | .expr "=" args => .expr "kw" args
  | v => v
def fixKw : List JVal → List JVal
  | [v] => [kwOf v]
  | vars => vars
def nospecialize (vars : List JVal) : JVal :=
  .expr "escape" [.expr "meta" (.sym "nospecialize" :: fixKw vars)]
def specialize (vars : List JVal) : JVal :=
  .expr "escape" [.expr "meta" (.sym "specialize" :: fixKw vars)]

/-- `@isdefined(s::Symbol)`, `base/essentials.jl:184-186`. -/
def isdefinedMacro (s : String) : JVal := .expr "escape" [.expr "isdefined" [.sym s]]

/-- `@_gc_preserve_begin(arg1)` and `@_gc_preserve_end(token)`, `base/essentials.jl:46-52`. -/
def gcPreserveBegin (a : JVal) : JVal := .expr "gc_preserve_begin" [esc a]
def gcPreserveEnd (t : JVal) : JVal := .expr "gc_preserve_end" [esc t]

/-- `@_propagate_inbounds_meta` and `@_nospecializeinfer_meta`, `base/essentials.jl:377-382`. -/
def propagateInboundsMeta : JVal := .expr "meta" [.sym "inline", .sym "propagate_inbounds"]
def nospecializeinferMeta : JVal := .expr "meta" [.sym "nospecializeinfer"]

/-- `@eval(ex)` and `@eval(mod, ex)`, `base/essentials.jl:488-501`. -/
def evalMacro2 (mod ex : JVal) : JVal :=
  .expr "let" [.expr "=" [.sym "eval_local_result",
      .expr "escape" [.expr "call" [.globalRef "Core" "eval", mod, .expr "quote" [ex]]]],
    .expr "block" [.expr "latestworld-if-toplevel" [], .sym "eval_local_result"]]
def evalMacro1 (module_ : String) (ex : JVal) : JVal := evalMacro2 (.module_ module_) ex

/-- `@boundscheck(blk)` and `@inbounds(blk)`, `base/essentials.jl:939-977`. -/
def boundscheckMacro (blk : JVal) : JVal := .expr "if" [.expr "boundscheck" [], esc blk]
def inboundsMacro (blk : JVal) : JVal :=
  .expr "block" [.expr "inbounds" [.bool true], .expr "local" [.expr "=" [.sym "val", esc blk]],
    .expr "inbounds" [.sym "pop"], .sym "val"]

/-- `@label(name::Symbol)`, `base/essentials.jl:1020-1023`. -/
def label1 (name : String) : R JVal :=
  if name = "_" then .error (.error "use `@label expr` for anonymous blocks; `@label _` is not allowed")
  else .ok (esc (.expr "symboliclabel" [.sym name]))

/-- `@label(name::Symbol, body)`, `base/essentials.jl:1025-1042`: the body of a `for` or
`while` loop is wrapped in a `name#cont` block so `continue name` can target it. -/
def label2 (name : String) (body : JVal) : R JVal :=
  if name = "_" then .error (.error "use `@label expr` for anonymous blocks; `@label _ expr` is not allowed")
  else
    let body := match body with
      | .expr "for" (a1 :: a2 :: _) =>
        .expr "for" [a1, .expr "symbolicblock" [.sym (name ++ "#cont"), a2]]
      | .expr "while" (a1 :: a2 :: _) =>
        .expr "while" [a1, .expr "symbolicblock" [.sym (name ++ "#cont"), a2]]
      | b => b
    .ok (esc (.expr "symbolicblock" [.sym name, body]))

/-- `@label(body)`, `base/essentials.jl:1044-1048`. -/
def label0 (body : JVal) : JVal := esc (.expr "symbolicblock" [.sym "loop-exit", body])

/-- `@goto(name)`, `base/essentials.jl:1058-1060`. -/
def gotoMacro (name : String) : JVal := esc (.expr "symbolicgoto" [.sym name])

/-- `@__LINE__`, `base/essentials.jl:1568-1570`: the line of `__source__`. -/
def lineMacro (source : JVal) : R JVal :=
  match source with
  | .lineNode l _ => .ok (.int l)
  | _ => .error (.method "getproperty")

/-- `@world(sym, world)`, `base/essentials.jl:1646-1660`. -/
def worldMacro (module_ : String) (sym world : JVal) : R JVal :=
  let world := if (match world with | .sym "∞" => true | _ => false)
    then JVal.expr "call" [.opaque 0] else world
  match sym with
  | .sym s => .ok (.expr "call" [.opaque 1, esc world, .quoteNode (.globalRef module_ s)])
  | .globalRef m n => .ok (.expr "call" [.opaque 1, esc world, .quoteNode (.globalRef m n)])
  | .expr "." [a, .quoteNode (.sym n)] =>
    .ok (.expr "call" [.opaque 1, esc world, .expr "call" [.opaque 2, esc a, .quoteNode (.sym n)]])
  | _ => .error (.error "`@world` requires a symbol or GlobalRef")

end JuliaLean.BootCov.Macros

end

section

/-!
Remaining methods of `base/boot.jl` and `base/essentials.jl` (master
`bbfa0ce4150`): the stand-alone `Core` printing functions, identity
conversions, tuple helpers, `Pairs`, small predicates and the `Core` hooks.
-/

namespace JuliaLean.BootCov.Misc

open JuliaLean
open JuliaLean.BootCov
open JuliaLean.BootCov.IntConv
/-- `cconvert(::Type{T}, x) = x isa T ? x : convert(T, x)`, `base/essentials.jl:739`. -/
def cconvert {α : Type} (isT : α → Bool) (convert : α → R α) (x : α) : R α :=
  if isT x then .ok x else convert x
/-- `cconvert(::Type{<:Ptr}, x) = x`, `base/essentials.jl:741`. -/
def cconvertPtr {α : Type} (x : α) : α := x
/-- `unsafe_convert(::Type{P}, x::Ptr) = convert(P, x)`: pointer conversion keeps the
address, `base/essentials.jl:744`. -/
def unsafeConvertPtr (x : Ptr) : Ptr := ⟨x.addr⟩
/-- `unsafe_convert(Ptr{UInt8}, s)` and `unsafe_convert(Ptr{Int8}, s)` (`jl_string_ptr`),
`base/essentials.jl:745-746`: the address of the string data. -/
def unsafeConvertString (dataAddr : JInt .u64) : Ptr := ⟨dataAddr⟩
def convertUnionBottom {α : Type} (_ : List α) : R α :=
  .error (.argument "cannot convert a value to Union{} for assignment")
def cconvertUnionBottom {α : Type} (x : List α) : R α := convertUnionBottom x

/-! ## Tuples, `base/essentials.jl:521-667` -/

/-- `argtail(_, rest...) = rest`. -/
def argtail {α : Type} : List α → R (List α)
  | _ :: rest => .ok rest
  | [] => .error (.method "argtail")
/-- `tail(x::Tuple) = argtail(x...)` and `tail(::Tuple{}) = throw(ArgumentError(...))`. -/
def tail {α : Type} : List α → R (List α)
  | [] => .error (.argument "Cannot call tail on an empty tuple.")
  | x => argtail x

/-- `_tuple_error(T, x) = throw(MethodError(convert, (T, x)))`, line 650. -/
def tupleError {α : Type} : R α := .error (.method "convert")

/-- `cvt1(n)`, lines 659-665: the `n`-th element converted to the `n`-th field type. -/
def cvt1 {α : Type} (isa : Nat → α → Bool) (convert : Nat → α → R α) (x : List α) (n : Nat) :
    R α :=
  match x[n - 1]? with
  | some xn => if isa n xn then .ok xn else convert n xn
  | none => .error .bounds

/-- `ntuple(cvt1, Val(N))`: apply `cvt1` to positions `n, n+1, ...` in order, stopping at the
first error. -/
def cvtFrom {α : Type} (isa : Nat → α → Bool) (convert : Nat → α → R α) : Nat → List α → R (List α)
  | _, [] => .ok []
  | n, xn :: xs => do
    let y ← if isa n xn then pure xn else convert n xn
    let ys ← cvtFrom isa convert (n + 1) xs
    pure (y :: ys)

/-- `convert(::Type{T}, x::NTuple{N,Any}) where {N, T<:Tuple}`, lines 653-667: `fits` is
`typeintersect(NTuple{N,Any}, T) !== Union{}`. -/
def convertTuple {α : Type} (fits : Bool) (isa : Nat → α → Bool) (convert : Nat → α → R α)
    (x : List α) : R (List α) :=
  if !fits then tupleError else cvtFrom isa convert 1 x

/-! ## Small functions -/

/-- `blackbox(x) = compilerbarrier(:blackbox, x)` and `inferencebarrier(x)`
(`base/essentials.jl:9`, 1201): the value is unchanged. -/
def blackbox {α : Type} (x : α) : α := x
def inferencebarrier {α : Type} (x : α) : α := x

/-- `throw_boundserror(A)`, `throw_boundserror(A, I)`, `throw_boundserror(A, i1, i2, I...)`,
`_throw_boundserror_indices(A)` and `(A, i1, I...)`, `base/essentials.jl:15-19`:
`BoundsError(A, indices)`. -/
def throwBoundserror (A : JVal) (I : List JVal) : R JVal × JVal :=
  (.error .bounds, .obj "BoundsError" [some A, some (.tuple I)])
def throwBoundserror1 (A : JVal) : R JVal × JVal := throwBoundserror A []
def throwBoundserror2 (A I : JVal) : R JVal × JVal :=
  (.error .bounds, .obj "BoundsError" [some A, some I])
def throwBoundserror3 (A i1 i2 : JVal) (I : List JVal) : R JVal × JVal :=
  throwBoundserror A (i1 :: i2 :: I)
def throwBoundserrorIndices (A : JVal) (I : List JVal) : R JVal × JVal := throwBoundserror A I

/-- `==(a::GlobalRef, b::GlobalRef) = a.mod === b.mod && a.name === b.name`, line 23. -/
def globalRefEq (a b : String × String) : Bool := a.1 == b.1 && a.2 == b.2

/-- `oftype(x, y) = y isa typeof(x) ? y : convert(typeof(x), y)::typeof(x)`, line 718. -/
def oftype {α : Type} (isa : α → Bool) (convert : α → R α) (y : α) : R α :=
  if isa y then .ok y
  else do
    let r ← convert y
    if isa r then .ok r else .error (.typeError "typeassert")

/-- `unsigned(x::Int) = reinterpret(UInt, x)` and `signed(x::UInt) = reinterpret(Int, x)`,
lines 720-721. -/
def unsignedInt (x : JInt64) : JInt .u64 := bitcastInt .u64 x
def signedUInt (x : JInt .u64) : JInt64 := bitcastInt .i64 x

/-- `reinterpret(::Type{Out}, x)`, lines 787-794: `bitcast` when both types are primitive,
otherwise the full `_reinterpret` defined later in Base. -/
def reinterpret {α β : Type} (primitive : Bool) (bitcast : α → β) (full : α → R β) (x : α) : R β :=
  if primitive then .ok (bitcast x) else full x

/-- `sizeof(x) = Core.sizeof(x)`, line 841, and `ifelse(c, x, y) = Core.ifelse(c, x, y)`,
line 884. -/
def sizeof {α : Type} (coreSizeof : α → Nat) (x : α) : Nat := coreSizeof x
def ifelse {α : Type} (c : Bool) (x y : α) : α := if c then x else y

/-- `isempty(itr)`, lines 1225-1229; `isdone` returns `none` for `missing`. -/
def isempty {σ α : Type} (isdone : σ → Option Bool) (iterate : σ → Option α) (itr : σ) : Bool :=
  match isdone itr with
  | some d => d
  | none => (iterate itr).isNone

/-- `values(itr) = itr`, line 1253. -/
def values {α : Type} (itr : α) : α := itr

/-- `(+)(x::Int, y::Int) = add_int(x, y)`, `(-)(x::Int, y::Int) = sub_int(x, y)` and
`!(x::Bool) = not_int(x)`, lines 1257-1284. -/
def addInt (x y : JInt64) : JInt64 := JInt.wrap .i64 (x.val + y.val)
def subInt (x y : JInt64) : JInt64 := JInt.wrap .i64 (x.val - y.val)
def notBool (x : Bool) : Bool := !x

/-- `ismissing(x) = x === missing` and `isdone(_, _...) = missing`, lines 1532, 1591. -/
def ismissing (x : Option JVal) : Bool := x.isNone
def isdoneDefault {α : Type} (_ : α) : Option Bool := none

/-- `isiterable(T) = hasmethod(iterate, Tuple{T})`, lines 1608-1610. -/
def isiterable {τ : Type} (hasmethod : τ → Bool) (T : τ) : Bool := hasmethod T

/-- `_resolve_in_world(world, gr) = invoke_in_world(UInt(world), Core.getglobal, gr.mod, gr.name)`,
lines 1662-1663. -/
def resolveInWorld (getglobal : JInt .u64 → String → String → R JVal) (world : BuiltinInt)
    (gr : String × String) : R JVal := do
  let w ← ctor .u64 world
  getglobal w gr.1 gr.2

/-- `Pairs{K,V,I,A}(data, itr)` (line 508): each argument is converted unless it already
has the declared type. -/
def pairsKVIA {α : Type} (isA isI : α → Bool) (convA convI : α → R α) (data itr : α) : R (α × α) := do
  let d ← if isA data then pure data else convA data
  let i ← if isI itr then pure itr else convI itr
  pure (d, i)

/-- The parameters `(K, V, I, A)` the outer `Pairs` constructors choose, lines 509-511:
`Pairs{K,V}` takes `I`, `A` from the arguments, `Pairs{K}` also takes `V = eltype(A)`, and
`Pairs(data, itr)` takes `K = eltype(I)` unless `I === Nothing`, then `keytype(A)`. -/
def pairsKV (K V I A : String) : String × String × String × String := (K, V, I, A)
def pairsK (eltype : String → String) (K I A : String) : String × String × String × String :=
  (K, eltype A, I, A)
def pairs0 (eltype keytype : String → String) (I A : String) : String × String × String × String :=
  (if I != "Nothing" then eltype I else keytype A, eltype A, I, A)

/-- `pairs(::Type{NamedTuple}) = Pairs{Symbol, V, Nothing, NT} where {V, NT <: NamedTuple}`,
line 513: the key type is `Symbol` and the iterator type `Nothing`. -/
def pairsNamedTupleType : String × String := ("Symbol", "Nothing")

/-- `Colon() = new()`, line 1160. -/
def colonCtor : JVal := .obj "Colon" []

/-- `Val{x}() = new()` and `Val(x) = Val{x}()`, lines 1190-1193: the parameter `x` lives
in the type, paired here with the field-less instance. -/
def valT (x : JVal) : JVal × JVal := (x, .obj "Val" [])
def valCtor (x : JVal) : JVal × JVal := valT x

/-- `show(io, ::Colon)`, lines 1164-1167: the type name, then `"()"`. -/
def showColon (showTypeName : String) : String := showTypeName ++ "()"

end JuliaLean.BootCov.Misc

end

section

/-!
Default-constructor generation of `base/essentials.jl` (master `bbfa0ce4150`, lines
1290-1504): `_fieldtypes_constrain_typevars`, `_defaultctor_typeinfo` and `_defaultctors`.

Arrays `Array{Any,1}(undef, k)` are lists of `k` slots, `none` for `#undef`; `@inbounds a[i] = x`
is `setAt a i x`; splatting an array into a call (`Expr(head, a...)`, `Core.svec(a...)`) is
`splat a`, which throws `UndefRefError` at an undefined slot. A counted `while` loop over
`fts[i]` (`i = 1, ..., n`) is a recursion over the list of remaining field types, carrying
`i`. The `jl_method_def` calls are recorded as the returned `MethodDef`s, in call order; each
holds the argument types and type variables of the `argdata` svec and the `:lambda`
expression handed to `jl_lower`.
-/

namespace JuliaLean.BootCov.DefaultCtors

open JuliaLean
open JuliaLean.BootCov
open JuliaLean.BootCov.Types

/-- The type `Any`. -/
def anyTy : JType := .dt "Any" true []

/-- `ft === Any`. -/
def isAnyTy : JType → Bool
  | .dt "Any" _ [] => true
  | _ => false

/-- The typeassert `x::TypeVar`. -/
def asTypeVar : JType → R JType
  | t@(.tvar _ _ _ _) => .ok t
  | _ => .error (.typeError "typeassert")

/-- `tv.ub` of a `TypeVar`. -/
def tvUb : JType → JType
  | .tvar _ _ _ ub => ub
  | t => t

/-- `tv2 === tv` for two `TypeVar`s: object identity. -/
def sameVar : JType → JType → Bool
  | .tvar a _ _ _, .tvar b _ _ _ => a == b
  | _, _ => false

/-! ## `_fieldtypes_constrain_typevars(tvars, fts)`, lines 1292-1329 -/

/-- The first inner loop (lines 1300-1307): `j = 1, ..., n`; `constrained = true; break`
at the first `has_typevar(fts[j], tv)`. -/
def fieldLoop (tv : JType) : List JType → Bool
  | [] => false
  | ft :: fts => if hasTypevar ft tv then true else fieldLoop tv fts

/-- The second inner loop (lines 1309-1322), run only when the first found nothing:
`tv2 = tvars[j]::TypeVar` for `j = i + 1, ..., nparams`; `true` at the first
`has_typevar(tv2.ub, tv)`, `false` at the first `tv2 === tv`. -/
def ubLoop (tv : JType) : List JType → R Bool
  | [] => .ok false
  | t :: ts => do
    let tv2 ← asTypeVar t
    if hasTypevar (tvUb tv2) tv then .ok true
    else if sameVar tv2 tv then .ok false
    else ubLoop tv ts

/-- The outer loop (lines 1296-1327) for `i = nparams, ..., 1`; `tvars.getD i` is
`tvars[i + 1]` and `tvars.drop (i + 1)` lists `tvars[j]` for `j = i + 2, ..., nparams`. -/
def outerLoop (tvars fts : List JType) : Nat → R Bool
  | 0 => .ok true
  | i + 1 => do
    let tv ← asTypeVar (tvars.getD i .bottom)
    let constrained ← if fieldLoop tv fts then pure true else ubLoop tv (tvars.drop (i + 1))
    if constrained then outerLoop tvars fts i else .ok false

def fieldtypesConstrainTypevars (tvars fts : List JType) : R Bool :=
  outerLoop tvars fts tvars.length

/-! ## `_defaultctor_typeinfo(ty)`, lines 1332-1350 -/

/-- `while isa(ua, UnionAll); nparams += 1; ua = ua.body; end`. -/
def peelLoop : Nat → JType → Nat × JType
  | n, .unionAll _ b => peelLoop (n + 1) b
  | n, t => (n, t)

/-- `tvars[i] = (ua::UnionAll).var; ua = (ua::UnionAll).body` for `i = 1, ..., nparams`. -/
def varsLoop : Nat → JType → R (List JType)
  | 0, _ => .ok []
  | k + 1, .unionAll v b => do
    let vs ← varsLoop k b
    pure (v :: vs)
  | _ + 1, _ => .error (.typeError "typeassert")

def isDataType : JType → Bool
  | .dt _ _ _ => true
  | _ => false

/-- `_defaultctor_typeinfo(ty)`; `getFieldtypes` is `jl_get_fieldtypes`. -/
def defaultctorTypeinfo (getFieldtypes : JType → List JType) (ty : JType) :
    R (JType × List JType × List JType) :=
  let (nparams, ua) := peelLoop 0 ty
  if isDataType ua then do
    let tvars ← varsLoop nparams ty
    pure (ua, tvars, getFieldtypes ua)
  else .error (.typeError "typeassert")

/-! ## `_defaultctors(ty, functionloc)`, lines 1355-1504 -/

/-- `Core.Argument(i)`. -/
def argument (i : Nat) : JVal := .obj "Argument" [some (.int i)]
/-- `Expr(:ssavalue, k)`. -/
def ssa (k : Nat) : JVal := .expr "ssavalue" [.int k]

/-- `Array{Any,1}(Core.undef, k)`. -/
def undefArr (k : Nat) : List (Option JVal) := List.replicate k none
/-- `@inbounds a[i] = x` (one-based). -/
def setAt (a : List (Option JVal)) (i : Nat) (x : JVal) : List (Option JVal) :=
  a.set (i - 1) (some x)
/-- The bounds-checked `a[i] = x`. -/
def setChecked (a : List (Option JVal)) (i : Nat) (x : JVal) : R (List (Option JVal)) :=
  if 1 ≤ i ∧ i ≤ a.length then .ok (setAt a i x) else .error .bounds
/-- Splatting an array: every slot is read, an undefined one throws `UndefRefError`. -/
def splat : List (Option JVal) → R (List JVal)
  | [] => .ok []
  | none :: _ => .error .undefRef
  | some x :: xs => do
    let ys ← splat xs
    pure (x :: ys)
/-- The typeassert `names[i]::Symbol`. -/
def asSymbol : JVal → R JVal
  | v@(.sym _) => .ok v
  | _ => .error (.typeError "typeassert")

/-- One `jl_method_def(svec(atypes, tvars, functionloc), C_NULL, jl_lower(lambda, ...))`. -/
structure MethodDef where
  atypes : List JVal
  tvars : List JVal
  lambda : JVal

/-- Lines 1376-1384: `argnames[i + 1] = names[i]::Symbol` and the count of `Any` fields,
for `i = 1, ..., n` (`n = length(fts)`). -/
def argnamesLoop : Nat → List JVal → List JType → List (Option JVal) → Nat →
    R (List (Option JVal) × Nat)
  | _, _, [], a, nany => .ok (a, nany)
  | i, nm :: nms, ft :: fts, a, nany => do
    let s ← asSymbol nm
    let a := setAt a (i + 1) s
    let nany := if isAnyTy ft then nany + 1 else nany
    argnamesLoop (i + 1) nms fts a nany
  | _, [], _ :: _, _, _ => .error .bounds

/-- Lines 1394-1397: `curly_args[i + 1] = Expr(:static_parameter, i)`, `i = 1, ..., nparams`. -/
def curlyLoop : Nat → Nat → List (Option JVal) → List (Option JVal)
  | _, 0, a => a
  | i, k + 1, a => curlyLoop (i + 1) k (setAt a (i + 1) (.expr "static_parameter" [.int i]))

/-- Lines 1405-1408: `new_args[i + 1] = Core.Argument(i + 1)`, `i = 1, ..., n`. -/
def newArgsLoop : Nat → Nat → List (Option JVal) → List (Option JVal)
  | _, 0, a => a
  | i, k + 1, a => newArgsLoop (i + 1) k (setAt a (i + 1) (argument (i + 1)))

/-- Lines 1418-1421: `atypes_arr[i + 1] = fts[i]`. -/
def atypesLoop : Nat → List JType → List (Option JVal) → List (Option JVal)
  | _, [], a => a
  | i, ft :: fts, a => atypesLoop (i + 1) fts (setAt a (i + 1) (.ty ft))

/-- Lines 1429-1437: `all_any` is false at the first `fts[i] !== Any`. -/
def allAnyLoop : List JType → Bool
  | [] => true
  | ft :: fts => if !isAnyTy ft then false else allAnyLoop fts

/-- The `fieldtype(self, i)` statement of field `i`, line 1462. -/
def ftStmt (i bidx : Nat) : JVal :=
  .expr "=" [ssa bidx, .expr "call" [.globalRef "Core" "fieldtype", argument 1, .int i]]
/-- The `isa(arg, ft) ? arg : convert(ft, arg)` statement of field `i`, lines 1465-1469. -/
def cnvtStmt (i bidx : Nat) : JVal :=
  .expr "=" [ssa (bidx + 1), .expr "if"
    [.expr "call" [.globalRef "Core" "isa", argument (i + 1), ssa bidx], argument (i + 1),
     .expr "call" [.globalRef "Base" "convert", ssa bidx, argument (i + 1)]]]

/-- Lines 1448-1475: for `i = 1, ..., n`, an `Any` field passes `Core.Argument(i + 1)`;
any other field gets the two statements at `bidx` and `bidx + 1` and passes the second's
SSA value; `bidx += 2`. -/
def innerLoop : Nat → Nat → List JType → List (Option JVal) → List (Option JVal) →
    List (Option JVal) × List (Option JVal)
  | _, _, [], body, na => (body, na)
  | i, bidx, ft :: fts, body, na =>
    if isAnyTy ft then innerLoop (i + 1) bidx fts body (setAt na i (argument (i + 1)))
    else
      let body := setAt body bidx (ftStmt i bidx)
      let body := setAt body (bidx + 1) (cnvtStmt i bidx)
      innerLoop (i + 1) (bidx + 2) fts body (setAt na i (ssa (bidx + 1)))

/-- Lines 1486-1491: `typedt = UnionAll(tvars[i], typedt)` for `i = nparams, ..., 1`. -/
def wrapLoop (tvars : List JType) : Nat → JType → R JType
  | 0, t => .ok t
  | i + 1, t => do
    let t ← unionAllCtor (tvars.getD i .bottom) t
    wrapLoop tvars i t

/-- Lines 1494-1497: `inner_atypes_arr[i + 1] = Any`. -/
def anyArgsLoop : Nat → Nat → List (Option JVal) → List (Option JVal)
  | _, 0, a => a
  | i, k + 1, a => anyArgsLoop (i + 1) k (setAt a (i + 1) (.ty anyTy))

/-- `UInt(functionloc.line)` (line 1366): `InexactError` for a negative line. -/
def srcLine : JVal → R Nat
  | .lineNode l _ => if l < 0 then .error (.inexact "convert" "UInt64") else .ok l.toNat
  | _ => .error (.typeError "getfield")

/-- The outer constructor (lines 1386-1427) `T(x::FT1, ...) = new{A,...}(x, ...)`. -/
def outerCtor (ty : JType) (tvars fts : List JType) (argnames : JVal) (functionloc : JVal) :
    R MethodDef := do
  let nparams := tvars.length
  let n := fts.length
  let newTarget ← if nparams != 0 then do
      let curlyArgs := curlyLoop 1 nparams (setAt (undefArr (nparams + 1)) 1 (.ty ty))
      let cargs ← splat curlyArgs
      pure (JVal.expr "curly" cargs)
    else pure (argument 1)
  let newArgs := newArgsLoop 1 n (setAt (undefArr (n + 1)) 1 newTarget)
  let nargs ← splat newArgs
  let lambda := JVal.expr "lambda" [argnames,
    .expr "block" [functionloc, .expr "return" [.expr "new" nargs]]]
  let atypesArr := atypesLoop 1 fts (setAt (undefArr (n + 1)) 1 (.ty (typeKind ty)))
  let outerAtypes ← splat atypesArr
  pure ⟨outerAtypes, tvars.map .ty, lambda⟩

/-- The inner constructor (lines 1442-1502) `(::Type{T{A,...}})(x, ...)` with converts. -/
def innerCtor (dt : JType) (tvars fts : List JType) (nany : Nat) (argnames : JVal)
    (functionloc : JVal) : R MethodDef := do
  let nparams := tvars.length
  let n := fts.length
  let nstmts := (n - nany) + (n - nany) + 1
  let (bodyArgs, newArgs) := innerLoop 1 1 fts (undefArr nstmts) (undefArr n)
  let na ← splat newArgs
  let bodyArgs ← setChecked bodyArgs nstmts (.expr "return" [.expr "new" (argument 1 :: na)])
  let stmts ← splat bodyArgs
  let lambda := JVal.expr "lambda" [argnames, .expr "block" (functionloc :: stmts)]
  let typedt ← wrapLoop tvars nparams (typeKind dt)
  let innerAtypesArr := anyArgsLoop 1 n (setAt (undefArr (n + 1)) 1 (.ty typedt))
  let innerAtypes ← splat innerAtypesArr
  pure ⟨innerAtypes, [], lambda⟩

/-- `_defaultctors(ty, functionloc)`: `getFieldtypes` is `jl_get_fieldtypes` and `getNames`
reads `dt.name.names`. The result lists the methods defined, in order. -/
def defaultctors (getFieldtypes : JType → List JType) (getNames : JType → List JVal)
    (ty : JType) (functionloc : JVal) : R (List MethodDef) := do
  let (dt, tvars, fts) ← defaultctorTypeinfo getFieldtypes ty
  let nparams := tvars.length
  let n := fts.length
  let names := getNames dt
  let _ ← srcLine functionloc
  let self := JVal.sym "#ctor-self#"
  let (argnames, nany) ← argnamesLoop 1 names fts (setAt (undefArr (n + 1)) 1 self) 0
  let argnamesV := JVal.obj "Array{Any,1}" argnames
  let constrained ← fieldtypesConstrainTypevars tvars fts
  if constrained then do
    let outer ← outerCtor ty tvars fts argnamesV functionloc
    if nparams = 0 ∧ allAnyLoop fts then return [outer]
    let inner ← innerCtor dt tvars fts nany argnamesV functionloc
    pure [outer, inner]
  else do
    let inner ← innerCtor dt tvars fts nany argnamesV functionloc
    pure [inner]

/-- `length(t::AbstractArray) = (@inline; prod(size(t)))`, `base/essentials.jl:13`:
`prod` of the size tuple multiplies left to right with `Int` wrapping (`prod(()) = 1`). -/
def lengthAbstract (size : List JInt64) : JInt64 :=
  match size with
  | [] => JInt.lit .i64 1
  | d :: ds => ds.foldl (· * ·) d

end JuliaLean.BootCov.DefaultCtors

end


/-!
# Typed model of `base/essentials.jl`

Julia method source is pinned to `f755f49a9e41380d7da126b3c1db9fe7f83dd027`. Each translated
method is preceded by its exact source lines. The file keeps untranslated method bodies visible.
-/

namespace JuliaLean.base.essentials

open JuliaLean JuliaLean.BootCov

def prodDims : List (JInt .i64) → JInt .i64
  | [] => JInt.wrap .i64 1
  | d :: ds => d * prodDims ds

structure PairsModel (K V I A : Type) where
  data : A
  itr : I

inductive ColonModel where
  | mk

inductive ValValue {α : Type} (value : α) where
  | mk : ValValue value

def isUnionAll : JType → Bool
  | .unionAll _ _ => true
  | _ => false

structure EffectFlags where
  consistent : Bool
  effectFree : Bool
  nothrow : Bool
  terminatesGlobally : Bool
  terminatesLocally : Bool
  notaskstate : Bool
  inaccessiblememonly : Bool
  noub : Bool
  noubIfNoinbounds : Bool
  consistentOverlay : Bool
  nortcall : Bool

def EffectFlags.toList (f : EffectFlags) : List JVal :=
  [f.consistent, f.effectFree, f.nothrow, f.terminatesGlobally, f.terminatesLocally,
    f.notaskstate, f.inaccessiblememonly, f.noub, f.noubIfNoinbounds, f.consistentOverlay,
    f.nortcall].map JVal.bool

def effectMeta (internal : Bool) (flags : EffectFlags) : JVal :=
  if internal then .expr "meta" [.expr "purity" flags.toList] else .bool false

def cvtTupleElement {T X Y A : Type} (fieldtype : T → Nat → Y) (getfield : X → Nat → A)
    (isa : Y → A → Bool) (convert : Y → A → Except Exc A) (t : T) (x : X) (n : Nat) : Except Exc A := do
  let Tn := fieldtype t n
  let xn := getfield x n
  if isa Tn xn then pure xn else convert Tn xn


def anyTy : JType := .dt "Any" true []
def isAnyTy : JType → Bool
  | .dt "Any" _ [] => true
  | _ => false
def typeKind (t : JType) : JType := .dt "Type" true [t]
def argument (i : Nat) : JVal := .obj "Argument" [some (.int i)]
def ssa (i : Nat) : JVal := .expr "ssavalue" [.int i]
def undefArr (n : Nat) : List (Option JVal) := List.replicate n none
def setAt (a : List (Option JVal)) (i : Nat) (x : JVal) : List (Option JVal) := a.set (i - 1) (some x)
def setChecked (a : List (Option JVal)) (i : Nat) (x : JVal) : Except Exc (List (Option JVal)) :=
  if 1 ≤ i ∧ i ≤ a.length then .ok (setAt a i x) else .error .bounds
def splat : List (Option JVal) → Except Exc (List JVal)
  | [] => .ok []
  | none :: _ => .error .undefRef
  | some x :: xs => do
    let rest ← splat xs
    pure (x :: rest)
def asSymbol : JVal → Except Exc JVal
  | value@(.sym _) => .ok value
  | _ => .error (.typeError "typeassert")

structure MethodDef where
  atypes : List JVal
  tvars : List JVal
  lambda : JVal

structure DefaultCtorOps where
  getFieldtypes : JType → List JType
  getNames : JType → List JVal
  ccallHasTypevar : JType → JType → Int32
  isTypevar : JType → Bool
  upperBound : JType → JType
  sameType : JType → JType → Bool
  typeKind : JType → JType
  unionAll : JType → JType → Except Exc JType
  sourceLine : JVal → Except Exc Nat
  recordMethod : MethodDef → Except Exc Unit

def argnamesLoop : Nat → List JVal → List JType → List (Option JVal) → Nat →
    Except Exc (List (Option JVal) × Nat)
  | _, _, [], a, nany => .ok (a, nany)
  | i, name :: names, fieldType :: fieldTypes, a, nany => do
    let symbol ← asSymbol name
    let a := setAt a (i + 1) symbol
    let nany := if isAnyTy fieldType then nany + 1 else nany
    argnamesLoop (i + 1) names fieldTypes a nany
  | _, [], _ :: _, _, _ => .error .bounds

def curlyLoop : Nat → Nat → List (Option JVal) → List (Option JVal)
  | _, 0, a => a
  | i, k + 1, a => curlyLoop (i + 1) k (setAt a (i + 1) (.expr "static_parameter" [.int i]))

def newArgsLoop : Nat → Nat → List (Option JVal) → List (Option JVal)
  | _, 0, a => a
  | i, k + 1, a => newArgsLoop (i + 1) k (setAt a (i + 1) (argument (i + 1)))

def atypesLoop : Nat → List JType → List (Option JVal) → List (Option JVal)
  | _, [], a => a
  | i, fieldType :: fieldTypes, a => atypesLoop (i + 1) fieldTypes (setAt a (i + 1) (.ty fieldType))

def allAnyLoop : List JType → Bool
  | [] => true
  | fieldType :: rest => isAnyTy fieldType && allAnyLoop rest

def ftStmt (i bidx : Nat) : JVal :=
  .expr "=" [ssa bidx, .expr "call" [.globalRef "Core" "fieldtype", argument 1, .int i]]
def cnvtStmt (i bidx : Nat) : JVal :=
  .expr "=" [ssa (bidx + 1), .expr "if"
    [.expr "call" [.globalRef "Core" "isa", argument (i + 1), ssa bidx], argument (i + 1),
     .expr "call" [.globalRef "Base" "convert", ssa bidx, argument (i + 1)]]]

def innerLoop : Nat → Nat → List JType → List (Option JVal) → List (Option JVal) →
    List (Option JVal) × List (Option JVal)
  | _, _, [], body, args => (body, args)
  | i, bidx, fieldType :: fieldTypes, body, args =>
    if isAnyTy fieldType then
      innerLoop (i + 1) bidx fieldTypes body (setAt args i (argument (i + 1)))
    else
      let body := setAt body bidx (ftStmt i bidx)
      let body := setAt body (bidx + 1) (cnvtStmt i bidx)
      innerLoop (i + 1) (bidx + 2) fieldTypes body (setAt args i (ssa (bidx + 1)))

def wrapLoop (ops : DefaultCtorOps) (tvars : List JType) : Nat → JType → Except Exc JType
  | 0, t => .ok t
  | i + 1, t => do
    let wrapped ← ops.unionAll (tvars.getD i .bottom) t
    wrapLoop ops tvars i wrapped

def anyArgsLoop : Nat → Nat → List (Option JVal) → List (Option JVal)
  | _, 0, a => a
  | i, k + 1, a => anyArgsLoop (i + 1) k (setAt a (i + 1) (.ty anyTy))

def srcLine : JVal → Except Exc Nat
  | .lineNode line _ => if line < 0 then .error (.inexact "convert" "UInt64") else .ok line.toNat
  | _ => .error (.typeError "getfield")

def outerCtor (ops : DefaultCtorOps) (ty : JType) (tvars fieldTypes : List JType)
    (argnames functionloc : JVal) : Except Exc MethodDef := do
  let nparams := tvars.length
  let n := fieldTypes.length
  let newTarget ← if nparams != 0 then do
      let curlyArgs := curlyLoop 1 nparams (setAt (undefArr (nparams + 1)) 1 (.ty ty))
      let args ← splat curlyArgs
      pure (.expr "curly" args)
    else pure (argument 1)
  let newArgs := newArgsLoop 1 n (setAt (undefArr (n + 1)) 1 newTarget)
  let args ← splat newArgs
  let lambda := .expr "lambda" [argnames, .expr "block" [functionloc, .expr "return" [.expr "new" args]]]
  let atypesArr := atypesLoop 1 fieldTypes (setAt (undefArr (n + 1)) 1 (.ty (ops.typeKind ty)))
  let atypes ← splat atypesArr
  pure ⟨atypes, tvars.map JVal.ty, lambda⟩

def innerCtor (ops : DefaultCtorOps) (dt : JType) (tvars fieldTypes : List JType)
    (nany : Nat) (argnames functionloc : JVal) : Except Exc MethodDef := do
  let nparams := tvars.length
  let n := fieldTypes.length
  let nstmts := (n - nany) + (n - nany) + 1
  let (bodyArgs, newArgs) := innerLoop 1 1 fieldTypes (undefArr nstmts) (undefArr n)
  let args ← splat newArgs
  let bodyArgs ← setChecked bodyArgs nstmts (.expr "return" [.expr "new" (argument 1 :: args)])
  let statements ← splat bodyArgs
  let lambda := .expr "lambda" [argnames, .expr "block" (functionloc :: statements)]
  let typedt ← wrapLoop ops tvars nparams (ops.typeKind dt)
  let atypesArr := anyArgsLoop 1 n (setAt (undefArr (n + 1)) 1 (.ty typedt))
  let atypes ← splat atypesArr
  pure ⟨atypes, [], lambda⟩
/-- Errors of the bound methods: the installed `BootCov.Exc` exceptions, Julia's
`ConcurrencyViolationError(msg)` thrown by atomic-order checks (`src/builtins.c:1146-1171`),
and `undefinedBehaviour` for an access that Julia leaves undefined (a read past the end with
bounds checking off, a read of a null `SimpleVector` slot). -/
inductive Err where
  | core (e : Exc)
  | concurrency (msg : String)
  | undefinedBehaviour (what : String)
  deriving Repr, DecidableEq

abbrev RE (α : Type) := Except Err α

/-- `Core.compilerbarrier(setting, val)` (`src/builtins.c:2628-2640`). -/
def compilerbarrier {α : Type} (setting : String) (val : α) : RE α :=
  if setting == "type" || setting == "const" || setting == "conditional" || setting == "blackbox"
  then .ok val
  else .error (.core (.error
    "The first argument of `compilerbarrier` must be either of `:type`, `:const`, `:conditional` or `:blackbox`."))

/--
Julia source: base/essentials.jl:9-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
blackbox(x) = compilerbarrier(:blackbox, x)
```
-/
def blackbox {α : Type} (x : α) : RE α := compilerbarrier "blackbox" x

/--
Julia source: base/essentials.jl:12-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(a::Array) = getfield(a, :size)
```
-/
def sizeArray {A D : Type} (getfield : A → String → D) (a : A) : D := getfield a "size"

/--
Julia source: base/essentials.jl:13-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(t::AbstractArray) = (@inline; prod(size(t)))
```
-/
def lengthAbstract {A D : Type} (size : A → D) (prod : D → JInt .i64) (t : A) : JInt .i64 := prod (size t)

/-- A `GenericMemory` object on the heap: its slots (`none` is `#undef`), its `kind`
parameter (`:atomic` or `:not_atomic`), and its type's layout: element size in bytes
(`layout->size`, 8 for a boxed element) and the `arrayelem_isunion` flag. -/
structure MemObj where
  slots : List (Option JVal)
  atomic : Bool
  elsize : Nat
  isunion : Bool

abbrev Heap := List MemObj

/-- Methods that read or write shared memory; `none` is non-termination (a user `iterate`
that never returns `nothing`). -/
abbrev HM := StateT Heap (ExceptT Err Option)

/-- A memory object, by heap handle (its identity). -/
structure Mem where
  handle : Nat
  deriving DecidableEq

def memObj (m : Mem) : HM MemObj := do
  match (← get)[m.handle]? with
  | some o => pure o
  | none => throw (.undefinedBehaviour "dangling memory handle")

/-- `length(m::GenericMemory)`: its `length` field. -/
def memLength (m : Mem) : HM Nat := do pure (← memObj m).slots.length

/--
Julia source: base/essentials.jl:14-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(a::GenericMemory) = (getfield(a, :length),)
```
-/
def sizeGenericMemory (m : Mem) : HM (List (JInt .i64)) := do
  pure [JInt.wrap .i64 (← memLength m)]

/--
Julia source: base/essentials.jl:15-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
throw_boundserror(A) = (@noinline; throw(BoundsError(A, ())))
```
-/
def throwBoundserror {A I R : Type} (throwBounds : A → List I → Except Exc R) (a : A) : Except Exc R := throwBounds a []

/--
Julia source: base/essentials.jl:16-16 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
throw_boundserror(A, I) = (@noinline; throw(BoundsError(A, I)))
```
-/
def throwBoundserrorIndices {A I R : Type} (throwBounds : A → List I → Except Exc R) (a : A) (indices : List I) : Except Exc R := throwBounds a indices

/--
Julia source: base/essentials.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
throw_boundserror(A, i1, i2, I...) = (@noinline; throw(BoundsError(A, (i1, i2, I...))))
```
-/
def throwBoundserrorMany {A I R : Type} (throwBounds : A → List I → Except Exc R) (a : A) (i1 i2 : I) (rest : List I) : Except Exc R := throwBounds a (i1 :: i2 :: rest)

/--
Julia source: base/essentials.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_throw_boundserror_indices(A) = (@noinline; throw(BoundsError(A, ())))
```
-/
def throwBoundserrorIndicesEmpty {A I R : Type} (throwBounds : A → List I → Except Exc R) (a : A) : Except Exc R := throwBounds a []

/--
Julia source: base/essentials.jl:19-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_throw_boundserror_indices(A, i1, I...) = (@noinline; throw(BoundsError(A, (i1, I...))))
```
-/
def throwBoundserrorIndicesMany {A I R : Type} (throwBounds : A → List I → Except Exc R) (a : A) (i1 : I) (rest : List I) : Except Exc R := throwBounds a (i1 :: rest)

/-- A `Module` object: `id` is its identity (`===`), `name` its `name` field, `parent` the
identity of its `parent` field, `istopmod` the runtime `istopmod` flag (`src/julia.h`). -/
structure Module where
  id : Nat
  name : String
  parent : Nat
  istopmod : Bool
  deriving Repr, DecidableEq

/-- A `GlobalRef` object: its `mod` field (a module object) and `name` field (a Symbol). -/
structure GlobalRefV where
  mod : Module
  name : String

/--
Julia source: base/essentials.jl:23-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(a::GlobalRef, b::GlobalRef) = a.mod === b.mod && a.name === b.name
```
-/
def globalRefEq (a b : GlobalRefV) : Bool := a.mod.id == b.mod.id && a.name == b.name

/--
Julia source: base/essentials.jl:46-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _gc_preserve_begin(arg1)
    Expr(:gc_preserve_begin, esc(arg1))
end
```
-/
def gcPreserveBegin (arg1 : JVal) : JVal := .expr "gc_preserve_begin" [esc arg1]

/--
Julia source: base/essentials.jl:50-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _gc_preserve_end(token)
    Expr(:gc_preserve_end, esc(token))
end
```
-/
def gcPreserveEnd (token : JVal) : JVal := .expr "gc_preserve_end" [esc token]

/--
Julia source: base/essentials.jl:125-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro nospecialize(vars...)
    if nfields(vars) === 1
        # in argument position, need to fix `@nospecialize x=v` to `@nospecialize (kw x v)`
        var = getfield(vars, 1)
        if isa(var, Expr) && var.head === :(=)
            var.head = :kw
        end
    end
    return Expr(:escape, Expr(:meta, :nospecialize, vars...))
end
```
-/
def nospecialize (vars : List JVal) : JVal :=
  let vars := match vars with
    | [value] => [match value with | .expr "=" args => .expr "kw" args | other => other]
    | _ => vars
  .expr "escape" [.expr "meta" (.sym "nospecialize" :: vars)]

/--
Julia source: base/essentials.jl:142-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro specialize(vars...)
    if nfields(vars) === 1
        # in argument position, need to fix `@specialize x=v` to `@specialize (kw x v)`
        var = getfield(vars, 1)
        if isa(var, Expr) && var.head === :(=)
            var.head = :kw
        end
    end
    return Expr(:escape, Expr(:meta, :specialize, vars...))
end
```
-/
def specialize (vars : List JVal) : JVal :=
  let vars := match vars with
    | [value] => [match value with | .expr "=" args => .expr "kw" args | other => other]
    | _ => vars
  .expr "escape" [.expr "meta" (.sym "specialize" :: vars)]

/--
Julia source: base/essentials.jl:184-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro isdefined(s::Symbol)
    return Expr(:escape, Expr(:isdefined, s))
end
```
-/
def isdefinedMacro (sym : String) : JVal := .expr "escape" [.expr "isdefined" [.sym sym]]

/-- `jl_module_name(m)` (`src/module.c:2423`): the `name` field. -/
def moduleName (m : Module) : String := m.name

/--
Julia source: base/essentials.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_nameof(m::Module) = ccall(:jl_module_name, Ref{Symbol}, (Any,), m)
```
-/
def nameofModule (m : Module) : JVal := .sym (moduleName m)

/-- The module objects of a session, by identity, and `jl_top_module`. -/
structure Modules where
  get : Nat → Module
  top : Nat

/-- `jl_base_relative_to(m)` (`src/toplevel.c:369-379`): the first enclosing module flagged
`istopmod`, else `jl_top_module` once the self-parented root is reached. `none` is
non-termination (a parent cycle that never reaches a root). -/
def baseRelativeTo (ms : Modules) (m : Module) : Option Module :=
  if m.istopmod then some m
  else if m.parent == m.id then some (ms.get ms.top)
  else baseRelativeTo ms (ms.get m.parent)
partial_fixpoint

/--
Julia source: base/essentials.jl:190-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _is_internal(__module__)
    return _nameof(__module__) === :Base ||
      _nameof(ccall(:jl_base_relative_to, Any, (Any,), __module__)::Module) === :Compiler
end
```
-/
def isInternal (ms : Modules) (m : Module) : Option Bool := do
  let rel ← baseRelativeTo ms m
  pure (moduleName m == "Base" || moduleName rel == "Compiler")

/-- An effect-annotation macro: `_is_internal(__module__) && Expr(:meta, Expr(:purity, ...))`
with the installed `effectMeta` and the macro's flags. -/
def effectMacro (flags : EffectFlags) (ms : Modules) (m : Module) : Option JVal :=
  (isInternal ms m).map fun internal => effectMeta internal flags

/--
Julia source: base/essentials.jl:196-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _total_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#true,
        #=:effect_free=#true,
        #=:nothrow=#true,
        #=:terminates_globally=#true,
        #=:terminates_locally=#false,
        #=:notaskstate=#true,
        #=:inaccessiblememonly=#true,
        #=:noub=#true,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#true))
end
```
-/
def totalMeta := effectMacro ⟨true, true, true, true, false, true, true, true, false, false, true⟩

/--
Julia source: base/essentials.jl:211-224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _foldable_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#true,
        #=:effect_free=#true,
        #=:nothrow=#false,
        #=:terminates_globally=#true,
        #=:terminates_locally=#false,
        #=:notaskstate=#true,
        #=:inaccessiblememonly=#true,
        #=:noub=#true,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#true))
end
```
-/
def foldableMeta := effectMacro ⟨true, true, false, true, false, true, true, true, false, false, true⟩

/--
Julia source: base/essentials.jl:226-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _terminates_locally_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#false,
        #=:nothrow=#false,
        #=:terminates_globally=#false,
        #=:terminates_locally=#true,
        #=:notaskstate=#false,
        #=:inaccessiblememonly=#false,
        #=:noub=#false,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def terminatesLocallyMeta :=
  effectMacro ⟨false, false, false, false, true, false, false, false, false, false, false⟩

/--
Julia source: base/essentials.jl:241-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _terminates_globally_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#false,
        #=:nothrow=#false,
        #=:terminates_globally=#true,
        #=:terminates_locally=#true,
        #=:notaskstate=#false,
        #=:inaccessiblememonly=#false,
        #=:noub=#false,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def terminatesGloballyMeta :=
  effectMacro ⟨false, false, false, true, true, false, false, false, false, false, false⟩

/--
Julia source: base/essentials.jl:256-269 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _terminates_globally_notaskstate_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#false,
        #=:nothrow=#false,
        #=:terminates_globally=#true,
        #=:terminates_locally=#true,
        #=:notaskstate=#true,
        #=:inaccessiblememonly=#false,
        #=:noub=#false,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def terminatesGloballyNotaskstateMeta :=
  effectMacro ⟨false, false, false, true, true, true, false, false, false, false, false⟩

/--
Julia source: base/essentials.jl:271-284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _terminates_globally_noub_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#false,
        #=:nothrow=#false,
        #=:terminates_globally=#true,
        #=:terminates_locally=#true,
        #=:notaskstate=#false,
        #=:inaccessiblememonly=#false,
        #=:noub=#true,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def terminatesGloballyNoubMeta :=
  effectMacro ⟨false, false, false, true, true, false, false, true, false, false, false⟩

/--
Julia source: base/essentials.jl:286-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _effect_free_terminates_locally_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#true,
        #=:nothrow=#false,
        #=:terminates_globally=#false,
        #=:terminates_locally=#true,
        #=:notaskstate=#false,
        #=:inaccessiblememonly=#false,
        #=:noub=#false,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def effectFreeTerminatesLocallyMeta :=
  effectMacro ⟨false, true, false, false, true, false, false, false, false, false, false⟩

/--
Julia source: base/essentials.jl:301-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _nothrow_noub_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#false,
        #=:nothrow=#true,
        #=:terminates_globally=#false,
        #=:terminates_locally=#false,
        #=:notaskstate=#false,
        #=:inaccessiblememonly=#false,
        #=:noub=#true,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def nothrowNoubMeta :=
  effectMacro ⟨false, false, true, false, false, false, false, true, false, false, false⟩

/--
Julia source: base/essentials.jl:316-329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _nothrow_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#false,
        #=:nothrow=#true,
        #=:terminates_globally=#false,
        #=:terminates_locally=#false,
        #=:notaskstate=#false,
        #=:inaccessiblememonly=#false,
        #=:noub=#false,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def nothrowMeta := effectMacro ⟨false, false, true, false, false, false, false, false, false, false, false⟩

/--
Julia source: base/essentials.jl:331-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _noub_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#false,
        #=:nothrow=#false,
        #=:terminates_globally=#false,
        #=:terminates_locally=#false,
        #=:notaskstate=#false,
        #=:inaccessiblememonly=#false,
        #=:noub=#true,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def noubMeta := effectMacro ⟨false, false, false, false, false, false, false, true, false, false, false⟩

/--
Julia source: base/essentials.jl:346-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _notaskstate_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#false,
        #=:nothrow=#false,
        #=:terminates_globally=#false,
        #=:terminates_locally=#false,
        #=:notaskstate=#true,
        #=:inaccessiblememonly=#false,
        #=:noub=#false,
        #=:noub_if_noinbounds=#false,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def notaskstateMeta := effectMacro ⟨false, false, false, false, false, true, false, false, false, false, false⟩

/--
Julia source: base/essentials.jl:361-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _noub_if_noinbounds_meta()
    return _is_internal(__module__) && Expr(:meta, Expr(:purity,
        #=:consistent=#false,
        #=:effect_free=#false,
        #=:nothrow=#false,
        #=:terminates_globally=#false,
        #=:terminates_locally=#false,
        #=:notaskstate=#false,
        #=:inaccessiblememonly=#false,
        #=:noub=#false,
        #=:noub_if_noinbounds=#true,
        #=:consistent_overlay=#false,
        #=:nortcall=#false))
end
```
-/
def noubIfNoinboundsMeta :=
  effectMacro ⟨false, false, false, false, false, false, false, false, true, false, false⟩

/--
Julia source: base/essentials.jl:377-379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _propagate_inbounds_meta()
    return Expr(:meta, :inline, :propagate_inbounds)
end
```
-/
def propagateInboundsMeta : JVal := .expr "meta" [.sym "inline", .sym "propagate_inbounds"]

/--
Julia source: base/essentials.jl:380-382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro _nospecializeinfer_meta()
    return Expr(:meta, :nospecializeinfer)
end
```
-/
def nospecializeinferMeta : JVal := .expr "meta" [.sym "nospecializeinfer"]

/--
Julia source: base/essentials.jl:385-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checkbounds(::Type{Bool}, A::Union{Array, Memory}, i::Int)
    @inline
    ult_int(bitcast(UInt, sub_int(i, 1)), bitcast(UInt, length(A)))
end
```
-/
def checkboundsBool (len i : JInt .i64) : Bool :=
  JuliaLean.base.int.ult_int
    (JuliaLean.base.int.bitcast .u64
      (JuliaLean.base.int.sub_int i (JuliaLean.base.int.lit .i64 1)) rfl)
    (JuliaLean.base.int.bitcast .u64 len rfl)

/--
Julia source: base/essentials.jl:389-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checkbounds(A::AbstractArray, I...)
    @inline
    checkbounds(Bool, A, I...) || _throw_boundserror_indices(A, I...)
    nothing
end
```
-/
def checkboundsGeneric {A I : Type} (check : A → List I → Bool)
    (throwBounds : A → List I → Except Exc Unit) (a : A) (indices : List I) : Except Exc Unit :=
  if check a indices then .ok () else throwBounds a indices

/--
Julia source: base/essentials.jl:395-395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
default_access_order(::GenericMemory{:not_atomic}) = :not_atomic
```
-/
def defaultAccessOrder (atomic : Bool) : String := if atomic then "monotonic" else "not_atomic"

/--
Julia source: base/essentials.jl:396-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
default_access_order(::GenericMemory{:atomic}) = :monotonic
```
-/
def defaultAccessOrderMemory (atomic : Bool) : String := if atomic then "monotonic" else "not_atomic"

/--
Julia source: base/essentials.jl:397-397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
default_access_order(::GenericMemoryRef{:not_atomic}) = :not_atomic
```
-/
def defaultAccessOrderRef (atomic : Bool) : String := if atomic then "monotonic" else "not_atomic"

/--
Julia source: base/essentials.jl:398-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
default_access_order(::GenericMemoryRef{:atomic}) = :monotonic
```
-/
def defaultAccessOrderMemoryRef (atomic : Bool) : String := if atomic then "monotonic" else "not_atomic"

def liftHM {α : Type} : RE α → HM α
  | .ok a => pure a
  | .error e => throw e

/-- A `GenericMemoryRef`: its memory and 0-based slot offset (`memoryrefoffset - 1`). -/
structure MRef where
  mem : Mem
  index : Nat

/-- `jl_get_atomic_order(order, loading, storing)` (`src/builtins.c:1146-1163`); `none` is
`jl_memory_order_invalid`, `some "not_atomic"` is `jl_memory_order_notatomic`. -/
def atomicOrder (order : String) (loading storing : Bool) : Option String :=
  if order == "not_atomic" then some order
  else if order == "unordered" && (loading != storing) then some order
  else if order == "monotonic" && (loading || storing) then some order
  else if order == "acquire" && loading then some order
  else if order == "release" && storing then some order
  else if order == "acquire_release" && loading && storing then some order
  else if order == "sequentially_consistent" then some order
  else none

/-- `jl_get_atomic_order_checked` (`src/builtins.c:1165-1171`). -/
def atomicOrderChecked (order : String) (loading storing : Bool) : RE String :=
  match atomicOrder order loading storing with
  | some o => .ok o
  | none => .error (.concurrency "invalid atomic ordering")

/-- The order check shared by `memoryrefget` and `memoryrefset!`
(`src/builtins.c:2328-2337, 2356-2368`). -/
def checkAccessOrder (atomic : Bool) (order : String) (loading storing : Bool)
    (wrongAtomic wrongPlain : String) : RE Unit :=
  if !atomic then
    if order != "not_atomic" then do
      let _ ← atomicOrderChecked order loading storing
      .error (.concurrency wrongAtomic)
    else .ok ()
  else do
    let o ← atomicOrderChecked order loading storing
    if o == "not_atomic" then .error (.concurrency wrongPlain) else .ok ()

/-- `memoryrefnew(mem, i, boundscheck)` (`src/builtins.c:2256-2273`): the builtin checks
`(size_t)(i - 1) < length` whatever `boundscheck` is, else `BoundsError(mem, i)` (checked on
nightly: `Core.memoryrefnew(m, 5, false)` and `(m, 0, false)` on a 3-slot memory). -/
def memoryrefnewMem (m : Mem) (i : JInt .i64) (_boundscheck : Bool) : HM MRef := do
  let len ← memLength m
  if 1 ≤ i.val ∧ i.val ≤ len then pure ⟨m, (i.val - 1).toNat⟩
  else throw (.core .bounds)

/-- `memoryrefget(ref, order, boundscheck)` (`src/builtins.c:2318-2341`): order check, a
`BoundsError` for empty memory, then the slot; `#undef` is `UndefRefError`. -/
def memoryrefget (r : MRef) (order : String) (_boundscheck : Bool) : HM JVal := do
  let o ← memObj r.mem
  liftHM (checkAccessOrder o.atomic order true false
    "memoryrefget: non-atomic memory cannot be accessed atomically"
    "memoryrefget: atomic memory cannot be accessed non-atomically")
  if o.slots.length = 0 then throw (.core .bounds)
  match o.slots[r.index]? with
  | some (some v) => pure v
  | some none => throw (.core .undefRef)
  | none => throw (.undefinedBehaviour "memoryrefget past the end")

/-- `default_access_order(a)` (essentials.jl:395-398), the installed model, on the kind. -/
def defaultAccessOrderMem (m : Mem) : HM String := do
  pure (defaultAccessOrder (← memObj m).atomic)

/-- `checkbounds(A, i)` for a one-dimensional linear index: `BoundsError` unless
`1 ≤ i ≤ length(A)` (`BootCov.Arrays.checkboundsBool`). -/
def checkboundsLinear (len i : JInt .i64) : HM Unit :=
  if Arrays.checkboundsBool len i then pure () else throw (.core .bounds)

/--
Julia source: base/essentials.jl:400-404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(A::GenericMemory, i::Int)
    @_noub_if_noinbounds_meta
    (@_boundscheck) && checkbounds(A, i)
    memoryrefget(memoryrefnew(A, i, false), default_access_order(A), false)
end
```
-/
def getindexGenericMemory (boundscheck : Bool) (m : Mem) (i : JInt .i64) : HM JVal := do
  if boundscheck then checkboundsLinear (JInt.wrap .i64 (← memLength m)) i
  let r ← memoryrefnewMem m i false
  memoryrefget r (← defaultAccessOrderMem m) false

/--
Julia source: base/essentials.jl:406-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(A::GenericMemoryRef) = memoryrefget(A, default_access_order(A), @_boundscheck)
```
-/
def getindexGenericMemoryRef (boundscheck : Bool) (r : MRef) : HM JVal := do
  memoryrefget r (← defaultAccessOrderMem r.mem) boundscheck

/--
Julia source: base/essentials.jl:419-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nameof(m::Module) = (@_total_meta; ccall(:jl_module_name, Ref{Symbol}, (Any,), m))
```
-/
def nameof (m : Module) : JVal := .sym (moduleName m)

-- UNTRANSLATED: generic function declaration with no method body.
/-
Julia source: base/essentials.jl:471-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function convert end
```
-/

/--
Julia source: base/essentials.jl:474-474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Union{}}, _...) = throw(ArgumentError("cannot convert a value to Union{} for assignment"))
```
-/
def convertUnionBottom {α R : Type} (_ : List α) : Except Exc R :=
  .error (.argument "cannot convert a value to Union{} for assignment")

/--
Julia source: base/essentials.jl:476-476 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Type}, x::Type) = x # the ssair optimizer is strongly dependent on this method existing to avoid over-specialization
```
-/
def convertTypeIdentity {α : Type} (x : α) : α := x

-- Source reference: base/essentials.jl:480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def convertStringRepresentationIdentity {S : Type} (x : S) : S := x

/--
Julia source: base/essentials.jl:480-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{String}, x::String) = x
```
-/
def convertStringIdentity (x : String) : String := convertStringRepresentationIdentity x

/--
Julia source: base/essentials.jl:488-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro eval(ex)
    return Expr(:let, Expr(:(=), :eval_local_result,
            Expr(:escape, Expr(:call, GlobalRef(Core, :eval), __module__, Expr(:quote, ex)))),
        Expr(:block,
            Expr(:var"latestworld-if-toplevel"),
            :eval_local_result))
end
```
-/
def evalMacro1 (esc : JVal → JVal) (module_ ex : JVal) : JVal :=
  .expr "let" [.expr "=" [.sym "eval_local_result",
    esc (.expr "call" [.globalRef "Core" "eval", module_, .expr "quote" [ex]])],
    .expr "block" [.expr "latestworld-if-toplevel" [], .sym "eval_local_result"]]

/--
Julia source: base/essentials.jl:495-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro eval(mod, ex)
    return Expr(:let, Expr(:(=), :eval_local_result,
            Expr(:escape, Expr(:call, GlobalRef(Core, :eval), mod, Expr(:quote, ex)))),
        Expr(:block,
            Expr(:var"latestworld-if-toplevel"),
            :eval_local_result))
end
```
-/
def evalMacro2 (esc : JVal → JVal) (mod ex : JVal) : JVal :=
  .expr "let" [.expr "=" [.sym "eval_local_result",
    esc (.expr "call" [.globalRef "Core" "eval", mod, .expr "quote" [ex]])],
    .expr "block" [.expr "latestworld-if-toplevel" [], .sym "eval_local_result"]]

/--
Julia source: base/essentials.jl:508-508 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Pairs{K, V, I, A}(data, itr) where {K, V, I, A} = $(Expr(:new, :(Pairs{K, V, I, A}), :(data isa A ? data : convert(A, data)), :(itr isa I ? itr : convert(I, itr))))
```
-/
def pairsCtorFull {K V I A D J : Type}
    (isData : D → Bool) (asData : D → A) (convertData : D → Except Exc A)
    (isIter : J → Bool) (asIter : J → I) (convertIter : J → Except Exc I)
    (data : D) (iter : J) : Except Exc (PairsModel K V I A) := do
  let data ← if isData data then pure (asData data) else convertData data
  let iter ← if isIter iter then pure (asIter iter) else convertIter iter
  pure ⟨data, iter⟩

/--
Julia source: base/essentials.jl:509-509 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Pairs{K, V}(data::A, itr::I) where {K, V, I, A} = $(Expr(:new, :(Pairs{K, V, I, A}), :data, :itr))
```
-/
def pairsCtorKV {K V I A : Type} (data : A) (iter : I) : PairsModel K V I A := ⟨data, iter⟩

/--
Julia source: base/essentials.jl:510-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Pairs{K}(data::A, itr::I) where {K, I, A} = $(Expr(:new, :(Pairs{K, eltype(A), I, A}), :data, :itr))
```
-/
def pairsCtorK {K I A : Type} (eltype : Type → Type)
    (data : A) (iter : I) : PairsModel K (eltype A) I A := ⟨data, iter⟩

/--
Julia source: base/essentials.jl:511-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Pairs(data::A, itr::I) where {I, A} = $(Expr(:new, :(Pairs{I !== Nothing ? eltype(I) : keytype(A), eltype(A), I, A}), :data, :itr))
```
-/
def pairsCtor {A I : Type} (isNothingI : Bool) (eltype keytype : Type → Type)
    (data : A) (iter : I) : PairsModel (if isNothingI then keytype A else eltype I) (eltype A) I A :=
  ⟨data, iter⟩

/--
Julia source: base/essentials.jl:513-513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pairs(::Type{NamedTuple}) = Pairs{Symbol, V, Nothing, NT} where {V, NT <: NamedTuple}
```
-/
def pairsNamedTupleType : JType :=
  let any := JType.dt "Any" true []
  let bot := JType.bottom
  let namedTuple := JType.dt "NamedTuple" true []
  let V := JType.tvar 0 "V" bot any
  let NT := JType.tvar 1 "NT" bot namedTuple
  JType.unionAll V (JType.unionAll NT
    (JType.dt "Pairs" false [JType.dt "Symbol" false [], V, JType.dt "Nothing" false [], NT]))

/--
Julia source: base/essentials.jl:523-523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
argtail(_, rest...) = rest
```
-/
def argtail {α : Type} (_ : α) (rest : List α) : List α := rest

/--
Julia source: base/essentials.jl:541-541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tail(x::Tuple) = argtail(x...)
```
-/
def tail {α : Type} : List α → Except Exc (List α)
  | first :: rest => .ok (argtail first rest)
  | [] => .error (.argument "Cannot call tail on an empty tuple.")

/--
Julia source: base/essentials.jl:542-542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tail(::Tuple{}) = throw(ArgumentError("Cannot call tail on an empty tuple."))
```
-/
def tailEmpty {α : Type} : Except Exc (List α) := .error (.argument "Cannot call tail on an empty tuple.")

/--
Julia source: base/essentials.jl:544-550 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unwrap_unionall(@nospecialize(a))
    @_foldable_meta
    while isa(a,UnionAll)
        a = a.body
    end
    return a
end
```
-/
def unwrapUnionall (a : JType) : JType := Types.unwrapUnionall a

/-- The one lift from the installed `BootCov.R` results. -/
def liftR {α : Type} : R α → RE α
  | .ok a => .ok a
  | .error e => .error (.core e)

/--
Julia source: base/essentials.jl:552-558 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rewrap_unionall(@nospecialize(t), @nospecialize(u))
    @_foldable_meta
    if !isa(u, UnionAll)
        return t
    end
    return UnionAll(u.var, rewrap_unionall(t, u.body))
end
```
-/
def rewrapUnionall (t u : JType) : RE JType := liftR (Types.rewrapUnionall t u)

/--
Julia source: base/essentials.jl:560-571 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rewrap_unionall(t::Core.TypeofVararg, @nospecialize(u))
    @_foldable_meta
    isdefined(t, :T) || return t
    if !isa(u, UnionAll)
        return t
    end
    T = rewrap_unionall(t.T, u)
    if !isdefined(t, :N) || t.N === u.var
        return Vararg{T}
    end
    return Vararg{T, t.N}
end
```
-/
def rewrapUnionallVararg (T N : Option JType) (u : JType) : RE JType :=
  liftR (Types.rewrapUnionallVararg T N u)

/--
Julia source: base/essentials.jl:574-582 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rename_unionall(@nospecialize(u))
    if !isa(u, UnionAll)
        return u
    end
    var = u.var::TypeVar
    body = UnionAll(var, rename_unionall(u.body))
    nv = TypeVar(var.name, var.lb, var.ub)
    return UnionAll(nv, body{nv})
end
```
-/
def renameUnionall (typevarInfo : JType → Except Exc (String × JType × JType))
    (unionAll : JType → JType → Except Exc JType)
    (typevar : String → JType → JType → JType)
    (instantiate : JType → JType → Except Exc JType) : JType → Except Exc JType
  | .unionAll var body => do
    let (name, lb, ub) ← typevarInfo var
    let body ← renameUnionall typevarInfo unionAll typevar instantiate body
    let body ← unionAll var body
    let nv := typevar name lb ub
    let body ← instantiate body nv
    let body ← unionAll nv body
    pure body
  | u => .ok u

/--
Julia source: base/essentials.jl:585-587 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function widen_diagonal(@nospecialize(t), troot::UnionAll)
    return ccall(:jl_widen_diagonal, Any, (Any, Any), t, troot)
end
```
-/
def widenDiagonal (widen : JType → JType → JType) (t root : JType) : JType := widen t root

/--
Julia source: base/essentials.jl:589-591 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isvarargtype(@nospecialize(t))
    return isa(t, Core.TypeofVararg)
end
```
-/
def isvarargtype : JType → Bool
  | .vararg _ _ => true
  | _ => false

/--
Julia source: base/essentials.jl:593-601 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isvatuple(@nospecialize(t))
    @_foldable_meta
    t = unwrap_unionall(t)
    if isa(t, DataType)
        n = length(t.parameters)
        return n > 0 && isvarargtype(t.parameters[n])
    end
    return false
end
```
-/
def isvatuple (t : JType) : Bool :=
  match unwrapUnionall t with
  | .dt _ _ params => match params.getLast? with | some p => isvarargtype p | none => false
  | _ => false

/--
Julia source: base/essentials.jl:603-606 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unwrapva(@nospecialize(t))
    isa(t, Core.TypeofVararg) || return t
    return isdefined(t, :T) ? t.T : Any
end
```
-/
def unwrapva (any : JType) : JType → JType
  | .vararg (some t) _ => t
  | .vararg none _ => any
  | t => t

/--
Julia source: base/essentials.jl:608-613 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unconstrain_vararg_length(va::Core.TypeofVararg)
    # construct a new Vararg type where its length is unconstrained,
    # but its element type still captures any dependencies the input
    # element type may have had on the input length
    return Vararg{unwrapva(va)}
end
```
-/
def unconstrainVarargLength (va : JType) : JType :=
  .vararg (some (unwrapva (.dt "Any" true []) va)) none

/--
Julia source: base/essentials.jl:617-646 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function datatype_min_ninitialized(@nospecialize t0)
    t = unwrap_unionall(t0)
    t isa DataType || return 0
    isabstracttype(t) && return 0
    if t.name === _NAMEDTUPLE_NAME
        names, types = t.parameters[1], t.parameters[2]
        if names isa Tuple
            return length(names)
        end
        t = unwrap_unionall(types)
        t isa DataType || return 0
        t.name === Tuple.name || return 0
    end
    if t.name === Tuple.name
        n = length(t.parameters)
        n == 0 && return 0
        va = t.parameters[n]
        if isvarargtype(va)
            n -= 1
            if isdefined(va, :N)
                va = va.N
                if va isa Int
                    n += va
                end
            end
        end
        return n
    end
    return length(t.name.names) - t.name.n_uninitialized
end
```
-/
def datatypeMinNinitialized (isabstract : JType → Bool)
    (fieldCount uninitialized : JType → Nat) (t0 : JType) : Int :=
  let t := unwrapUnionall t0
  match t with
  | .dt name _ params =>
    if isabstract t then 0
    else if name == "NamedTuple" then
      match params with
      | .names names :: _ => names.length
      | _ :: types :: _ =>
        match unwrapUnionall types with
        | .dt "Tuple" _ tupleParams => tupleMinInitialized tupleParams
        | _ => 0
      | _ => 0
    else if name == "Tuple" then tupleMinInitialized params
    else (fieldCount t : Int) - uninitialized t
  | _ => 0
where
  tupleMinInitialized (params : List JType) : Int :=
    let n : Int := params.length
    if params.isEmpty then 0
    else match params.getLast? with
      | some va =>
        if isvarargtype va then match va with
          | .vararg _ (some (.intParam k)) => n - 1 + k
          | .vararg _ _ => n - 1
          | _ => n
        else n
      | _ => n

/--
Julia source: base/essentials.jl:650-650 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_tuple_error(T::Type, x) = (@noinline; throw(MethodError(convert, (T, x))))
```
-/
def tupleError {T X R : Type} (_ : T) (_ : X) : Except Exc R := .error (.method "convert")

/--
Julia source: base/essentials.jl:652-652 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, x::T) where {T<:Tuple} = x
```
-/
def convertTupleIdentity {T : Type} (x : T) : T := x

/--
Julia source: base/essentials.jl:653-667 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function convert(::Type{T}, x::NTuple{N,Any}) where {N, T<:Tuple}
    # First see if there could be any conversion of the input type that'd be a subtype of the output.
    # If not, we'll throw an explicit MethodError (otherwise, it might throw a typeassert).
    if typeintersect(NTuple{N,Any}, T) === Union{}
        _tuple_error(T, x)
    end
    function cvt1(n)
        @inline
        Tn = fieldtype(T, n)
        xn = getfield(x, n, #=boundscheck=#false)
        xn isa Tn && return xn
        return convert(Tn, xn)
    end
    return ntuple(cvt1, Val(N))::NTuple{N,Any}
end
```
-/
def convertTuple {T X Y A B : Type}
    (disjoint : Nat → T → Bool)
    (fieldtype : T → Nat → Y) (getfield : X → Nat → A)
    (isa : Y → A → Bool)
    (sameType : ∀ y a, isa y a = true → A = B)
    (convert : Y → A → Except Exc B)
    (ntuple : Nat → (Nat → Except Exc B) → Except Exc (List B))
    (target : T) (x : X) (n : Nat) : Except Exc (List B) :=
  if disjoint n target then tupleError target x
  else ntuple n (fun index => do
    let Tn := fieldtype target index
    let xn := getfield x index
    if h : isa Tn xn = true then
      pure (Eq.mp (sameType Tn xn h) xn)
    else convert Tn xn)

/--
Julia source: base/essentials.jl:718-718 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
oftype(x, y) = y isa typeof(x) ? y : convert(typeof(x), y)::typeof(x)
```
-/
def oftype {A B : Type}
    (isa : A → B → Bool)
    (sameType : ∀ x y, isa x y = true → B = A)
    (convert : A → B → Except Exc A)
    (x : A) (y : B) : Except Exc A :=
  if h : isa x y = true then
    .ok (Eq.mp (sameType x y h) y)
  else
    convert x y

/--
Julia source: base/essentials.jl:720-720 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsigned(x::Int) = reinterpret(UInt, x)
```
-/
def unsignedInt (x : JInt .i64) : JInt .u64 := JInt.wrap .u64 x.val

/--
Julia source: base/essentials.jl:721-721 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signed(x::UInt) = reinterpret(Int, x)
```
-/
def signedUInt (x : JInt .u64) : JInt .i64 := JInt.wrap .i64 x.val

-- UNTRANSLATED: generic function declaration with no method body.
/-
Julia source: base/essentials.jl:737-737 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cconvert end
```
-/

/--
Julia source: base/essentials.jl:739-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{T}, x) where {T} = x isa T ? x : convert(T, x) # do the conversion eagerly in most cases
```
-/
def cconvert {T X : Type} (isa : X → Bool) (assert : X → T)
    (convert : X → Except Exc T) (x : X) : Except Exc T :=
  if isa x then .ok (assert x) else convert x

/--
Julia source: base/essentials.jl:740-740 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{Union{}}, x...) = convert(Union{}, x...)
```
-/
def cconvertUnionBottom {α R : Type} (convert : List α → Except Exc R) (xs : List α) : Except Exc R := convert xs

/--
Julia source: base/essentials.jl:741-741 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cconvert(::Type{<:Ptr}, x) = x # but defer the conversion to Ptr to unsafe_convert
```
-/
def cconvertPointer {α : Type} (x : α) : α := x

/--
Julia source: base/essentials.jl:742-742 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{T}, x::T) where {T} = x # unsafe_convert (like convert) defaults to assuming the convert occurred
```
-/
def unsafeConvertIdentity {α : Type} (x : α) : α := x

/--
Julia source: base/essentials.jl:743-743 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{T}, x::T) where {T<:Ptr} = x  # to resolve ambiguity with the next method
```
-/
def unsafeConvertPointerIdentity {α : Type} (x : α) : α := x

/--
Julia source: base/essentials.jl:744-744 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{P}, x::Ptr) where {P<:Ptr} = convert(P, x)
```
-/
def unsafeConvertPointer {P Ptr R : Type} (convert : P → Ptr → R) (target : P) (ptr : Ptr) : R := convert target ptr

/--
Julia source: base/essentials.jl:745-745 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{UInt8}}, s::String) = ccall(:jl_string_ptr, Ptr{UInt8}, (Any,), s)
```
-/
def unsafeConvertStringUInt8 {R : Type} (stringPointer : String → R) (s : String) : R := stringPointer s

/--
Julia source: base/essentials.jl:746-746 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{Int8}}, s::String) = ccall(:jl_string_ptr, Ptr{Int8}, (Any,), s)
```
-/
def unsafeConvertStringInt8 {R : Type} (stringPointer : String → R) (s : String) : R := stringPointer s

-- UNTRANSLATED: generic function declaration with no method body.
/-
Julia source: base/essentials.jl:751-751 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _reinterpret end
```
-/

/--
Julia source: base/essentials.jl:787-794 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reinterpret(::Type{Out}, x) where {Out}
    @inline
    if isprimitivetype(Out) && isprimitivetype(typeof(x))
        return bitcast(Out, x)
    end
    # only available when Base is fully loaded.
    return _reinterpret(Out, x)
end
```
-/
def reinterpret {O X R : Type} (isPrimitiveOut : O → Bool) (isPrimitiveValue : X → Bool)
    (bitcast full : O → X → R) (out : O) (x : X) : R :=
  if isPrimitiveOut out && isPrimitiveValue x then bitcast out x else full out x

/--
Julia source: base/essentials.jl:841-841 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sizeof(x) = Core.sizeof(x)
```
-/
def sizeof {X N : Type} (coreSizeof : X → N) (x : X) : N := coreSizeof x

/--
Julia source: base/essentials.jl:894-894 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ifelse(condition::Bool, x, y) = Core.ifelse(condition, x, y)
```
-/
def ifelse {α : Type} (condition : Bool) (x y : α) : α := if condition then x else y
/-- `Core.ifelse(c, x, y)` (`src/builtins.c:734-739`): `TypeError` unless `c` is a `Bool`. -/
def coreIfelse (c x y : JVal) : RE JVal :=
  match c with
  | .bool false => .ok y
  | .bool true => .ok x
  | _ => .error (.core (.typeError "ifelse"))

/-- A call `ifelse(c, x, y)` of `ifelse(condition::Bool, x, y) = Core.ifelse(condition, x, y)`
(essentials.jl:894): the argument expressions are evaluated left to right before the call;
a non-`Bool` condition has no method (`MethodError`, checked on nightly). -/
def ifelseCall {m : Type → Type} [Monad m] [MonadExceptOf Err m] {E : Type}
    (eval : E → m JVal) (c x y : E) : m JVal := do
  let cv ← eval c
  let xv ← eval x
  let yv ← eval y
  match cv with
  | .bool _ => match coreIfelse cv xv yv with
    | .ok v => pure v
    | .error e => throw e
  | _ => throw (Err.core (.method "ifelse"))


/--
Julia source: base/essentials.jl:903-903 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
esc(@nospecialize(e)) = Expr(:escape, e)
```
-/
def esc (e : JVal) : JVal := .expr "escape" [e]

/--
Julia source: base/essentials.jl:949-951 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro boundscheck(blk)
    return Expr(:if, Expr(:boundscheck), esc(blk))
end
```
-/
def boundscheckMacro (block : JVal) : JVal := .expr "if" [.expr "boundscheck" [], esc block]

/--
Julia source: base/essentials.jl:981-987 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro inbounds(blk)
    return Expr(:block,
        Expr(:inbounds, true),
        Expr(:local, Expr(:(=), :val, esc(blk))),
        Expr(:inbounds, :pop),
        :val)
end
```
-/
def inboundsMacro (block : JVal) : JVal :=
  .expr "block" [.expr "inbounds" [.bool true],
    .expr "local" [.expr "=" [.sym "val", esc block]],
    .expr "inbounds" [.sym "pop"], .sym "val"]

/--
Julia source: base/essentials.jl:1030-1033 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro label(name::Symbol)
    name === :_ && error("use `@label expr` for anonymous blocks; `@label _` is not allowed")
    return esc(Expr(:symboliclabel, name))
end
```
-/
def label1 (name : String) : Except Exc JVal :=
  if name == "_" then .error (.error "use `@label expr` for anonymous blocks; `@label _` is not allowed")
  else .ok (esc (.expr "symboliclabel" [.sym name]))

/--
Julia source: base/essentials.jl:1035-1052 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro label(name::Symbol, body)
    name === :_ && error("use `@label expr` for anonymous blocks; `@label _ expr` is not allowed")
    # If body is a syntactic loop, wrap its body in a continue block
    # This allows `continue name` to work by breaking to `name#cont`
    if body isa Expr && (body.head === :for || body.head === :while)
        cont_name = Symbol(string(name, "#cont"))
        if body.head === :for
            loop_body = body.args[2]
            wrapped_body = Expr(:symbolicblock, cont_name, loop_body)
            body = Expr(:for, body.args[1], wrapped_body)
        else  # while
            loop_body = body.args[2]
            wrapped_body = Expr(:symbolicblock, cont_name, loop_body)
            body = Expr(:while, body.args[1], wrapped_body)
        end
    end
    return esc(Expr(:symbolicblock, name, body))
end
```
-/
def label2 (name : String) (body : JVal) : Except Exc JVal :=
  if name == "_" then .error (.error "use `@label expr` for anonymous blocks; `@label _ expr` is not allowed")
  else
    let body := match body with
      | .expr "for" (iter :: loopBody :: _) =>
        .expr "for" [iter, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]
      | .expr "while" (condition :: loopBody :: _) =>
        .expr "while" [condition, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]
      | other => other
    .ok (esc (.expr "symbolicblock" [.sym name, body]))

/--
Julia source: base/essentials.jl:1054-1058 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro label(body)
    # 1-arg form: create anonymous block that participates in the default break scope.
    # Uses `loop-exit` as the internal label so that `break` and `break _` both target it.
    return esc(Expr(:symbolicblock, Symbol("loop-exit"), body))
end
```
-/
def label0 (body : JVal) : JVal := esc (.expr "symbolicblock" [.sym "loop-exit", body])

/--
Julia source: base/essentials.jl:1068-1070 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro goto(name::Symbol)
    return esc(Expr(:symbolicgoto, name))
end
```
-/
def gotoMacro (name : String) : JVal := esc (.expr "symbolicgoto" [.sym name])

/-- An `Array`: its `ref` and `size` fields. -/
structure Arr where
  ref : MRef
  size : List (JInt .i64)

/-- `memoryrefnew(ref, i, boundscheck)` (`src/builtins.c:2275-2296`): offset `i - 1` from `ref`
in `size_t` arithmetic, so the slot is `(offset(ref) + i - 1) mod 2^64`, checked against the
length whatever `boundscheck` is, else `BoundsError(ref, i)` (checked on nightly: on a
3-slot memory, a ref at slot 2 with `i = 3` throws, with `i = 0` gives slot 1). -/
def memoryrefnewRef (r : MRef) (i : JInt .i64) (_boundscheck : Bool) : HM MRef := do
  let len ← memLength r.mem
  let j := ((r.index : Int) + i.val - 1) % (2 ^ 64 : Int)
  if j < len then pure ⟨r.mem, j.toNat⟩
  else throw (.core .bounds)

/--
Julia source: base/essentials.jl:1073-1077 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(A::Array, i::Int)
    @_noub_if_noinbounds_meta
    @boundscheck checkbounds(A, i)
    memoryrefget(memoryrefnew(getfield(A, :ref), i, false), :not_atomic, false)
end
```
-/
def getindexArray (boundscheck : Bool) (a : Arr) (i : JInt .i64) : HM JVal := do
  if boundscheck then checkboundsLinear (prodDims a.size) i
  let r ← memoryrefnewRef a.ref i false
  memoryrefget r "not_atomic" false

/-- `memoryrefset!(ref, x, order, boundscheck)` (`src/builtins.c:2349-2373`). -/
def memoryrefset (r : MRef) (x : JVal) (order : String) (_boundscheck : Bool) : HM JVal := do
  let o ← memObj r.mem
  liftHM (checkAccessOrder o.atomic order false true
    "memoryrefset!: non-atomic memory cannot be written atomically"
    "memoryrefset!: atomic memory cannot be written non-atomically")
  if o.slots.length = 0 then throw (.core .bounds)
  if r.index < o.slots.length then
    modify fun heap => heap.set r.mem.handle { o with slots := o.slots.set r.index (some x) }
    pure x
  else throw (.undefinedBehaviour "memoryrefset! past the end")

/--
Julia source: base/essentials.jl:1079-1084 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(A::Array{Any}, @nospecialize(x), i::Int)
    @_noub_if_noinbounds_meta
    @boundscheck checkbounds(A, i)
    memoryrefset!(memoryrefnew(getfield(A, :ref), i, false), x, :not_atomic, false)
    return A
end
```
-/
def setindexArrayAny (boundscheck : Bool) (a : Arr) (x : JVal) (i : JInt .i64) : HM Arr := do
  if boundscheck then checkboundsLinear (prodDims a.size) i
  let r ← memoryrefnewRef a.ref i false
  let _ ← memoryrefset r x "not_atomic" false
  pure a

/--
Julia source: base/essentials.jl:1085-1090 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function setindex!(A::Memory{Any}, @nospecialize(x), i::Int)
    @_noub_if_noinbounds_meta
    (@_boundscheck) && checkbounds(A, i)
    memoryrefset!(memoryrefnew(A, i, false), x, :not_atomic, false)
    return A
end
```
-/
def setindexMemoryAny (boundscheck : Bool) (m : Mem) (x : JVal) (i : JInt .i64) : HM Mem := do
  if boundscheck then checkboundsLinear (JInt.wrap .i64 (← memLength m)) i
  let r ← memoryrefnewMem m i false
  let _ ← memoryrefset r x "not_atomic" false
  pure m

/--
Julia source: base/essentials.jl:1091-1091 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setindex!(A::MemoryRef{T}, x) where {T} = (memoryrefset!(A, convert(T, x), :not_atomic, @_boundscheck); A)
```
-/
def setindexMemoryRef (convert : JType → JVal → RE JVal) (T : JType) (boundscheck : Bool)
    (r : MRef) (x : JVal) : HM MRef := do
  let value ← liftHM (convert T x)
  let _ ← memoryrefset r value "not_atomic" boundscheck
  pure r

/--
Julia source: base/essentials.jl:1092-1092 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setindex!(A::MemoryRef{Any}, @nospecialize(x)) = (memoryrefset!(A, x, :not_atomic, @_boundscheck); A)
```
-/
def setindexMemoryRefAny (boundscheck : Bool) (r : MRef) (x : JVal) : HM MRef := do
  let _ ← memoryrefset r x "not_atomic" boundscheck
  pure r

/-- A `SimpleVector` object: its address (`pointer_from_objref`) and slots. A slot is `none`
only in vectors from `jl_alloc_svec` (not public); `Core.svec` fills every slot. -/
structure SVecObj where
  addr : JInt .u64
  slots : List (Option JVal)

/-- `Core._svec_ref(v, i)` (`src/builtins.c:2683-2696`): `BoundsError` outside `1:length(v)`;
a null slot is returned as a null value, which crashes the caller (checked on nightly:
segmentation fault), so it is undefined behaviour here. -/
def svecRefV (v : SVecObj) (i : Int) : RE JVal := do
  match ← liftR (Arrays.svecRef v.slots i) with
  | some x => .ok x
  | none => .error (.undefinedBehaviour "null SimpleVector slot")

/--
Julia source: base/essentials.jl:1096-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(v::SimpleVector, i::Int) = (@_foldable_meta; Core._svec_ref(v, i))
```
-/
def getindexSVec (v : SVecObj) (i : Int) : RE JVal := svecRefV v i

/--
Julia source: base/essentials.jl:1097-1099 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function length(v::SimpleVector)
    Core._svec_len(v)
end
```
-/
def lengthSVec (v : SVecObj) : Nat := Arrays.svecLength v.slots

/--
Julia source: base/essentials.jl:1100-1100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
firstindex(::SimpleVector) = 1
```
-/
def firstindexSVec (_ : SVecObj) : Nat := 1

/--
Julia source: base/essentials.jl:1101-1101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lastindex(v::SimpleVector) = length(v)
```
-/
def lastindexSVec (v : SVecObj) : Nat := lengthSVec v

/--
Julia source: base/essentials.jl:1102-1102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(v::SimpleVector, i=1) = (length(v) < i ? nothing : (v[i], i + 1))
```
-/
def iterateSVec (v : SVecObj) (i : Int := 1) : RE (Option (JVal × Int)) :=
  if (lengthSVec v : Int) < i then .ok none
  else do
    let x ← getindexSVec v i
    pure (some (x, i + 1))

/--
Julia source: base/essentials.jl:1103-1103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{SimpleVector}) = Any
```
-/
def eltypeSVec : String := "Any"

/--
Julia source: base/essentials.jl:1104-1104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keys(v::SimpleVector) = OneTo(length(v))
```
-/
def keysSVec (v : SVecObj) : Nat := lengthSVec v

/--
Julia source: base/essentials.jl:1105-1105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(v::SimpleVector) = (length(v) == 0)
```
-/
def isemptySVec (v : SVecObj) : Bool := lengthSVec v == 0

/--
Julia source: base/essentials.jl:1106-1106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(v::SimpleVector) = (OneTo(length(v)),)
```
-/
def axesSVec (v : SVecObj) : List Nat := [lengthSVec v]

/--
Julia source: base/essentials.jl:1107-1107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(v::SimpleVector, d::Integer) = d <= 1 ? axes(v)[d] : OneTo(1)
```
-/
def axesSVecDim (v : SVecObj) (d : Int) : Except Exc Nat :=
  if d ≤ 1 then if d = 1 then .ok (axesSVec v)[0]! else .error .bounds else .ok 1

/--
Julia source: base/essentials.jl:1109-1115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ==(v1::SimpleVector, v2::SimpleVector)
    length(v1)==length(v2) || return false
    for i = 1:length(v1)
        v1[i] == v2[i] || return false
    end
    return true
end
```
-/
def equalSVec (eq : JVal → JVal → RE JVal) (v1 v2 : SVecObj) : RE Bool := do
  if lengthSVec v1 != lengthSVec v2 then return false
  let rec loop : List Nat → RE Bool
    | [] => .ok true
    | k :: ks => do
      let a ← getindexSVec v1 (k + 1)
      let b ← getindexSVec v2 (k + 1)
      match ← eq a b with
      | .bool true => loop ks
      | .bool false => .ok false
      | _ => .error (.core (.typeError "if"))
  loop (List.range (lengthSVec v1))

/-- `similar(Array{Any}, dims)` (`Array{Any,N}(undef, dims)`, boot.jl): a fresh `Memory{Any}`
of `prod(dims)` unassigned slots and its `Array` header. -/
def allocArrayAny (dims : List (JInt .i64)) : HM Arr := do
  let heap ← get
  let obj : MemObj :=
    ⟨List.replicate (prodDims dims).val.toNat none, false, 8, false⟩
  set (heap ++ [obj])
  pure ⟨⟨⟨heap.length⟩, 0⟩, dims⟩

/-- `copyto!(dest::AbstractArray, src)` (abstractarray.jl:941-951) for an `Array{Any}` `dest`
(linear `eachindex`) and a source given by its `iterate`: each source element is produced first
(its errors come first), then `ArgumentError("destination has fewer elements than required")`
if `dest` is full, then `dest[k] = x`. -/
def copytoArrayAny {Src St : Type} (iterate : Src → Option St → HM (Option (JVal × St)))
    (dest : Arr) (src : Src) (k : Nat) (st : Option St) : HM Unit := do
  match ← iterate src st with
  | none => pure ()
  | some (x, next) =>
      let o ← memObj dest.ref.mem
      if (prodDims dest.size).val ≤ k then
        throw (.core (.argument "destination has fewer elements than required"))
      modify fun heap => heap.set dest.ref.mem.handle
        { o with slots := o.slots.set (dest.ref.index + k) (some x) }
      copytoArrayAny iterate dest src (k + 1) (some next)
partial_fixpoint

/-- `Any[ f(x) for x in itr ]` for an `itr` of known shape: `collect(Any, Generator(f, itr))`,
i.e. `_collect(Any, itr, HasShape)` (array.jl:686-687) allocates `similar(Array{Any},
axes(itr))` (`axes`/`size` is the iterator's own method) and then `copyto!`s the generator,
whose `iterate` (generator.jl:44-50) calls `f` on each element of `itr`. -/
def comprehensionAny {I St : Type} (size : I → HM (List (JInt .i64)))
    (iterate : I → Option St → HM (Option (JVal × St))) (f : JVal → HM JVal) (itr : I) :
    HM Arr := do
  let dest ← allocArrayAny (← size itr)
  copytoArrayAny (fun itr st => do
      match ← iterate itr st with
      | none => pure none
      | some (x, next) => pure (some (← f x, next)))
    dest itr 0 none
  pure dest

/-- `getindex(v::SimpleVector, i)` at a value: only the `Int` method applies (essentials.jl:1096);
any other index value is a `MethodError` (checked on nightly with an `Int32` index). -/
def getindexSVecValue (v : SVecObj) : JVal → RE JVal
  | .int i => getindexSVec v i
  | _ => .error (.core (.method "getindex"))

/--
Julia source: base/essentials.jl:1117-1117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, v::SimpleVector) = Any[ f(v[i]) for i = 1:length(v) ]
```
-/
def mapSVec (f : JVal → HM JVal) (v : SVecObj) : HM Arr :=
  comprehensionAny (fun _ => pure [JInt.wrap .i64 (lengthSVec v)])
    (fun (_ : Unit) (st : Option Nat) => do
      let i := st.getD 1
      if lengthSVec v < i then pure none else pure (some (.int i, i + 1)))
    (fun i => do f (← liftHM (getindexSVecValue v i))) ()

/-- Reading every element of an `Array{Any}` for a splat `xs...` (`iterate` of an `Array`):
an unassigned slot is `UndefRefError`. -/
def readAllAny (a : Arr) : HM (List JVal) := do
  let o ← memObj a.ref.mem
  ((List.range (prodDims a.size).val.toNat).mapM fun k =>
    match o.slots[a.ref.index + k]? with
    | some (some x) => pure x
    | _ => throw (.core .undefRef))

/--
Julia source: base/essentials.jl:1119-1119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(v::SimpleVector, I::AbstractArray) = Core.svec(Any[ v[i] for i in I ]...)
```
-/
def getindexSVecArray {I St : Type} (size : I → HM (List (JInt .i64)))
    (iterate : I → Option St → HM (Option (JVal × St))) (newAddr : JInt .u64) (v : SVecObj)
    (indices : I) : HM SVecObj := do
  let a ← comprehensionAny size iterate (fun i => liftHM (getindexSVecValue v i)) indices
  let xs ← readAllAny a
  pure ⟨newAddr, xs.map some⟩

/--
Julia source: base/essentials.jl:1121-1121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{Any}}, sv::SimpleVector) = convert(Ptr{Any},pointer_from_objref(sv)) + sizeof(Ptr)
```
-/
def unsafeConvertSVec (v : SVecObj) : IntConv.Ptr := ⟨JInt.wrap .u64 (v.addr.val + 8)⟩

-- UNTRANSLATED: generic function declaration with no method body.
/-
Julia source: base/essentials.jl:1149-1149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isassigned end
```
-/

/--
Julia source: base/essentials.jl:1151-1154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isassigned(v::SimpleVector, i::Int)
    @boundscheck 1 <= i <= length(v) || return false
    return true
end
```
-/
def isassignedSVec (v : SVecObj) (i : Int) : Bool := Arrays.svecIsassigned v.slots i

/--
Julia source: base/essentials.jl:1170-1170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Colon() = new()
```
-/
def colonCtor : ColonModel := ⟨⟩

/--
Julia source: base/essentials.jl:1174-1177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::Colon)
    show_type_name(io, Colon.name)
    print(io, "()")
end
```
-/
def showColon {IO : Type} (colonName : JVal)
    (showTypeName : IO → JVal → Except Exc Unit)
    (print : IO → String → Except Exc Unit) (io : IO) : Except Exc Unit := do
  showTypeName io colonName
  print io "()"

/--
Julia source: base/essentials.jl:1200-1200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    Val{x}() where {x} = new()
```
-/
def valValueDefault {α : Type} (x : α) : ValValue x := .mk

/--
Julia source: base/essentials.jl:1203-1203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Val(x) = Val{x}()
```
-/
def valCtor {α : Type} (x : α) : ValValue x := valValueDefault x

/--
Julia source: base/essentials.jl:1211-1211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
inferencebarrier(@nospecialize(x)) = compilerbarrier(:type, x)
```
-/
def inferencebarrier {α : Type} (x : α) : RE α := compilerbarrier "type" x

/--
Julia source: base/essentials.jl:1235-1239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isempty(itr)
    d = isdone(itr)
    d !== missing && return d
    iterate(itr) === nothing
end
```
-/
def isempty {I S : Type} (isdone : I → List S → Option Bool)
    (iterate : I → List S → Option (S × List S)) (itr : I) (state : List S := []) : Bool :=
  match isdone itr state with
  | some done_ => done_
  | none => (iterate itr state).isNone

/--
Julia source: base/essentials.jl:1263-1263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
values(itr) = itr
```
-/
def values {α : Type} (iterator : α) : α := iterator

/--
Julia source: base/essentials.jl:1267-1267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(+)(x::Int, y::Int) = add_int(x, y)
```
-/
def addInt (x y : JInt .i64) : JInt .i64 := JuliaLean.base.int.add_int x y

/--
Julia source: base/essentials.jl:1268-1268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(-)(x::Int, y::Int) = sub_int(x, y)
```
-/
def subInt (x y : JInt .i64) : JInt .i64 := JuliaLean.base.int.sub_int x y

/-- `Core.Intrinsics.not_int` on a `Bool` (`src/runtime_intrinsics.c:1687`; `Bool` is one
bit, checked on nightly: `not_int(true), not_int(false) == (false, true)`). -/
def notIntBool (x : Bool) : Bool := !x

/--
Julia source: base/essentials.jl:1294-1294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
!(x::Bool) = not_int(x)
```
-/
def notBool (x : Bool) : Bool := notIntBool x

/--
Julia source: base/essentials.jl:1296-1296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(a::Array{T,1}) where {T} = getfield(getfield(a, :size), 1)
```
-/
def lengthArray1 {A S N : Type} (getfield : A → String → S) (getindex : S → Nat → N) (a : A) : N := getindex (getfield a "size") 1

/--
Julia source: base/essentials.jl:1298-1298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
has_typevar(@nospecialize(t), v::TypeVar) = ccall(:jl_has_typevar, Int32, (Any, Any), t, v) !== Int32(0)
```
-/
def hasTypevar (ccall : JType → JType → Int32) (t v : JType) : Bool := ccall t v != 0

/--
Julia source: base/essentials.jl:1302-1339 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _fieldtypes_constrain_typevars(tvars::Array{Any,1}, fts::Core.SimpleVector)
    nparams = length(tvars)
    n = length(fts)
    i = nparams
    while i !== 0
        @inbounds tv = tvars[i]::TypeVar
        constrained = false
        j = 1
        while j !== n + 1
            ft = fts[j]
            if has_typevar(ft, tv)
                constrained = true
                break
            end
            j += 1
        end
        if !constrained
            j = i + 1
            remaining = nparams - i
            while remaining !== 0
                @inbounds tv2 = tvars[j]::TypeVar
                if has_typevar(tv2.ub, tv)
                    constrained = true
                    break
                end
                if tv2 === tv
                    constrained = false
                    break
                end
                j += 1
                remaining = remaining - 1
            end
        end
        constrained || return false
        i -= 1
    end
    return true
end
```
-/
def fieldtypesConstrainTypevars (ccall : JType → JType → Int32)
    (isTypevar : JType → Bool) (upperBound : JType → JType)
    (sameType : JType → JType → Bool) (tvars fts : List JType) : Except Exc Bool :=
  outer ccall isTypevar upperBound sameType fts tvars.reverse []
where
  inner (ccall : JType → JType → Int32) (isTypevar : JType → Bool)
      (upperBound : JType → JType) (sameType : JType → JType → Bool)
      (later : List JType) (tv : JType) : Except Exc Bool := do
    match later with
    | [] => pure false
    | tv2 :: rest =>
      if !isTypevar tv2 then .error (.typeError "typeassert")
      else if hasTypevar ccall (upperBound tv2) tv then pure true
      else if sameType tv2 tv then pure false
      else inner ccall isTypevar upperBound sameType rest tv
  outer (ccall : JType → JType → Int32) (isTypevar : JType → Bool)
      (upperBound : JType → JType) (sameType : JType → JType → Bool)
      (fts : List JType) : List JType → List JType → Except Exc Bool
    | [], _ => pure true
    | tv :: rest, later => do
      if !isTypevar tv then .error (.typeError "typeassert") else
        let constrained := fts.any fun ft => hasTypevar ccall ft tv
        if constrained then outer ccall isTypevar upperBound sameType fts rest (later ++ [tv])
        else do
          let linked ← inner ccall isTypevar upperBound sameType later.reverse tv
          if linked then outer ccall isTypevar upperBound sameType fts rest (later ++ [tv])
          else pure false

/--
Julia source: base/essentials.jl:1342-1360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _defaultctor_typeinfo(@nospecialize(ty::Type))
    nparams = 0
    ua = ty
    while isa(ua, UnionAll)
        nparams = nparams + 1
        ua = ua.body
    end
    dt = ua::DataType
    tvars = Array{Any,1}(Core.undef, nparams)
    ua = ty
    i = 1
    while i !== nparams + 1
        @inbounds tvars[i] = (ua::UnionAll).var
        ua = (ua::UnionAll).body
        i = i + 1
    end
    fts = ccall(:jl_get_fieldtypes, Any, (Any,), dt)::Core.SimpleVector
    return dt, tvars, fts
end
```
-/
def defaultctorTypeinfo (fieldtypes : JType → List JType)
    (ty : JType) : Except Exc (JType × List JType × List JType) :=
  let (_, dt) := peelUnionalls ty
  match dt with
  | .dt _ _ _ => .ok (dt, unionallVars ty, fieldtypes dt)
  | _ => .error (.typeError "typeassert")
where
  peelUnionalls : JType → Nat × JType
    | .unionAll _ body => let (n, t) := peelUnionalls body; (n + 1, t)
    | t => (0, t)
  unionallVars : JType → List JType
    | .unionAll var body => var :: unionallVars body
    | _ => []

/--
Julia source: base/essentials.jl:1365-1514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _defaultctors(@nospecialize(ty), functionloc)
    typeinfo = _defaultctor_typeinfo(ty)
    dt = getfield(typeinfo, 1)
    tvars = getfield(typeinfo, 2)
    fts = getfield(typeinfo, 3)
    nparams = length(tvars)

    mod = dt.name.module
    n = length(fts)
    names = dt.name.names::Core.SimpleVector
    src_file = ccall(:jl_symbol_name, Ptr{UInt8}, (Any,), functionloc.file)
    src_line = UInt(functionloc.line)

    is_parametric = nparams !== 0

    # Build argument names using actual field names for slot names (better debugging).
    # The body references arguments via Core.Argument(N) to avoid issues with
    # all-underscore field names being write-only in lowering.
    self = Symbol("#ctor-self#")
    argnames = Array{Any,1}(Core.undef, n + 1)
    @inbounds argnames[1] = self
    i = 1
    nany = 0
    while i !== n + 1
        @inbounds argnames[i + 1] = names[i]::Symbol
        if fts[i] === Any
            nany = nany + 1
        end
        i = i + 1
    end

    if _fieldtypes_constrain_typevars(tvars, fts)
        # Outer constructor: T(x::FT1, y::FT2, ...) = new{A,B,...}(x, y, ...)
        # Build lambda body with direct `new`, no convert calls
        if is_parametric
            # new(apply_type(ty, static_parameter(1), ...), args...)
            curly_args = Array{Any,1}(Core.undef, nparams + 1)
            @inbounds curly_args[1] = ty
            i = 1
            while i !== nparams + 1
                @inbounds curly_args[i + 1] = Expr(:static_parameter, i)
                i = i + 1
            end
            new_target = Expr(:curly, curly_args...)
        else
            new_target = Core.Argument(1)
        end
        new_args = Array{Any,1}(Core.undef, n + 1)
        @inbounds new_args[1] = new_target
        i = 1
        while i !== n + 1
            @inbounds new_args[i + 1] = Core.Argument(i + 1)
            i = i + 1
        end
        new_expr = Expr(:new, new_args...)
        lambda = Expr(:lambda, argnames,
            Expr(:block, functionloc, Expr(:return, new_expr)))
        ci = ccall(:jl_lower, Any, (Any, Any, Ptr{UInt8}, UInt, UInt, Int32),
                   lambda, mod, src_file, src_line, sub_int(UInt(0), UInt(1)), Int32(0))[1]

        # Build argdata: svec(svec(Type{ty}, ft1, ft2, ...), svec(tvars...), functionloc)
        atypes_arr = Array{Any,1}(Core.undef, n + 1)
        @inbounds atypes_arr[1] = Core.apply_type(Type, ty)
        i = 1
        while i !== n + 1
            @inbounds atypes_arr[i + 1] = fts[i]
            i = i + 1
        end
        outer_atypes = Core.svec(atypes_arr...)
        outer_tvars = Core.svec(tvars...)
        argdata = Core.svec(outer_atypes, outer_tvars, functionloc)
        ccall(:jl_method_def, Any, (Any, Ptr{Nothing}, Any, Any),
              argdata, C_NULL, ci, mod)

        # For non-parametric types where all fields are Any, outer constructor suffices
        if nparams === 0
            all_any = true
            i = 1
            while i !== n + 1
                if fts[i] !== Any
                    all_any = false
                    break
                end
                i = i + 1
            end
            if all_any
                return
            end
        end
    end

    # Inner constructor: (::Type{T{A,B,...}})(x, y, ...) with convert calls
    # Build lambda body using Core.Argument references
    nstmts = ((n - nany) + (n - nany)) + 1
    body_args = Array{Any,1}(Core.undef, nstmts)
    new_args = Array{Any,1}(Core.undef, n)
    i = 1
    bidx = 1
    while i !== n + 1
        ft = fts[i]
        if ft === Any
            @inbounds new_args[i] = Core.Argument(i + 1)
        else
            # Use an isa check to avoid depending on convert inlining.
            # This matches the old convert-for-type-decl pattern:
            #   isa(arg, fieldtype(self, i)) ? arg : convert(fieldtype(self, i), arg)
            # The isa check is important because user code may define ambiguous
            # convert methods (e.g. convert(::Any, v::T) = v) that prevent the
            # optimizer from inlining convert(fieldtype(self, i), arg) when the
            # field type is Any after specialization.
            ft_expr = Expr(:call, GlobalRef(Core, :fieldtype), Core.Argument(1), i)
            ft_ssa = Expr(:ssavalue, bidx)
            cnvt_ssa = Expr(:ssavalue, bidx + 1)
            isa_check = Expr(:call, GlobalRef(Core, :isa), Core.Argument(i + 1), ft_ssa)
            convert_expr = Expr(:call, GlobalRef(Base, :convert), ft_ssa, Core.Argument(i + 1))
            @inbounds body_args[bidx] = Expr(:(=), ft_ssa, ft_expr)
            @inbounds body_args[bidx + 1] = Expr(:(=), cnvt_ssa, Expr(:if, isa_check,
                                               Core.Argument(i + 1), convert_expr))
            @inbounds new_args[i] = cnvt_ssa
            bidx = bidx + 2
        end
        i = i + 1
    end
    body_args[nstmts] = Expr(:return, Expr(:new, Core.Argument(1), new_args...))
    lambda = Expr(:lambda, argnames,
        Expr(:block, functionloc, body_args...))
    ci = ccall(:jl_lower, Any, (Any, Any, Ptr{UInt8}, UInt, UInt, Int32),
               lambda, mod, src_file, src_line, sub_int(UInt(0), UInt(1)), Int32(0))[1]

    # Build argdata: svec(svec(UnionAll...Type{dt}..., Any, Any, ...), svec(), functionloc)
    inner_atypes_arr = Array{Any,1}(Core.undef, n + 1)
    typedt = Core.apply_type(Type, dt)
    i = nparams
    while i !== 0
        @inbounds typedt = UnionAll(tvars[i], typedt)
        i = i - 1
    end
    @inbounds inner_atypes_arr[1] = typedt
    i = 1
    while i !== n + 1
        @inbounds inner_atypes_arr[i + 1] = Any
        i = i + 1
    end
    inner_atypes = Core.svec(inner_atypes_arr...)
    inner_tvars = Core.svec()
    argdata = Core.svec(inner_atypes, inner_tvars, functionloc)
    ccall(:jl_method_def, Any, (Any, Ptr{Nothing}, Any, Any),
          argdata, C_NULL, ci, mod)
    return
end
```
-/
def defaultctors (ops : DefaultCtorOps) (ty functionloc : JVal) : Except Exc (List MethodDef) := do
  let ty ← match ty with | .ty t => pure t | _ => .error (.typeError "typeassert")
  let (dt, tvars, fieldTypes) ← defaultctorTypeinfo ops.getFieldtypes ty
  let nparams := tvars.length
  let n := fieldTypes.length
  let names := ops.getNames dt
  let _ ← srcLine functionloc
  let self := .sym "#ctor-self#"
  let (argnames, nany) ← argnamesLoop 1 names fieldTypes (setAt (undefArr (n + 1)) 1 self) 0
  let argnames := .obj "Array{Any,1}" argnames
  let constrained ← fieldtypesConstrainTypevars ops.ccallHasTypevar ops.isTypevar ops.upperBound ops.sameType tvars fieldTypes
  if constrained then do
    let outer ← outerCtor ops ty tvars fieldTypes argnames functionloc
    ops.recordMethod outer
    if nparams == 0 && allAnyLoop fieldTypes then pure [outer]
    else do
      let inner ← innerCtor ops dt tvars fieldTypes nany argnames functionloc
      ops.recordMethod inner
      pure [outer, inner]
  else do
    let inner ← innerCtor ops dt tvars fieldTypes nany argnames functionloc
    ops.recordMethod inner
    pure [inner]

/--
Julia source: base/essentials.jl:1542-1542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ismissing(x) = x === missing
```
-/
def ismissing {α : Type} (isMissing : α → Bool) (x : α) : Bool := isMissing x

-- UNTRANSLATED: generic function declaration with no method body.
/-
Julia source: base/essentials.jl:1544-1544 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function popfirst! end
```
-/

-- UNTRANSLATED: generic function declaration with no method body.
/-
Julia source: base/essentials.jl:1570-1570 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function peek end
```
-/

/--
Julia source: base/essentials.jl:1578-1580 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro __LINE__()
    return __source__.line
end
```
-/
def lineMacro (lineNumber : JVal → Except Exc JVal) (source : JVal) : Except Exc JVal := lineNumber source

/-- The `missing` singleton (`Missing` has no fields). -/
def missingV : JVal := .obj "Missing" []

/-- The user-extensible methods `isempty(itr)` calls: `isdone(itr)` (returning any value) and
`iterate(itr)` (`nothing` or a value and state). -/
structure IterMethods (m : Type → Type) (I S : Type) where
  isdone : I → m JVal
  iterate : I → m (Option (JVal × S))

/--
Julia source: base/essentials.jl:1601-1601 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdone(_, _...) = missing
```
-/
def isdoneDefault {m : Type → Type} [Monad m] {I : Type} (_ : I) : m JVal := pure missingV
/-- An iterator with no `isdone` method of its own. -/
def withFallbackIsdone {m : Type → Type} [Monad m] {I S : Type}
    (iterate : I → m (Option (JVal × S))) : IterMethods m I S :=
  ⟨isdoneDefault, iterate⟩


-- UNTRANSLATED: generic function declaration with no method body.
/-
Julia source: base/essentials.jl:1610-1610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate end
```
-/

/--
Julia source: base/essentials.jl:1618-1620 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isiterable(T)::Bool
    return hasmethod(iterate, Tuple{T})
end
```
-/
def isiterable {T : Type} (hasmethod : T → Bool) (t : T) : Bool := hasmethod t

/--
Julia source: base/essentials.jl:1656-1670 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro world(sym, world)
    if world == :∞
        world = Expr(:call, get_world_counter)
    end
    if isa(sym, Symbol)
        return :($(_resolve_in_world)($(esc(world)), $(QuoteNode(GlobalRef(__module__, sym)))))
    elseif isa(sym, GlobalRef)
        return :($(_resolve_in_world)($(esc(world)), $(QuoteNode(sym))))
    elseif isa(sym, Expr) && sym.head === :(.) &&
            length(sym.args) == 2 && isa(sym.args[2], QuoteNode) && isa(sym.args[2].value, Symbol)
        return :($(_resolve_in_world)($(esc(world)), $(GlobalRef)($(esc(sym.args[1])), $(sym.args[2]))))
    else
        error("`@world` requires a symbol or GlobalRef")
    end
end
```
-/
def worldMacro (moduleName : JVal → String) (getWorldCounter : JVal)
    (module_ sym world : JVal) : Except Exc JVal :=
  let world := match world with
    | .sym "∞" => .expr "call" [getWorldCounter]
    | other => other
  let resolver := .globalRef "Base" "_resolve_in_world"
  match sym with
  | .sym name => .ok (.expr "call" [resolver, esc world, .quoteNode (.globalRef (moduleName module_) name)])
  | .globalRef m name => .ok (.expr "call" [resolver, esc world, .quoteNode (.globalRef m name)])
  | .expr "." [a, .quoteNode (.sym name)] =>
    .ok (.expr "call" [resolver, esc world, .expr "globalref" [esc a, .quoteNode (.sym name)]])
  | _ => .error (.error "`@world` requires a symbol or GlobalRef")

/--
Julia source: base/essentials.jl:1672-1673 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_resolve_in_world(world::Integer, gr::GlobalRef) =
    invoke_in_world(UInt(world), Core.getglobal, gr.mod, gr.name)
```
-/
def resolveInWorld {W G R : Type} (toUInt : W → Except Exc G)
    (invokeInWorld : G → String → String → R) (world : W) (gr : String × String) : Except Exc R := do
  let unsignedWorld ← toUInt world
  pure (invokeInWorld unsignedWorld gr.1 gr.2)

end JuliaLean.base.essentials

namespace JuliaLean.base.essentials.Archive20261101PrimitiveNot

/-- Bind the existing runtime intrinsic, using the established one-bit Bool
representation used by base.bool.boolBits/boolFromBits; this is a representation
adapter, not another Boolean-negation algorithm or a correctness assumption.
Julia source: src/runtime_intrinsics.c:1686-1687 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
#define not_op(a) ~a
un_iintrinsic_fast(APInt_not, not_op, not_int, u)
```
The installed callee is JuliaLean.C.jlNotInt at
JuliaLean/src/runtime_intrinsics_c.lean:46, unchanged.
-/
def notIntBool (x : Bool) : Bool :=
  (JuliaLean.C.jlNotInt (BitVec.ofNat 1 (if x then 1 else 0))).toNat == 1

/--
Julia source: base/essentials.jl:1294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
!(x::Bool) = not_int(x)
```
-/
def notBool (x : Bool) : Bool := notIntBool x

end JuliaLean.base.essentials.Archive20261101PrimitiveNot

namespace JuliaLean.base.essentials.Models1Group18

open JuliaLean JuliaLean.BootCov

/-- Throw the source BoundsError immediately. The installed Exc representation records the exception class; it does not expose BoundsError object/index payloads. All arguments have already been evaluated at method entry.
Julia source: base/essentials.jl:15-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:15-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- throw_boundserror(A) = (@noinline; throw(BoundsError(A, ())))
-- /Source
def throwBoundserror {A R : Type} (_a : A) : Except Exc R := .error .bounds


/-- Throw the source BoundsError immediately. The installed Exc representation records the exception class; it does not expose BoundsError object/index payloads. All arguments have already been evaluated at method entry.
Julia source: base/essentials.jl:16-16 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:16-16 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- throw_boundserror(A, I) = (@noinline; throw(BoundsError(A, I)))
-- /Source
def throwBoundserrorIndices {A I R : Type} (_a : A) (_indices : I) : Except Exc R := .error .bounds


/-- Throw the source BoundsError immediately. The installed Exc representation records the exception class; it does not expose BoundsError object/index payloads. All arguments have already been evaluated at method entry.
Julia source: base/essentials.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- throw_boundserror(A, i1, i2, I...) = (@noinline; throw(BoundsError(A, (i1, i2, I...))))
-- /Source
def throwBoundserrorMany {A I R : Type} (_a : A) (_i1 _i2 : I) (_rest : List I) : Except Exc R := .error .bounds


/-- Throw the source BoundsError immediately. The installed Exc representation records the exception class; it does not expose BoundsError object/index payloads. All arguments have already been evaluated at method entry.
Julia source: base/essentials.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _throw_boundserror_indices(A) = (@noinline; throw(BoundsError(A, ())))
-- /Source
def throwBoundserrorIndicesEmpty {A R : Type} (_a : A) : Except Exc R := .error .bounds


/-- Throw the source BoundsError immediately. The installed Exc representation records the exception class; it does not expose BoundsError object/index payloads. All arguments have already been evaluated at method entry.
Julia source: base/essentials.jl:19-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:19-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _throw_boundserror_indices(A, i1, I...) = (@noinline; throw(BoundsError(A, (i1, I...))))
-- /Source
def throwBoundserrorIndicesMany {A I R : Type} (_a : A) (_i1 : I) (_rest : List I) : Except Exc R := .error .bounds



open JuliaLean

/-- Values of syntax arguments. `Atom` contains every non-Expr, non-Symbol Julia
object, with its original identity; no operation here inspects such an object.
Every Expr is represented by a reference, so cycles and shared subexpressions
are retained. Symbols are interned and represented by their names.
See base/boot.jl:128-131 and doc/src/manual/metaprogramming.md:51-67,190-192. -/
inductive SyntaxValue (Atom : Type) where
  | atom (value : Atom)
  | symbol (name : String)
  | exprRef (handle : Nat)

/-- Logical contents of an Expr. Handles, not these records, are Julia identities.
The args field is never reassigned or mutated by either macro. A none slot is #undef, which can arise after resize!(expr.args); it is preserved without being read. -/
structure SyntaxNode (Atom : Type) where
  head : String
  args : List (Option (SyntaxValue Atom))

abbrev SyntaxHeap (Atom : Type) := List (SyntaxNode Atom)
abbrev SyntaxM (Atom : Type) (α : Type) := StateT (SyntaxHeap Atom) (Except Err) α

/-- A reference is either an ordinary Julia value or an allocated Expr identity. -/
def syntaxValueValid {Atom : Type} (heap : SyntaxHeap Atom) : SyntaxValue Atom → Prop
  | .exprRef handle => handle < heap.length
  | _ => True

/-- Representation invariants. A Tuple's field count fits DataTypeLayout.nfields
(UInt32, base/runtime_internals.jl:624-626). Expr.args is a machine-sized Julia
Vector, and every Expr reference points to the heap. The heap may contain cycles.
Heap handles are mathematical locations, not Julia arithmetic operands. -/
def syntaxInputValid {Atom : Type} (heap : SyntaxHeap Atom)
    (vars : List (SyntaxValue Atom)) : Prop :=
  vars.length ≤ IntTy.u32.max.toNat ∧
  (∀ value ∈ vars, syntaxValueValid heap value) ∧
  (∀ node ∈ heap,
    node.args.length ≤ IntTy.i64.max.toNat ∧
    ∀ slot ∈ node.args, ∀ value, slot = some value → syntaxValueValid heap value)

/-- A concrete heap read; the error denotes an invalid representation, never a
Julia exception on a well-formed Expr reference. -/
def syntaxRead {Atom : Type} (handle : Nat) : SyntaxM Atom (SyntaxNode Atom) := do
  match (← get)[handle]? with
  | some node => pure node
  | none => throw (.undefinedBehaviour "dangling Expr reference")

/-- Concrete `setfield!` for Expr.head. Other fields and all aliases retain their
identity. Retrieving the record is representation administration, not a second
Julia-level evaluation of a user expression. -/
def syntaxSetHead {Atom : Type} (handle : Nat) (head : String) : SyntaxM Atom Unit := do
  let node ← syntaxRead handle
  modify fun heap => heap.set handle { node with head := head }

/-- Concrete logical allocation at the existing `Expr(head,args...)` primitive
boundary, base/boot.jl:327 / BootCov.mkExpr. Two calls allocate distinct Expr
objects and distinct argument vectors; argument values are retained by identity.
As in the installed Expr primitive, resource exhaustion and GC are outside this
logical heap model. This adds identity to the existing value-tree representation,
without an implementation callback or a supplied correctness premise. -/
def syntaxExpr {Atom : Type} (head : String) (args : List (SyntaxValue Atom)) :
    SyntaxM Atom (SyntaxValue Atom) := do
  let heap ← get
  let handle := heap.length
  set (heap ++ [⟨head, args.map some⟩])
  pure (.exprRef handle)

/-- `nfields(vars)` at base/essentials.jl:126,143. The UInt32 field-count invariant
makes this existing Int64 wrapping operation exact on every represented Tuple. -/
def syntaxNfields {Atom : Type} (vars : List (SyntaxValue Atom)) : JInt .i64 :=
  JInt.wrap .i64 vars.length

/-- `getfield(vars,1)` at base/essentials.jl:128,145. The source calls this only
following its singleton tuple test. -/
def syntaxFirst {Atom : Type} (vars : List (SyntaxValue Atom)) :
    SyntaxM Atom (SyntaxValue Atom) :=
  match vars with
  | [] => throw (.core .bounds)
  | value :: _ => pure value

/-- `@nospecialize`, base/essentials.jl:125-134. The original Expr object is changed
in place for a singleton assignment expression; aliases see the new head. The
inner metadata Expr is allocated before the outer escape Expr, as in Julia. -/
-- Source: base/essentials.jl:125-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro nospecialize(vars...)
--     if nfields(vars) === 1
--         # in argument position, need to fix `@nospecialize x=v` to `@nospecialize (kw x v)`
--         var = getfield(vars, 1)
--         if isa(var, Expr) && var.head === :(=)
--             var.head = :kw
--         end
--     end
--     return Expr(:escape, Expr(:meta, :nospecialize, vars...))
-- end
-- /Source
def nospecializeHeap {Atom : Type} (vars : List (SyntaxValue Atom)) :
    SyntaxM Atom (SyntaxValue Atom) := do
  if syntaxNfields vars == JInt.wrap .i64 1 then
    let var ← syntaxFirst vars
    match var with
    | .exprRef handle =>
      let node ← syntaxRead handle
      if node.head == "=" then syntaxSetHead handle "kw"
    | _ => pure ()
  let metadata ← syntaxExpr "meta" (.symbol "nospecialize" :: vars)
  syntaxExpr "escape" [metadata]

/-- `@specialize`, base/essentials.jl:142-151. This reverses the compiler hint by
emitting :specialize metadata, while preserving the same in-place syntax repair
and allocation order as the source. Compiler interpretation of the annotation
is outside the macro-expansion method. -/
-- Source: base/essentials.jl:142-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro specialize(vars...)
--     if nfields(vars) === 1
--         # in argument position, need to fix `@specialize x=v` to `@specialize (kw x v)`
--         var = getfield(vars, 1)
--         if isa(var, Expr) && var.head === :(=)
--             var.head = :kw
--         end
--     end
--     return Expr(:escape, Expr(:meta, :specialize, vars...))
-- end
-- /Source
def specializeHeap {Atom : Type} (vars : List (SyntaxValue Atom)) :
    SyntaxM Atom (SyntaxValue Atom) := do
  if syntaxNfields vars == JInt.wrap .i64 1 then
    let var ← syntaxFirst vars
    match var with
    | .exprRef handle =>
      let node ← syntaxRead handle
      if node.head == "=" then syntaxSetHead handle "kw"
    | _ => pure ()
  let metadata ← syntaxExpr "meta" (.symbol "specialize" :: vars)
  syntaxExpr "escape" [metadata]


/-- Preserve the left-to-right short circuit before querying the installed module-parent runtime model. Modules.get and Modules.top are the pre-existing module-table boundary; no new runtime oracle is introduced.
Julia source: base/essentials.jl:190-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:190-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _is_internal(__module__)
--     return _nameof(__module__) === :Base ||
--       _nameof(ccall(:jl_base_relative_to, Any, (Any,), __module__)::Module) === :Compiler
-- end
-- /Source
def isInternal (ms : Modules) (m : Module) : Option Bool := do
  if moduleName m == "Base" then
    pure true
  else
    let relative ← baseRelativeTo ms m
    pure (moduleName relative == "Compiler")


/-- A source argument to _is_internal. Module values retain the existing runtime
identity/parent record. Other represents every non-Module Julia value; no operation
inspects its contents. This restores the unannotated source argument domain. -/
inductive ModuleInput (Other : Type) where
  | module (value : Module)
  | other (value : Other)

/-- Full source argument domain of _is_internal, including the first _nameof MethodError on a non-Module argument (its sole pinned method is at188). The typed isInternal helper is used by macros whose implicit __module__ is always a Module.
Julia source: base/essentials.jl:190-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:190-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _is_internal(__module__)
--     return _nameof(__module__) === :Base ||
--       _nameof(ccall(:jl_base_relative_to, Any, (Any,), __module__)::Module) === :Compiler
-- end
-- /Source
def isInternalAny {Other : Type} (ms : Modules) (arg : ModuleInput Other) :
    Option (Except Err Bool) :=
  match arg with
  | .module value => (isInternal ms value).map Except.ok
  | .other _ => some (.error (.core (.method "_nameof")))

/-- Internal compiler-annotation macro with source-order module gating and the exact eleven source flags. The installed effectMeta constructor emits syntax only; compiler interpretation remains outside this macro model.
Julia source: base/essentials.jl:196-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:196-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro _total_meta()
--     return _is_internal(__module__) && Expr(:meta, Expr(:purity,
--         #=:consistent=#true,
--         #=:effect_free=#true,
--         #=:nothrow=#true,
--         #=:terminates_globally=#true,
--         #=:terminates_locally=#false,
--         #=:notaskstate=#true,
--         #=:inaccessiblememonly=#true,
--         #=:noub=#true,
--         #=:noub_if_noinbounds=#false,
--         #=:consistent_overlay=#false,
--         #=:nortcall=#true))
-- end
-- /Source
def totalMeta (ms : Modules) (m : Module) : Option JVal :=
  (isInternal ms m).map fun internal =>
    effectMeta internal ⟨true, true, true, true, false, true, true, true, false, false, true⟩


/-- Internal compiler-annotation macro with source-order module gating and the exact eleven source flags. The installed effectMeta constructor emits syntax only; compiler interpretation remains outside this macro model.
Julia source: base/essentials.jl:211-224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:211-224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro _foldable_meta()
--     return _is_internal(__module__) && Expr(:meta, Expr(:purity,
--         #=:consistent=#true,
--         #=:effect_free=#true,
--         #=:nothrow=#false,
--         #=:terminates_globally=#true,
--         #=:terminates_locally=#false,
--         #=:notaskstate=#true,
--         #=:inaccessiblememonly=#true,
--         #=:noub=#true,
--         #=:noub_if_noinbounds=#false,
--         #=:consistent_overlay=#false,
--         #=:nortcall=#true))
-- end
-- /Source
def foldableMeta (ms : Modules) (m : Module) : Option JVal :=
  (isInternal ms m).map fun internal =>
    effectMeta internal ⟨true, true, false, true, false, true, true, true, false, false, true⟩


/-- Internal compiler-annotation macro with source-order module gating and the exact eleven source flags. The installed effectMeta constructor emits syntax only; compiler interpretation remains outside this macro model.
Julia source: base/essentials.jl:226-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:226-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro _terminates_locally_meta()
--     return _is_internal(__module__) && Expr(:meta, Expr(:purity,
--         #=:consistent=#false,
--         #=:effect_free=#false,
--         #=:nothrow=#false,
--         #=:terminates_globally=#false,
--         #=:terminates_locally=#true,
--         #=:notaskstate=#false,
--         #=:inaccessiblememonly=#false,
--         #=:noub=#false,
--         #=:noub_if_noinbounds=#false,
--         #=:consistent_overlay=#false,
--         #=:nortcall=#false))
-- end
-- /Source
def terminatesLocallyMeta (ms : Modules) (m : Module) : Option JVal :=
  (isInternal ms m).map fun internal =>
    effectMeta internal ⟨false, false, false, false, true, false, false, false, false, false, false⟩


/-- Internal compiler-annotation macro with source-order module gating and the exact eleven source flags. The installed effectMeta constructor emits syntax only; compiler interpretation remains outside this macro model.
Julia source: base/essentials.jl:241-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:241-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro _terminates_globally_meta()
--     return _is_internal(__module__) && Expr(:meta, Expr(:purity,
--         #=:consistent=#false,
--         #=:effect_free=#false,
--         #=:nothrow=#false,
--         #=:terminates_globally=#true,
--         #=:terminates_locally=#true,
--         #=:notaskstate=#false,
--         #=:inaccessiblememonly=#false,
--         #=:noub=#false,
--         #=:noub_if_noinbounds=#false,
--         #=:consistent_overlay=#false,
--         #=:nortcall=#false))
-- end
-- /Source
def terminatesGloballyMeta (ms : Modules) (m : Module) : Option JVal :=
  (isInternal ms m).map fun internal =>
    effectMeta internal ⟨false, false, false, true, true, false, false, false, false, false, false⟩


/-- Internal compiler-annotation macro with source-order module gating and the exact eleven source flags. The installed effectMeta constructor emits syntax only; compiler interpretation remains outside this macro model.
Julia source: base/essentials.jl:256-269 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:256-269 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro _terminates_globally_notaskstate_meta()
--     return _is_internal(__module__) && Expr(:meta, Expr(:purity,
--         #=:consistent=#false,
--         #=:effect_free=#false,
--         #=:nothrow=#false,
--         #=:terminates_globally=#true,
--         #=:terminates_locally=#true,
--         #=:notaskstate=#true,
--         #=:inaccessiblememonly=#false,
--         #=:noub=#false,
--         #=:noub_if_noinbounds=#false,
--         #=:consistent_overlay=#false,
--         #=:nortcall=#false))
-- end
-- /Source
def terminatesGloballyNotaskstateMeta (ms : Modules) (m : Module) : Option JVal :=
  (isInternal ms m).map fun internal =>
    effectMeta internal ⟨false, false, false, true, true, true, false, false, false, false, false⟩


/-- Internal compiler-annotation macro with source-order module gating and the exact eleven source flags. The installed effectMeta constructor emits syntax only; compiler interpretation remains outside this macro model.
Julia source: base/essentials.jl:271-284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:271-284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro _terminates_globally_noub_meta()
--     return _is_internal(__module__) && Expr(:meta, Expr(:purity,
--         #=:consistent=#false,
--         #=:effect_free=#false,
--         #=:nothrow=#false,
--         #=:terminates_globally=#true,
--         #=:terminates_locally=#true,
--         #=:notaskstate=#false,
--         #=:inaccessiblememonly=#false,
--         #=:noub=#true,
--         #=:noub_if_noinbounds=#false,
--         #=:consistent_overlay=#false,
--         #=:nortcall=#false))
-- end
-- /Source
def terminatesGloballyNoubMeta (ms : Modules) (m : Module) : Option JVal :=
  (isInternal ms m).map fun internal =>
    effectMeta internal ⟨false, false, false, true, true, false, false, true, false, false, false⟩


/-- Internal compiler-annotation macro with source-order module gating and the exact eleven source flags. The installed effectMeta constructor emits syntax only; compiler interpretation remains outside this macro model.
Julia source: base/essentials.jl:286-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:286-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro _effect_free_terminates_locally_meta()
--     return _is_internal(__module__) && Expr(:meta, Expr(:purity,
--         #=:consistent=#false,
--         #=:effect_free=#true,
--         #=:nothrow=#false,
--         #=:terminates_globally=#false,
--         #=:terminates_locally=#true,
--         #=:notaskstate=#false,
--         #=:inaccessiblememonly=#false,
--         #=:noub=#false,
--         #=:noub_if_noinbounds=#false,
--         #=:consistent_overlay=#false,
--         #=:nortcall=#false))
-- end
-- /Source
def effectFreeTerminatesLocallyMeta (ms : Modules) (m : Module) : Option JVal :=
  (isInternal ms m).map fun internal =>
    effectMeta internal ⟨false, true, false, false, true, false, false, false, false, false, false⟩


/-- Internal compiler-annotation macro with source-order module gating and the exact eleven source flags. The installed effectMeta constructor emits syntax only; compiler interpretation remains outside this macro model.
Julia source: base/essentials.jl:301-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:301-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro _nothrow_noub_meta()
--     return _is_internal(__module__) && Expr(:meta, Expr(:purity,
--         #=:consistent=#false,
--         #=:effect_free=#false,
--         #=:nothrow=#true,
--         #=:terminates_globally=#false,
--         #=:terminates_locally=#false,
--         #=:notaskstate=#false,
--         #=:inaccessiblememonly=#false,
--         #=:noub=#true,
--         #=:noub_if_noinbounds=#false,
--         #=:consistent_overlay=#false,
--         #=:nortcall=#false))
-- end
-- /Source
def nothrowNoubMeta (ms : Modules) (m : Module) : Option JVal :=
  (isInternal ms m).map fun internal =>
    effectMeta internal ⟨false, false, true, false, false, false, false, true, false, false, false⟩


/-- Internal compiler-annotation macro with source-order module gating and the exact eleven source flags. The installed effectMeta constructor emits syntax only; compiler interpretation remains outside this macro model.
Julia source: base/essentials.jl:316-329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:316-329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro _nothrow_meta()
--     return _is_internal(__module__) && Expr(:meta, Expr(:purity,
--         #=:consistent=#false,
--         #=:effect_free=#false,
--         #=:nothrow=#true,
--         #=:terminates_globally=#false,
--         #=:terminates_locally=#false,
--         #=:notaskstate=#false,
--         #=:inaccessiblememonly=#false,
--         #=:noub=#false,
--         #=:noub_if_noinbounds=#false,
--         #=:consistent_overlay=#false,
--         #=:nortcall=#false))
-- end
-- /Source
def nothrowMeta (ms : Modules) (m : Module) : Option JVal :=
  (isInternal ms m).map fun internal =>
    effectMeta internal ⟨false, false, true, false, false, false, false, false, false, false, false⟩


/-- Internal compiler-annotation macro with source-order module gating and the exact eleven source flags. The installed effectMeta constructor emits syntax only; compiler interpretation remains outside this macro model.
Julia source: base/essentials.jl:331-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:331-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro _noub_meta()
--     return _is_internal(__module__) && Expr(:meta, Expr(:purity,
--         #=:consistent=#false,
--         #=:effect_free=#false,
--         #=:nothrow=#false,
--         #=:terminates_globally=#false,
--         #=:terminates_locally=#false,
--         #=:notaskstate=#false,
--         #=:inaccessiblememonly=#false,
--         #=:noub=#true,
--         #=:noub_if_noinbounds=#false,
--         #=:consistent_overlay=#false,
--         #=:nortcall=#false))
-- end
-- /Source
def noubMeta (ms : Modules) (m : Module) : Option JVal :=
  (isInternal ms m).map fun internal =>
    effectMeta internal ⟨false, false, false, false, false, false, false, true, false, false, false⟩


/-- Internal compiler-annotation macro with source-order module gating and the exact eleven source flags. The installed effectMeta constructor emits syntax only; compiler interpretation remains outside this macro model.
Julia source: base/essentials.jl:346-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:346-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro _notaskstate_meta()
--     return _is_internal(__module__) && Expr(:meta, Expr(:purity,
--         #=:consistent=#false,
--         #=:effect_free=#false,
--         #=:nothrow=#false,
--         #=:terminates_globally=#false,
--         #=:terminates_locally=#false,
--         #=:notaskstate=#true,
--         #=:inaccessiblememonly=#false,
--         #=:noub=#false,
--         #=:noub_if_noinbounds=#false,
--         #=:consistent_overlay=#false,
--         #=:nortcall=#false))
-- end
-- /Source
def notaskstateMeta (ms : Modules) (m : Module) : Option JVal :=
  (isInternal ms m).map fun internal =>
    effectMeta internal ⟨false, false, false, false, false, true, false, false, false, false, false⟩


/-- Internal compiler-annotation macro with source-order module gating and the exact eleven source flags. The installed effectMeta constructor emits syntax only; compiler interpretation remains outside this macro model.
Julia source: base/essentials.jl:361-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:361-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro _noub_if_noinbounds_meta()
--     return _is_internal(__module__) && Expr(:meta, Expr(:purity,
--         #=:consistent=#false,
--         #=:effect_free=#false,
--         #=:nothrow=#false,
--         #=:terminates_globally=#false,
--         #=:terminates_locally=#false,
--         #=:notaskstate=#false,
--         #=:inaccessiblememonly=#false,
--         #=:noub=#false,
--         #=:noub_if_noinbounds=#true,
--         #=:consistent_overlay=#false,
--         #=:nortcall=#false))
-- end
-- /Source
def noubIfNoinboundsMeta (ms : Modules) (m : Module) : Option JVal :=
  (isInternal ms m).map fun internal =>
    effectMeta internal ⟨false, false, false, false, false, false, false, false, true, false, false⟩


/-- Bind the existing syntax construction to the concrete installed escape constructor. For the one-argument form, target is the implicit __module__; for the two-argument form it is the supplied module expression. Runtime evaluation is emitted as syntax, not replaced with a callback.
Julia source: base/essentials.jl:488-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:488-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro eval(ex)
--     return Expr(:let, Expr(:(=), :eval_local_result,
--             Expr(:escape, Expr(:call, GlobalRef(Core, :eval), __module__, Expr(:quote, ex)))),
--         Expr(:block,
--             Expr(:var"latestworld-if-toplevel"),
--             :eval_local_result))
-- end
-- /Source
def evalOne (target code : JVal) : JVal :=
  JuliaLean.base.essentials.evalMacro1 JuliaLean.base.essentials.esc target code


/-- Bind the existing syntax construction to the concrete installed escape constructor. For the one-argument form, target is the implicit __module__; for the two-argument form it is the supplied module expression. Runtime evaluation is emitted as syntax, not replaced with a callback.
Julia source: base/essentials.jl:495-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:495-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro eval(mod, ex)
--     return Expr(:let, Expr(:(=), :eval_local_result,
--             Expr(:escape, Expr(:call, GlobalRef(Core, :eval), mod, Expr(:quote, ex)))),
--         Expr(:block,
--             Expr(:var"latestworld-if-toplevel"),
--             :eval_local_result))
-- end
-- /Source
def evalTwo (target code : JVal) : JVal :=
  JuliaLean.base.essentials.evalMacro2 JuliaLean.base.essentials.esc target code



open JuliaLean

/-- An initialized SimpleVector's contents, whose Julia Int length is representable.
Used only for stored type parameters and field names (base/essentials.jl:622,631,645).
This is concrete metadata, not a function returning an assumed runtime answer. -/
structure MinInitVector (α : Type) where
  values : List α
  lengthFits : values.length ≤ IntTy.i64.max.toNat

/-- A stored Tuple value, with the actual UInt32 datatype field-count bound from
base/runtime_internals.jl:624-626. Its elements are not inspected by this method. -/
structure MinInitTuple (Atom : Type) where
  fields : List Atom
  fieldCountFits : fields.length ≤ IntTy.u32.max.toNat

/-- TypeName identity. The two distinguished identities are the actual Tuple and
NamedTuple TypeNames, not their printed name strings. All other TypeNames retain
an object identity token. -/
inductive MinInitNameIdentity where
  | tupleName
  | namedTupleName
  | other (identity : Nat)
  deriving BEq, DecidableEq

/-- Concrete TypeName fields read by the method or isabstracttype. The pinned
TypeName dump in doc/src/devdocs/types.md:175-209 specifies names::SimpleVector,
n_uninitialized::Int32 (line205), and flags::UInt8 (line206). -/
structure MinInitTypeName where
  identity : MinInitNameIdentity
  names : MinInitVector String
  nUninitialized : JInt .i32
  flags : JInt .u8

/-- Read-only runtime objects sufficient for every branch of
base/essentials.jl:617-646. Handles preserve arbitrary sharing and cycles.
Every DataType, UnionAll, Tuple value, Vararg object, and machine Int uses its
corresponding constructor. `other` includes all remaining objects/types, whose
contents are never inspected. The unobserved UnionAll binder and Vararg element
are retained as original object tokens. Vararg N is undefined exactly when its
optional handle is none. -/
inductive MinInitObject (Atom : Type) where
  | dataType (name : MinInitTypeName) (parameters : MinInitVector Nat)
  | unionAll (binder : Atom) (body : Nat)
  | tuple (values : MinInitTuple Atom)
  | vararg (element : Option Atom) (length : Option Nat)
  | machineInt (value : JInt .i64)
  | other (value : Atom)

abbrev MinInitHeap (Atom : Type) := List (MinInitObject Atom)
/-- As in the installed cyclic module traversal, none denotes nontermination.
The error case preserves the installed essentials error type. -/
abbrev MinInitM (α : Type) := ExceptT Err Option α

/-- Read a represented runtime object. A dangling handle is invalid representation
(undefined behavior), not a default answer or a fabricated Julia exception. -/
def minInitRead {Atom : Type} (heap : MinInitHeap Atom) (handle : Nat) :
    MinInitM (MinInitObject Atom) :=
  match heap[handle]? with
  | some object => pure object
  | none => throw (.undefinedBehaviour "dangling datatype metadata handle")

/-- Enriched-representation lift of the existing unwrapUnionall operation,
base/essentials.jl:544-550. The original JType tree cannot retain the TypeName
metadata required below, so this helper follows concrete UnionAll body handles.
It does not invoke a type solver or any arbitrary implementation parameter. -/
-- Source: base/essentials.jl:544-550 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unwrap_unionall(@nospecialize(a))
--     @_foldable_meta
--     while isa(a,UnionAll)
--         a = a.body
--     end
--     return a
-- end
-- /Source
def minInitUnwrap {Atom : Type} (heap : MinInitHeap Atom) (handle : Nat) : MinInitM Nat := do
  match ← minInitRead heap handle with
  | .unionAll _ body => minInitUnwrap heap body
  | _ => pure handle
partial_fixpoint

/-- `isabstracttype` restricted to the already-checked DataType domain, as needed
by base/essentials.jl:620. The source's TypeEq/TypeEgal and UnionAll tests are false
on this domain. The UInt8 bit operation uses the installed intrinsic model.
Additional callee dependency: base/runtime_internals.jl:1186-1192. -/
-- Source: base/runtime_internals.jl:1186-1192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function isabstracttype(@nospecialize(t))
--     @_total_meta
--     t = unwrap_unionall(t)
--     isType(t) && return true
--     # TODO: what to do for `Union`?
--     return isa(t, DataType) && (t.name.flags & 0x1) == 0x1
-- end
-- /Source
def minInitDatatypeIsabstract (name : MinInitTypeName) : Bool :=
  JuliaLean.base.int.and_int name.flags (JInt.wrap .u8 1) == JInt.wrap .u8 1

/-- Length of an initialized stored SimpleVector; the representation bound makes
this Int64 representation exact. Source uses at base/essentials.jl:631,645. -/
def minInitLength {α : Type} (vector : MinInitVector α) : JInt .i64 :=
  JInt.wrap .i64 vector.values.length

/-- Checked one-based SimpleVector access. The Nat conversion is a representation
address calculation after the source index has been checked, not replacement of
any Julia machine arithmetic. All metadata slots here are initialized; invalid
indices retain BoundsError. Source uses at base/essentials.jl:622,633. -/
def minInitParameter {α : Type} (vector : MinInitVector α) (index : JInt .i64) :
    MinInitM α := do
  if index.val < 1 then throw (.core .bounds)
  else match vector.values[(index.val - 1).toNat]? with
    | some value => pure value
    | none => throw (.core .bounds)

/-- Source tail, base/essentials.jl:630-645. It is shared by the direct DataType
path and the NamedTuple fallback without moving any earlier test or access.
All n -= 1, n += va, and field-count subtraction operations use installed Int64
wrapping operations. The stored Int32 n_uninitialized is sign-extended first,
as required by promotion (base/int.jl:811). -/
def minInitDatatypeTail {Atom : Type} (heap : MinInitHeap Atom)
    (name : MinInitTypeName) (parameters : MinInitVector Nat) : MinInitM (JInt .i64) := do
  if name.identity == .tupleName then
    let mut n := minInitLength parameters
    if n == JInt.wrap .i64 0 then return JInt.wrap .i64 0
    let parameter ← minInitParameter parameters n
    let va ← minInitRead heap parameter
    match va with
    | .vararg _ length =>
      n := JuliaLean.base.essentials.subInt n (JInt.wrap .i64 1)
      match length with
      | some lengthHandle =>
        let lengthValue ← minInitRead heap lengthHandle
        match lengthValue with
        | .machineInt value => n := JuliaLean.base.essentials.addInt n value
        | _ => pure ()
      | none => pure ()
    | _ => pure ()
    return n
  return JuliaLean.base.essentials.subInt (minInitLength name.names)
    (JuliaLean.base.int.sext_int .i64 name.nUninitialized (by decide))

/-- `datatype_min_ninitialized`, base/essentials.jl:617-646. The supplied heap is
a concrete snapshot of runtime objects, not a collection of callee callbacks.
Both NamedTuple parameter reads occur before inspecting names, retaining source
errors and their order. The NamedTuple fallback does not repeat isabstracttype,
matching Julia. Metadata is never mutated. -/
-- Source: base/essentials.jl:617-646 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function datatype_min_ninitialized(@nospecialize t0)
--     t = unwrap_unionall(t0)
--     t isa DataType || return 0
--     isabstracttype(t) && return 0
--     if t.name === _NAMEDTUPLE_NAME
--         names, types = t.parameters[1], t.parameters[2]
--         if names isa Tuple
--             return length(names)
--         end
--         t = unwrap_unionall(types)
--         t isa DataType || return 0
--         t.name === Tuple.name || return 0
--     end
--     if t.name === Tuple.name
--         n = length(t.parameters)
--         n == 0 && return 0
--         va = t.parameters[n]
--         if isvarargtype(va)
--             n -= 1
--             if isdefined(va, :N)
--                 va = va.N
--                 if va isa Int
--                     n += va
--                 end
--             end
--         end
--         return n
--     end
--     return length(t.name.names) - t.name.n_uninitialized
-- end
-- /Source
def datatypeMinNinitializedHeap {Atom : Type} (heap : MinInitHeap Atom)
    (t0 : Nat) : MinInitM (JInt .i64) := do
  let t ← minInitUnwrap heap t0
  let object ← minInitRead heap t
  match object with
  | .dataType name parameters =>
    if minInitDatatypeIsabstract name then return JInt.wrap .i64 0
    if name.identity == .namedTupleName then
      let namesHandle ← minInitParameter parameters (JInt.wrap .i64 1)
      let typesHandle ← minInitParameter parameters (JInt.wrap .i64 2)
      let names ← minInitRead heap namesHandle
      match names with
      | .tuple values => return JInt.wrap .i64 values.fields.length
      | _ => pure ()
      let types ← minInitUnwrap heap typesHandle
      let typesObject ← minInitRead heap types
      match typesObject with
      | .dataType tupleName tupleParameters =>
        if tupleName.identity != .tupleName then return JInt.wrap .i64 0
        minInitDatatypeTail heap tupleName tupleParameters
      | _ => return JInt.wrap .i64 0
    else
      minInitDatatypeTail heap name parameters
  | _ => return JInt.wrap .i64 0


/-- The Union{} C-conversion method uses the already installed concrete convert-to-bottom implementation, retaining its immediate ArgumentError.
Julia source: base/essentials.jl:740-740 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:740-740 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cconvert(::Type{Union{}}, x...) = convert(Union{}, x...)
-- /Source
def cconvertBottom {A R : Type} (args : List A) : Except Exc R :=
  JuliaLean.base.essentials.convertUnionBottom args



open JuliaLean

/-- Read an Expr.args Array{Any,1} element with the source's checked access.
Absent indices produce BoundsError; an allocated but undefined slot produces
UndefRefError. The index is a Julia Int64, and conversion to a logical list
address happens only after the lower-bound test. This representation adapter
is required by base/essentials.jl:1042,1044,1046,1048; the installed getindexArray
uses JVal memory, which cannot retain this richer SyntaxValue identity heap. -/
def syntaxArg {Atom : Type} (handle : Nat) (index : JInt .i64) :
    SyntaxM Atom (SyntaxValue Atom) := do
  let node ← syntaxRead handle
  if index.val < 1 then throw (.core .bounds)
  else match node.args[(index.val - 1).toNat]? with
    | none => throw (.core .bounds)
    | some none => throw (.core .undefRef)
    | some (some value) => pure value

/-- The named-block @label macro, base/essentials.jl:1035-1052. It preserves all
input Expr objects and argument arrays. A syntactic loop receives a fresh body
wrapper targeting name#cont and a fresh loop. The source reads argument 2 before
allocating that wrapper, and reads argument 1 only afterward. Slots beyond 2
are never inspected. The invalid '_' label is rejected before any body access.
Logical Expr allocation uses the established syntaxExpr primitive boundary;
compiler/lowering interpretation and resource exhaustion are outside expansion. -/
-- Source: base/essentials.jl:1035-1052 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro label(name::Symbol, body)
--     name === :_ && error("use `@label expr` for anonymous blocks; `@label _ expr` is not allowed")
--     # If body is a syntactic loop, wrap its body in a continue block
--     # This allows `continue name` to work by breaking to `name#cont`
--     if body isa Expr && (body.head === :for || body.head === :while)
--         cont_name = Symbol(string(name, "#cont"))
--         if body.head === :for
--             loop_body = body.args[2]
--             wrapped_body = Expr(:symbolicblock, cont_name, loop_body)
--             body = Expr(:for, body.args[1], wrapped_body)
--         else  # while
--             loop_body = body.args[2]
--             wrapped_body = Expr(:symbolicblock, cont_name, loop_body)
--             body = Expr(:while, body.args[1], wrapped_body)
--         end
--     end
--     return esc(Expr(:symbolicblock, name, body))
-- end
-- /Source
def labelHeap {Atom : Type} (name : String) (body : SyntaxValue Atom) :
    SyntaxM Atom (SyntaxValue Atom) := do
  if name == "_" then
    throw (.core (.error "use `@label expr` for anonymous blocks; `@label _ expr` is not allowed"))
  let mut body := body
  match body with
  | .exprRef handle =>
    let node ← syntaxRead handle
    if node.head == "for" || node.head == "while" then
      let contName := name ++ "#cont"
      if node.head == "for" then
        let loopBody ← syntaxArg handle (JInt.wrap .i64 2)
        let wrappedBody ← syntaxExpr "symbolicblock" [.symbol contName, loopBody]
        let header ← syntaxArg handle (JInt.wrap .i64 1)
        body ← syntaxExpr "for" [header, wrappedBody]
      else
        let loopBody ← syntaxArg handle (JInt.wrap .i64 2)
        let wrappedBody ← syntaxExpr "symbolicblock" [.symbol contName, loopBody]
        let header ← syntaxArg handle (JInt.wrap .i64 1)
        body ← syntaxExpr "while" [header, wrappedBody]
  | _ => pure ()
  let labelled ← syntaxExpr "symbolicblock" [.symbol name, body]
  syntaxExpr "escape" [labelled]


/-- A constructible SimpleVector. Slot counts are representable Julia Ints;
null internal slots are deliberately allowed. The stored pointer is already a
machine UInt64 in SVecObj. The proof is a representation invariant, not a
successful-access or callee-correctness premise. Source: base/essentials.jl:1096-1106. -/
structure SizedSVec where
  obj : SVecObj
  lengthFits : obj.slots.length ≤ IntTy.i64.max.toNat

/-- OneTo{Int64} is represented by its stored stop field; lower bound and step are
fixed at one by the type. Source: base/range.jl:478-486. -/
structure OneTo64 where
  stop : JInt .i64


/-- Machine-sized SimpleVector method, binding the existing stored-slot/length primitive. Invalid signed indices retain BoundsError; null internal slots retain the installed undefined-behavior marker.
Julia source: base/essentials.jl:1096-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:1096-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getindex(v::SimpleVector, i::Int) = (@_foldable_meta; Core._svec_ref(v, i))
-- /Source
def svecGetindex64 (v : SizedSVec) (i : JInt .i64) : RE JVal :=
  svecRefV v.obj i.val


/-- Machine-sized SimpleVector method, binding the existing stored-slot/length primitive. Invalid signed indices retain BoundsError; null internal slots retain the installed undefined-behavior marker.
Julia source: base/essentials.jl:1097-1099 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:1097-1099 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function length(v::SimpleVector)
--     Core._svec_len(v)
-- end
-- /Source
def svecLength64 (v : SizedSVec) : JInt .i64 :=
  JInt.wrap .i64 (Arrays.svecLength v.obj.slots)


/-- Machine-sized SimpleVector method, binding the existing stored-slot/length primitive. Invalid signed indices retain BoundsError; null internal slots retain the installed undefined-behavior marker.
Julia source: base/essentials.jl:1100-1100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:1100-1100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- firstindex(::SimpleVector) = 1
-- /Source
def svecFirstindex64 (_v : SizedSVec) : JInt .i64 := JInt.wrap .i64 1


/-- Machine-sized SimpleVector method, binding the existing stored-slot/length primitive. Invalid signed indices retain BoundsError; null internal slots retain the installed undefined-behavior marker.
Julia source: base/essentials.jl:1101-1101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:1101-1101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- lastindex(v::SimpleVector) = length(v)
-- /Source
def svecLastindex64 (v : SizedSVec) : JInt .i64 := svecLength64 v


/-- Required extra dependency: OneTo specialized to Int64, using the installed
machine-integer max implementation. Bool rejection is impossible in this fixed
Int64 constructor. This is a concrete callee model, not an abstract range callback.
Julia source: base/range.jl:485-491,505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:485-491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct OneTo{T<:Integer} <: AbstractOneTo{T}
--     stop::T # invariant: stop >= zero(stop)
--     function OneTo{T}(stop) where {T<:Integer}
--         throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
--         T === Bool && throwbool(stop)
--         return new(max(zero(T), stop))
--     end
-- /Source
-- Source: base/range.jl:505-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- OneTo(stop::T) where {T<:Integer} = OneTo{T}(stop)
-- /Source
def oneTo64 (stop : JInt .i64) : OneTo64 :=
  ⟨JuliaLean.base.int.max_BitInteger (JInt.wrap .i64 0) stop⟩

/-- Return a typed OneTo range from the actual machine length.
Julia source: base/essentials.jl:1104-1104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:1104-1104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- keys(v::SimpleVector) = OneTo(length(v))
-- /Source
def svecKeys64 (v : SizedSVec) : OneTo64 := oneTo64 (svecLength64 v)


/-- The one-dimensional axes tuple contains one OneTo{Int64} range.
Julia source: base/essentials.jl:1106-1106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:1106-1106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(v::SimpleVector) = (OneTo(length(v)),)
-- /Source
def svecAxes64 (v : SizedSVec) : List OneTo64 := [oneTo64 (svecLength64 v)]


namespace MapState

open JuliaLean JuliaLean.BootCov JuliaLean.base.essentials

/-- The number of slots must be a nonnegative Julia Int. This bound alone does
not assert that a boxed output array of the same length can be allocated. -/
structure SizedSVec where
  obj : SVecObj
  machineSize : obj.slots.length ≤ IntTy.i64.max.toNat

/-- The existing Heap identity boundary, with ExceptT outside StateT so that
caught exceptions retain writes. f below is the ACTUAL Julia function argument,
not a missing-callee substitute or a supplied correctness law. -/
abbrev KeptHM (α : Type) := ExceptT Err (StateT Heap Option) α

/-- Return every terminating outcome together with its observable final heap. -/
def runKept {α : Type} (action : KeptHM α) (heap : Heap) :
    Option (Except Err α × Heap) := action.run heap

/-- Bind a fixed, pure installed SimpleVector primitive. No state is lost on error.
Dependency: Core._svec_ref at source base/essentials.jl:1096, implemented by the
installed getindexSVec/svecRefV/BootCov.Arrays.svecRef chain. -/
def readSlot (v : SizedSVec) (i : JInt .i64) : KeptHM JVal :=
  match JuliaLean.base.essentials.getindexSVec v.obj i.val with
  | .ok value => pure value
  | .error error => throw error

/-- Logical handle zero denotes the runtime's already-existing empty
Memory{Any} instance. Reserving this identity only renumbers logical handles;
it does not rule out any Julia heap. Allocation of another empty Array reuses
this memory identity while constructing its Array header, as in the installed
Arr representation. -/
def HeapInvariant (heap : Heap) : Prop :=
  heap[0]? = some (⟨[], false, 8, false⟩ : MemObj)

/-- The largest count allowed for a non-union, boxed 8-byte Memory{Any} by
src/genericmemory.c:55-73 on the configured 64-bit platform. Its constraints
are nel < 2^63-2 and 8*nel < 2^63-2, giving nel ≤ 2^60-1. This is runtime
metadata; actual counts and indices remain JInt values. -/
def anyAllocationMax : Nat := 2 ^ 60 - 1

/-- Allocation for the fixed non-atomic, boxed Memory{Any} layout.
Source dependencies: base/boot.jl:762,821-824 and src/genericmemory.c:55-73,75-102
at f755f49a9e41380d7da126b3c1db9fe7f83dd027. The zero branch returns the canonical
empty Memory identity. Positive allocation uses the INSTALLED memorynew size
checker, with its actual fixed eight-byte layout bound, and appends the slots
it returns. No arbitrary allocator or successful-allocation assumption is
supplied. Physical resource exhaustion is outside the installed memorynew
logical allocation model; this binding does not claim to add that semantics. -/
def allocateChecked (n : JInt .i64) : KeptHM Arr := do
  if n.val = 0 then
    pure ⟨⟨⟨0⟩, 0⟩, [n]⟩
  else
    match Arrays.memorynew anyAllocationMax n with
    | .error error => throw (.core error)
    | .ok slots =>
      let heap ← get
      set (heap ++ [⟨slots, false, 8, false⟩])
      pure ⟨⟨⟨heap.length⟩, 0⟩, [n]⟩

/-- Bind ONLY installed setindexArrayAny, whose exceptions precede its sole
write. It checks bounds, computes the reference, checks memory order, then
writes; successful writes are retained, including when a later f call fails.
Dependency: base/essentials.jl:1079-1084 and memoryrefset in the existing file. -/
def storeSlot (a : Arr) (value : JVal) (i : JInt .i64) : KeptHM Unit := fun heap =>
  match (JuliaLean.base.essentials.setindexArrayAny true a value i).run heap with
  | none => none
  | some (.error error) => some (.error error, heap)
  | some (.ok (_, heap')) => some (.ok (), heap')

/-- Structural fuel is exactly the immutable source vector's remaining length;
it is a Lean termination device, not a Julia integer or an allocation bound.
Every source loop index is JInt, and the final iteration stops before adding
one, just as OrdinalRange iteration compares with last(r) before incrementing
(base/range.jl:935-942). f is called after reading v[i] and before storing its
result. The fixed store call preserves its own checks and exception order. -/
def mapLoop (f : JVal → KeptHM JVal) (v : SizedSVec) (a : Arr)
    (last : JInt .i64) : Nat → JInt .i64 → KeptHM Unit
  | 0, _ => pure ()
  | remaining + 1, i => do
    let input ← readSlot v i
    let output ← f input
    storeSlot a output i
    if i.val = last.val then pure ()
    else mapLoop f v a last remaining (JuliaLean.base.essentials.addInt i (JInt.lit .i64 1))

/-- Source method at base/essentials.jl:1117. Preserves f's ordinary and
exceptional represented heap effects and exact allocate/read/f/store order.
`HeapInvariant` designates the canonical empty Memory{Any}. The function is
interpreted at the existing logical Heap/Arr and allocation boundary. -/
-- Source: base/essentials.jl:1117-1117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- map(f, v::SimpleVector) = Any[ f(v[i]) for i = 1:length(v) ]
-- /Source
def mapSVec (f : JVal → KeptHM JVal) (v : SizedSVec) : KeptHM Arr := do
  let n := JInt.wrap .i64 v.obj.slots.length
  let output ← allocateChecked n
  mapLoop f v output n v.obj.slots.length (JInt.lit .i64 1)
  pure output


end MapState

/-- Retain the source bounds-check-elision flag and chained machine comparisons. This pinned method tests bounds only; it does not read the slot or inspect whether an internal slot is null.
Julia source: base/essentials.jl:1151-1154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:1151-1154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function isassigned(v::SimpleVector, i::Int)
--     @boundscheck 1 <= i <= length(v) || return false
--     return true
-- end
-- /Source
def svecIsassigned64 (boundscheck : Bool) (v : SizedSVec) (i : JInt .i64) : Bool := Id.run do
  if boundscheck then
    if !(JuliaLean.base.int.sle_int (JInt.wrap .i64 1) i &&
        JuliaLean.base.int.sle_int i (svecLength64 v)) then
      return false
  return true



open JuliaLean JuliaLean.BootCov

/-- Local recognition of the canonical missing singleton used by the comparison
at base/essentials.jl:1237. The installed missingV reserves `.obj "Missing" []`
for the unique fieldless Missing value; this helper does not translate the later
public ismissing method. Every other returned JVal is retained unchanged. -/
def isemptyMissingHint : JVal → Bool
  | .obj "Missing" [] => true
  | _ => false

/-- isempty at the EXISTING explicit IterMethods boundary, base/essentials.jl:1235-1239.
The wrapper implements all source control flow while the same monad preserves
callee errors, nontermination, and state effects. User-defined isdone and iterate
remain the installed explicit interface; this is not a model of their internals.
A non-missing hint is returned unchanged, including a non-Bool result. -/
-- Source: base/essentials.jl:1235-1239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function isempty(itr)
--     d = isdone(itr)
--     d !== missing && return d
--     iterate(itr) === nothing
-- end
-- /Source
def isemptyAtBoundary {m : Type → Type} [Monad m] {I S : Type}
    (methods : IterMethods m I S) (itr : I) : m JVal := do
  let hint ← methods.isdone itr
  if !isemptyMissingHint hint then return hint
  let next ← methods.iterate itr
  return .bool next.isNone


namespace TypevarQuery

open JuliaLean JuliaLean.base.essentials
open JuliaLean.base.essentials.Models1Group18

/-- Concrete runtime forms read by jl_has_bound_typevars. Addresses are logical
heap locations, retaining exact object identity, sharing and cycles. A DataType's
hasfreetypevars is its stored cache bit, not a supplied function/oracle. -/
inductive Object (Atom : Type) where
  | dataType (hasFreeTypevars : Bool) (parameters : MinInitVector Nat)
  | typevar (lower upper : Nat)
  | unionAll (var body : Nat)
  | typeApp (head param : Nat)
  | unionType (a b : Nat)
  | intersectType (a b : Nat)
  | typeEq (parameter : Nat)
  | typeEgal (parameter : Nat)
  | vararg (element length : Option Nat)
  | other (value : Atom)

/-- Read-only runtime heap and the identities of jl_bottom_type / jl_any_type.
The constructor tags and fields represent actual objects; dangling addresses or
a non-TypeVar UnionAll binder are invalid representations, never a default answer.
Source: src/jltypes.c:270-340. -/
structure World (Atom : Type) where
  objects : List (Object Atom)
  bottom : Nat
  anyType : Nat

abbrev M (α : Type) := ExceptT Err Option α

/-- Concrete heap read. None in the effect monad means nontermination; an invalid
pointer is explicitly undefined behavior, consistent with the existing model. -/
def readObject {Atom : Type} (world : World Atom) (handle : Nat) : M (Object Atom) :=
  match world.objects[handle]? with
  | some object => pure object
  | none => throw (.undefinedBehaviour "dangling typevar-query object")

/-- The actual TypeVar dispatch domain of has_typevar(t,v::TypeVar). Its fields
and heap equality are representation facts, not semantic correctness premises. -/
structure TypeVarRef {Atom : Type} (world : World Atom) where
  handle : Nat
  lower : Nat
  upper : Nat
  objectEq : world.objects[handle]? = some (.typevar lower upper)

/-- jl_typeenv_t, newest entry first. None is a C NULL val; some var is the
self-binding that masks any older binding of the same variable. -/
structure EnvEntry where
  var : Nat
  val : Option Nat

abbrev Env := List EnvEntry

/-- Nearest-binding lookup from src/jltypes.c:48-56, preserving the C pointer
comparison and the masking effect of a self-binding. -/
-- Source: src/jltypes.c:48-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static int typeenv_has_ne(jl_typeenv_t *env, jl_tvar_t *v) JL_NOTSAFEPOINT
-- {
--     while (env != NULL) {
--         if (env->var == v)
--             return env->val != (jl_value_t*)v; // consider it actually not present if it is bound to itself unchanging
--         env = env->prev;
--     }
--     return 0;
-- }
-- /Source
def envHasNe (env : Env) (var : Nat) : Bool :=
  match env with
  | [] => false
  | entry :: rest =>
    if entry.var == var then entry.val != some var else envHasNe rest var

/-- Read a UnionAll binder's fields. The C cast has a TypeVar representation
invariant; violating it is undefined behavior, not a Julia TypeError. -/
def binderBounds {Atom : Type} (world : World Atom) (var : Nat) : M (Nat × Nat) := do
  match ← readObject world var with
  | .typevar lower upper => pure (lower, upper)
  | _ => throw (.undefinedBehaviour "UnionAll binder is not a TypeVar")

mutual
/-- Complete local implementation of the strictly needed C primitive. Each
short-circuit is in source order: TypeApp head before parameter, UnionAll lower
bound before upper bound before a temporarily masked body, left before right,
and Vararg's undefined-T test before N, followed by T. Scope changes do not leak
from a recursive call into siblings. Every terminal C result is exactly 0 or 1,
represented internally by Bool and converted back to Int32 by jlHasTypevar below.
No subtype or normalization operation is required. -/
-- Source: src/jltypes.c:270-340 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- // test whether a type has vars bound by the given environment
-- int jl_has_bound_typevars(jl_value_t *v, jl_typeenv_t *env) JL_NOTSAFEPOINT
-- {
--     while (1) {
--         if (jl_is_datatype(v) && !((jl_datatype_t*)v)->hasfreetypevars)
--             return 0;
--         if (jl_is_typevar(v)) {
--             return typeenv_has_ne(env, (jl_tvar_t*)v);
--         }
--         if (jl_is_typeapp(v)) {
--             jl_typeapp_t *ta = (jl_typeapp_t*)v;
--             if (jl_has_bound_typevars(ta->head, env))
--                 return 1;
--             v = ta->param;
--             continue;
--         }
--         while (jl_is_unionall(v)) {
--             jl_unionall_t *ua = (jl_unionall_t*)v;
--             if (ua->var->lb != jl_bottom_type && jl_has_bound_typevars(ua->var->lb, env))
--                 return 1;
--             if (ua->var->ub != (jl_value_t*)jl_any_type && jl_has_bound_typevars(ua->var->ub, env))
--                 return 1;
--             // Temporarily remove this var from env if necessary
--             // Note that te might be bound more than once in the env, so
--             // we remove it by setting it to itself in a new env.
--             if (typeenv_has_ne(env, ua->var)) {
--                 jl_typeenv_t *newenv = (jl_typeenv_t*)alloca(sizeof(jl_typeenv_t));
--                 newenv->var = ua->var;
--                 newenv->val = (jl_value_t*)ua->var;
--                 newenv->prev = env;
--                 env = newenv;
--             }
--             v = ua->body;
--         }
--         // After unwrapping UnionAll, body might be TypeApp or TypeVar;
--         // restart the loop so those checks at the top fire.
--         if (jl_is_typeapp(v) || jl_is_typevar(v))
--             continue;
--         if (jl_is_datatype(v)) {
--             if (!((jl_datatype_t*)v)->hasfreetypevars)
--                 return 0;
--             size_t i;
--             for (i = 0; i < jl_nparams(v); i++) {
--                 if (jl_has_bound_typevars(jl_tparam(v, i), env))
--                     return 1;
--             }
--             return 0;
--         }
--         else if (jl_is_uniontype(v) || jl_is_intersecttype(v)) {
--             if (jl_has_bound_typevars(((jl_uniontype_t*)v)->a, env))
--                 return 1;
--            v = ((jl_uniontype_t*)v)->b;
--         }
--         else if (jl_is_some_Type(v)) {
--             v = jl_some_Type_T(v);
--         }
--         else if (jl_is_vararg(v)) {
--             jl_vararg_t *vm = (jl_vararg_t *)v;
--             if (!vm->T)
--                 return 0;
--             if (vm->N) {
--                 if (jl_has_bound_typevars(vm->N, env))
--                     return 1;
--             }
--             v = vm->T;
--         }
--         else {
--             return 0;
--         }
--     }
-- }
-- /Source
def hasBoundTypevars {Atom : Type} (world : World Atom) (value : Nat) (env : Env) : M Bool := do
  match ← readObject world value with
  | .dataType hasFree parameters =>
    if !hasFree then return false
    scanParameters world parameters (JInt.wrap .u64 0) env
  | .typevar _ _ => return envHasNe env value
  | .typeApp head param =>
    if ← hasBoundTypevars world head env then return true
    hasBoundTypevars world param env
  | .unionAll var body =>
    let (lower, upper) ← binderBounds world var
    if lower != world.bottom then
      if ← hasBoundTypevars world lower env then return true
    if upper != world.anyType then
      if ← hasBoundTypevars world upper env then return true
    let env := if envHasNe env var then ⟨var, some var⟩ :: env else env
    hasBoundTypevars world body env
  | .unionType a b | .intersectType a b =>
    if ← hasBoundTypevars world a env then return true
    hasBoundTypevars world b env
  | .typeEq parameter | .typeEgal parameter => hasBoundTypevars world parameter env
  | .vararg element length =>
    match element with
    | none => return false
    | some element =>
      match length with
      | some length =>
        if ← hasBoundTypevars world length env then return true
      | none => pure ()
      hasBoundTypevars world element env
  | .other _ => return false
partial_fixpoint

/-- The DataType parameter loop at src/jltypes.c:308-316, with its actual size_t
(UInt64) counter. Parameter storage has a representable length, so this counter
cannot wrap before the loop terminates. No parameter follows a successful hit. -/
def scanParameters {Atom : Type} (world : World Atom) (parameters : MinInitVector Nat)
    (index : JInt .u64) (env : Env) : M Bool := do
  if index < JInt.wrap .u64 parameters.values.length then
    match parameters.values[index.val.toNat]? with
    | none => throw (.undefinedBehaviour "invalid datatype parameter index")
    | some parameter =>
      if ← hasBoundTypevars world parameter env then return true
      scanParameters world parameters (JuliaLean.base.int.add_int index (JInt.wrap .u64 1)) env
  else return false
partial_fixpoint
end

/-- jl_has_typevar returns the exact C int encoding of the Boolean query; all
primitive branches return either 0 or 1, so conversion to Julia Int32 is exact. -/
-- Source: src/jltypes.c:342-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT int jl_has_typevar(jl_value_t *t, jl_tvar_t *v) JL_NOTSAFEPOINT
-- {
--     jl_typeenv_t env = { v, NULL, NULL };
--     return jl_has_bound_typevars(t, &env);
-- }
-- /Source
def jlHasTypevar {Atom : Type} (world : World Atom) (t : Nat) (v : TypeVarRef world) :
    M (JInt .i32) := do
  let found ← hasBoundTypevars world t [⟨v.handle, none⟩]
  pure (JInt.wrap .i32 (if found then 1 else 0))

/-- has_typevar at base/essentials.jl:1298. The first argument may be any runtime
object; the second has the actual TypeVar representation required by dispatch.
The primitive is implemented above, rather than assumed via a callback. -/
-- Source: base/essentials.jl:1298-1298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- has_typevar(@nospecialize(t), v::TypeVar) = ccall(:jl_has_typevar, Int32, (Any, Any), t, v) !== Int32(0)
-- /Source
def hasTypevar {Atom : Type} (world : World Atom) (t : Nat) (v : TypeVarRef world) : M Bool := do
  let result ← jlHasTypevar world t v
  pure (result != JInt.wrap .i32 0)

/-- The observed slots of a one-dimensional Any array or SimpleVector. The
length is a Julia Int and every slot is represented, including #undef/null. -/
abbrev Slots := MinInitVector (Option Nat)

/-- The source's ::TypeVar assertion (base/essentials.jl:1307,1322). This is a
concrete tag test; its successful proof records only a stored representation fact. -/
def assertTypevar {Atom : Type} (world : World Atom) (handle : Nat) : M (TypeVarRef world) :=
  match equality : world.objects[handle]? with
  | some (.typevar lower upper) => pure ⟨handle, lower, upper, equality⟩
  | some _ => throw (.core (.typeError "typeassert"))
  | none => throw (.undefinedBehaviour "dangling object at TypeVar assertion")

/-- @inbounds read of tvars::Array{Any,1}, retaining UndefRefError for an undefined
allocated slot. The outer/later loop counters stay within this bounded vector.
The unreachable out-of-range branches mark a loop/representation-invariant
violation; this helper does not specify arbitrary unchecked Array accesses,
whose backing capacity and offset are outside Slots. Source:1307,1322. -/
def tvarArrayRead (array : Slots) (index : JInt .i64) : M Nat := do
  if index.val < 1 then
    throw (.undefinedBehaviour "unchecked typevar array index")
  else match array.values[(index.val - 1).toNat]? with
    | none => throw (.undefinedBehaviour "unchecked typevar array index")
    | some none => throw (.core .undefRef)
    | some (some handle) => pure handle

/-- The checked fts::SimpleVector access at base/essentials.jl:1311. As in the
installed getindexSVec primitive, bounds fail with BoundsError, while reading a
null SimpleVector slot is undefined behavior (not Array's UndefRefError). -/
def fieldSvecRead (fields : Slots) (index : JInt .i64) : M Nat := do
  if index.val < 1 then throw (.core .bounds)
  else match fields.values[(index.val - 1).toNat]? with
    | none => throw (.core .bounds)
    | some none => throw (.undefinedBehaviour "null SimpleVector field-type slot")
    | some (some handle) => pure handle

/-- Inner field scan, base/essentials.jl:1309-1317. The stop comparison computes
n+1 with the source's Int64 wrap, even when n is typemax(Int64). Fields are read
in forward order, and nothing after the first constraining field is inspected. -/
def scanFields {Atom : Type} (world : World Atom) (fields : Slots)
    (tv : TypeVarRef world) (n j : JInt .i64) : M Bool := do
  if j == JuliaLean.base.essentials.addInt n (JInt.wrap .i64 1) then return false
  let ft ← fieldSvecRead fields j
  if ← hasTypevar world ft tv then return true
  let j := JuliaLean.base.essentials.addInt j (JInt.wrap .i64 1)
  scanFields world fields tv n j
partial_fixpoint

/-- Later-variable scan, base/essentials.jl:1319-1333. It reads i+1, i+2, ...
in original array order. The upper-bound query precedes the same-object check,
so a bound hit is not overridden by identity; a failed query on the same variable
stops before any subsequent entry. Remaining and j are actual Int64 counters. -/
def scanLater {Atom : Type} (world : World Atom) (variables : Slots)
    (tv : TypeVarRef world) (j remaining : JInt .i64) : M Bool := do
  if remaining == JInt.wrap .i64 0 then return false
  let tv2Handle ← tvarArrayRead variables j
  let tv2 ← assertTypevar world tv2Handle
  if ← hasTypevar world tv2.upper tv then return true
  if tv2.handle == tv.handle then return false
  let j := JuliaLean.base.essentials.addInt j (JInt.wrap .i64 1)
  let remaining := JuliaLean.base.essentials.subInt remaining (JInt.wrap .i64 1)
  scanLater world variables tv j remaining
partial_fixpoint

/-- Outer reverse-index loop, base/essentials.jl:1306-1337. Array contents are
never reversed or mutated: i walks nparams,nparams-1,...,1, while the later scan
retains ascending source indices. Failed assertions/queries short-circuit before
earlier variables, and a constraining field suppresses the later-variable scan. -/
def constrainLoop {Atom : Type} (world : World Atom) (variables fields : Slots)
    (nparams n i : JInt .i64) : M Bool := do
  if i == JInt.wrap .i64 0 then return true
  let tvHandle ← tvarArrayRead variables i
  let tv ← assertTypevar world tvHandle
  let constrained ← scanFields world fields tv n (JInt.wrap .i64 1)
  let constrained ← if !constrained then
      scanLater world variables tv
        (JuliaLean.base.essentials.addInt i (JInt.wrap .i64 1))
        (JuliaLean.base.essentials.subInt nparams i)
    else pure constrained
  if !constrained then return false
  let i := JuliaLean.base.essentials.subInt i (JInt.wrap .i64 1)
  constrainLoop world variables fields nparams n i
partial_fixpoint

/-- _fieldtypes_constrain_typevars, base/essentials.jl:1302-1339. All callee queries,
object identities, TypeVar upper bounds, assertions, and optional array/SVec slots
are concrete. No caller-supplied implementation functions remain. The documented
outermost-to-innermost variable order is kept; every arithmetic operation is the
installed Julia Int64 operation. This internal method introduces no invented
public contract. -/
-- Source: base/essentials.jl:1302-1339 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _fieldtypes_constrain_typevars(tvars::Array{Any,1}, fts::Core.SimpleVector)
--     nparams = length(tvars)
--     n = length(fts)
--     i = nparams
--     while i !== 0
--         @inbounds tv = tvars[i]::TypeVar
--         constrained = false
--         j = 1
--         while j !== n + 1
--             ft = fts[j]
--             if has_typevar(ft, tv)
--                 constrained = true
--                 break
--             end
--             j += 1
--         end
--         if !constrained
--             j = i + 1
--             remaining = nparams - i
--             while remaining !== 0
--                 @inbounds tv2 = tvars[j]::TypeVar
--                 if has_typevar(tv2.ub, tv)
--                     constrained = true
--                     break
--                 end
--                 if tv2 === tv
--                     constrained = false
--                     break
--                 end
--                 j += 1
--                 remaining = remaining - 1
--             end
--         end
--         constrained || return false
--         i -= 1
--     end
--     return true
-- end
-- /Source
def fieldtypesConstrainTypevars {Atom : Type} (world : World Atom)
    (tvars fts : Slots) : M Bool := do
  let nparams := JInt.wrap .i64 tvars.values.length
  let n := JInt.wrap .i64 fts.values.length
  let i := nparams
  constrainLoop world tvars fts nparams n i


end TypevarQuery

/-- Test the existing canonical Missing singleton by its reserved runtime tag.
The already installed JVal abstraction uses .obj "Missing" [] uniquely for the
zero-field Base.Missing singleton; an unrelated user type called Missing has a
distinct qualified type tag. This binds the identity check to the concrete value,
with no supplied predicate and no overloaded equality dispatch.
Julia source: base/essentials.jl:1542-1542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:1542-1542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ismissing(x) = x === missing
-- /Source
def ismissingSingleton (x : JVal) : Bool := isemptyMissingHint x


/-- The actual LineNumberNode fields supplied by Julia macro expansion.
line is an Int64 and file is either a Symbol (its interned name) or nothing.
All signed line values are represented, including 0 for an unknown location.
Source: base/boot.jl:133-136,710-714; base/essentials.jl:1573-1580. -/
structure MacroSource where
  line : JInt .i64
  file : Option String

/-- Expand to the line field of the implicit, typed macro source record.
The record is the existing macro-context boundary, not a user-supplied field
lookup function. Reading this built-in field cannot invoke user getproperty.
Julia source: base/essentials.jl:1578-1580 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/essentials.jl:1578-1580 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro __LINE__()
--     return __source__.line
-- end
-- /Source
def lineMacro64 (source : MacroSource) : JInt .i64 := source.line



end JuliaLean.base.essentials.Models1Group18


namespace JuliaLean.base.essentials.Models2Group19

open JuliaLean JuliaLean.BootCov

/-- The two dispatch-selected calls of `length(::AbstractArray)`.
Neither the array subtype nor the type returned by its `size` method is fixed
by this method. The result of `prod` is likewise not asserted to be Int.
The effect parameter retains custom mutation, exceptions, and divergence;
no callee correctness law is assumed. A concrete dispatch instantiation must
use its installed Base operations when those are the selected methods.
Julia source: base/essentials.jl:13. -/
-- Source: base/essentials.jl:13-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(t::AbstractArray) = (@inline; prod(size(t)))
-- /Source
structure LengthOps (m : Type → Type) (A D R : Type) where
  size : A → m D
  prod : D → m R

/-- Obtain the size once, then call the product selected by its returned type.
This adds effects and the full result domain to the frozen pure abstraction.
Julia source: base/essentials.jl:13. -/
-- Source: base/essentials.jl:13-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(t::AbstractArray) = (@inline; prod(size(t)))
-- /Source
def lengthAbstract {m : Type → Type} [Monad m] {A D R : Type}
    (ops : LengthOps m A D R) (a : A) : m R := do
  let dims ← ops.size a
  ops.prod dims

/-- Representation of the runtime Bool test at a short-circuit condition.
`other` includes every non-Bool result; it is not coerced to Bool. The tag is
the representation's actual runtime type classification, not an overridable
conversion or a user-provided truth predicate.
Julia source: base/essentials.jl:391. -/
-- Source: base/essentials.jl:389-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(A::AbstractArray, I...)
--     @inline
--     checkbounds(Bool, A, I...) || _throw_boundserror_indices(A, I...)
--     nothing
-- end
-- /Source
inductive Condition (Other : Type) where
  | bool (value : Bool)
  | other (value : Other)

/-- The selected `checkbounds(Bool, A, I...)` call. `I` may be a tagged
universal value type, so a List I represents a heterogeneous Julia tuple.
Custom axes, index types, errors, non-Bool returns, and effects are retained.
The fixed first argument `Bool` is represented by this dedicated operation.
Julia source: base/essentials.jl:389-393. -/
-- Source: base/essentials.jl:389-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(A::AbstractArray, I...)
--     @inline
--     checkbounds(Bool, A, I...) || _throw_boundserror_indices(A, I...)
--     nothing
-- end
-- /Source
structure BoundsOps (m : Type → Type) (A I Other : Type) where
  check : A → List I → m (Condition Other)

/-- Perform the custom bounds check once, enforce Julia's Bool condition,
and call the installed concrete BoundsError helper at the false branch.
The existing Exc boundary preserves exception classes, but not BoundsError
object/index payloads. The original array and all indices reach the helper.
Julia source: base/essentials.jl:389-393. -/
-- Source: base/essentials.jl:389-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(A::AbstractArray, I...)
--     @inline
--     checkbounds(Bool, A, I...) || _throw_boundserror_indices(A, I...)
--     nothing
-- end
-- /Source
def checkbounds {m : Type → Type} [Monad m] [MonadExceptOf Exc m]
    {A I Other : Type} (ops : BoundsOps m A I Other)
    (a : A) (indices : List I) : m Unit := do
  match ← ops.check a indices with
  | .bool true => pure ()
  | .bool false =>
      let failure : Except Exc Unit := match indices with
        | [] => Models1Group18.throwBoundserrorIndicesEmpty a
        | first :: rest => Models1Group18.throwBoundserrorIndicesMany a first rest
      match failure with
      | .ok result => pure result
      | .error error => throw error
  | .other _ => throw (.typeError "non-boolean (condition)")

end JuliaLean.base.essentials.Models2Group19

namespace JuliaLean.base.essentials.Models2Group19

open JuliaLean JuliaLean.BootCov

/-- A Julia value classified by actual membership in one fixed target type.
The member payload retains the original value/identity; the other payload
includes all values outside that target. Tags are representation invariants
for the builtin isa test, not arbitrary predicates or conversion laws.
For oftype, Target is the value carrier of the concrete runtime typeof(x),
so every x in that carrier fixes the same target; this covers all runtime
types by polymorphism, including custom objects and type objects.
Julia source: base/essentials.jl:718. -/
-- Source: base/essentials.jl:718-718 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- oftype(x, y) = y isa typeof(x) ? y : convert(typeof(x), y)::typeof(x)
-- /Source
inductive Membership (Target Other : Type) where
  | member (value : Target)
  | other (value : Other)

/-- The selected generic convert call at a fixed target type. Its return
value is still a dynamic membership value: custom convert may fail, mutate,
diverge, or return a value outside the requested target. The target type is
fixed by this interface instantiation, not supplied by a callee-correctness
hypothesis. Concrete dispatch instantiations use installed Base models.
Julia source: base/essentials.jl:718. -/
-- Source: base/essentials.jl:718-718 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- oftype(x, y) = y isa typeof(x) ? y : convert(typeof(x), y)::typeof(x)
-- /Source
structure ConversionOps (m : Type → Type) (Target Other : Type) where
  convert : Membership Target Other → m (Membership Target Other)

/-- Preserve an already compatible y without conversion. Otherwise call
convert once, then enforce the explicit typeof(x) assertion on its actual
return value. All selected effects before that assertion are retained.
Julia source: base/essentials.jl:718. -/
-- Source: base/essentials.jl:718-718 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- oftype(x, y) = y isa typeof(x) ? y : convert(typeof(x), y)::typeof(x)
-- /Source
def oftype {m : Type → Type} [Monad m] [MonadExceptOf Exc m]
    {Target Other : Type} (ops : ConversionOps m Target Other)
    (_x : Target) (y : Membership Target Other) : m Target := do
  match y with
  | .member value => pure value
  | .other _ =>
      match ← ops.convert y with
      | .member value => pure value
      | .other _ => throw (.typeError "typeassert")

end JuliaLean.base.essentials.Models2Group19

namespace JuliaLean.base.essentials.Models2Group19

open JuliaLean.BootCov

/-- The fallback cconvert method observes actual isa membership in its
fixed type argument T. Target is the entire set of values inhabiting T,
including heterogeneous concrete subtypes when T is abstract or a union;
Other is its complement. An existing member is retained unchanged.
Otherwise the selected convert result is returned without a type assertion,
including an outside result as permitted by cconvert's documented contract.
The method constructs no target type and introduces no additional conversion.
Julia source: base/essentials.jl:739. -/
-- Source: base/essentials.jl:739-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cconvert(::Type{T}, x) where {T} = x isa T ? x : convert(T, x) # do the conversion eagerly in most cases
-- /Source
def cconvert {m : Type → Type} [Monad m] {Target Other : Type}
    (ops : ConversionOps m Target Other) (x : Membership Target Other) :
    m (Membership Target Other) :=
  match x with
  | .member _ => pure x
  | .other _ => ops.convert x

end JuliaLean.base.essentials.Models2Group19

namespace JuliaLean.base.essentials.Models2Group19

open JuliaLean JuliaLean.BootCov

/-- A live native-64-bit String storage view. objectAddress is the actual
address of the existing Julia object, not its hash, contents, or an allocated
address invented by this conversion. bytes is the current raw data snapshot;
invalid UTF-8 and embedded NUL bytes are included. The immutable runtime
length fits native Int, and the size word plus bytes and terminator occupy
a nonwrapping live allocation. Later pointer use still requires the original
object to remain alive. No allocator or GC rooting is performed here.

The installed identity runtime uses this same String layout: bytes begin at
objectAddress + 8 (JuliaLean/src/builtins_identity_c.lean:547-551,857-860).
This local view avoids importing that unrelated, unbuilt module.
Julia source: base/essentials.jl:745-746. -/
-- Source: base/essentials.jl:745-746 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_convert(::Type{Ptr{UInt8}}, s::String) = ccall(:jl_string_ptr, Ptr{UInt8}, (Any,), s)
-- unsafe_convert(::Type{Ptr{Int8}}, s::String) = ccall(:jl_string_ptr, Ptr{Int8}, (Any,), s)
-- /Source
structure StringStorage where
  objectAddress : JInt .u64
  bytes : List (JInt .u8)
  nonnull : objectAddress.val ≠ 0
  lengthFits : bytes.length < (2 : Nat) ^ 63
  spanFits : objectAddress.val + 8 + (bytes.length : Int) < (2 : Int) ^ 64

/-- A byte pointer with its fixed Julia element type kept in the model type;
raw is the installed native pointer representation. This distinguishes the
Int8 and UInt8 return types without changing any address bits.
Julia source: base/essentials.jl:745-746. -/
-- Source: base/essentials.jl:745-746 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_convert(::Type{Ptr{UInt8}}, s::String) = ccall(:jl_string_ptr, Ptr{UInt8}, (Any,), s)
-- unsafe_convert(::Type{Ptr{Int8}}, s::String) = ccall(:jl_string_ptr, Ptr{Int8}, (Any,), s)
-- /Source
structure BytePointer (element : IntTy) where
  raw : IntConv.Ptr

/-- The concrete String data projection on the installed native layout.
Read the existing object's base address, advance past its native size word,
and use the installed UInt-to-Ptr bitcast. The span invariant makes this
wrapping machine addition exact on every represented live object. This
operation neither reads/validates bytes nor allocates/copies storage.
The exact jl_string_ptr C definition is not bundled; no C source text is
reconstructed here. Its storage projection uses the current baseline's
explicit +8 String layout, rather than an arbitrary runtime callback.
Julia source: base/essentials.jl:745-746. -/
-- Source: base/essentials.jl:745-746 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_convert(::Type{Ptr{UInt8}}, s::String) = ccall(:jl_string_ptr, Ptr{UInt8}, (Any,), s)
-- unsafe_convert(::Type{Ptr{Int8}}, s::String) = ccall(:jl_string_ptr, Ptr{Int8}, (Any,), s)
-- /Source
def stringDataPointer (s : StringStorage) : IntConv.Ptr :=
  IntConv.ptrOfUInt (s.objectAddress + JInt.wrap .u64 8)

/-- Return a UInt8 pointer into this same live String's data, including
arbitrary bytes. The returned pointer does not itself retain a GC root.
Julia source: base/essentials.jl:745. -/
-- Source: base/essentials.jl:745-745 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_convert(::Type{Ptr{UInt8}}, s::String) = ccall(:jl_string_ptr, Ptr{UInt8}, (Any,), s)
-- /Source
def unsafeConvertStringUInt8 (s : StringStorage) : BytePointer .u8 :=
  ⟨stringDataPointer s⟩

/-- Return an Int8 pointer into the identical String storage; changing the
pointed-to byte type does not alter the pointer's address bits.
Julia source: base/essentials.jl:746. -/
-- Source: base/essentials.jl:746-746 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_convert(::Type{Ptr{Int8}}, s::String) = ccall(:jl_string_ptr, Ptr{Int8}, (Any,), s)
-- /Source
def unsafeConvertStringInt8 (s : StringStorage) : BytePointer .i8 :=
  ⟨stringDataPointer s⟩

end JuliaLean.base.essentials.Models2Group19
namespace JuliaLean.base.essentials.Models2Group19.Reinterpret

open JuliaLean JuliaLean.BootCov

/-- The stored UInt16 flag test used by the primitive and concrete predicates.
The mask and both native operations are the installed UInt16 models.
Julia source: base/runtime_internals.jl:885-891,1161. -/
-- Source: base/runtime_internals.jl:885-891 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function isprimitivetype(@nospecialize t)
--     @_total_meta
--     t = unwrap_unionall(t)
--     # TODO: what to do for `Union`?
--     isa(t, DataType) || return false
--     return (t.flags & 0x0080) == 0x0080
-- end
-- /Source
def flagSet (flags mask : JInt .u16) : Bool :=
  JuliaLean.base.int.eq_int (JuliaLean.base.int.and_int flags mask) mask

/-- A primitive's logical width and actual padded storage size. The width is
a mathematical index of the installed BitVec payload, not Julia arithmetic.
The size is the runtime layout's UInt32; the bound makes the payload fit that
constructible storage. No byte-alignment or native-integer-width restriction
is imposed. At this source pin, non-byte widths are accepted and a 24-bit
primitive occupies four bytes (manual/types.md:299-316).

Only declared value bits are in the payload representation. Unused high bits
and whole padding bytes are outside the installed jlBitcast value abstraction;
no claim is made about their physical contents or boxing allocation addresses.
Julia source: base/runtime_internals.jl:624-640; base/essentials.jl:787-794. -/
-- Source: base/runtime_internals.jl:624-640 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct DataTypeLayout
--     size::UInt32
--     nfields::UInt32
--     npointers::UInt32
--     firstptr::Int32
--     alignment::UInt16
--     flags::UInt16
--     # haspadding : 1;
--     # fielddesc_type : 2;
--     # arrayelem_isboxed : 1;
--     # arrayelem_isunion : 1;
--     # arrayelem_isatomic : 1;
--     # arrayelem_islocked : 1;
--     # isbitsegal : 1;
--     # unused_bits : 7;
--     # padding : 1;
-- end
-- /Source
structure PrimitiveLayout where
  logicalBits : Nat
  storageBytes : JInt .u32
  widthFits : logicalBits ≤ 8 * storageBytes.val.toNat
  deriving DecidableEq

/-- A canonical identity key of an existing Julia DataType, with the immutable
metadata needed here. The complete key is its identity; `nominal` distinguishes
types that share every layout/flag field, and is not a Julia integer value or
an exposed native address. Equality of keys therefore determines metadata.
Metadata alone never identifies a type, and names/widths are not identity tests.

The optional layout avoids fabricating a layout for abstract/nonconcrete
DataTypes. A concrete primitive always has its real layout. The metadata
fields are records, not implementations of isprimitivetype, isconcretetype,
bitcast, or any other runtime operation. Fresh keys can be returned by an
effectful user fallback; there is no fixed finite table of accepted types.
Julia source: base/runtime_internals.jl:885-891,1161;
src/runtime_intrinsics.c:439-453. -/
-- Source: src/runtime_intrinsics.c:439-453 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- jl_value_t *jl_bitcast(jl_value_t *ty, jl_value_t *v)
-- {
--     JL_TYPECHK(bitcast, datatype, ty);
--     if (!jl_is_concrete_type(ty) || !jl_is_primitivetype(ty))
--         jl_error("bitcast: target type not a leaf primitive type");
--     if (!jl_is_primitivetype(jl_typeof(v)))
--         jl_error("bitcast: value not a primitive type");
--     if (jl_datatype_nbits((jl_datatype_t*)jl_typeof(v)) != jl_datatype_nbits((jl_datatype_t*)ty))
--         jl_error("bitcast: argument bitsize does not match bitsize of target type");
--     if (ty == jl_typeof(v))
--         return v;
--     if (ty == (jl_value_t*)jl_bool_type)
--         return *(uint8_t*)jl_data_ptr(v) & 1 ? jl_true : jl_false;
--     return jl_new_bits(ty, jl_data_ptr(v));
-- }
-- /Source
structure DataTypeKey where
  nominal : Nat
  flags : JInt .u16
  layout : Option PrimitiveLayout
  layoutPresent : flagSet flags (JInt.wrap .u16 0x0080) = true →
    flagSet flags (JInt.wrap .u16 0x0002) = true → layout.isSome = true
  deriving DecidableEq

/-- The concrete DataType branch of isprimitivetype. It reads the real flag;
it neither assumes that the target is a leaf nor unwraps the original target.
Julia source: base/runtime_internals.jl:885-891. -/
-- Source: base/runtime_internals.jl:885-891 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function isprimitivetype(@nospecialize t)
--     @_total_meta
--     t = unwrap_unionall(t)
--     # TODO: what to do for `Union`?
--     isa(t, DataType) || return false
--     return (t.flags & 0x0080) == 0x0080
-- end
-- /Source
def datatypePrimitive (type : DataTypeKey) : Bool :=
  flagSet type.flags (JInt.wrap .u16 0x0080)

/-- The concrete DataType branch of isconcretetype. The raw DataType check is
performed by bitcast before this helper is called.
Julia source: base/runtime_internals.jl:1161. -/
-- Source: base/runtime_internals.jl:1161-1161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isconcretetype(@nospecialize(t)) = (@_total_meta; isa(t, DataType) && (t.flags & 0x0002) == 0x0002)
-- /Source
def datatypeConcrete (type : DataTypeKey) : Bool :=
  flagSet type.flags (JInt.wrap .u16 0x0002)

/-- Read a concrete primitive's stored layout after its runtime checks.
The proof arguments are representation invariants of the real DataType and
do not add a runtime check or a callee correctness assumption.
Julia source: base/essentials.jl:790; src/runtime_intrinsics.c:439-453. -/
-- Source: src/runtime_intrinsics.c:439-453 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- jl_value_t *jl_bitcast(jl_value_t *ty, jl_value_t *v)
-- {
--     JL_TYPECHK(bitcast, datatype, ty);
--     if (!jl_is_concrete_type(ty) || !jl_is_primitivetype(ty))
--         jl_error("bitcast: target type not a leaf primitive type");
--     if (!jl_is_primitivetype(jl_typeof(v)))
--         jl_error("bitcast: value not a primitive type");
--     if (jl_datatype_nbits((jl_datatype_t*)jl_typeof(v)) != jl_datatype_nbits((jl_datatype_t*)ty))
--         jl_error("bitcast: argument bitsize does not match bitsize of target type");
--     if (ty == jl_typeof(v))
--         return v;
--     if (ty == (jl_value_t*)jl_bool_type)
--         return *(uint8_t*)jl_data_ptr(v) & 1 ? jl_true : jl_false;
--     return jl_new_bits(ty, jl_data_ptr(v));
-- }
-- /Source
def primitiveLayout (type : DataTypeKey) (primitive : datatypePrimitive type = true)
    (concrete : datatypeConcrete type = true) : PrimitiveLayout :=
  type.layout.get (type.layoutPresent primitive concrete)

/-- The original type argument, retaining UnionAll wrappers and all remaining
type forms. `original` carries the complete original runtime object; the body
is its actual UnionAll body view. Remaining types, including unions/bottom,
TypeVar, TypeEq/TypeEgal and TypeApp, are never inspected by this method and
remain in `other`. Distinct nominal runtime objects have distinct payloads.
Julia source: base/essentials.jl:544-550,787-794. -/
-- Source: base/essentials.jl:544-550 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unwrap_unionall(@nospecialize(a))
--     @_foldable_meta
--     while isa(a,UnionAll)
--         a = a.body
--     end
--     return a
-- end
-- /Source
inductive TypeView (Atom : Type) where
  | datatype (type : DataTypeKey)
  | unionAll (original : Atom) (body : TypeView Atom)
  | other (original : Atom)

/-- Follow the actual finite UnionAll body chain without replacing the
original argument. A live immutable UnionAll chain is acyclic; arbitrary
DataType parameter graphs need not be traversed.
Julia source: base/essentials.jl:544-550. -/
-- Source: base/essentials.jl:544-550 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unwrap_unionall(@nospecialize(a))
--     @_foldable_meta
--     while isa(a,UnionAll)
--         a = a.body
--     end
--     return a
-- end
-- /Source
def unwrapUnionAll {Atom : Type} : TypeView Atom → TypeView Atom
  | .unionAll _ body => unwrapUnionAll body
  | value => value

/-- The fixed primitive predicate with its real UnionAll unwrapping and
DataType test. A UnionAll primitive family can pass this predicate while
remaining an invalid raw target for bitcast's later DataType assertion.
Julia source: base/runtime_internals.jl:885-891. -/
-- Source: base/runtime_internals.jl:885-891 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function isprimitivetype(@nospecialize t)
--     @_total_meta
--     t = unwrap_unionall(t)
--     # TODO: what to do for `Union`?
--     isa(t, DataType) || return false
--     return (t.flags & 0x0080) == 0x0080
-- end
-- /Source
def isPrimitiveType {Atom : Type} (type : TypeView Atom) : Bool :=
  match unwrapUnionAll type with
  | .datatype data => datatypePrimitive data
  | _ => false

/-- Actual Julia values partitioned by the primitive flag of their concrete
typeof. Primitive payloads include every logical bit pattern, not just valid
numeric/character values or the two canonical Bool patterns. Nonprimitive
payloads retain the original value, including mutable object identity. The
constructor proofs describe runtime representation and are not user callee
laws. Both the source and a fallback result may have any user-defined type.
Julia source: base/essentials.jl:787-794. -/
-- Source: base/essentials.jl:787-794 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function reinterpret(::Type{Out}, x) where {Out}
--     @inline
--     if isprimitivetype(Out) && isprimitivetype(typeof(x))
--         return bitcast(Out, x)
--     end
--     # only available when Base is fully loaded.
--     return _reinterpret(Out, x)
-- end
-- /Source
inductive Value (Atom : Type) where
  | primitive (type : DataTypeKey)
      (primitive : datatypePrimitive type = true)
      (concrete : datatypeConcrete type = true)
      (bits : BitVec (primitiveLayout type primitive concrete).logicalBits)
  | other (type : DataTypeKey)
      (notPrimitive : datatypePrimitive type = false)
      (concrete : datatypeConcrete type = true)
      (original : Atom)

/-- Read the actual concrete typeof stored in the dynamic value view.
This is a built-in field projection, not a dispatch-selected operation.
Julia source: base/essentials.jl:789. -/
-- Source: base/essentials.jl:787-794 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function reinterpret(::Type{Out}, x) where {Out}
--     @inline
--     if isprimitivetype(Out) && isprimitivetype(typeof(x))
--         return bitcast(Out, x)
--     end
--     # only available when Base is fully loaded.
--     return _reinterpret(Out, x)
-- end
-- /Source
def typeofValue {Atom : Type} : Value Atom → DataTypeKey
  | .primitive type _ _ _ => type
  | .other type _ _ _ => type

/-- The actual distinguished Bool type singleton. Equality to this canonical
key implies all its metadata, in particular the eight-bit logical width.
A user primitive with the same width remains a different type key.
Julia source: base/boot.jl:276; src/runtime_intrinsics.c:439-453. -/
-- Source: src/runtime_intrinsics.c:439-453 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- jl_value_t *jl_bitcast(jl_value_t *ty, jl_value_t *v)
-- {
--     JL_TYPECHK(bitcast, datatype, ty);
--     if (!jl_is_concrete_type(ty) || !jl_is_primitivetype(ty))
--         jl_error("bitcast: target type not a leaf primitive type");
--     if (!jl_is_primitivetype(jl_typeof(v)))
--         jl_error("bitcast: value not a primitive type");
--     if (jl_datatype_nbits((jl_datatype_t*)jl_typeof(v)) != jl_datatype_nbits((jl_datatype_t*)ty))
--         jl_error("bitcast: argument bitsize does not match bitsize of target type");
--     if (ty == jl_typeof(v))
--         return v;
--     if (ty == (jl_value_t*)jl_bool_type)
--         return *(uint8_t*)jl_data_ptr(v) & 1 ? jl_true : jl_false;
--     return jl_new_bits(ty, jl_data_ptr(v));
-- }
-- /Source
structure Runtime where
  boolType : DataTypeKey
  boolPrimitive : datatypePrimitive boolType = true
  boolConcrete : datatypeConcrete boolType = true
  boolWidth : (primitiveLayout boolType boolPrimitive boolConcrete).logicalBits = 8

/-- The fixed bitcast primitive, with the pinned C check order and errors.
The raw target is checked before unwrapping could hide a UnionAll; concrete
and primitive target checks precede the source test and logical-width check.
Same-type conversion returns the complete original value before Bool handling.
The Bool path uses the installed low-bit canonicalizer. Other primitive
results use the installed arbitrary-width jlBitcast payload operation.

The existing Exc interface records exception class and context but does not
retain TypeError's expected/actual object payload. Physical allocation and
unused padding are the existing jlBitcast abstraction boundary, as described
by PrimitiveLayout; no new primitive implementation callback is introduced.
Julia source: base/essentials.jl:790; src/runtime_intrinsics.c:439-453. -/
-- Source: src/runtime_intrinsics.c:439-453 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- jl_value_t *jl_bitcast(jl_value_t *ty, jl_value_t *v)
-- {
--     JL_TYPECHK(bitcast, datatype, ty);
--     if (!jl_is_concrete_type(ty) || !jl_is_primitivetype(ty))
--         jl_error("bitcast: target type not a leaf primitive type");
--     if (!jl_is_primitivetype(jl_typeof(v)))
--         jl_error("bitcast: value not a primitive type");
--     if (jl_datatype_nbits((jl_datatype_t*)jl_typeof(v)) != jl_datatype_nbits((jl_datatype_t*)ty))
--         jl_error("bitcast: argument bitsize does not match bitsize of target type");
--     if (ty == jl_typeof(v))
--         return v;
--     if (ty == (jl_value_t*)jl_bool_type)
--         return *(uint8_t*)jl_data_ptr(v) & 1 ? jl_true : jl_false;
--     return jl_new_bits(ty, jl_data_ptr(v));
-- }
-- /Source
def bitcast {Atom : Type} (runtime : Runtime) (out : TypeView Atom)
    (x : Value Atom) : Except Exc (Value Atom) :=
  match out with
  | .datatype target =>
      if concrete : datatypeConcrete target = true then
        if primitive : datatypePrimitive target = true then
          match x with
          | .other _ _ _ _ =>
              .error (.error "bitcast: value not a primitive type")
          | .primitive source sourcePrimitive sourceConcrete bits =>
              if width : (primitiveLayout source sourcePrimitive sourceConcrete).logicalBits =
                  (primitiveLayout target primitive concrete).logicalBits then
                if target = source then
                  .ok x
                else if target = runtime.boolType then
                  let value := JuliaLean.C.bitcastBool (BitVec.ofNat 8 bits.toNat)
                  let canonical : BitVec 8 := BitVec.ofNat 8 (if value then 1 else 0)
                  .ok (.primitive runtime.boolType runtime.boolPrimitive runtime.boolConcrete
                    (BitVec.cast runtime.boolWidth.symm canonical))
                else
                  .ok (.primitive target primitive concrete
                    (BitVec.cast width (JuliaLean.C.jlBitcast bits)))
              else
                .error (.error "bitcast: argument bitsize does not match bitsize of target type")
        else
          .error (.error "bitcast: target type not a leaf primitive type")
      else
        .error (.error "bitcast: target type not a leaf primitive type")
  | _ => .error (.typeError "bitcast")

/-- The sole open dispatch leaf of this method. Its argument types are not
fixed by reinterpret, and its result is not asserted to have type Out.
The effect carrier may retain mutation, arbitrary exceptions, and divergence.
No callee correctness law is assumed. A concrete instantiation uses the
installed Base implementation when that is the dispatch-selected method.
Julia source: base/essentials.jl:787-794. -/
-- Source: base/essentials.jl:787-794 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function reinterpret(::Type{Out}, x) where {Out}
--     @inline
--     if isprimitivetype(Out) && isprimitivetype(typeof(x))
--         return bitcast(Out, x)
--     end
--     # only available when Base is fully loaded.
--     return _reinterpret(Out, x)
-- end
-- /Source
structure Ops (m : Type → Type) (Atom : Type) where
  fallback : TypeView Atom → Value Atom → m (Value Atom)

/-- Mirror the two short-circuit predicates, the fixed bitcast path, and the
single dispatch-selected fallback. The fallback receives the original type
argument, including its UnionAll wrappers, and the original x unchanged.
Julia source: base/essentials.jl:787-794. -/
-- Source: base/essentials.jl:787-794 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function reinterpret(::Type{Out}, x) where {Out}
--     @inline
--     if isprimitivetype(Out) && isprimitivetype(typeof(x))
--         return bitcast(Out, x)
--     end
--     # only available when Base is fully loaded.
--     return _reinterpret(Out, x)
-- end
-- /Source
def reinterpret {m : Type → Type} [Monad m] [MonadExceptOf Exc m]
    {Atom : Type} (runtime : Runtime) (ops : Ops m Atom)
    (out : TypeView Atom) (x : Value Atom) : m (Value Atom) :=
  if isPrimitiveType out then
    if datatypePrimitive (typeofValue x) then
      match bitcast runtime out x with
      | .ok result => pure result
      | .error error => throw error
    else ops.fallback out x
  else ops.fallback out x

end JuliaLean.base.essentials.Models2Group19.Reinterpret
namespace JuliaLean.base.essentials.Models2Group19.SimpleVector

open JuliaLean JuliaLean.BootCov JuliaLean.base.essentials

/-- Lift an installed, fixed primitive result into the surrounding effect
carrier, preserving its exact Err, including undefined behavior. This adapter
does not restore or replace any state maintained by that carrier. It is used
for the concrete SimpleVector getindex selected by native Int64 indices.
Julia source: base/essentials.jl:1096,1102. -/
-- Source: base/essentials.jl:1096-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getindex(v::SimpleVector, i::Int) = (@_foldable_meta; Core._svec_ref(v, i))
-- /Source
def liftResult {m : Type → Type} [Monad m] [MonadExceptOf Err m] {α : Type}
    (result : RE α) : m α :=
  match result with
  | .ok value => pure value
  | .error error => throw error

/-- The three calls whose dispatch depends on the unannotated state i.
The fixed SimpleVector length is a native Int64, and the literal increment
argument is likewise Int64. A custom comparison can return a non-Bool; a
custom index method and addition may return arbitrary, different value and
next-state types. Their effects, errors, and divergence remain in m. These
fields are actual dispatch-selected calls and carry no correctness laws.
Concrete native dispatch is bound separately in nativeIterationOps.
Julia source: base/essentials.jl:1102. -/
-- Source: base/essentials.jl:1102-1102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iterate(v::SimpleVector, i=1) = (length(v) < i ? nothing : (v[i], i + 1))
-- /Source
structure IterationOps (m : Type → Type) (I V Next NonBool : Type) where
  less : JInt .i64 → I → m (Models2Group19.Condition NonBool)
  getindex : Models1Group18.SizedSVec → I → m V
  add : I → JInt .i64 → m Next

/-- Full generic-state SimpleVector iteration. Read the installed native
length, call comparison once, then enforce the Bool condition. A true result
stops before indexing and addition. A false result evaluates v[i] before
i + 1, retaining all effects and failures in that order. No index conversion,
state-type assertion, or successful-access premise is introduced.
Julia source: base/essentials.jl:1102. -/
-- Source: base/essentials.jl:1102-1102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iterate(v::SimpleVector, i=1) = (length(v) < i ? nothing : (v[i], i + 1))
-- /Source
def iterate {m : Type → Type} [Monad m] [MonadExceptOf Err m]
    {I V Next NonBool : Type} (ops : IterationOps m I V Next NonBool)
    (v : Models1Group18.SizedSVec) (i : I) : m (Option (V × Next)) := do
  let condition ← ops.less (Models1Group18.svecLength64 v) i
  match condition with
  | .bool true => pure none
  | .bool false =>
      let value ← ops.getindex v i
      let next ← ops.add i (JInt.wrap .i64 1)
      pure (some (value, next))
  | .other _ => throw (Err.core (Exc.typeError "non-boolean (condition)"))

/-- The closed native Int64 instantiation. Signed comparison, SimpleVector
slot access, and wrapping addition all use their installed concrete models.
The slot primitive preserves BoundsError for invalid signed indices and the
existing undefined-behavior marker for null internal slots. There is no
supplied callback implementing known Base behavior in this specialization.
Julia source: base/essentials.jl:1096,1102,1267; base/int.jl:84. -/
-- Source: base/essentials.jl:1102-1102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iterate(v::SimpleVector, i=1) = (length(v) < i ? nothing : (v[i], i + 1))
-- /Source
-- Source: base/int.jl:84-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (<)(x::T, y::T) where {T<:BitSigned}  = slt_int(x, y)
-- /Source
-- Source: base/essentials.jl:1096-1096 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getindex(v::SimpleVector, i::Int) = (@_foldable_meta; Core._svec_ref(v, i))
-- /Source
-- Source: base/essentials.jl:1267-1267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (+)(x::Int, y::Int) = add_int(x, y)
-- /Source
def nativeIterationOps {m : Type → Type} [Monad m] [MonadExceptOf Err m] :
    IterationOps m (JInt .i64) JVal (JInt .i64) Empty where
  less := fun length index =>
    pure (.bool (JuliaLean.base.int.lt_BitSigned length index))
  getindex := fun vector index => liftResult (Models1Group18.svecGetindex64 vector index)
  add := fun index one => pure (JuliaLean.base.essentials.addInt index one)

/-- Native-state iteration with every dispatch leaf fixed to Base's installed
Int64/SimpleVector implementation. The generic method above retains the
remaining state-type domain, so this wrapper is not the generic translation.
Julia source: base/essentials.jl:1102. -/
-- Source: base/essentials.jl:1102-1102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iterate(v::SimpleVector, i=1) = (length(v) < i ? nothing : (v[i], i + 1))
-- /Source
def iterateNative {m : Type → Type} [Monad m] [MonadExceptOf Err m]
    (v : Models1Group18.SizedSVec) (i : JInt .i64) : m (Option (JVal × JInt .i64)) :=
  iterate (nativeIterationOps (m := m)) v i

/-- The no-explicit-state method generated by i=1. Its starting state is the
native Int64 value one, and all subsequent calls are the closed native ones.
Julia source: base/essentials.jl:1102. -/
-- Source: base/essentials.jl:1102-1102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- iterate(v::SimpleVector, i=1) = (length(v) < i ? nothing : (v[i], i + 1))
-- /Source
def iterateDefault {m : Type → Type} [Monad m] [MonadExceptOf Err m]
    (v : Models1Group18.SizedSVec) : m (Option (JVal × JInt .i64)) :=
  iterateNative v (JInt.wrap .i64 1)

end JuliaLean.base.essentials.Models2Group19.SimpleVector
namespace JuliaLean.base.essentials.Models2Group19.SimpleVector

open JuliaLean
open JuliaLean.base.essentials (Err)
open JuliaLean.base.essentials.Models1Group18 (SizedSVec OneTo64 svecAxes64 oneTo64)
open JuliaLean.base.essentials.Models2Group19 (Condition)

/-- A native OneTo{Int64} result or an arbitrary other result returned by
selected tuple indexing. Custom Integer indexing need not return a range;
there is no result-type assertion in the source. The payloads retain any
returned object identities.
Julia source: base/essentials.jl:1107. -/
-- Source: base/essentials.jl:1107-1107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(v::SimpleVector, d::Integer) = d <= 1 ? axes(v)[d] : OneTo(1)
-- /Source
inductive AxisResult (Custom : Type) where
  | native (axis : OneTo64)
  | custom (value : Custom)

/-- Only the calls selected on d's unfixed Integer type are parameters.
The comparison receives d followed by the native Int literal one. The
indexing call receives the actual fixed tuple produced by axes(v), followed
by the same d. D includes every signed, unsigned, big, and custom Integer
representation; Other includes all non-Bool comparison results. Known
concrete dispatch instantiations must use their installed Base models.
Julia source: base/essentials.jl:1107. -/
-- Source: base/essentials.jl:1107-1107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(v::SimpleVector, d::Integer) = d <= 1 ? axes(v)[d] : OneTo(1)
-- /Source
structure AxesOps (m : Type → Type) (D Other Custom : Type) where
  le : D → JInt .i64 → m (Condition Other)
  getindex : List OneTo64 → D → m (AxisResult Custom)

/-- Evaluate the comparison and its Bool condition before constructing the
true-branch axes tuple. The fixed SimpleVector axes and OneTo(1) operations
are installed concrete models, not dispatch parameters. A selected tuple
index result is returned unchanged, and every selected error/effect remains
in the carrier. No native-only restriction on d is imposed.
Julia source: base/essentials.jl:1107. -/
-- Source: base/essentials.jl:1107-1107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(v::SimpleVector, d::Integer) = d <= 1 ? axes(v)[d] : OneTo(1)
-- /Source
def axes {m : Type → Type} [Monad m] [MonadExceptOf Err m]
    {D Other Custom : Type} (ops : AxesOps m D Other Custom)
    (v : SizedSVec) (d : D) : m (AxisResult Custom) := do
  match ← ops.le d (JInt.wrap .i64 1) with
  | .bool true => ops.getindex (svecAxes64 v) d
  | .bool false => pure (.native (oneTo64 (JInt.wrap .i64 1)))
  | .other _ => throw (.core (.typeError "non-boolean (condition)"))

end JuliaLean.base.essentials.Models2Group19.SimpleVector
namespace JuliaLean.base.essentials.Models2Group19.SimpleVector

open JuliaLean JuliaLean.BootCov JuliaLean.base.essentials
open JuliaLean.base.essentials.Models2Group19

/-- Element comparison is selected on the two stored values, whose types the
SimpleVector method does not fix. The actual Bool/non-Bool result partition
preserves Julia's short-circuit type check. Effects and errors remain in m.
Julia source: base/essentials.jl:1109-1115. -/
-- Source: base/essentials.jl:1109-1115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ==(v1::SimpleVector, v2::SimpleVector)
--     length(v1)==length(v2) || return false
--     for i = 1:length(v1)
--         v1[i] == v2[i] || return false
--     end
--     return true
-- end
-- /Source
structure EqualityOps (m : Type → Type) (Other : Type) where
  equal : JVal → JVal → m (Condition Other)

/-- The real left-to-right equality loop. Each index reads the left vector
before the right, using the installed native SimpleVector indexing primitive.
Only Boolean true advances. False stops immediately; non-Bool raises TypeError;
null slots retain the installed undefined-behavior observation.
Julia source: base/essentials.jl:1109-1115. -/
-- Source: base/essentials.jl:1109-1115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ==(v1::SimpleVector, v2::SimpleVector)
--     length(v1)==length(v2) || return false
--     for i = 1:length(v1)
--         v1[i] == v2[i] || return false
--     end
--     return true
-- end
-- /Source
def equalityLoop {m : Type → Type} [Monad m] [MonadExceptOf Err m]
    {Other : Type} (ops : EqualityOps m Other)
    (left right : Models1Group18.SizedSVec) : List (JInt .i64) → m Bool
  | [] => pure true
  | index :: rest => do
      let a ← liftResult (Models1Group18.svecGetindex64 left index)
      let b ← liftResult (Models1Group18.svecGetindex64 right index)
      match ← ops.equal a b with
      | .bool true => equalityLoop ops left right rest
      | .bool false => pure false
      | .other _ => throw (.core (.typeError "non-boolean (condition)"))

/-- Full SimpleVector equality with arbitrary selected element comparisons.
Lengths are real native Int64 values and their equality is the installed
machine operation. List.range is only a structural encoding of the finite
UnitRange iteration domain; every actual loop index is constructed with
native wrapping arithmetic, and SizedSVec ensures all source indices fit.
The vectors' immutable slots and their stored object handles are retained;
mutable state reachable through those handles belongs to the selected callee's
world. No reflexivity, purity, termination, or comparison law is imposed.
Julia source: base/essentials.jl:1109-1115.
Documentation: doc/src/manual/control-flow.md:378-386,516-541. -/
-- Source: base/essentials.jl:1109-1115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ==(v1::SimpleVector, v2::SimpleVector)
--     length(v1)==length(v2) || return false
--     for i = 1:length(v1)
--         v1[i] == v2[i] || return false
--     end
--     return true
-- end
-- /Source
def equal {m : Type → Type} [Monad m] [MonadExceptOf Err m]
    {Other : Type} (ops : EqualityOps m Other)
    (left right : Models1Group18.SizedSVec) : m Bool := do
  if JuliaLean.base.int.eq_int (Models1Group18.svecLength64 left)
      (Models1Group18.svecLength64 right) then
    let stop := Models1Group18.svecLength64 left
    let indices := (List.range stop.val.toNat).map fun k =>
      JuliaLean.base.int.add_int (JInt.wrap .i64 (Int.ofNat k)) (JInt.wrap .i64 1)
    equalityLoop ops left right indices
  else
    pure false

end JuliaLean.base.essentials.Models2Group19.SimpleVector
namespace JuliaLean.base.essentials.Models2Group19

/-- The distinguished Core.TypeName object stored in Base.Colon's name
field. This single token denotes that actual metadata object, retaining the
fixed field projection instead of accepting an arbitrary name argument.
Its qualification and printed spelling are determined by the selected IO
operation, as in base/show.jl:1211-1246.
Julia source: base/essentials.jl:1174-1177. -/
-- Source: base/essentials.jl:1174-1177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, ::Colon)
--     show_type_name(io, Colon.name)
--     print(io, "()")
-- end
-- /Source
inductive ColonTypeName where
  | colon
  deriving DecidableEq

/-- The two calls selected on an IO subtype that this method does not fix.
The first result is unconstrained and discarded; print's actual result is
returned without a Unit/Nothing assertion. The effect carrier retains the
IO context, output state, exceptions, and divergence. There is no callee
correctness or qualification law. Concrete IO instantiations use their
installed selected methods.
Julia source: base/essentials.jl:1174-1177.
Documentation: doc/src/manual/networking-and-streams.md:114-120;
doc/src/manual/functions.md:132-137. -/
-- Source: base/essentials.jl:1174-1177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, ::Colon)
--     show_type_name(io, Colon.name)
--     print(io, "()")
-- end
-- /Source
structure ShowColonOps (m : Type → Type) (IO First R : Type) where
  showTypeName : IO → ColonTypeName → m First
  print : IO → String → m R

/-- Display the fixed Colon type name on the original IO, then request the
literal parentheses on that same IO only after the first call succeeds.
Discard the first result and return print's complete result with its effects.
The existing ColonModel is the source's no-data singleton argument.
Julia source: base/essentials.jl:1174-1177. -/
-- Source: base/essentials.jl:1174-1177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function show(io::IO, ::Colon)
--     show_type_name(io, Colon.name)
--     print(io, "()")
-- end
-- /Source
def showColon {m : Type → Type} [Monad m] {IO First R : Type}
    (ops : ShowColonOps m IO First R) (io : IO)
    (_colon : JuliaLean.base.essentials.ColonModel) : m R := do
  let _ ← ops.showTypeName io .colon
  ops.print io "()"

end JuliaLean.base.essentials.Models2Group19

namespace JuliaLean.Multidim

/-- `length(t::AbstractArray) = prod(size(t))` (`base/essentials.jl:13`) with
`size(iter::CartesianIndices) = map(length, iter.indices)` (`base/multidimensional.jl:488`):
a product in wrapping `Int` arithmetic. -/
def ciLength (R : List Rng) : I64 := R.foldl (fun p r => p * i64 r.len) (i64 1)

end JuliaLean.Multidim

namespace JuliaLean.ArrayOps

open JuliaLean

variable {α β : Type}

/-- `getindex(A::Array, i::Int)` (`base/essentials.jl:1063-1067`): bounds check. -/
def getAt (a : List α) (i : JInt64) : Jl α :=
  if h : 1 ≤ i.val ∧ i.val ≤ a.length then
    .ok (a[(i.val - 1).toNat]'(by omega))
  else .error .boundsError

end JuliaLean.ArrayOps
