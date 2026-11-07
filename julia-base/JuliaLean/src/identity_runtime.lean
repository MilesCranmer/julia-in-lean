import JuliaLean.src.genericmemory_c
import JuliaLean.base.array
import JuliaLean.base.iterators
import JuliaLean.src.support.hashing_c

/-! Native 64-bit ABI data for the identity-table C mirrors. Payloads and
pointer cells use the installed GenericMemory RawState/ByteHeap. Datatype and
object records are runtime metadata, with nominal identity represented by
addresses, never display names. -/
namespace JuliaLean.src.identity_runtime
open JuliaLean
namespace GM
export JuliaLean.src.genericmemory_c (MemoryObject RawState boxedDictLayout interpretRawEffect)
end GM
abbrev Word := UInt64
abbrev Memory := GM.MemoryObject

inductive Error where
  | array (error : JuliaLean.base.array.Error)
  | julia (error : JlError)
  | keyError (key : Word)
  | keyTypeError (expected key : Word)
  | typeAssertion (expected value : Word)
  | userException (value : Word)
  | abort (assertion : String)
  | undefinedBehavior (operation : String) (address : Word)
  deriving Repr

structure Field where
  offset : Nat
  size : Nat
  isPointer : Bool
  fieldType : Word
  deriving Repr, Inhabited

structure Datatype where
  name : Word
  hash : Word
  parameters : Word
  isMutable : Bool
  isAbstract : Bool
  isConcrete : Bool
  size : Nat
  bits : Nat
  hasPadding : Bool
  isBitsEgal : Bool
  firstPointer : Int
  fields : List Field
  pointerOffsets : List Nat
  deriving Repr, Inhabited

/-- Field views of Symbol, TypeName, Module, SimpleVector, String, TypeVar,
Union, UnionAll, TypeEq/TypeEgal and Vararg runtime objects. -/
structure Object where
  hash : Word := 0
  length : Nat := 0
  name : Word := 0
  lower : Word := 0
  upper : Word := 0
  left : Word := 0
  right : Word := 0
  «variable» : Word := 0
  body : Word := 0
  typeArgument : Word := 0
  countArgument : Word := 0
  deriving Repr, Inhabited

inductive Tag where
  | invalid | typeofbottom | unionall | uniontype | typeeq | typeegal | datatype
  | tvar | vararg | gotoifnot | returnnode | enternode | pinode | phinode | phicnode
  | upsilonnode | globalref | quotenode | symbol | module_ | simplevector | string
  | task | cancelSource | waitEntry | bool_ | nothing | char | int16 | int32 | int64
  | int8 | uint16 | uint32 | uint64 | uint8 | addrspacecore | intrinsic | argument
  | slotnumber | ssavalue | gotonode | dynamic
  deriving Repr, DecidableEq, Inhabited

/-- src/julia.h:1110-1171, with the enum's initial jl_null_tag = 0. -/
def smallTag : Nat → Tag
  | 1 => .typeofbottom | 2 => .unionall | 3 => .uniontype | 4 => .typeeq | 5 => .typeegal
  | 6 => .datatype | 7 => .tvar | 8 => .vararg | 9 => .gotoifnot | 10 => .returnnode
  | 11 => .enternode | 12 => .pinode | 13 => .phinode | 14 => .phicnode
  | 15 => .upsilonnode | 16 => .globalref | 17 => .quotenode | 18 => .symbol
  | 19 => .module_ | 20 => .simplevector | 21 => .string | 22 => .task
  | 23 => .cancelSource | 24 => .waitEntry | 25 => .bool_ | 26 => .nothing | 27 => .char
  | 28 => .int16 | 29 => .int32 | 30 => .int64 | 31 => .int8 | 32 => .uint16
  | 33 => .uint32 | 34 => .uint64 | 35 => .uint8 | 36 => .addrspacecore
  | 37 => .intrinsic | 38 => .argument | 39 => .slotnumber | 40 => .ssavalue
  | 41 => .gotonode | _ => .invalid

inductive Event where
  | load (address value : Word)
  | writeBarrier (owner address oldValue newValue : Word)
  | atomicStore (address value : Word) (order : JuliaLean.base.genericmemory.MemoryOrder)
  | atomicIntegerLoad (address value : Word) (bytes : Nat) (order : JuliaLean.base.genericmemory.MemoryOrder)
  | atomicIntegerStore (address value : Word) (bytes : Nat) (order : JuliaLean.base.genericmemory.MemoryOrder)
  | localAtomicLoad (index : Nat) (value : Word)
  | localAtomicStore (index : Nat) (value : Word)
  | localWriteBarrier (parent : Word) (index : Nat) (oldValue newValue : Word)
  | memset (address size : Word)
  | memcpy (destination source size : Word)
  | pushRoots (locals : List Nat)
  | popRoots
  deriving Repr

structure Globals where
  nothing : Word
  anyType : Word
  tupleTypename : Word
  typenameType : Word
  emptyMemory : Memory

structure World where
  raw : GM.RawState
  objects : Word → Option Object
  datatypes : Word → Option Datatype
  typenameHashes : Word → Option Word
  smallTypes : Nat → Option Word
  internedSymbols : String → Option Word := fun _ => none
  globals : Globals
  memories : Word → Option Memory := fun _ => none
  locals : List (Option Memory) := []
  roots : List (List Nat) := []
  events : List Event := []

instance {E H : Type} : Lean.Order.MonoBind (JuliaLean.base.iterators.Exec E H) where
  bind_mono_left := by
    intro α β first second next h world
    have point := h world
    change Lean.Order.FlatOrder.rel (b := none) (first world) (second world) at point
    change Lean.Order.FlatOrder.rel (b := none)
      (JuliaLean.base.iterators.bind first next world)
      (JuliaLean.base.iterators.bind second next world)
    unfold JuliaLean.base.iterators.bind
    generalize firstRun : first world = firstResult at point ⊢
    generalize secondRun : second world = secondResult at point ⊢
    cases point with
    | bot => exact .bot
    | refl => exact .refl
  bind_mono_right := by
    intro α β action first second h world
    change Lean.Order.FlatOrder.rel (b := none)
      (JuliaLean.base.iterators.bind action first world)
      (JuliaLean.base.iterators.bind action second world)
    cases run : action world with
    | none =>
      simp only [JuliaLean.base.iterators.bind, run]
      exact .refl
    | some result =>
      rcases result with ⟨result, state⟩
      cases result with
      | error error =>
        simp only [JuliaLean.base.iterators.bind, run]
        exact .refl
      | ok value =>
        have point := h value state
        change Lean.Order.FlatOrder.rel (b := none) (first value state) (second value state) at point
        simpa only [JuliaLean.base.iterators.bind, run] using point

abbrev M (A : Type) := JuliaLean.base.iterators.Exec Error World A

def fail {A : Type} (error : Error) : M A := JuliaLean.base.iterators.fail error

def getWorld : M World := fun world => some (.ok world, world)
def modifyWorld (f : World → World) : M Unit := fun world => some (.ok (), f world)

instance : MonadExceptOf Error M where
  throw := fail
  tryCatch action handler := fun world => match action world with
    | none => none
    | some (.error error, world) => handler error world
    | some (.ok value, world) => some (.ok value, world)

instance : MonadExceptOf JuliaLean.base.array.Error M where
  throw error := fail (.array error)
  tryCatch action handler := fun world => match action world with
    | none => none
    | some (.error (.array error), world) => handler error world
    | other => other

def objectAt (address : Word) : M Object := do
  match (← getWorld).objects address with
  | some object => pure object
  | none => fail (.undefinedBehavior "runtime object field access" address)

def datatypeAt (address : Word) : M Datatype := do
  match (← getWorld).datatypes address with
  | some datatype => pure datatype
  | none => fail (.undefinedBehavior "datatype field access" address)

def readableRange (heap : JuliaLean.base.pointer.ByteHeap) (address size : Nat) : Bool := Id.run do
  if address + size > 2 ^ 64 then return false
  for offset in [0:size] do
    if !heap.validByte (address + offset) then return false
  return true

def requireReadable (address : Word) (size : Nat) : M Unit := do
  let heap := (← getWorld).raw.heap
  if address = 0 || !(readableRange heap address.toNat size) then
    fail (.undefinedBehavior "native memory load" address)
  else pure ()

/-- The byte heap is total; validByte and the nonwrapping range mark C's
readable domain. Pointer words are little-endian on the target ABI. -/
def loadWord (address : Word) : M Word := do
  requireReadable address 8
  pure (JuliaLean.src.support.hashing_c.load64 (← getWorld).raw.heap address.toNat)

def loadByte (address : Word) : M UInt8 := do
  requireReadable address 1
  pure (JuliaLean.src.support.hashing_c.byteAt (← getWorld).raw.heap address.toNat)

def encodeWord (value : Word) : List JuliaLean.base.pointer.Byte :=
  (List.range 8).map fun i => JInt.wrap .u8 ((value >>> UInt64.ofNat (8*i)).toNat % 256)

/-- Atomic loads and jl_gc_write_atomic use the same bytes as GenericMemory.
The barrier is recorded before the release/relaxed store, as in
src/julia.h:1483-1487. No GC operation is substituted for the pointer write. -/
def atomicLoad (address : Word) : M Word := do
  let value ← loadWord address
  modifyWorld fun world => { world with events := world.events ++ [.load address value] }
  pure value

def gcWriteAtomic (owner address value : Word)
    (order : JuliaLean.base.genericmemory.MemoryOrder) : M Unit := do
  let old ← loadWord address
  modifyWorld fun world =>
    let raw := GM.interpretRawEffect world.raw (.deletionBarrier owner.toNat address.toNat)
    { world with
      raw := { raw with heap := raw.heap.writeBytes address.toNat (encodeWord value) }
      events := world.events ++ [.writeBarrier owner address old value,
                                  .atomicStore address value order] }

/-- src/julia.h:201-208, jl_typetagof, and :1175-1179, jl_to_typeof. -/
def typetag (value : Word) : M Word := do
  if value.toNat < 8 then fail (.undefinedBehavior "jl_typetagof" value)
  else return (← loadWord (value-8)) &&& (~~~(15 : Word))

def tagKind (tag : Word) : Tag := if tag < 1024 then smallTag (tag.toNat / 16) else .dynamic

def toTypeof (tag : Word) : M Word := do
  if tag < 1024 then
    match (← getWorld).smallTypes (tag.toNat / 8) with
    | some datatype => pure datatype
    | none => fail (.undefinedBehavior "jl_small_typeof" tag)
  else pure tag

def typeof (value : Word) : M Word := do toTypeof (← typetag value)

def memoryOwner (memory : Memory) : Word := UInt64.ofNat memory.metadata.owner

def cellAddress (memory : Memory) (index : Word) : Word :=
  UInt64.ofNat memory.ptr + 8*index

def plainReadCell (memory : Memory) (index : Word) : M Word := do
  if index.toNat ≥ memory.length then
    fail (.undefinedBehavior "GenericMemory pointer indexing" (cellAddress memory index))
  else loadWord (cellAddress memory index)

def readCell (memory : Memory) (index : Word) : M Word := do
  if index.toNat ≥ memory.length then
    fail (.undefinedBehavior "GenericMemory pointer indexing" (cellAddress memory index))
  else atomicLoad (cellAddress memory index)

def writeCell (memory : Memory) (index value : Word)
    (order : JuliaLean.base.genericmemory.MemoryOrder) : M Unit := do
  if index.toNat ≥ memory.length then
    fail (.undefinedBehavior "GenericMemory pointer indexing" (cellAddress memory index))
  else gcWriteAtomic (memoryOwner memory) (cellAddress memory index) value order

def newLocal (value : Option Memory) : M Nat := do
  let index := (← getWorld).locals.length
  modifyWorld fun world => { world with locals := world.locals ++ [value] }
  pure index

def readLocal (index : Nat) : M Memory := do
  match (← getWorld).locals[index]? with
  | some (some memory) => pure memory
  | _ => fail (.undefinedBehavior "local GenericMemory pointer" (UInt64.ofNat index))

def writeLocal (index : Nat) (value : Memory) : M Unit := do
  if index ≥ (← getWorld).locals.length then fail (.undefinedBehavior "local pointer store" (UInt64.ofNat index))
  else modifyWorld fun world => { world with locals := world.locals.set index (some value) }

def pushRoots (indices : List Nat) : M Unit :=
  modifyWorld fun world => { world with
    roots := indices :: world.roots
    events := world.events ++ [.pushRoots indices] }

def popRoots : M Unit := do
  match (← getWorld).roots with
  | [] => fail (.abort "JL_GC_POP without a frame")
  | _ :: rest => modifyWorld fun world => { world with
      roots := rest
      events := world.events ++ [.popRoots] }

/-- The remaining low-level GC allocation boundary. The installed array model
performs GenericMemory's size/layout checks; this operation is only the backing
allocation used after those checks, not an identity-table callback. -/
structure GC where
  allocateBoxedMemory : Nat → M Memory

/-- src/genericmemory.c:217-220 and :75-102; the element type is Memory{Any}.
The installed allocation model selects the canonical empty memory, checks byte
size/overflow and uses eight-byte boxed pointer cells. -/
def allocMemoryAny (gc : GC) (count : Word) : M Memory := do
  let memory ← JuliaLean.base.array.allocGenericMemory (some ⟨8, true, false⟩)
    (do pure (← getWorld).globals.emptyMemory) gc.allocateBoxedMemory count.toNat
  let owner := memoryOwner memory
  modifyWorld fun world => { world with
    memories := fun address =>
      if address == owner then some memory else world.memories address }
  pure memory

end JuliaLean.src.identity_runtime
