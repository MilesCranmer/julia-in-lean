import JuliaLean.src.gf_c
import JuliaLean.Compiler.src.cicache

/-!
The runtime objects that `Compiler/src/reinfer.jl` and `Compiler/src/bindinginvalidations.jl`
read and write, as explicit data: methods, method instances, code instances with their edge
lists, bindings with their partitions over world ranges, and the C runtime queries these files
call (method lookup, invoke lookup, image membership, binding access ranges) as an input
relation `Oracle`.

Objects are named by small integer ids, which stand for Julia object identity (`===`). A world
is a `Nat`; every world the runtime produces is at most `typemaxUInt`.

The oracle is the boundary of the model. Its functions answer exactly the queries that the
pinned Julia code makes through `ccall`s and through functions defined outside these files
(`_methods_by_ftype`, `_findsup`, `jl_sig_contributors_world`, `jl_linkage_blob_dep_world`,
`binding_access_range`, `typeintersect`, `<:`, `===` on types). The difftest fills it with the
answers the pinned Julia gives; properties take it as a hypothesis with the promises the C side
makes.
-/

namespace JuliaLean.Compiler.Reinfer

open JuliaLean.C JuliaLean.Compiler.CICache

/-- `CI_FLAGS_NATIVE_CACHE_VALID` (`Compiler/src/reinfer.jl:10`). -/
def ciFlagsNativeCacheValid : Nat := 0b1000

/-- `WORLD_AGE_REVALIDATION_SENTINEL` (`Compiler/src/reinfer.jl:11`): a code instance loaded from
an image whose edges still have to be verified carries this `max_world`. -/
def worldAgeRevalidationSentinel : Nat := 1

/-- `METHOD_SIG_LATEST_WHICH`, `METHOD_SIG_LATEST_ONLY`, `METHOD_SIG_NO_LOSERS`
(`Compiler/src/reinfer.jl:460-466`; the same bits as `src/julia_internal.h`). -/
def methodSigLatestWhich : Nat := JuliaLean.C.methodSigLatestWhich
def methodSigLatestOnly : Nat := JuliaLean.C.methodSigLatestOnly
def methodSigNoLosers : Nat := JuliaLean.C.methodSigNoLosers

/-- `x & bit != 0` on the small flag words. -/
def hasBit (x bit : Nat) : Bool := (x &&& bit) != 0

/-- A statement of a lowered `CodeInfo`, as far as the `GlobalRef` scans of
`Compiler/src/bindinginvalidations.jl` read it: the binding of the statement when it is itself a
`GlobalRef` (`convert(Core.Binding, stmt)`), and the values `userefs(stmt)` yields, in order
(`some b` for a `GlobalRef` to binding `b`, `none` for anything else). -/
structure Stmt where
  gr : Option Nat
  uses : List (Option Nat)
  deriving Inhabited, BEq, Repr

/-- A method: the gf.c record `JuliaLean.C.Method` (whose `uid` is the object id, `sig`,
`primaryWorld`, `dispatchStatus` and the assigned prefix of `interferences`, in definition
order), plus what `reinfer.jl` and `bindinginvalidations.jl` read besides.

`interferencesLen` is `length(m.interferences)`, the allocated length of the `Memory`; the
assigned entries are always a prefix of it (`Compiler/src/reinfer.jl:509-512`). -/
structure MethodR where
  m : JuliaLean.C.Method
  interferencesLen : Nat
  /-- `m.did_scan_source`: bit `0x1` the source was scanned for `GlobalRef`s, `0x4` a binding
  it reads changed since the require world. -/
  didScanSource : Nat
  /-- `external_blob_index(m)`: the linkage blob of the image owning `m`, or `typemaxUInt`. -/
  blob : Nat
  /-- `get_methodtable(m) !== nothing`. -/
  hasMethodTable : Bool
  /-- The statements of `_uncompressed_ir(m).code`, or `none` when `m.source` is not defined or
  not a `MaybeCompressed` (`Compiler/src/bindinginvalidations.jl:176-177`). -/
  source : Option (List Stmt)
  /-- `has_image_globalref(m)` (`base/runtime_internals.jl:2093`). -/
  hasImageGlobalref : Bool
  /-- `specializations(m)`: method instance ids. -/
  specializations : List Nat := []
  /-- `m.module`, as an object id. -/
  module_ : Nat := 0
  deriving Inhabited

namespace MethodR
def uid (m : MethodR) : Nat := m.m.uid
def sig (m : MethodR) : Val := m.m.sig
def primaryWorld (m : MethodR) : Nat := m.m.primaryWorld
def dispatchStatus (m : MethodR) : Nat := m.m.dispatchStatus
def interferences (m : MethodR) : List Nat := m.m.interferences
end MethodR

/-- A type object in an edge list: its identity (`objectid`, for the `IdDict` memo of lookups)
and its structure. -/
structure Sig where
  oid : Nat
  t : Val
  deriving Inhabited

/-- A method instance: its method (`mi.def`), `mi.specTypes` and `mi.dispatch_status`. -/
structure MIR where
  id : Nat
  def_ : Nat
  specTypes : Sig
  dispatchStatus : Nat
  /-- The cache chain `mi.cache`, `ci.next`, ... as code instance ids (empty: not defined). -/
  cache : List Nat := []
  deriving Inhabited

/-- One item of an edge list (`ci.edges`, a `SimpleVector`), by its Julia type. -/
inductive Edge where
  | ci (id : Nat)
  | mi (id : Nat)
  | method (uid : Nat)
  /-- An `Int`: the count of the expected matches that follow (negative: not fully covering). -/
  | int (k : Int)
  /-- A type: a call signature or an `invoke` signature. -/
  | ty (t : Sig)
  | binding (id : Nat)
  /-- `Core.PossiblyAmbiguous()`, the marker before an edge recorded as possibly ambiguous. -/
  | possiblyAmbiguous
  | methodTable
  deriving Inhabited

/-- A code instance: the fields the verifier reads and writes. -/
structure CIR where
  id : Nat
  mi : Nat
  /-- `ci.owner === nothing`. -/
  ownerNothing : Bool
  minWorld : Nat
  maxWorld : Nat
  flags : Nat
  /-- `ci.edges` when `isdefined(ci, :edges)`. -/
  edges : Option (Array Edge)
  /-- `external_blob_index(ci)`. -/
  blob : Nat
  deriving Inhabited

namespace CIR
/-- `codeinst.edges` read as a `SimpleVector` (an undefined field reads as `svec()` only in
the model; a CodeInstance built by `jl_new_codeinst` always has it). -/
def callees (c : CIR) : Array Edge := c.edges.getD #[]
end CIR

/-- `PARTITION_KIND_*`, `PARTITION_FLAG_*` and `PARTITION_MASK_*`
(`base/runtime_internals.jl:248-269`). -/
def partitionKindConst : Nat := 0x0
def partitionKindConstImport : Nat := 0x1
def partitionKindGlobal : Nat := 0x2
def partitionKindImplicitGlobal : Nat := 0x3
def partitionKindImplicitConst : Nat := 0x4
def partitionKindExplicit : Nat := 0x5
def partitionKindImported : Nat := 0x6
def partitionKindFailed : Nat := 0x7
def partitionKindDeclared : Nat := 0x8
def partitionKindGuard : Nat := 0x9
def partitionKindUndefConst : Nat := 0xa
def partitionKindBackdatedConst : Nat := 0xb
def partitionFlagExported : Nat := 0x10
def partitionFlagDeprecated : Nat := 0x20
def partitionFlagDepwarn : Nat := 0x40
def partitionMaskKind : Nat := 0x0f
def partitionMaskFlag : Nat := 0x1f0

/-- `BINDING_FLAG_ANY_IMPLICIT_EDGES` (`base/runtime_internals.jl:271`). -/
def bindingFlagAnyImplicitEdges : Nat := 0x8

/-- `binding_kind(bpart)` (`base/runtime_internals.jl:319`). -/
def bindingKind (kind : Nat) : Nat := kind &&& partitionMaskKind

/-- `is_some_imported` (`base/runtime_internals.jl:277`). -/
def isSomeImported (k : Nat) : Bool :=
  k == partitionKindImplicitGlobal || k == partitionKindImplicitConst ||
  k == partitionKindExplicit || k == partitionKindImported

/-- `is_some_implicit` (`base/runtime_internals.jl:278`). -/
def isSomeImplicit (k : Nat) : Bool :=
  k == partitionKindImplicitGlobal || k == partitionKindImplicitConst ||
  k == partitionKindGuard || k == partitionKindFailed

/-- `is_some_explicit_imported` (`base/runtime_internals.jl:279`). -/
def isSomeExplicitImported (k : Nat) : Bool :=
  k == partitionKindExplicit || k == partitionKindImported

/-- `is_some_binding_imported` (`base/runtime_internals.jl:280`). -/
def isSomeBindingImported (k : Nat) : Bool :=
  isSomeExplicitImported k || k == partitionKindImplicitGlobal

/-- A binding partition: `min_world`, `max_world`, the full `kind` word (kind and flags) and,
for an imported kind, the binding id of `partition_restriction(bpart)`. -/
structure Partition where
  /-- Object identity of the partition (`===`). -/
  pid : Nat := 0
  minWorld : Nat
  maxWorld : Nat
  kind : Nat
  restriction : Option Nat := none
  deriving Inhabited, BEq, Repr

/-- `is_leaf_partition(partition)` (`Compiler/src/abstractinterpretation.jl:4058-4059`). -/
def isLeafPartition (p : Partition) : Bool := !isSomeBindingImported (bindingKind p.kind)

/-- A binding: its partitions, newest first (`b.partitions` and the `next` chain), and
`b.flags`. -/
structure BindingR where
  id : Nat
  partitions : List Partition
  flags : Nat := 0
  /-- `b.globalref.mod`, as an object id. -/
  module_ : Nat := 0
  deriving Inhabited

/-- The answers of the runtime queries the model does not compute itself. All take and return
object ids and worlds; a missing answer is a model failure (`throw` of a non-`julia:` string). -/
structure Oracle where
  /-- `a <: b` on types. -/
  sub : Val → Val → Except String Bool
  /-- `typeintersect(a, b)`. -/
  isect : Val → Val → Except String Val
  /-- `a === b` on types. -/
  egal : Val → Val → Except String Bool
  /-- `_methods_by_ftype(sig, nothing, lim, world, false, min, max, has_ambig)` with
  `min = 1, max = typemax(UInt), has_ambig = 0` on entry: the matched method uids in result
  order (`none` is `nothing`), and the final `min[]`, `max[]`, `has_ambig[]`. -/
  matchingMethods : Val → Int → Nat → Except String (Option (List Nat) × Nat × Nat × Int)
  /-- `_findsup(sig, mt, world)`: the matched method uid, and the validity range. -/
  findsup : Val → Nat → Except String (Option Nat × Nat × Nat)
  /-- `jl_sig_contributors_world(sig, mt, image)` for `image ≠ typemax(UInt)`. -/
  sigContributorsWorld : Val → Nat → Except String Nat
  /-- `jl_linkage_blob_dep_world(image, blob)`. -/
  linkageBlobDepWorld : Nat → Nat → Except String Nat
  /-- `binding_access_range(b, WorldWithRange(world, WorldRange(get_require_world(), world)),
  false)[1]` for the binding id `b` and the world given. -/
  bindingAccessRange : Nat → Nat → Except String WorldRange

/-- The process state the verifier reads (`get_world_counter()`, `get_require_world()`,
`jl_first_image_replacement_world`) and the objects. -/
structure Heap where
  worldCounter : Nat
  requireWorld : Nat
  firstImageReplacementWorld : Nat := typemaxUInt
  /-- `JLOptions().code_coverage != 0 || JLOptions().malloc_log != 0`. -/
  instrumenting : Bool := false
  /-- `generating_output(true)` / `generating_output()`. -/
  generatingOutputIncremental : Bool := false
  generatingOutput : Bool := false
  methods : Array MethodR
  mis : Array MIR
  cis : Array CIR
  bindings : Array BindingR
  /-- `jl_get_module_binding(mod, name, true)`: the binding of each `(module, name)` pair, as
  object ids. -/
  moduleBindings : List ((Nat × Nat) × Nat) := []
  deriving Inhabited

/-- Side effects that leave the modelled objects but are visible to the runtime: cache
insertions, backedge stores, binding backedges and invalidation calls. -/
inductive Event where
  | miCacheInsert (mi ci : Nat)
  | storeBackedges (ci : Nat)
  | bindingBackedge (b method : Nat)
  | invalidateCI (ci world : Nat)
  | logBindingInvalidation
  /-- A branch marker, for the difftest's path coverage only; it does not stand for anything
  the runtime does. -/
  | path (tag : String)
  deriving Inhabited, BEq, Repr

/-- `jl_new_codeinst`-time and later object lookups. A bad id is a model failure. -/
def Heap.method (H : Heap) (uid : Nat) : Except String MethodR :=
  match H.methods.find? (·.uid == uid) with
  | some m => pure m
  | none => throw s!"model: no method {uid}"

def Heap.miR (H : Heap) (id : Nat) : Except String MIR :=
  match H.mis.find? (·.id == id) with
  | some m => pure m
  | none => throw s!"model: no method instance {id}"

def Heap.ciR (H : Heap) (id : Nat) : Except String CIR :=
  match H.cis.find? (·.id == id) with
  | some c => pure c
  | none => throw s!"model: no code instance {id}"

def Heap.bindingR (H : Heap) (id : Nat) : Except String BindingR :=
  match H.bindings.find? (·.id == id) with
  | some b => pure b
  | none => throw s!"model: no binding {id}"

def Heap.setCI (H : Heap) (c : CIR) : Heap :=
  { H with cis := H.cis.map fun d => if d.id == c.id then c else d }

def Heap.setMI (H : Heap) (m : MIR) : Heap :=
  { H with mis := H.mis.map fun d => if d.id == m.id then m else d }

def Heap.setMethod (H : Heap) (m : MethodR) : Heap :=
  { H with methods := H.methods.map fun d => if d.uid == m.uid then m else d }

/-- The state the modelled functions run in: the heap, the side effects so far, and the
verifier's workspace (`VerifyMethodWorkspace`), whose fields are defined in
`JuliaLean/Compiler/src/reinfer.lean` and kept here as an opaque payload type `W`. -/
structure RS (W : Type) where
  heap : Heap
  events : Array Event := #[]
  ws : W
  deriving Inhabited

abbrev RM (W : Type) := StateT (RS W) (Except String)

def getHeap {W : Type} : RM W Heap := do return (← get).heap
def modifyHeap {W : Type} (f : Heap → Heap) : RM W Unit :=
  modify fun s => { s with heap := f s.heap }
def emit {W : Type} (e : Event) : RM W Unit :=
  modify fun s => { s with events := s.events.push e }
def liftE {W α : Type} (x : Except String α) : RM W α := StateT.lift x

/-- Throw the Julia exception `exc`. -/
def jlThrow {α : Type} {m : Type → Type} [MonadExcept String m] (exc : String) (msg : String := "") :
    m α :=
  throw s!"julia:{exc}: {msg}"

end JuliaLean.Compiler.Reinfer
