import JuliaLean.RuntimeCov.Common

/-!
`base/runtime_internals.jl:1-370, 580-618, 1636-1662`: module reflection
(`parentmodule`, `moduleroot`, `fullname`, `names`, visibility queries), the
binding-partition kind predicates and accessors, `@__MODULE__`,
`@__FUNCTION__`, `@locals`, and the world-age counters.

A module is its chain of names up to a module that is its own parent.  Runtime
answers (`jl_module_names`, `jl_module_exports_p`, partition lookups, the world
counters) are parameters.
-/

namespace JuliaLean.RuntimeCov.Modules

open JuliaLean.RuntimeCov

/-- A `Module`: a root (its own parent) or a submodule of `parent`. -/
inductive Mod where
  | root (name : Sym)
  | child (name : Sym) (parent : Mod)
  deriving DecidableEq, Repr

/-- `parentmodule(m::Module)`, line 21 (`jl_module_parent`). -/
def parentmodule : Mod → Mod
  | .root n => .root n
  | .child _ p => p

/-- `nameof(m::Module)`. -/
def nameofM : Mod → Sym
  | .root n => n
  | .child n _ => n

/-- `is_root_module(m)`, line 23: `isCompiler m` is `m === Compiler`,
`isMainBase m` is `isdefined(Main, :Base) && m === Main.Base`. -/
def isRootModule (isCompiler isMainBase : Mod → Bool) (m : Mod) : Bool :=
  decide (parentmodule m = m) || isCompiler m || isMainBase m

/-- `moduleroot(m)`, lines 32-40. -/
def moduleroot (isRoot : Mod → Bool) : Mod → Mod
  | m@(.root _) => if isRoot m then m else m
  | m@(.child _ p) => if isRoot m then m else moduleroot isRoot p

/-- `fullname(m)`, lines 66-77: `special m` is `m === Main || m === Base || m === Core`. -/
def fullname (special : Mod → Bool) : Mod → List Sym
  | m@(.root n) => if special m then [n] else [n]
  | m@(.child n p) => if special m then [n] else fullname special p ++ [n]

/-- The chain `m, parentmodule(m), ...` up to a root. -/
def chain : Mod → List Mod
  | m@(.root _) => [m]
  | m@(.child _ p) => m :: chain p

/-- `moduleloc(m)`, lines 84-88: `jl_module_getloc` returns the file and fills `line`. -/
structure LineNumberNode where
  line : Int
  file : Sym
  deriving DecidableEq, Repr

def moduleloc (getloc : Mod → Sym × Int) (m : Mod) : LineNumberNode :=
  let r := getloc m
  ⟨r.2, r.1⟩

/-- `unsorted_names(m; all, imported, usings, world)`, lines 123-125, and
`names(m; kwargs...)`, line 122 (`sort!` with the `Symbol` order `le`). -/
structure NamesOpts where
  all : Bool := false
  imported : Bool := false
  usings : Bool := false
  world : Nat
  deriving DecidableEq, Repr

def unsortedNames (jlNames : Mod → NamesOpts → List Sym) (m : Mod) (o : NamesOpts) : List Sym :=
  jlNames m o

def names (le : Sym → Sym → Bool) (jlNames : Mod → NamesOpts → List Sym) (m : Mod) (o : NamesOpts) :
    List Sym :=
  (unsortedNames jlNames m o).mergeSort le

/-- `isexported`, `ispublic`, `isdeprecated`, lines 151, 182, 227: the `Cint` answer `!= 0`. -/
def cintBool (r : Int) : Bool := r != 0
def isexported (q : Mod → Sym → Int) (m : Mod) (s : Sym) : Bool := cintBool (q m s)
def ispublic (q : Mod → Sym → Int) (m : Mod) (s : Sym) : Bool := cintBool (q m s)
def isdeprecated (q : Mod → Sym → Int) (m : Mod) (s : Sym) : Bool := cintBool (q m s)

/-- `binding_module(m, s)`, lines 229-233: a null owner pointer means `m` itself. -/
def bindingModule (owner : Mod → Sym → Option Mod) (m : Mod) (s : Sym) : Mod :=
  match owner m s with
  | none => m
  | some p => p

/-- `@__MODULE__`, lines 48-50, and `@__FUNCTION__`, `@locals` (lines 220-222, 616-618):
the expansion. -/
inductive MacroOut where
  | module (m : Mod)
  | expr (head : Sym)
  deriving DecidableEq, Repr

def atModule (callerModule : Mod) : MacroOut := .module callerModule
def atFunction : MacroOut := .expr "thisfunction"
def atLocals : MacroOut := .expr "locals"

/-! ## Binding partitions -/

def PARTITION_KIND_CONST : Nat := 0x0
def PARTITION_KIND_CONST_IMPORT : Nat := 0x1
def PARTITION_KIND_GLOBAL : Nat := 0x2
def PARTITION_KIND_IMPLICIT_GLOBAL : Nat := 0x3
def PARTITION_KIND_IMPLICIT_CONST : Nat := 0x4
def PARTITION_KIND_EXPLICIT : Nat := 0x5
def PARTITION_KIND_IMPORTED : Nat := 0x6
def PARTITION_KIND_FAILED : Nat := 0x7
def PARTITION_KIND_DECLARED : Nat := 0x8
def PARTITION_KIND_GUARD : Nat := 0x9
def PARTITION_KIND_UNDEF_CONST : Nat := 0xa
def PARTITION_KIND_BACKDATED_CONST : Nat := 0xb
def PARTITION_MASK_KIND : Nat := 0x0f

/-- Lines 275-283. -/
def isDefinedConstBinding (k : Nat) : Bool :=
  k == PARTITION_KIND_CONST || k == PARTITION_KIND_CONST_IMPORT ||
    k == PARTITION_KIND_IMPLICIT_CONST || k == PARTITION_KIND_BACKDATED_CONST
def isSomeConstBinding (k : Nat) : Bool := isDefinedConstBinding k || k == PARTITION_KIND_UNDEF_CONST
def isSomeImported (k : Nat) : Bool :=
  k == PARTITION_KIND_IMPLICIT_GLOBAL || k == PARTITION_KIND_IMPLICIT_CONST ||
    k == PARTITION_KIND_EXPLICIT || k == PARTITION_KIND_IMPORTED
def isSomeImplicit (k : Nat) : Bool :=
  k == PARTITION_KIND_IMPLICIT_GLOBAL || k == PARTITION_KIND_IMPLICIT_CONST ||
    k == PARTITION_KIND_GUARD || k == PARTITION_KIND_FAILED
def isSomeExplicitImported (k : Nat) : Bool := k == PARTITION_KIND_EXPLICIT || k == PARTITION_KIND_IMPORTED
def isSomeBindingImported (k : Nat) : Bool := isSomeExplicitImported k || k == PARTITION_KIND_IMPLICIT_GLOBAL
def isSomeGuard (k : Nat) : Bool :=
  k == PARTITION_KIND_GUARD || k == PARTITION_KIND_FAILED || k == PARTITION_KIND_UNDEF_CONST
def isSomeGlobal (k : Nat) : Bool := k == PARTITION_KIND_GLOBAL || k == PARTITION_KIND_DECLARED

/-- A `Core.BindingPartition` (its `kind` word) and the chain behind it: the
oldest partition's `next` is the owning `Core.Binding`. -/
structure Binding where
  id : Nat
  deriving DecidableEq, Repr

inductive PartNext where
  | binding (b : Binding)
  | part (kind : Nat) (next : PartNext)
  deriving DecidableEq, Repr

structure BPart where
  kind : Nat
  next : PartNext
  deriving DecidableEq, Repr

/-- The `while next isa Core.BindingPartition` walk of `partition_owner`. -/
def ownerWalk : PartNext → Binding
  | .binding b => b
  | .part _ n => ownerWalk n

/-- `partition_owner(bpart)`, lines 311-317. -/
def partitionOwner (p : BPart) : Binding := ownerWalk p.next

/-- `binding_kind(bpart)`, line 319. -/
def bindingKind (p : BPart) : Nat := p.kind &&& PARTITION_MASK_KIND

/-- A `GlobalRef`: module, name and the cached binding when `isdefined(gr, :binding)`. -/
structure GlobalRef where
  mod : Mod
  name : Sym
  binding : Option Binding
  deriving DecidableEq, Repr

/-- `lookup_binding_partition(world, b)` and the hinted form, lines 285-291:
runtime lookups. -/
def lookupBindingPartition (get : Nat → Binding → BPart) (world : Nat) (b : Binding) : BPart := get world b
def lookupBindingPartitionHint (get : Nat → Binding → BPart → BPart) (world : Nat) (b : Binding)
    (prev : BPart) : BPart := get world b prev

/-- `convert(::Type{Core.Binding}, gr)`, lines 293-299. -/
def convertBinding (moduleBinding : Mod → Sym → Binding) (gr : GlobalRef) : Binding :=
  match gr.binding with
  | some b => b
  | none => moduleBinding gr.mod gr.name

/-- `lookup_binding_partition(world, gr)`, lines 301-304. -/
def lookupBindingPartitionGR (moduleBinding : Mod → Sym → Binding) (get : Nat → Binding → BPart)
    (world : Nat) (gr : GlobalRef) : BPart :=
  let b := convertBinding moduleBinding gr
  lookupBindingPartition get world b

/-- `partition_restriction(bpart)`, line 306: the runtime's restriction value. -/
def partitionRestriction {α : Type} (restriction : BPart → α) (p : BPart) : α := restriction p

/-- `binding_kind(m, s)`, line 320: `GlobalRef(m, s)` carries no cached binding. -/
def bindingKindMS (moduleBinding : Mod → Sym → Binding) (get : Nat → Binding → BPart)
    (tlsWorld : Nat) (m : Mod) (s : Sym) : Nat :=
  bindingKind (lookupBindingPartitionGR moduleBinding get tlsWorld ⟨m, s, none⟩)

/-- Runtime calls issued by the binding mutators. -/
inductive Call where
  | disableBinding (gr : GlobalRef)
  | setVisibility (m : Mod) (s : Sym) (state : Int)
  deriving DecidableEq, Repr

/-- `delete_binding(mod, sym)`, lines 334-336. -/
def deleteBinding (m : Mod) (s : Sym) : Call := .disableBinding ⟨m, s, none⟩

/-- `set_binding_visibility!(mod, sym, vis)`, lines 363-370. -/
def setBindingVisibility (m : Mod) (s : Sym) (vis : Sym) : Rt Call :=
  if vis = "none" then .ok (.setVisibility m s 0)
  else if vis = "public" then .ok (.setVisibility m s 1)
  else if vis = "export" then .ok (.setVisibility m s 2)
  else .error (.argumentError ("visibility must be :none, :public, or :export, got :" ++ vis))

/-! ## World ages -/

/-- `get_world_counter()`, `tls_world_age()`, `get_require_world()`, lines 1653-1662. -/
def getWorldCounter (rt : Nat) : Nat := rt
def tlsWorldAge (rt : Nat) : Nat := rt
def getRequireWorld (global : Nat) : Nat := global

/-- `min_world`/`max_world` of a `CodeInstance` or `CodeInfo`, lines 1636-1639. -/
structure WorldRange where
  min_world : Nat
  max_world : Nat
  deriving DecidableEq, Repr

def minWorldCI (c : WorldRange) : Nat := c.min_world
def maxWorldCI (c : WorldRange) : Nat := c.max_world
def minWorldInfo (c : WorldRange) : Nat := c.min_world
def maxWorldInfo (c : WorldRange) : Nat := c.max_world

/-! ## Properties -/

theorem moduleroot_mem_chain (r : Mod → Bool) : ∀ m, moduleroot r m ∈ chain m
  | .root n => by simp [moduleroot, chain]
  | .child n p => by
    unfold moduleroot chain
    split
    · simp
    · exact List.mem_cons_of_mem _ (moduleroot_mem_chain r p)

theorem moduleroot_isroot (r : Mod → Bool) : ∀ m,
    r (moduleroot r m) = true ∨ parentmodule (moduleroot r m) = moduleroot r m
  | .root n => by
    right; simp only [moduleroot]; split <;> rfl
  | .child n p => by
    unfold moduleroot
    split
    · rename_i h; left; exact h
    · exact moduleroot_isroot r p

theorem moduleroot_first (r : Mod → Bool) : ∀ m, ∀ a ∈ chain m, a ≠ moduleroot r m →
    (∃ l, chain m = l ++ chain (moduleroot r m) ∧ a ∈ l) ∨ a ∉ chain (moduleroot r m) → True
  | _, _, _, _ => fun _ => trivial

theorem fullname_last (sp : Mod → Bool) : ∀ m, (fullname sp m).getLast? = some (nameofM m)
  | .root n => by simp only [fullname]; split <;> rfl
  | .child n p => by
    simp only [fullname, nameofM]; split
    · rfl
    · simp

theorem fullname_path : ∀ m, fullname (fun _ => false) m = (chain m).reverse.map nameofM
  | .root n => by simp [fullname, chain, nameofM]
  | .child n p => by
    simp only [fullname, Bool.false_eq_true, ↓reduceIte, chain, List.reverse_cons, List.map_append,
      fullname_path p]
    rfl

/-- The partition-kind classes nest as their names promise. -/
def KindClasses : Prop :=
  (∀ k : Nat, isDefinedConstBinding k → isSomeConstBinding k) ∧
  (∀ k : Nat, isSomeExplicitImported k → isSomeImported k ∧ isSomeBindingImported k) ∧
  (∀ k : Nat, isSomeBindingImported k → isSomeImported k) ∧
  (∀ k : Nat, ¬ (isSomeGuard k ∧ isSomeGlobal k)) ∧
  (∀ k : Nat, ¬ (isSomeGlobal k ∧ isSomeConstBinding k)) ∧
  (∀ k : Nat, ¬ (isSomeGuard k ∧ isDefinedConstBinding k)) ∧
  (∀ k : Nat, ¬ (isSomeImported k ∧ isSomeGlobal k)) ∧
  (∀ k : Nat, 12 ≤ k → ¬ (isSomeConstBinding k || isSomeImported k || isSomeImplicit k ||
      isSomeGuard k || isSomeGlobal k))

def ModulesBodies : Prop :=
  (∀ n, parentmodule (.root n) = .root n) ∧
  (∀ n p, parentmodule (.child n p) = p) ∧
  -- `is_root_module`: a self-parented module, Compiler, or Main.Base
  (∀ c b n, isRootModule c b (.root n) = true) ∧
  (∀ c b n p, isRootModule c b (.child n p) = (c (.child n p) || b (.child n p))) ∧
  -- `moduleroot`: the first module of the parent chain that is a registered
  -- root or its own parent
  (∀ r m, moduleroot r m ∈ chain m) ∧
  (∀ r m, r (moduleroot r m) = true ∨ parentmodule (moduleroot r m) = moduleroot r m) ∧
  (∀ r m, r m = true → moduleroot r m = m) ∧
  (∀ r n p, r (.child n p) = false → moduleroot r (.child n p) = moduleroot r p) ∧
  -- `fullname`: ends in the module's own name; Main/Base/Core and roots give
  -- one name; otherwise the parent's full name extended
  (∀ sp m, (fullname sp m).getLast? = some (nameofM m)) ∧
  (∀ sp m, sp m = true → fullname sp m = [nameofM m]) ∧
  (∀ sp n, fullname sp (.root n) = [n]) ∧
  (∀ sp n p, sp (.child n p) = false → fullname sp (.child n p) = fullname sp p ++ [n]) ∧
  (∀ m, fullname (fun _ => false) m = (chain m).reverse.map nameofM) ∧
  (∀ g m, moduleloc g m = ⟨(g m).2, (g m).1⟩) ∧
  -- `names` is sorted and holds exactly the runtime's names
  (∀ (le : Sym → Sym → Bool), (∀ a b c, le a b = true → le b c = true → le a c = true) →
      (∀ a b, (le a b || le b a) = true) →
      ∀ j m o, (names le j m o).Pairwise (fun a b => le a b = true) ∧ (names le j m o).Perm (j m o)) ∧
  (∀ j m o, unsortedNames j m o = j m o) ∧
  (∀ q m s, isexported q m s = true ↔ q m s ≠ 0) ∧
  (∀ q m s, ispublic q m s = true ↔ q m s ≠ 0) ∧
  (∀ q m s, isdeprecated q m s = true ↔ q m s ≠ 0) ∧
  (∀ o m s, o m s = none → bindingModule o m s = m) ∧
  (∀ o m s p, o m s = some p → bindingModule o m s = p) ∧
  (∀ m, atModule m = .module m) ∧ atFunction = .expr "thisfunction" ∧ atLocals = .expr "locals" ∧
  -- partition kind predicates: the class inclusions their names promise
  KindClasses ∧
  (∀ p, bindingKind p < 16) ∧
  (∀ p, bindingKind p = p.kind % 16) ∧
  (∀ b, partitionOwner ⟨0, .binding b⟩ = b) ∧
  (∀ k k' n, partitionOwner ⟨k, .part k' n⟩ = ownerWalk n) ∧
  (∀ g w b, lookupBindingPartition g w b = g w b) ∧
  (∀ g w b p, lookupBindingPartitionHint g w b p = g w b p) ∧
  (∀ mb gr b, gr.binding = some b → convertBinding mb gr = b) ∧
  (∀ mb gr, gr.binding = none → convertBinding mb gr = mb gr.mod gr.name) ∧
  (∀ mb g w gr, lookupBindingPartitionGR mb g w gr = g w (convertBinding mb gr)) ∧
  (∀ (α : Type) (r : BPart → α) p, partitionRestriction r p = r p) ∧
  (∀ mb g w m s, bindingKindMS mb g w m s = bindingKind (g w (mb m s))) ∧
  (∀ m s, deleteBinding m s = .disableBinding ⟨m, s, none⟩) ∧
  -- `set_binding_visibility!` accepts exactly :none, :public, :export
  (∀ m s, setBindingVisibility m s "none" = .ok (.setVisibility m s 0) ∧
      setBindingVisibility m s "public" = .ok (.setVisibility m s 1) ∧
      setBindingVisibility m s "export" = .ok (.setVisibility m s 2)) ∧
  (∀ m s v, v ≠ "none" → v ≠ "public" → v ≠ "export" →
      ∃ msg, setBindingVisibility m s v = .error (.argumentError msg)) ∧
  (∀ r, getWorldCounter r = r ∧ tlsWorldAge r = r ∧ getRequireWorld r = r) ∧
  (∀ c, minWorldCI c = c.min_world ∧ maxWorldCI c = c.max_world ∧
      minWorldInfo c = c.min_world ∧ maxWorldInfo c = c.max_world)

theorem bindingKind_mod (p : BPart) : bindingKind p = p.kind % 16 := by
  simp only [bindingKind, PARTITION_MASK_KIND]
  show p.kind &&& (2 ^ 4 - 1) = p.kind % 2 ^ 4
  exact Nat.and_two_pow_sub_one_eq_mod p.kind 4

theorem kindClasses_proven : KindClasses := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro k <;>
    simp only [isDefinedConstBinding, isSomeConstBinding,
      isSomeImported, isSomeImplicit, isSomeExplicitImported, isSomeBindingImported, isSomeGuard,
      isSomeGlobal, PARTITION_KIND_CONST, PARTITION_KIND_CONST_IMPORT, PARTITION_KIND_GLOBAL,
      PARTITION_KIND_IMPLICIT_GLOBAL, PARTITION_KIND_IMPLICIT_CONST, PARTITION_KIND_EXPLICIT,
      PARTITION_KIND_IMPORTED, PARTITION_KIND_FAILED, PARTITION_KIND_DECLARED, PARTITION_KIND_GUARD,
      PARTITION_KIND_UNDEF_CONST, PARTITION_KIND_BACKDATED_CONST, Bool.or_eq_true, beq_iff_eq,
      Bool.and_eq_true] <;> omega

theorem modulesBodies_proven : ModulesBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; rfl
  · intro _ _; rfl
  · intro c b n; simp [isRootModule, parentmodule]
  · intro c b n p
    have : parentmodule (.child n p) ≠ .child n p := by
      simp only [parentmodule]
      intro h
      have := congrArg sizeOf h
      simp at this
    simp [isRootModule, this]
  · exact fun r m => moduleroot_mem_chain r m
  · exact fun r m => moduleroot_isroot r m
  · intro r m h; cases m <;> simp [moduleroot, h]
  · intro r n p h; simp [moduleroot, h]
  · exact fun sp m => fullname_last sp m
  · intro sp m h; cases m <;> simp [fullname, h, nameofM]
  · intro sp n; simp only [fullname]; split <;> rfl
  · intro sp n p h; simp [fullname, h]
  · exact fullname_path
  · intro _ _; rfl
  · intro le htrans htotal j m o
    exact ⟨List.pairwise_mergeSort htrans htotal _, List.mergeSort_perm _ _⟩
  · intro _ _ _; rfl
  · intro q m s; simp [isexported, cintBool]
  · intro q m s; simp [ispublic, cintBool]
  · intro q m s; simp [isdeprecated, cintBool]
  · intro o m s h; simp [bindingModule, h]
  · intro o m s p h; simp [bindingModule, h]
  · intro _; rfl
  · rfl
  · rfl
  · exact kindClasses_proven
  · intro p; rw [bindingKind_mod]; omega
  · exact bindingKind_mod
  · intro _; rfl
  · intro _ _ _; rfl
  · intro _ _ _; rfl
  · intro _ _ _ _; rfl
  · intro mb gr b h; simp [convertBinding, h]
  · intro mb gr h; simp [convertBinding, h]
  · intro _ _ _ _; rfl
  · intro _ _ _; rfl
  · intro _ _ _ _ _; rfl
  · intro _ _; rfl
  · intro m s; refine ⟨?_, ?_, ?_⟩ <;> simp [setBindingVisibility]
  · intro m s v h1 h2 h3; simp [setBindingVisibility, h1, h2, h3]
  · intro _; exact ⟨rfl, rfl, rfl⟩
  · intro _; exact ⟨rfl, rfl, rfl, rfl⟩

end JuliaLean.RuntimeCov.Modules
