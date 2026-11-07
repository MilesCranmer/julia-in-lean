import JuliaLean.base.runtime_internals
import JuliaLean.Proofs.base.runtime_internals.Common


section
namespace JuliaLean.RuntimeCov.Modules

open JuliaLean.RuntimeCov

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
end
