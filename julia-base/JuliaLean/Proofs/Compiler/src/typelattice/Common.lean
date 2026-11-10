import JuliaLean.Compiler.src.typelattice

/-!
Shared vocabulary for the properties of `Compiler/src/abstractlattice.jl` and
`Compiler/src/typelattice.jl`.

A model computation runs in `CM` (a fresh-id counter and an error). A Julia exception is the
error `"julia:<Exception>: <message>"`; any other error (an exhausted fuel budget, an unknown type
name, `unmodelled:`) is a failure of the model and never a Julia outcome. The statements below are
therefore partial-correctness statements: they constrain what a call returns when it returns, and
they say nothing about runs that end in a model failure.

Assumptions on subtyping and egality are stated about the model's `issub`/`egal`, in the same
partial-correctness form, and are passed to each theorem as hypotheses. Each is a law Julia's
subtyping is meant to satisfy.
-/

namespace JuliaLean.Proofs.Compiler.Lattice

open JuliaLean.Compiler JuliaLean.C

/-- Whenever `m` returns (from any state), its result satisfies `P`. -/
def Returns {α : Type} (m : CM α) (P : α → Prop) : Prop :=
  ∀ s r s', m.run s = .ok (r, s') → P r

/-- `m` throws the Julia exception `exc` from every state. -/
def ThrowsJulia {α : Type} (exc : String) (m : CM α) : Prop :=
  ∀ s, ∃ msg : String, m.run s = .error s!"julia:{exc}: {msg}"

theorem jlThrow_run {α : Type} (exc msg : String) (s : Nat) :
    (jlThrow exc msg : CM α).run s = .error s!"julia:{exc}: {msg}" := rfl

theorem pure_run {α : Type} (x : α) (s : Nat) : (pure x : CM α).run s = .ok (x, s) := rfl

theorem run_bind_ok {α β : Type} {m : CM α} {k : α → CM β} {s : Nat} {a : α} {s₁ : Nat}
    (h : m.run s = .ok (a, s₁)) : (m >>= k).run s = (k a).run s₁ := by
  rw [StateT.run_bind, h]; rfl

theorem run_bind_error {α β : Type} {m : CM α} {k : α → CM β} {s : Nat} {e : String}
    (h : m.run s = .error e) : (m >>= k).run s = .error e := by
  rw [StateT.run_bind, h]; rfl

theorem run_bind_inv {α β : Type} {m : CM α} {k : α → CM β} {s : Nat} {r : β} {s' : Nat}
    (h : (m >>= k).run s = .ok (r, s')) :
    ∃ a s₁, m.run s = .ok (a, s₁) ∧ (k a).run s₁ = .ok (r, s') := by
  rw [StateT.run_bind] at h
  cases hm : m.run s with
  | error e => rw [hm] at h; cases h
  | ok p => rw [hm] at h; exact ⟨p.1, p.2, rfl, h⟩

/-- `e` is a slot wrapper (`AnyConditional` or `AnyMustAlias`). -/
def _root_.JuliaLean.Compiler.LElt.isSlotWrapper (e : LElt) : Bool := e.isAnyConditional || e.isAnyMustAlias

/-- The causes of a `LimitedAccuracy`, and none for any other element. -/
def limitedCauses : LElt → List ObjId
  | .limitedAccuracy _ cs _ => cs
  | _ => []

theorem idset_step_keep (acc : List ObjId) (x c : ObjId) (h : c ∈ acc) :
    c ∈ (if acc.contains x then acc else acc ++ [x]) := by
  split <;> simp_all

theorem idset_step_add (acc : List ObjId) (x : ObjId) :
    x ∈ (if acc.contains x then acc else acc ++ [x]) := by
  split
  · rename_i h; exact List.mem_of_elem_eq_true h
  · simp

theorem idset_foldl_keep (t : List ObjId) : ∀ (acc : List ObjId) (c : ObjId), c ∈ acc →
    c ∈ t.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc := by
  induction t with
  | nil => intro acc c h; exact h
  | cons x t ih => intro acc c h; exact ih _ c (idset_step_keep acc x c h)

theorem idset_foldl_add (t : List ObjId) : ∀ (acc : List ObjId) (c : ObjId), c ∈ t →
    c ∈ t.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc := by
  induction t with
  | nil => intro acc c h; cases h
  | cons x t ih =>
    intro acc c h
    rcases List.mem_cons.mp h with rfl | h
    · exact idset_foldl_keep t _ _ (idset_step_add acc _)
    · exact ih _ c h

/-- `union!(s, t)` keeps the elements of `s` and adds those of `t`. -/
theorem idsetUnion_left (s t : List ObjId) : ∀ c ∈ s, c ∈ idsetUnion s t :=
  fun c h => idset_foldl_keep t s c h

theorem idsetUnion_right (s t : List ObjId) : ∀ c ∈ t, c ∈ idsetUnion s t :=
  fun c h => idset_foldl_add t s c h

theorem idset_step_mem (acc : List ObjId) (x c : ObjId) :
    c ∈ (if acc.contains x then acc else acc ++ [x]) ↔ c ∈ acc ∨ c = x := by
  split
  · rename_i h
    have hx : x ∈ acc := List.mem_of_elem_eq_true h
    constructor
    · exact Or.inl
    · intro h'
      rcases h' with h' | h'
      · exact h'
      · rw [h']; exact hx
  · simp

theorem idset_foldl_mem (t : List ObjId) : ∀ (acc : List ObjId) (c : ObjId),
    c ∈ t.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc ↔
      c ∈ acc ∨ c ∈ t := by
  induction t with
  | nil => intro acc c; simp
  | cons x t ih =>
    intro acc c
    rw [List.foldl_cons, ih, idset_step_mem]
    simp only [List.mem_cons, or_assoc]

/-- `union!(s, t)` holds exactly the elements of `s` and of `t`. -/
theorem idsetUnion_mem (s t : List ObjId) (c : ObjId) :
    c ∈ idsetUnion s t ↔ c ∈ s ∨ c ∈ t :=
  idset_foldl_mem t s c

/-- `m` returns `r` from every state. -/
def AlwaysReturns {α : Type} (m : CM α) (r : α) : Prop :=
  ∀ s, ∃ s', m.run s = .ok (r, s')

theorem ignorelimited_la (t : LElt) (cs : List ObjId) (cid : ObjId) :
    ignorelimited (.limitedAccuracy t cs cid) = t := rfl

theorem ignorelimited_of_not_limited {x : LElt} (h : x.isLimited = false) : ignorelimited x = x := by
  cases x <;> first | rfl | (simp [LElt.isLimited] at h)

/-- Which kind of layer a lattice is (its constructor). -/
def layerKind : Lattice → Nat
  | .jlType => 0
  | .consts => 1
  | .partials _ => 2
  | .conditionals _ => 3
  | .interConditionals _ => 4
  | .mustAliases _ => 5
  | .interMustAliases _ => 6
  | .inference _ => 7

/-- Number of `widenlattice` steps from a layer down to `JLTypeLattice`. -/
def layerDepth : Lattice → Nat
  | .jlType => 0
  | .consts => 1
  | .partials p | .conditionals p | .interConditionals p | .mustAliases p
  | .interMustAliases p | .inference p => layerDepth p + 1

/-! ## Assumptions on subtyping (Julia promises these; see the docstring of each) -/

/-- `t <: t` for every type `t` (reflexivity of `jl_subtype`). -/
def SubReflexive : Prop :=
  ∀ n E t s r s', t.isType = true → (issub n E t t).run s = .ok (r, s') → r = true

/-- `a <: b` and `b <: c` imply `a <: c` (transitivity of `jl_subtype`). -/
def SubTransitive : Prop :=
  ∀ n₁ n₂ n₃ E a b c s₁ s₁' s₂ s₂' s₃ r s₃',
    (issub n₁ E a b).run s₁ = .ok (true, s₁') → (issub n₂ E b c).run s₂ = .ok (true, s₂') →
    (issub n₃ E a c).run s₃ = .ok (r, s₃') → r = true

/-- `x === x` for every object (reflexivity of `jl_egal`). -/
def EgalReflexive : Prop :=
  ∀ n E x s r s', (JuliaLean.Compiler.egal n E x x).run s = .ok (r, s') → r = true

end JuliaLean.Proofs.Compiler.Lattice
