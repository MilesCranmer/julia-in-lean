import JuliaLean.base.array
import JuliaLean.Proofs.base.abstractarray.common.shape_arithmetic

namespace JuliaLean.AbstractArraySpecs

/-- A typed zero-dimensional concatenation has the requested storage element type
and exactly its converted element. The converted value may have a proper subtype of
T, as for `convert(Any, x)`. Conversion errors are propagated. -/
def Hvn0ValueSpec : Prop :=
  ∀ {α β : Type} (accepts : Nat → Nat → Prop) (conv : Nat → TypedValue α → R (TypedValue β))
    (T : Nat) (x : TypedValue α),
    (∀ y, conv T x = .ok y → accepts T y.typeCode →
      ∃ out, hvn0Value fillScalar conv T x = .ok out ∧ out.elementType = T ∧
        out.storage.shape = [] ∧ out.storage.cells = [some y.payload]) ∧
    (∀ e, conv T x = .error e → hvn0Value fillScalar conv T x = .error e)

/-- The same typed zero-dimensional storage contract for the `x::Number` overload. -/
def Hvn0NumberSpec : Prop :=
  ∀ {α β : Type} (accepts : Nat → Nat → Prop) (conv : Nat → TypedValue α → R (TypedValue β))
    (T : Nat) (x : TypedValue α),
    (∀ y, conv T x = .ok y → accepts T y.typeCode →
      ∃ out, hvn0Number fillScalar conv T x = .ok out ∧ out.elementType = T ∧
        out.storage.shape = [] ∧ out.storage.cells = [some y.payload]) ∧
    (∀ e, conv T x = .error e → hvn0Number fillScalar conv T x = .error e)

/-- Nominal codes 0 and 1 represent a concrete scalar type (String or Int) and Any.
Any accepts every concrete type, and a concrete type accepts itself. -/
def scalarAccepts (target actual : Nat) : Prop := target = 1 ∨ target = actual

/-- `convert(Any, x)` returns x. Other targets in this counterexample's domain throw. -/
def convertAny {α : Type} (target : Nat) (x : TypedValue α) : R (TypedValue α) :=
  if target = 1 then .ok x else .error .inexactError

theorem hvn0ValueSpec_refuted : ¬ Hvn0ValueSpec := by
  intro h
  let x : TypedValue Nat := ⟨0, 7⟩
  obtain ⟨out, ho, ht, _, _⟩ := (h scalarAccepts convertAny 1 x).1 x (by rfl) (Or.inl rfl)
  have he : hvn0Value fillScalar convertAny 1 x = .ok ⟨0, ⟨[], [some 7]⟩⟩ := rfl
  rw [he] at ho
  cases ho
  contradiction

theorem hvn0NumberSpec_refuted : ¬ Hvn0NumberSpec := by
  intro h
  let x : TypedValue Nat := ⟨0, 7⟩
  obtain ⟨out, ho, ht, _, _⟩ := (h scalarAccepts convertAny 1 x).1 x (by rfl) (Or.inl rfl)
  have he : hvn0Number fillScalar convertAny 1 x = .ok ⟨0, ⟨[], [some 7]⟩⟩ := rfl
  rw [he] at ho
  cases ho
  contradiction

def HvnEmptySpec : Prop :=
  ∀ {α : Type} (T : Nat) (N : Int),
    (N < 0 → hvnEmpty (α := α) T N = .error .argumentError) ∧
    (0 < N → ∃ out, hvnEmpty (α := α) T N = .ok out ∧ out.elementType = T ∧
      out.storage.shape.length = N.toNat ∧
      (∀ n ∈ out.storage.shape, n.val = 0) ∧ out.storage.cells = [])

def HvnNumbersDimSpec : Prop :=
  ∀ {α β : Type} (conv : Nat → TypedValue α → R (TypedValue β)) (g : TypedValue α → TypedValue β)
    (T : Nat) (N : Int) (xs : List (TypedValue α)),
    (N < 0 → hvnNumbersDim conv T N xs = .error .argumentError) ∧
    (0 < N → xs ≠ [] → (xs.length : Int) < tmax →
      (∀ x ∈ xs, conv T x = .ok (g x)) →
      ∃ out, hvnNumbersDim conv T N xs = .ok out ∧ out.elementType = T ∧
        out.storage.shape.map (·.val) = List.replicate (N.toNat - 1) 1 ++ [(xs.length : Int)] ∧
        out.storage.cells = xs.map (fun x => some (g x).payload))

theorem hvnEmptySpec_proven : HvnEmptySpec := by
  intro α T N
  constructor
  · intro h; simp only [hvnEmpty, h, ite_true]; rfl
  · intro h
    have hn : N.toNat ≠ 0 := by omega
    have he : arrayUndef (β := α) (List.replicate N.toNat (i64 0)) =
        .ok ⟨List.replicate N.toNat (i64 0), []⟩ := by
      simp [arrayUndef, dimsInvalid, ← List.prod_eq_foldl, zero_val, hn, tmax]
    refine ⟨⟨T, ⟨List.replicate N.toNat (i64 0), []⟩⟩, ?_, rfl, ?_, ?_, rfl⟩
    · simp only [hvnEmpty, show ¬ N < 0 by omega, ite_false, he]; rfl
    · simp
    · intro n hmem
      have := List.mem_replicate.mp hmem
      rw [this.2, zero_val]

theorem mapM_converts {α β : Type} (conv : Nat → TypedValue α → R (TypedValue β))
    (g : TypedValue α → TypedValue β) (T : Nat) (xs : List (TypedValue α))
    (h : ∀ x ∈ xs, conv T x = .ok (g x)) :
    xs.mapM (conv T) = .ok (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, h x (by simp), List.map_cons,
      ih (fun y hy => h y (by simp [hy]))]
    rfl

theorem hvnNumbersDimSpec_proven : HvnNumbersDimSpec := by
  intro α β conv g T N xs
  constructor
  · intro h; simp only [hvnNumbersDim, h, ite_true]; rfl
  · intro hN _ hlen hc
    have hneg : ¬ N < 0 := by omega
    have hlit : (i64 (xs.length : Int)).val = xs.length := by
      rw [vlit, wrap_id _ (by omega) (by rw [tmax_eq] at hlen; omega)]
    refine ⟨⟨T, ⟨List.replicate (N - 1).toNat (i64 1) ++ [i64 xs.length],
      (xs.map g).map (fun y => some y.payload)⟩⟩, ?_, rfl, ?_, ?_⟩
    · simp only [hvnNumbersDim, hneg, ite_false, mapM_converts conv g T xs hc]
      rfl
    · simp only [List.map_append, List.map_replicate, one_val, List.map_cons, List.map_nil, hlit]
      rw [show (N - 1).toNat = N.toNat - 1 by omega]
    · simp [List.map_map]

end JuliaLean.AbstractArraySpecs
