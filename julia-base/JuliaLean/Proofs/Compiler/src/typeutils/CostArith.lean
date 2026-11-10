import JuliaLean.Compiler.src.typeutils.lattice

/-!
The arithmetic of the `unionsplitcost` loop (`Compiler/src/typeutils.jl:285-316`), as pure
functions of the union lengths. `costLoop` is the loop itself, with its overflow check; `costF`
is a closed form: `costF l * costM l = 2 * costP l`, that is, twice the product of the lengths
divided by the largest one (or by 2 when no length is larger).
-/

namespace JuliaLean.Proofs.Compiler.src.typeutils

open JuliaLean.Compiler

/-- One step of the loop for a union of `nti` members: `(nu, max)` before and after. -/
def costStep (p : Int × Nat) (nti : Nat) : Int × Nat :=
  if nti > p.2 then (p.1 * p.2, nti) else (p.1 * nti, p.2)

/-- The loop with its overflow check, over the union lengths of the arguments it reads (`none`
for an argument that is not a `Union`). -/
def costLoop : Int × Nat → List (Option Nat) → Int
  | p, [] => p.1
  | p, none :: xs => costLoop p xs
  | p, some x :: xs =>
    let q := costStep p x
    if q.1 > typemaxInt then typemaxInt else costLoop q xs

/-- The loop without the overflow check. -/
def costU (p : Int × Nat) (l : List Nat) : Int × Nat := l.foldl costStep p

/-- `max(2, l...)` and the product of `l`. -/
def costM (l : List Nat) : Nat := l.foldl max 2
def costP (l : List Nat) : Nat := l.foldl (· * ·) 1

/-- The closed form of the uncapped cost. -/
def costF : List Nat → Nat
  | [] => 1
  | x :: r => min x (costM r) * costF r

/-- The cost the loop returns: `costF` capped at `typemax(Int)`. -/
def costCapped (l : List Nat) : Int := if (costF l : Int) > typemaxInt then typemaxInt else costF l

theorem foldl_max_acc (l : List Nat) : ∀ a x, l.foldl max (max a x) = max x (l.foldl max a) := by
  induction l with
  | nil => intro a x; exact Nat.max_comm a x
  | cons y l ih =>
    intro a x
    simp only [List.foldl_cons]
    rw [show max (max a x) y = max (max a y) x by omega, ih]

theorem foldl_mul_acc (l : List Nat) : ∀ a x, l.foldl (· * ·) (a * x) = x * l.foldl (· * ·) a := by
  induction l with
  | nil => intro a x; exact Nat.mul_comm a x
  | cons y l ih =>
    intro a x
    simp only [List.foldl_cons]
    rw [show a * x * y = a * y * x by rw [Nat.mul_assoc, Nat.mul_comm x y, ← Nat.mul_assoc], ih]

theorem costM_cons (x : Nat) (r : List Nat) : costM (x :: r) = max x (costM r) := by
  simp only [costM, List.foldl_cons]; exact foldl_max_acc r 2 x

theorem costP_cons (x : Nat) (r : List Nat) : costP (x :: r) = x * costP r := by
  simp only [costP, List.foldl_cons, Nat.one_mul]
  have := foldl_mul_acc r 1 x
  rwa [Nat.one_mul] at this

theorem costM_ge_two (l : List Nat) : 2 ≤ costM l := by
  induction l with
  | nil => exact Nat.le_refl 2
  | cons x r ih => rw [costM_cons]; omega

theorem min_mul_max (a b : Nat) : min a b * max a b = a * b := by
  by_cases h : a ≤ b
  · rw [Nat.min_eq_left h, Nat.max_eq_right h]
  · rw [Nat.min_eq_right (by omega), Nat.max_eq_left (by omega), Nat.mul_comm]

/-- `costF l * max(2, l...) = 2 * prod(l)`. -/
theorem costF_mul_costM (l : List Nat) : costF l * costM l = 2 * costP l := by
  induction l with
  | nil => rfl
  | cons x r ih =>
    rw [costF, costM_cons, costP_cons]
    have h := min_mul_max x (costM r)
    grind

/-- The uncapped loop keeps `nu * max = nu₀ * max₀ * prod` and `max = max(max₀, l...)`. -/
theorem costU_inv (l : List Nat) : ∀ (p : Int × Nat),
    (costU p l).1 * ((costU p l).2 : Int) = p.1 * (p.2 : Int) * (costP l : Int) ∧
      (costU p l).2 = l.foldl max p.2 := by
  induction l with
  | nil => intro p; simp [costU, costP]
  | cons x r ih =>
    intro p
    obtain ⟨h1, h2⟩ := ih (costStep p x)
    simp only [costU, List.foldl_cons] at h1 h2 ⊢
    refine ⟨?_, ?_⟩
    · rw [h1, costP_cons]
      unfold costStep
      split <;> (simp only [Int.natCast_mul]; grind)
    · rw [h2]; unfold costStep; split <;> simp only <;> congr 1 <;> omega

/-- From `nu = 1, max = 2` the uncapped loop computes `costF`. -/
theorem costU_one_two (l : List Nat) : (costU (1, 2) l).1 = (costF l : Int) := by
  obtain ⟨h1, h2⟩ := costU_inv l (1, 2)
  have hF := costF_mul_costM l
  have hM : (costU (1, 2) l).2 = costM l := h2
  rw [hM] at h1
  have hpos : (0 : Int) < (costM l : Int) := by have := costM_ge_two l; omega
  have : (costU (1, 2) l).1 * (costM l : Int) = (costF l : Int) * (costM l : Int) := by
    rw [h1]
    have : ((costF l * costM l : Nat) : Int) = ((2 * costP l : Nat) : Int) := by rw [hF]
    simp only [Int.natCast_mul] at this
    simp only [this]; grind
  exact Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hpos) this

/-- With lengths at least 1, the uncapped `nu` never decreases. -/
theorem costU_ge (l : List Nat) (hl : ∀ x ∈ l, 1 ≤ x) : ∀ p : Int × Nat,
    0 ≤ p.1 → 1 ≤ p.2 → p.1 ≤ (costU p l).1 := by
  induction l with
  | nil => intro p _ _; exact Int.le_refl _
  | cons x r ih =>
    intro p h0 h1
    have hx : 1 ≤ x := hl x (List.mem_cons_self ..)
    have hstep : p.1 ≤ (costStep p x).1 ∧ 0 ≤ (costStep p x).1 ∧ 1 ≤ (costStep p x).2 := by
      unfold costStep
      split
      · refine ⟨?_, ?_, ?_⟩
        · have : (1 : Int) ≤ (p.2 : Int) := by omega
          have := Int.mul_le_mul_of_nonneg_left this h0
          simpa using this
        · exact Int.mul_nonneg h0 (by omega)
        · simp only; omega
      · refine ⟨?_, ?_, ?_⟩
        · have : (1 : Int) ≤ (x : Int) := by omega
          have := Int.mul_le_mul_of_nonneg_left this h0
          simpa using this
        · exact Int.mul_nonneg h0 (by omega)
        · exact h1
    have := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) (costStep p x) hstep.2.1 hstep.2.2
    simp only [costU, List.foldl_cons] at this ⊢
    exact Int.le_trans hstep.1 this

/-- The union length an argument contributes: 1 for a non-union. -/
def lenOrOne (o : Option Nat) : Nat := o.getD 1

/-- The loop with the overflow check returns the uncapped result capped at `typemax(Int)`. -/
theorem costLoop_eq (lens : List (Option Nat)) (hl : ∀ x, some x ∈ lens → 1 ≤ x) :
    ∀ p : Int × Nat, 0 ≤ p.1 → 1 ≤ p.2 → p.1 ≤ typemaxInt →
      costLoop p lens = (let u := (costU p (lens.map lenOrOne)).1
        if u > typemaxInt then typemaxInt else u) := by
  induction lens with
  | nil => intro p _ _ h; simp only [costLoop, costU, List.map_nil, List.foldl_nil]; rw [if_neg (by omega)]
  | cons o xs ih =>
    intro p h0 h1 hT
    have ih' := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    cases o with
    | none =>
      have hs : costStep p 1 = p := by
        unfold costStep; rw [if_neg (by omega)]; simp
      simp only [costLoop, List.map_cons, lenOrOne, Option.getD_none]
      rw [ih' p h0 h1 hT]
      simp only [costU, List.foldl_cons, hs]
      rfl
    | some x =>
      have hx : 1 ≤ x := hl x (List.mem_cons_self ..)
      have hall : ∀ y ∈ xs.map lenOrOne, 1 ≤ y := by
        intro y hy
        obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hy
        cases o with
        | none => exact Nat.le_refl 1
        | some z => exact hl z (List.mem_cons_of_mem _ ho)
      have hq0 : 0 ≤ (costStep p x).1 := by
        unfold costStep; split <;> exact Int.mul_nonneg h0 (by omega)
      have hq1 : 1 ≤ (costStep p x).2 := by
        unfold costStep; split
        · simp only; omega
        · exact h1
      simp only [costLoop, List.map_cons, lenOrOne, Option.getD_some]
      rw [show costU p (x :: List.map lenOrOne xs) = costU (costStep p x) (List.map lenOrOne xs)
        from rfl]
      by_cases hq : (costStep p x).1 > typemaxInt
      · rw [if_pos hq]
        have := costU_ge _ hall (costStep p x) hq0 hq1
        rw [if_pos (Int.lt_of_lt_of_le hq this)]
      · rw [if_neg hq, ih' (costStep p x) hq0 hq1 (by omega)]

/-- The capped loop from `nu = 1, max = 2` is `costCapped` of the lengths. -/
theorem costLoop_one_two (lens : List (Option Nat)) (hl : ∀ x, some x ∈ lens → 1 ≤ x) :
    costLoop (1, 2) lens = costCapped (lens.map lenOrOne) := by
  rw [costLoop_eq lens hl (1, 2) (by decide) (by decide) (by decide), costU_one_two]
  rfl

/-! ## Order independence and monotonicity of the closed form -/

theorem foldl_max_perm {l l' : List Nat} (h : l.Perm l') : ∀ a, l.foldl max a = l'.foldl max a := by
  induction h with
  | nil => intro a; rfl
  | cons x _ ih => intro a; simp only [List.foldl_cons]; exact ih _
  | swap x y l => intro a; simp only [List.foldl_cons]; congr 1; omega
  | trans _ _ ih1 ih2 => intro a; rw [ih1, ih2]

theorem foldl_mul_perm {l l' : List Nat} (h : l.Perm l') :
    ∀ a, l.foldl (· * ·) a = l'.foldl (· * ·) a := by
  induction h with
  | nil => intro a; rfl
  | cons x _ ih => intro a; simp only [List.foldl_cons]; exact ih _
  | swap x y l => intro a; simp only [List.foldl_cons]; congr 1; grind
  | trans _ _ ih1 ih2 => intro a; rw [ih1, ih2]

/-- `costF` does not depend on the order of the lengths. -/
theorem costF_perm {l l' : List Nat} (h : l.Perm l') : costF l = costF l' := by
  have h1 := costF_mul_costM l
  have h2 := costF_mul_costM l'
  have hM : costM l = costM l' := foldl_max_perm h 2
  have hP : costP l = costP l' := foldl_mul_perm h 1
  rw [hP, ← h2, ← hM] at h1
  exact Nat.eq_of_mul_eq_mul_right (by have := costM_ge_two l; omega) h1

/-- `l'` is `l` with each length lowered or kept (pointwise `≤`). -/
inductive PwLe : List Nat → List Nat → Prop
  | nil : PwLe [] []
  | cons {x' x : Nat} {r' r : List Nat} : x' ≤ x → PwLe r' r → PwLe (x' :: r') (x :: r)

theorem foldl_max_mono {l l' : List Nat} (h : PwLe l' l) :
    ∀ a a', a' ≤ a → l'.foldl max a' ≤ l.foldl max a := by
  induction h with
  | nil => intro a a' h; exact h
  | cons hxy _ ih => intro a a' h; simp only [List.foldl_cons]; exact ih _ _ (by omega)

/-- `costF` does not grow when each length shrinks. -/
theorem costF_mono {l l' : List Nat} (h : PwLe l' l) : costF l' ≤ costF l := by
  induction h with
  | nil => exact Nat.le_refl 1
  | @cons x' x r' r hx hr ih =>
    simp only [costF]
    have hM : costM r' ≤ costM r := foldl_max_mono hr 2 2 (Nat.le_refl 2)
    exact Nat.mul_le_mul (by omega) ih

theorem costCapped_perm {l l' : List Nat} (h : l.Perm l') : costCapped l = costCapped l' := by
  simp only [costCapped, costF_perm h]

theorem costCapped_mono {l l' : List Nat} (h : PwLe l' l) :
    costCapped l' ≤ costCapped l := by
  have := costF_mono h
  simp only [costCapped]
  split <;> split <;> omega

end JuliaLean.Proofs.Compiler.src.typeutils
