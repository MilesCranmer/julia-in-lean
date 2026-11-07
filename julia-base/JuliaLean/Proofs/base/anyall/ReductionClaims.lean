import JuliaLean.base.anyall

namespace JuliaLean.Reduce

/-- `any(f, itr)` and `all(f, itr)` follow three-valued logic when `f` returns `Bool` or
`missing`, and short-circuit: once a prefix decides the result, the rest of the
collection is never inspected (`base/anyall.jl:3-10, 32-39`). -/
def AnyAllThreeValued : Prop :=
  ∀ (f : Val → Val) (v : List Val),
    ((∀ x ∈ v, f x = .missing ∨ f x = .bool true ∨ f x = .bool false) →
      Vec.any f v = .ok (if v.any (fun x => f x = .bool true) then .bool true
        else if v.any (fun x => f x = .missing) then .missing else .bool false) ∧
      Vec.all f v = .ok (if v.any (fun x => f x = .bool false) then .bool false
        else if v.any (fun x => f x = .missing) then .missing else .bool true)) ∧
    (∀ w, Vec.any f v = .ok (.bool true) → Vec.any f (v ++ w) = .ok (.bool true)) ∧
    (∀ w, Vec.all f v = .ok (.bool false) → Vec.all f (v ++ w) = .ok (.bool false))

/-! ### `any` and `all` -/

section
variable {f : Val → Val} {x : Val}

theorem any_cons_missing (l : List Val) (hx : f x = .missing) :
    Vec.any f (x :: l) = (Vec.any f l).map fun r => if r = .bool false then .missing else r := by
  simp only [Vec.any, hx]

theorem any_cons_true (l : List Val) (hx : f x = .bool true) :
    Vec.any f (x :: l) = .ok (.bool true) := by
  simp only [Vec.any, hx]

theorem any_cons_false (l : List Val) (hx : f x = .bool false) :
    Vec.any f (x :: l) = Vec.any f l := by
  simp only [Vec.any, hx]

theorem all_cons_missing (l : List Val) (hx : f x = .missing) :
    Vec.all f (x :: l) = (Vec.all f l).map fun r => if r = .bool true then .missing else r := by
  simp only [Vec.all, hx]

theorem all_cons_false (l : List Val) (hx : f x = .bool false) :
    Vec.all f (x :: l) = .ok (.bool false) := by
  simp only [Vec.all, hx]

theorem all_cons_true (l : List Val) (hx : f x = .bool true) :
    Vec.all f (x :: l) = Vec.all f l := by
  simp only [Vec.all, hx]

end

theorem any_three (f : Val → Val) (v : List Val)
    (h : ∀ x ∈ v, f x = .missing ∨ f x = .bool true ∨ f x = .bool false) :
    Vec.any f v = .ok (if v.any (fun x => f x = .bool true) then .bool true
      else if v.any (fun x => f x = .missing) then .missing else .bool false) := by
  induction v with
  | nil => rfl
  | cons x rest ih =>
    have ih := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [List.any_cons, List.any_cons]
    generalize rest.any (fun x => decide (f x = .bool true)) = A at ih ⊢
    generalize rest.any (fun x => decide (f x = .missing)) = B at ih ⊢
    rcases h x List.mem_cons_self with hx | hx | hx
    · rw [any_cons_missing _ hx, ih]
      cases A <;> cases B <;> simp [hx, Except.map]
    · rw [any_cons_true _ hx]
      simp [hx]
    · rw [any_cons_false _ hx, ih]
      cases A <;> cases B <;> simp [hx]

theorem all_three (f : Val → Val) (v : List Val)
    (h : ∀ x ∈ v, f x = .missing ∨ f x = .bool true ∨ f x = .bool false) :
    Vec.all f v = .ok (if v.any (fun x => f x = .bool false) then .bool false
      else if v.any (fun x => f x = .missing) then .missing else .bool true) := by
  induction v with
  | nil => rfl
  | cons x rest ih =>
    have ih := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [List.any_cons, List.any_cons]
    generalize rest.any (fun x => decide (f x = .bool false)) = A at ih ⊢
    generalize rest.any (fun x => decide (f x = .missing)) = B at ih ⊢
    rcases h x List.mem_cons_self with hx | hx | hx
    · rw [all_cons_missing _ hx, ih]
      cases A <;> cases B <;> simp [hx, Except.map]
    · rw [all_cons_true _ hx, ih]
      cases A <;> cases B <;> simp [hx]
    · rw [all_cons_false _ hx]
      simp [hx]

theorem any_append (f : Val → Val) (v w : List Val) (h : Vec.any f v = .ok (.bool true)) :
    Vec.any f (v ++ w) = .ok (.bool true) := by
  induction v with
  | nil => simp [Vec.any] at h
  | cons x rest ih =>
    rw [List.cons_append]
    cases hx : f x with
    | missing =>
      rw [any_cons_missing _ hx] at h ⊢
      cases hr : Vec.any f rest with
      | error e => rw [hr] at h; simp [Except.map] at h
      | ok r =>
        rw [hr] at h
        have hr' : r = .bool true := by
          by_cases h2 : r = .bool false <;> simp [Except.map, h2] at h <;> exact h
        rw [ih (by rw [hr, hr'])]
        simp [Except.map]
    | bool b =>
      cases b
      · rw [any_cons_false _ hx] at h ⊢; exact ih h
      · exact any_cons_true _ hx
    | int t y => simp [Vec.any, hx] at h
    | f64 y => simp [Vec.any, hx] at h

theorem all_append (f : Val → Val) (v w : List Val) (h : Vec.all f v = .ok (.bool false)) :
    Vec.all f (v ++ w) = .ok (.bool false) := by
  induction v with
  | nil => simp [Vec.all] at h
  | cons x rest ih =>
    rw [List.cons_append]
    cases hx : f x with
    | missing =>
      rw [all_cons_missing _ hx] at h ⊢
      cases hr : Vec.all f rest with
      | error e => rw [hr] at h; simp [Except.map] at h
      | ok r =>
        rw [hr] at h
        have hr' : r = .bool false := by
          by_cases h2 : r = .bool true <;> simp [Except.map, h2] at h <;> exact h
        rw [ih (by rw [hr, hr'])]
        simp [Except.map]
    | bool b =>
      cases b
      · exact all_cons_false _ hx
      · rw [all_cons_true _ hx] at h ⊢; exact ih h
    | int t y => simp [Vec.all, hx] at h
    | f64 y => simp [Vec.all, hx] at h

theorem anyAllThreeValued_proven : AnyAllThreeValued :=
  fun f v => ⟨fun h => ⟨any_three f v h, all_three f v h⟩, any_append f v, all_append f v⟩

end JuliaLean.Reduce
