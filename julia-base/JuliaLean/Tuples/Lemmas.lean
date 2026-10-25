import JuliaLean.Tuples.Props

/-! Lemmas about the tuple model used by the proofs. -/

namespace JuliaLean.Tuples

variable {α β γ : Type}

@[simp] theorem liftJ_ok' (a : α) : liftJ (.ok a : Jl α) = .ok a := rfl
@[simp] theorem liftJ_error' (e : JlError) : liftJ (.error e : Jl α) = (.error (.jl e) : R α) := rfl
@[simp] theorem R.bind_ok (a : α) (f : α → R β) : (Except.ok a >>= f : R β) = f a := rfl
@[simp] theorem R.bind_error (e : Err) (f : α → R β) : (Except.error e >>= f : R β) = .error e := rfl
@[simp] theorem R.pure_eq (a : α) : (pure a : R α) = .ok a := rfl

theorem sameOutcome_refl [DecidableEq α] (r : R α) : SameOutcome r r := by
  cases r <;> simp [SameOutcome]

theorem sameOutcome_of_eq {r s : R α} (h : r = s) : SameOutcome r s := by
  subst h; cases r <;> simp [SameOutcome]

/-- A value or a `BoundsError`. -/
def OkOrBounds (r : R β) : Prop := (∃ b, r = .ok b) ∨ r = bounds

theorem getElem?_of_lt {l : List α} {i : Nat} (h : i < l.length) : l[i]? = some l[i] :=
  List.getElem?_eq_getElem h

theorem getElem?_of_ge {l : List α} {i : Nat} (h : l.length ≤ i) : l[i]? = none :=
  List.getElem?_eq_none h

theorem drop_cons_of_lt {l : List α} {i : Nat} (h : i < l.length) : l.drop i = l[i] :: l.drop (i + 1) :=
  List.drop_eq_getElem_cons h

theorem drop_nil_of_le {l : List α} {i : Nat} (h : l.length ≤ i) : l.drop i = [] :=
  List.drop_of_length_le h

theorem getfield_ok (t : List α) (k : Nat) (hk : k < t.length) :
    getfield t ((k : Int) + 1) = .ok t[k] := by
  unfold getfield
  have h1 : (1 : Int) ≤ (k : Int) + 1 := by omega
  have h2 : ((k : Int) + 1 - 1).toNat = k := by omega
  rw [if_pos h1, h2, getElem?_of_lt hk]

theorem getfield_bounds (t : List α) (i : Int) (h : ¬ (1 ≤ i ∧ i ≤ t.length)) :
    getfield t i = bounds := by
  unfold getfield
  by_cases h1 : 1 ≤ i
  · have h2 : t.length ≤ (i - 1).toNat := by omega
    rw [if_pos h1, getElem?_of_ge h2]
  · rw [if_neg h1]

theorem getfield_okOrBounds (t : List α) (i : Int) : OkOrBounds (getfield t i) := by
  unfold getfield OkOrBounds
  split
  · split
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr rfl
  · exact Or.inr rfl

theorem mapM_map' (g : Nat → γ) (f : γ → R β) (l : List Nat) :
    (l.map g).mapM f = l.mapM (f ∘ g) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.mapM_cons, ih]

theorem mapM_range_ok (n : Nat) (f : Nat → R β) (L : List β) (hl : L.length = n)
    (h : ∀ k (hk : k < L.length), f k = .ok L[k]) : (List.range n).mapM f = .ok L := by
  induction n generalizing f L with
  | zero =>
    cases L with
    | nil => rfl
    | cons _ _ => simp at hl
  | succ n ih =>
    cases L with
    | nil => simp at hl
    | cons b L =>
      rw [List.range_succ_eq_map, List.mapM_cons, mapM_map']
      have h0 : f 0 = .ok b := h 0 (by simp)
      have hr := ih (f ∘ Nat.succ) L (by simpa using hl)
        (fun k hk => h (k + 1) (by simp; omega))
      simp [h0, hr]

theorem mapM_okOrBounds (l : List γ) (f : γ → R β) (h : ∀ x ∈ l, OkOrBounds (f x)) :
    OkOrBounds (l.mapM f) := by
  induction l with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons a l ih =>
    rcases h a (by simp) with ⟨b, hb⟩ | hb
    · rcases ih (fun x hx => h x (by simp [hx])) with ⟨bs, hbs⟩ | hbs
      · exact Or.inl ⟨b :: bs, by simp [List.mapM_cons, hb, hbs]⟩
      · exact Or.inr (by simp [List.mapM_cons, hb, hbs, bounds])
    · exact Or.inr (by simp [List.mapM_cons, hb, bounds])

theorem mapM_bounds_of (l : List γ) (f : γ → R β) (h : ∀ x ∈ l, OkOrBounds (f x))
    (x : γ) (hx : x ∈ l) (hfx : f x = bounds) : l.mapM f = bounds := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp [List.mapM_cons, hfx, bounds]
    · rcases h a (by simp) with ⟨b, hb⟩ | hb
      · rw [List.mapM_cons, hb, R.bind_ok, ih (fun y hy => h y (by simp [hy])) hx']
        rfl
      · simp [List.mapM_cons, hb, bounds]

/-- Reading the consecutive positions `a, a+1, ..., a+len-1` gives the slice or
a `BoundsError`. -/
theorem mapM_slice (t : List α) (a : Int) (len : Nat) (f : Nat → Int) (hf : ∀ k, f k = a + k) :
    (List.range len).mapM (fun k => getfield t (f k)) =
      if len = 0 then .ok []
      else if 1 ≤ a ∧ a + len - 1 ≤ t.length then .ok ((t.drop (a - 1).toNat).take len)
      else bounds := by
  split
  · rename_i h; subst h; rfl
  · rename_i h0
    split
    · rename_i hin
      apply mapM_range_ok
      · simp; omega
      · intro k hk
        simp at hk
        rw [hf]
        have hk' : (a - 1).toNat + k < t.length := by omega
        have e : a + (k : Int) = (((a - 1).toNat + k : Nat) : Int) + 1 := by omega
        rw [e, getfield_ok t _ hk']
        simp
    · rename_i hout
      have hall : ∀ x ∈ List.range len, OkOrBounds (getfield t (f x)) :=
        fun x _ => getfield_okOrBounds t (f x)
      by_cases ha : 1 ≤ a
      · have hm : len - 1 ∈ List.range len := by simp; omega
        apply mapM_bounds_of _ _ hall (len - 1) hm
        apply getfield_bounds
        rw [hf]; omega
      · have hm : 0 ∈ List.range len := by simp; omega
        apply mapM_bounds_of _ _ hall 0 hm
        apply getfield_bounds
        rw [hf]; omega

theorem frontRec_ok (t : List α) (h : t ≠ []) : frontRec t = .ok t.dropLast := by
  induction t with
  | nil => exact absurd rfl h
  | cons v r ih =>
    cases r with
    | nil => rfl
    | cons w r' =>
      show (do let r ← frontRec (w :: r'); pure (v :: r)) = Except.ok (v :: w :: r').dropLast
      rw [ih (List.cons_ne_nil w r')]
      simp

theorem readRange_ok (t : List α) (i k : Nat) (h : i + k ≤ t.length) :
    readRange t i k = .ok ((t.drop i).take k) := by
  induction k generalizing i with
  | zero => simp [readRange]
  | succ k ih =>
    have hi : i < t.length := by omega
    have e : getfield t ((i : Int) + 1) = .ok t[i] := getfield_ok t i hi
    simp only [readRange, e, R.bind_ok, ih (i + 1) (by omega), drop_cons_of_lt hi,
      List.take_succ_cons]
    rfl

theorem front_spec (t : List α) :
    front t = if t = [] then argErr "Cannot call front on an empty tuple." else .ok t.dropLast := by
  unfold front
  split
  · rename_i h
    have hne : t ≠ [] := by intro e; subst e; simp at h
    rw [if_neg hne, frontAny32, readRange_ok t 0 _ (by omega)]
    simp [List.dropLast_eq_take]
  · split
    · rename_i _ e; subst e; rfl
    · rename_i _ hne; exact frontRec_ok t hne

end JuliaLean.Tuples
