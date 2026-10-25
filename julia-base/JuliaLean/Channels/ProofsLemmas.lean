import JuliaLean.Channels.Model

namespace JuliaLean.Channels

def wakeT (w : Wake) (t : Task) : Task :=
  match t.pc with
  | .parked k => { t with pc := .woken k w }
  | _ => t

def tsum (f : Task → Int) (ts : List Task) : Int := (ts.map f).sum

@[simp] theorem setPc_length (ts : List Task) (i : Nat) (pc : Pc) :
    (setPc ts i pc).length = ts.length := by
  induction ts generalizing i with
  | nil => simp [setPc]
  | cons t ts ih => cases i <;> simp [setPc, ih]

theorem setPc_getElem? (ts : List Task) (i : Nat) (pc : Pc) (j : Nat) :
    (setPc ts i pc)[j]? =
      if j = i then ts[j]?.map (fun t => { t with pc := pc }) else ts[j]? := by
  induction ts generalizing i j with
  | nil => simp [setPc]
  | cons t ts ih =>
    cases i <;> cases j <;> simp [setPc, ih]

@[simp] theorem setPc_map_op (ts : List Task) (i : Nat) (pc : Pc) :
    (setPc ts i pc).map Task.op = ts.map Task.op := by
  induction ts generalizing i with
  | nil => simp [setPc]
  | cons t ts ih => cases i <;> simp [setPc, ih]

@[simp] theorem wakeT_op (w : Wake) (t : Task) : (wakeT w t).op = t.op := by
  cases t with
  | mk op pc => cases pc <;> rfl

@[simp] theorem wake_length (ts : List Task) (j : Nat) (w : Wake) :
    (wake ts j w).length = ts.length := by
  induction ts generalizing j with
  | nil => simp [wake]
  | cons t ts ih => cases j <;> simp [wake, ih]

theorem wake_getElem? (ts : List Task) (j : Nat) (w : Wake) (k : Nat) :
    (wake ts j w)[k]? = if k = j then ts[k]?.map (wakeT w) else ts[k]? := by
  induction ts generalizing j k with
  | nil => simp [wake]
  | cons t ts ih => cases j <;> cases k <;> simp [wake, wakeT, ih] <;> rfl

@[simp] theorem wake_map_op (ts : List Task) (j : Nat) (w : Wake) :
    (wake ts j w).map Task.op = ts.map Task.op := by
  induction ts generalizing j with
  | nil => simp [wake]
  | cons t ts ih =>
    cases j with
    | zero => change (wakeT w t).op :: ts.map Task.op = t.op :: ts.map Task.op; simp
    | succ j => simp [wake, ih]

@[simp] theorem wakeT_idem (w : Wake) (t : Task) : wakeT w (wakeT w t) = wakeT w t := by
  cases t with
  | mk op pc => cases pc <;> rfl

@[simp] theorem wakeAll_length (ts : List Task) (q : List Nat) (w : Wake) :
    (wakeAll ts q w).length = ts.length := by
  induction q generalizing ts with
  | nil => rfl
  | cons j q ih => simpa [wakeAll, List.foldl_cons] using ih (wake ts j w)

theorem wakeAll_getElem? (ts : List Task) (q : List Nat) (w : Wake) (k : Nat) :
    (wakeAll ts q w)[k]? = if k ∈ q then ts[k]?.map (wakeT w) else ts[k]? := by
  induction q generalizing ts with
  | nil => simp [wakeAll]
  | cons j q ih =>
    simp only [wakeAll, List.foldl_cons] at *
    rw [ih, wake_getElem?]
    by_cases hq : k ∈ q <;> by_cases hj : k = j <;>
      simp [hq, hj, Option.map_map, Function.comp_def]

theorem wakeAll_pc_parked (ts : List Task) (q : List Nat) (w : Wake) (j : Nat)
    (k : Park) :
    ((wakeAll ts q w)[j]?).map Task.pc = some (.parked k) ↔
      j ∉ q ∧ ts[j]?.map Task.pc = some (.parked k) := by
  rw [wakeAll_getElem?]
  by_cases hj : j ∈ q <;> cases ht : ts[j]? with
  | none => simp [hj]
  | some t =>
    cases t with
    | mk op pc => cases pc <;> simp [hj, wakeT]

theorem wakeAll_pc_handoff (ts : List Task) (q : List Nat) (w : Wake) (j : Nat)
    (v : Val) (taker : Nat) :
    ((wakeAll ts q w)[j]?).map Task.pc = some (.handoff v taker) ↔
      ts[j]?.map Task.pc = some (.handoff v taker) := by
  rw [wakeAll_getElem?]
  by_cases hj : j ∈ q <;> cases ht : ts[j]? with
  | none => simp [hj]
  | some t =>
    cases t with
    | mk op pc => cases pc <;> simp [hj, wakeT]

theorem wakeAll_pc_woken (ts : List Task) (q : List Nat) (w : Wake) (j : Nat)
    (k : Park) (w' : Wake) :
    ((wakeAll ts q w)[j]?).map Task.pc = some (.woken k w') ↔
      ts[j]?.map Task.pc = some (.woken k w') ∨
        (j ∈ q ∧ ts[j]?.map Task.pc = some (.parked k) ∧ w' = w) := by
  rw [wakeAll_getElem?]
  by_cases hj : j ∈ q <;> cases ht : ts[j]? with
  | none => simp [hj]
  | some t =>
    cases t with
    | mk op pc => cases pc <;> simp [hj, wakeT, eq_comm]

@[simp] theorem wakeAll_map_op (ts : List Task) (q : List Nat) (w : Wake) :
    (wakeAll ts q w).map Task.op = ts.map Task.op := by
  induction q generalizing ts with
  | nil => rfl
  | cons j q ih => simpa [wakeAll, List.foldl_cons] using ih (wake ts j w)

@[simp] theorem tsum_nil (f : Task → Int) : tsum f [] = 0 := rfl

@[simp] theorem tsum_cons (f : Task → Int) (t : Task) (ts : List Task) :
    tsum f (t :: ts) = f t + tsum f ts := by simp [tsum]

theorem tsum_setPc (f : Task → Int) (ts : List Task) (i : Nat) (pc : Pc)
    (h : i < ts.length) :
    tsum f (setPc ts i pc) = tsum f ts - f ts[i] + f { ts[i] with pc := pc } := by
  induction ts generalizing i with
  | nil => simp at h
  | cons t ts ih =>
    cases i with
    | zero => simp [setPc, tsum_cons]; omega
    | succ i =>
      have hi : i < ts.length := by simpa using h
      simp only [setPc, tsum_cons, List.getElem_cons_succ]
      rw [ih i hi]
      dsimp only
      omega

theorem tsum_wake (f : Task → Int) (ts : List Task) (j : Nat) (w : Wake)
    (h : j < ts.length) :
    tsum f (wake ts j w) = tsum f ts - f ts[j] + f (wakeT w ts[j]) := by
  induction ts generalizing j with
  | nil => simp at h
  | cons t ts ih =>
    cases j with
    | zero => change tsum f (wakeT w t :: ts) = _; simp [tsum_cons]; omega
    | succ j =>
      have hj : j < ts.length := by simpa using h
      simp only [wake, tsum_cons, List.getElem_cons_succ]
      rw [ih j hj]
      omega

theorem tsum_wake_of_inv (f : Task → Int) (ts : List Task) (j : Nat) (w : Wake)
    (hf : ∀ t, f (wakeT w t) = f t) : tsum f (wake ts j w) = tsum f ts := by
  induction ts generalizing j with
  | nil => rfl
  | cons t ts ih =>
    cases j with
    | zero => change tsum f (wakeT w t :: ts) = _; simp [hf]
    | succ j => simp [wake, ih]

theorem tsum_wakeAll_of_inv (f : Task → Int) (ts : List Task) (q : List Nat)
    (w : Wake) (hf : ∀ t, f (wakeT w t) = f t) :
    tsum f (wakeAll ts q w) = tsum f ts := by
  induction q generalizing ts with
  | nil => rfl
  | cons j q ih =>
    simpa [wakeAll, List.foldl_cons, tsum_wake_of_inv f ts j w hf] using ih (wake ts j w)

theorem tsum_wake_out (f : Task → Int) (ts : List Task) (j : Nat) (w : Wake)
    (h : ts.length ≤ j) : wake ts j w = ts := by
  clear f
  induction ts generalizing j with
  | nil => rfl
  | cons t ts ih =>
    cases j with
    | zero => simp at h
    | succ j =>
      have hj : ts.length ≤ j := by simpa using h
      simp [wake, ih j hj]

theorem count_flatMap_tsum (x : Nat) (l : List Task) (g : Task → List Nat) :
    (((l.flatMap g).count x : Nat) : Int) =
      tsum (fun t => (((g t).count x : Nat) : Int)) l := by
  induction l with
  | nil => simp [tsum]
  | cons t ts ih => simp [List.flatMap_cons, List.count_append, tsum_cons, ih, Int.natCast_add]

theorem countP_tsum (p : Task → Bool) (l : List Task) :
    ((l.countP p : Nat) : Int) = tsum (fun t => if p t then 1 else 0) l := by
  induction l with
  | nil => simp [tsum]
  | cons t ts ih => cases hp : p t <;> simp [hp, tsum_cons, ih, Int.natCast_add] <;> omega

theorem countP_setPc (p : Task → Bool) (ts : List Task) (i : Nat) (pc : Pc)
    (t : Task) (h : ts[i]? = some t) :
    (setPc ts i pc).countP p + (if p t then 1 else 0) =
      ts.countP p + (if p { t with pc := pc } then 1 else 0) := by
  induction ts generalizing i with
  | nil => simp at h
  | cons a ts ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst t
      cases ha : p a <;> cases hb : p { a with pc := pc } <;>
        simp [setPc, ha, hb] <;> omega
    | succ i =>
      have hi := ih i (by simpa using h)
      cases ha : p a <;> simp [setPc, ha] <;> omega

theorem countP_wake (p : Task → Bool) (ts : List Task) (j : Nat) (w : Wake)
    (t : Task) (h : ts[j]? = some t) :
    (wake ts j w).countP p + (if p t then 1 else 0) =
      ts.countP p + (if p (wakeT w t) then 1 else 0) := by
  induction ts generalizing j with
  | nil => simp at h
  | cons a ts ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst t
      change (wakeT w a :: ts).countP p + _ = _
      cases ha : p a <;> cases hb : p (wakeT w a) <;>
        simp [ha, hb] <;> omega
    | succ j =>
      have hj := ih j (by simpa using h)
      cases ha : p a <;> simp [wake, ha] <;> omega

theorem countP_wakeAll_of_inv (p : Task → Bool) (ts : List Task) (q : List Nat)
    (w : Wake) (hf : ∀ t, p (wakeT w t) = p t) :
    (wakeAll ts q w).countP p = ts.countP p := by
  have hh := tsum_wakeAll_of_inv (fun t => if p t then 1 else 0) ts q w
    (fun t => by rw [hf t])
  rw [← countP_tsum, ← countP_tsum] at hh
  omega

theorem countP_wake_mono (p : Task → Bool) (ts : List Task) (j : Nat) (w : Wake)
    (hp : ∀ t, p t = true → p (wakeT w t) = true) :
    ts.countP p ≤ (wake ts j w).countP p := by
  induction ts generalizing j with
  | nil => simp [wake]
  | cons t ts ih =>
    cases j with
    | zero =>
      change (t :: ts).countP p ≤ (wakeT w t :: ts).countP p
      cases ht : p t with
      | false => cases hw : p (wakeT w t) <;> simp [ht, hw]
      | true => simp [ht, hp t ht]
    | succ j =>
      have hj := ih j
      cases ht : p t <;> simp [wake, ht] <;> omega

theorem countP_wakeAll_mono (p : Task → Bool) (ts : List Task) (q : List Nat)
    (w : Wake) (hp : ∀ t, p t = true → p (wakeT w t) = true) :
    ts.countP p ≤ (wakeAll ts q w).countP p := by
  induction q generalizing ts with
  | nil => simp [wakeAll]
  | cons j q ih =>
    exact Nat.le_trans (countP_wake_mono p ts j w hp) (ih (wake ts j w))

theorem tsum_nonneg (f : Task → Int) (l : List Task) (h : ∀ t, 0 ≤ f t) :
    0 ≤ tsum f l := by
  induction l with
  | nil => simp
  | cons t ts ih => rw [tsum_cons]; exact Int.add_nonneg (h t) ih

theorem tsum_append (f : Task → Int) (a b : List Task) :
    tsum f (a ++ b) = tsum f a + tsum f b := by
  induction a with
  | nil => simp
  | cons t ts ih => simp [tsum_cons, ih, Int.add_assoc]

end JuliaLean.Channels
