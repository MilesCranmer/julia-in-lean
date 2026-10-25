import JuliaLean.Dicts.ProofMerge
import JuliaLean.Dicts.Props

/-!
# Reference sets

Membership (`isSome` of `rfind`) after `rset`, `rdel`, `filter` and the folds
used by `union!`, `setdiff!` and `symdiff!`; the `symdiff!` toggle commutes
for distinct keys; a list of distinct keys all found in another list is no
longer than it.
-/

namespace JuliaLean.Dicts

variable {K V : Type}

/-! ## Membership -/

theorem isSome_rfind_iff {o : KeyOps K} {m : RMap K V} {x : K} :
    (rfind o m x).isSome = true ↔ ∃ e ∈ m, o.eq x e.1 = true := by
  unfold rfind
  rw [List.find?_isSome] <;> exact Iff.rfl

theorem isSome_rfind_perm {o : KeyOps K} {m m' : RMap K V} (hp : List.Perm m m') (x : K) :
    (rfind o m x).isSome = (rfind o m' x).isSome := by
  rw [Bool.eq_iff_iff, isSome_rfind_iff, isSome_rfind_iff]
  exact ⟨fun ⟨e, he, hq⟩ => ⟨e, hp.mem_iff.1 he, hq⟩, fun ⟨e, he, hq⟩ => ⟨e, hp.mem_iff.2 he, hq⟩⟩

theorem isSome_rfind_congr {o : KeyOps K} (hl : o.Lawful) (m : RMap K V) {x y : K}
    (h : o.eq x y = true) : (rfind o m x).isSome = (rfind o m y).isSome := by
  have e : (fun e : K × V => o.eq x e.1) = (fun e => o.eq y e.1) :=
    funext fun e => eq_congr_left hl h e.1
  unfold rfind
  rw [e]

theorem isSome_rfind_cons {o : KeyOps K} (e : K × V) (m : RMap K V) (x : K) :
    (rfind o (e :: m) x).isSome = (o.eq x e.1 || (rfind o m x).isSome) := by
  unfold rfind
  cases h : o.eq x e.1
  · rw [List.find?_cons_of_neg (p := fun e : K × V => o.eq x e.1) (by simp [h])] <;> rfl
  · rw [List.find?_cons_of_pos (p := fun e : K × V => o.eq x e.1) h] <;> rfl

theorem isSome_rfind_rset {o : KeyOps K} (hl : o.Lawful) (m : RMap K V) (k q : K) (v : V) :
    (rfind o (rset o m k v) q).isSome = (o.eq q k || (rfind o m q).isSome) := by
  rw [rfind_rset hl]
  cases o.eq q k <;> rfl

theorem isSome_rfind_rdel {o : KeyOps K} (hl : o.Lawful) (m : RMap K V) (k q : K) :
    (rfind o (rdel o m k) q).isSome = (!o.eq q k && (rfind o m q).isSome) := by
  cases h : o.eq q k
  · rw [rfind_rdel_ne hl m h] <;> rfl
  · rw [rfind_rdel_eq hl m h] <;> rfl

theorem isSome_rfind_filter {o : KeyOps K} (m : RMap K V) {p : K × V → Bool} {x : K} {c : Bool}
    (hp : ∀ e, o.eq x e.1 = true → p e = c) :
    (rfind o (m.filter p) x).isSome = ((rfind o m x).isSome && c) := by
  unfold rfind
  cases c
  · rw [find_filter_none (p := fun e : K × V => o.eq x e.1) (f := p) (fun e he => hp e he) m]
    simp
  · rw [find_filter_of (p := fun e : K × V => o.eq x e.1) (f := p) (fun e he => hp e he) m]
    simp

/-! ## `union!`: folding `rset` -/

theorem isSome_rfind_foldl_rset {o : KeyOps K} (hl : o.Lawful) (x : K) :
    ∀ (l m : RMap K Unit),
      (rfind o (l.foldl (fun m e => rset o m e.1 ()) m) x).isSome =
        ((rfind o m x).isSome || (rfind o l x).isSome)
  | [], m => by
    show (rfind o m x).isSome = ((rfind o m x).isSome || false)
    rw [Bool.or_false]
  | e :: l, m => by
    rw [List.foldl_cons, isSome_rfind_foldl_rset hl x l, isSome_rfind_rset hl, isSome_rfind_cons]
    cases o.eq x e.1 <;> cases (rfind o m x).isSome <;> cases (rfind o l x).isSome <;> rfl

/-! ## `setdiff!`: folding `rdel` -/

theorem foldl_rdel_eq (o : KeyOps K) :
    ∀ (l m : RMap K V), l.foldl (fun m e => rdel o m e.1) m =
      m.filter (fun e => l.all fun f => !o.eq f.1 e.1)
  | [], m => by
    show m = m.filter (fun _ => true)
    exact (List.filter_eq_self.2 (fun _ _ => rfl)).symm
  | f :: l, m => by
    rw [List.foldl_cons, foldl_rdel_eq o l]
    unfold rdel
    rw [List.filter_filter]
    apply List.filter_congr
    intro e _
    rw [List.all_cons, Bool.and_comm]

theorem all_not_eq {o : KeyOps K} (hl : o.Lawful) {L mt : RMap K V} (hp : List.Perm L mt) (x : K) :
    (L.all fun f => !o.eq f.1 x) = !(rfind o mt x).isSome := by
  rw [hp.all_eq]
  cases h : (rfind o mt x).isSome
  · show _ = true
    rw [List.all_eq_true]
    intro f hf
    have hfx : o.eq x f.1 = false := by
      cases hq : o.eq x f.1
      · rfl
      · exact absurd (isSome_rfind_iff.2 ⟨f, hf, hq⟩) (by rw [h]; decide)
    show (!o.eq f.1 x) = true
    rw [eq_false_symm hl hfx]
    rfl
  · show _ = false
    rw [List.all_eq_false]
    obtain ⟨e, he, hq⟩ := isSome_rfind_iff.1 h
    exact ⟨e, he, by show ¬ (!o.eq e.1 x) = true; rw [hl.symm _ _ hq]; decide⟩

/-! ## Counting distinct keys -/

theorem rdel_length_lt {o : KeyOps K} {m : RMap K V} {k : K} {f : K × V} (hf : f ∈ m)
    (hq : o.eq k f.1 = true) : (rdel o m k).length < m.length := by
  have h1 := List.length_filter_le (fun e : K × V => !o.eq k e.1) m
  have h2 : (m.filter fun e : K × V => !o.eq k e.1).length ≠ m.length := by
    intro h
    have h3 := (List.length_filter_eq_length_iff.1 h) f hf
    simp [hq] at h3
  show (m.filter fun e : K × V => !o.eq k e.1).length < m.length
  omega

/-- Pairwise non-`isequal` keys that all occur in `mt` are at most as many as `mt`. -/
theorem pigeon {o : KeyOps K} (hl : o.Lawful) :
    ∀ (ms mt : RMap K V), Distinct o ms → (∀ e ∈ ms, (rfind o mt e.1).isSome = true) →
      ms.length ≤ mt.length
  | [], _, _, _ => Nat.zero_le _
  | e :: ms, mt, hd, hall => by
    obtain ⟨f, hf, hq⟩ := isSome_rfind_iff.1 (hall e List.mem_cons_self)
    have hd' := List.pairwise_cons.1 hd
    have ih := pigeon hl ms (rdel o mt e.1) hd'.2 (fun e' he' => by
      rw [rfind_rdel_ne hl mt (eq_false_symm hl (hd'.1 e' he'))]
      exact hall e' (List.mem_cons_of_mem _ he'))
    have := rdel_length_lt hf hq
    rw [List.length_cons]
    omega

/-- With equal lengths the inclusion also holds the other way. -/
theorem pigeon_all {o : KeyOps K} (hl : o.Lawful) {ms mt : RMap K V} (hd : Distinct o ms)
    (hall : ∀ e ∈ ms, (rfind o mt e.1).isSome = true) (hlen : mt.length ≤ ms.length) :
    ∀ f ∈ mt, (rfind o ms f.1).isSome = true := by
  intro f hf
  cases h : (rfind o ms f.1).isSome
  · exfalso
    have hp := pigeon hl ms (rdel o mt f.1) hd (fun e he => by
      have hef : o.eq f.1 e.1 = false := by
        cases hq : o.eq f.1 e.1
        · rfl
        · rw [isSome_rfind_iff.2 ⟨e, he, hq⟩] at h
          cases h
      rw [rfind_rdel_ne hl mt (eq_false_symm hl hef)]
      exact hall e he)
    have := rdel_length_lt hf (hl.refl f.1)
    omega
  · rfl

/-! ## `symdiff!`: toggling membership -/

/-- One step of `symdiff!`: delete `e.1` if present, otherwise insert it. -/
def symStep (o : KeyOps K) (m : RMap K Unit) (e : K × Unit) : RMap K Unit :=
  if rmem o m e.1 then rdel o m e.1 else rset o m e.1 ()

theorem isSome_rfind_symStep {o : KeyOps K} (hl : o.Lawful) (m : RMap K Unit) (e : K × Unit)
    (x : K) : (rfind o (symStep o m e) x).isSome = ((rfind o m x).isSome != o.eq x e.1) := by
  unfold symStep rmem
  cases hm : (rfind o m e.1).isSome
  · rw [if_neg (by decide), isSome_rfind_rset hl]
    cases hq : o.eq x e.1
    · cases (rfind o m x).isSome <;> rfl
    · rw [isSome_rfind_congr hl m hq, hm] <;> rfl
  · rw [if_pos rfl, isSome_rfind_rdel hl]
    cases hq : o.eq x e.1
    · cases (rfind o m x).isSome <;> rfl
    · rw [isSome_rfind_congr hl m hq, hm] <;> rfl

theorem distinct_symStep {o : KeyOps K} {m : RMap K Unit} (h : Distinct o m) (e : K × Unit) :
    Distinct o (symStep o m e) := by
  unfold symStep
  split
  · exact distinct_rdel h _
  · exact distinct_rset h _ _

theorem symStep_perm {o : KeyOps K} {m1 m2 : RMap K Unit} (hp : List.Perm m1 m2) (e : K × Unit) :
    List.Perm (symStep o m1 e) (symStep o m2 e) := by
  unfold symStep rmem
  rw [isSome_rfind_perm hp]
  by_cases hc : (rfind o m2 e.1).isSome = true
  · rw [if_pos hc, if_pos hc]
    exact hp.filter _
  · rw [if_neg hc, if_neg hc]
    exact rset_perm hp _ _

theorem symStep_swap {o : KeyOps K} (hl : o.Lawful) (m : RMap K Unit) (x y : K × Unit)
    (hxy : o.eq x.1 y.1 = false) :
    List.Perm (symStep o (symStep o m y) x) (symStep o (symStep o m x) y) := by
  have hyx := eq_false_symm hl hxy
  have hx : (rfind o (symStep o m y) x.1).isSome = (rfind o m x.1).isSome := by
    rw [isSome_rfind_symStep hl, hxy]
    cases (rfind o m x.1).isSome <;> rfl
  have hy : (rfind o (symStep o m x) y.1).isSome = (rfind o m y.1).isSome := by
    rw [isSome_rfind_symStep hl, hyx]
    cases (rfind o m y.1).isSome <;> rfl
  have ex : symStep o (symStep o m y) x = if (rfind o m x.1).isSome = true
      then rdel o (symStep o m y) x.1 else rset o (symStep o m y) x.1 () := by
    show (if (rfind o (symStep o m y) x.1).isSome = true then _ else _) = _
    rw [hx]
  have ey : symStep o (symStep o m x) y = if (rfind o m y.1).isSome = true
      then rdel o (symStep o m x) y.1 else rset o (symStep o m x) y.1 () := by
    show (if (rfind o (symStep o m x) y.1).isSome = true then _ else _) = _
    rw [hy]
  have sx : symStep o m x = if (rfind o m x.1).isSome = true then rdel o m x.1
      else rset o m x.1 () := rfl
  have sy : symStep o m y = if (rfind o m y.1).isSome = true then rdel o m y.1
      else rset o m y.1 () := rfl
  rw [ex, ey, sx, sy]
  cases (rfind o m x.1).isSome <;> cases (rfind o m y.1).isSome
  · show List.Perm (rset o (rset o m y.1 ()) x.1 ()) (rset o (rset o m x.1 ()) y.1 ())
    exact rset_swap hl m x y hxy
  · show List.Perm ((x.1, ()) :: rdel o (rdel o m y.1) x.1) (rdel o ((x.1, ()) :: rdel o m x.1) y.1)
    rw [rdel_cons_ne (e := (x.1, ())) hyx, rdel_comm o m x.1 y.1]
  · show List.Perm (rdel o ((y.1, ()) :: rdel o m y.1) x.1) ((y.1, ()) :: rdel o (rdel o m x.1) y.1)
    rw [rdel_cons_ne (e := (y.1, ())) hxy, rdel_comm o m x.1 y.1]
  · show List.Perm (rdel o (rdel o m y.1) x.1) (rdel o (rdel o m x.1) y.1)
    rw [rdel_comm o m y.1 x.1]

theorem foldl_symStep_perm_init (o : KeyOps K) :
    ∀ (l : RMap K Unit) {m1 m2 : RMap K Unit}, List.Perm m1 m2 →
      List.Perm (l.foldl (symStep o) m1) (l.foldl (symStep o) m2)
  | [], _, _, hp => hp
  | e :: l, _, _, hp => foldl_symStep_perm_init o l (symStep_perm hp e)

theorem foldl_symStep_perm {o : KeyOps K} (hl : o.Lawful) {l l' : RMap K Unit}
    (hp : List.Perm l l') :
    Distinct o l → ∀ m : RMap K Unit, Distinct o m →
      List.Perm (l.foldl (symStep o) m) (l'.foldl (symStep o) m) := by
  induction hp with
  | nil => exact fun _ m _ => List.Perm.refl _
  | cons x _ ih => exact fun hd m hm => ih (List.pairwise_cons.1 hd).2 _ (distinct_symStep hm x)
  | swap x y l =>
    intro hd m _
    have hyx : o.eq y.1 x.1 = false := (List.pairwise_cons.1 hd).1 x List.mem_cons_self
    exact foldl_symStep_perm_init o l (symStep_swap hl m x y (eq_false_symm hl hyx))
  | trans p1 _ ih1 ih2 => exact fun hd m hm => (ih1 hd m hm).trans (ih2 (hd.perm hl p1) m hm)

theorem isSome_rfind_foldl_symStep {o : KeyOps K} (hl : o.Lawful) (x : K) :
    ∀ (l m : RMap K Unit), Distinct o l →
      (rfind o (l.foldl (symStep o) m) x).isSome = ((rfind o m x).isSome != (rfind o l x).isSome)
  | [], m, _ => by
    show (rfind o m x).isSome = ((rfind o m x).isSome != false)
    cases (rfind o m x).isSome <;> rfl
  | e :: l, m, hd => by
    have hd' := List.pairwise_cons.1 hd
    rw [List.foldl_cons, isSome_rfind_foldl_symStep hl x l _ hd'.2, isSome_rfind_symStep hl,
      isSome_rfind_cons]
    cases hq : o.eq x e.1
    · cases (rfind o m x).isSome <;> cases (rfind o l x).isSome <;> rfl
    · have hl' : (rfind o l x).isSome = false := by
        cases h : (rfind o l x).isSome
        · rfl
        · obtain ⟨f, hf, hxf⟩ := isSome_rfind_iff.1 h
          exact absurd (hd'.1 f hf) (by rw [eq_trans' hl hq hxf]; decide)
      rw [hl']
      cases (rfind o m x).isSome <;> rfl

end JuliaLean.Dicts
