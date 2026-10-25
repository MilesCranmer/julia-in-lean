import JuliaLean.Dicts.ProofGet

/-!
# Reachable tables and the `Dict` properties

A call sequence of total weight at most `2^30` from `Dict()` gives the
reference outcome, and every table it produces represents the reference map
with at most `2^30` pairs. Each `Dict` property applies one more call to such a
table.
-/

namespace JuliaLean.Dicts

variable {K V : Type}

theorem SameOutcome.bind_pure {α β γ δ : Type} {A : DR α} {B : DR β} {R : α → β → Prop}
    {S : γ → δ → Prop} (h : SameOutcome A B R) (f : α → γ) (g : β → δ)
    (hfg : ∀ a b, R a b → S (f a) (g b)) :
    SameOutcome (A >>= fun a => pure (f a)) (B >>= fun b => pure (g b)) S := by
  cases A <;> cases B
  · exact h
  · exact False.elim h
  · exact False.elim h
  · exact hfg _ _ h

theorem typemax_i64_val : (JInt.typemax .i64).val = 2 ^ 63 - 1 := by
  show wrapInt .i64 (IntTy.max .i64) = _
  rw [wrapInt_of_inRange .i64 _ ⟨by rw [i64_min, i64_max]; omega, Int.le_refl _⟩, i64_max]

theorem GenericMax.maxValuesOK {o : KeyOps K} (h : GenericMax o) : MaxValuesOK o :=
  Or.inl (by
    have h' : o.maxValues = JInt.typemax .i64 := h
    rw [h', typemax_i64_val]
    omega)

/-! ## One call, then a call sequence -/

theorem runOp_spec {o : KeyOps K} (hl : o.Lawful) (hmv : MaxValuesOK o) {t : Table K V}
    {m : RMap K V} (h : Rep o t m) (d : DOp K V) (hs : opHintSmall d = true)
    (hW : opWeight d ≤ 2 ^ 30) (hc : t.count + opWeight d ≤ 2 ^ 31) :
    SameOutcome (runOp o t d) (rop o m d)
      (fun t' m' => Rep o t' m' ∧ t'.count ≤ t.count + opWeight d) := by
  cases d with
  | base b =>
    have hc' : t.count + baseWeight b ≤ 2 ^ 32 := by
      have : t.count + baseWeight b ≤ 2 ^ 31 := hc
      omega
    exact (runBase_spec hl hmv h b hs (2 * (t.count + baseWeight b) + 21) hc' (Nat.le_refl _)).mono
      fun t' m' hr => by
        obtain ⟨hr1, hr2, -⟩ := hr
        exact ⟨hr1, hr2⟩
  | getf k v inner =>
    have hw : opWeight (DOp.getf k v inner : DOp K V) = 1 + baseListWeight inner := rfl
    show SameOutcome (getBang o t k (innerDefault o v inner) >>= fun r => pure r.2)
      (match rfind o m k with
        | some _ => pure m
        | none => (rbaseList o m inner >>= fun m => pure (rset o m k v)) : DR (RMap K V)) _
    cases hrf : rfind o m k with
    | some e =>
      rw [getBang_found hl h (by omega) hrf]
      exact ⟨h, by show t.count ≤ _; omega⟩
    | none =>
      have hinner := getBang_inner hl hmv h k v inner hs (by omega) (by omega) hrf
      refine SameOutcome.bind_pure hinner (fun r => r.2) (fun m' => rset o m' k v) ?_
      intro r m' hr
      obtain ⟨-, hr2, hr3⟩ := hr
      refine ⟨hr2, ?_⟩
      show r.2.count ≤ t.count + opWeight (DOp.getf k v inner)
      rw [hw]
      omega

theorem runOpsFrom_spec {o : KeyOps K} (hl : o.Lawful) (hmv : MaxValuesOK o) :
    ∀ (ops : List (DOp K V)) (t : Table K V) (m : RMap K V), Rep o t m →
      ops.all opHintSmall = true → (ops.map opWeight).sum ≤ 2 ^ 30 →
      t.count + (ops.map opWeight).sum ≤ 2 ^ 31 →
      SameOutcome (ops.foldlM (runOp o) t) (ops.foldlM (rop o) m)
        (fun t' m' => Rep o t' m' ∧ t'.count ≤ t.count + (ops.map opWeight).sum)
  | [], t, _, h, _, _, _ => ⟨h, Nat.le_add_right _ _⟩
  | d :: ops, t, m, h, hs, hW, hc => by
    have hw : ((d :: ops).map opWeight).sum = opWeight d + (ops.map opWeight).sum := rfl
    rw [hw] at hW hc ⊢
    simp only [List.all_cons, Bool.and_eq_true] at hs
    have hd := runOp_spec hl hmv h d hs.1 (by omega) (by omega)
    show SameOutcome (runOp o t d >>= fun t1 => ops.foldlM (runOp o) t1)
      (rop o m d >>= fun m1 => ops.foldlM (rop o) m1) _
    revert hd
    cases runOp o t d with
    | error e1 =>
      cases rop o m d with
      | error e2 => exact fun hd => hd
      | ok _ => exact fun hd => False.elim hd
    | ok t1 =>
      cases rop o m d with
      | error _ => exact fun hd => False.elim hd
      | ok m1 =>
        intro hd
        obtain ⟨hr1, hc1⟩ := hd
        have ih := runOpsFrom_spec hl hmv ops t1 m1 hr1 hs.2 (by omega) (by omega)
        show SameOutcome (ops.foldlM (runOp o) t1) (ops.foldlM (rop o) m1) _
        refine ih.mono fun t2 m2 hs2 => ?_
        obtain ⟨hr2, hc2⟩ := hs2
        exact ⟨hr2, by omega⟩

theorem runOps_spec {o : KeyOps K} (hl : o.Lawful) (hmv : MaxValuesOK o) (ops : List (DOp K V))
    (hs : OpsSmall ops) :
    SameOutcome (runOps o ops) (rrun o ops) (fun t m => Rep o t m ∧ t.count ≤ 2 ^ 30) := by
  have h0 : (Table.empty : Table K V).count = 0 := rfl
  have h := runOpsFrom_spec hl hmv ops Table.empty [] (empty_rep o) hs.2 hs.1
    (by have := hs.1; omega)
  refine h.mono fun t m hr => ?_
  obtain ⟨hr1, hr2⟩ := hr
  exact ⟨hr1, by have := hs.1; omega⟩

/-- A reachable table represents its reference map and holds at most `2^30` pairs. -/
theorem Reach.rep {o : KeyOps K} (hl : o.Lawful) (hmv : MaxValuesOK o) {t : Table K V}
    {m : RMap K V} (h : Reach o t m) : Rep o t m ∧ t.count ≤ 2 ^ 30 := by
  obtain ⟨ops, hs, h1, h2⟩ := h
  have := runOps_spec hl hmv ops hs
  rw [h1, h2] at this
  exact this

/-! ## The `Dict` properties -/

theorem opsAgree_thm : OpsAgree := by
  intro K V o hl hmv ops hs
  exact (runOps_spec hl hmv ops hs).mono fun t m h => Rep.agrees hl h.1

theorem setindexLookup_thm : SetindexLookup := by
  intro K V o hl hmv t m hR k v
  obtain ⟨h, hc⟩ := hR.rep hl hmv
  obtain ⟨t', h1, hr, -⟩ := h.setindex hl (by omega) k v
  exact ⟨t', h1, Rep.agrees hl hr, fun q => by rw [hr.dictGet hl q, rlookup_rset hl m k q v]⟩

theorem deleteLookup_thm : DeleteLookup := by
  intro K V o hl hmv t m hR k
  obtain ⟨h, -⟩ := hR.rep hl hmv
  obtain ⟨t', h1, hr, -⟩ := h.dictDelete hl k
  exact ⟨t', h1, Rep.agrees hl hr, fun q => by rw [hr.dictGet hl q, rlookup_rdel hl m k q]⟩

theorem popKeyAgrees_thm : PopKeyAgrees := by
  intro K V o hl hmv t m hR k dflt
  obtain ⟨h, -⟩ := hR.rep hl hmv
  refine ⟨?_, ?_⟩
  · cases hrf : rfind o m k with
    | none => exact h.popKey_absent hrf
    | some e =>
      obtain ⟨k0, w⟩ := e
      obtain ⟨t', h1, hr, -⟩ := h.popKey_found hl hrf
      exact ⟨t', h1, Rep.agrees hl hr⟩
  · obtain ⟨t', h1, hr, -⟩ := h.popKeyDefault hl k dflt
    exact ⟨t', h1, Rep.agrees hl hr⟩

theorem getBangValueAgrees_thm : GetBangValueAgrees := by
  intro K V o hl hmv t m hR k v
  obtain ⟨h, hc⟩ := hR.rep hl hmv
  cases hrf : rfind o m k with
  | none =>
    obtain ⟨t', h1, hr, -⟩ := getBangVal_absent hl h (by omega) hrf v
    exact ⟨t', h1, Rep.agrees hl hr⟩
  | some e =>
    obtain ⟨k0, w⟩ := e
    exact ⟨t, getBang_found hl h (by omega) hrf _, Rep.agrees hl h⟩

theorem getBangMutatingDefault_thm : GetBangMutatingDefault := by
  intro K V o hl hmv t m hR k v inner hin
  obtain ⟨hW, hs⟩ := hin
  obtain ⟨h, hc⟩ := hR.rep hl hmv
  cases hrf : rfind o m k with
  | some e =>
    obtain ⟨k0, w⟩ := e
    rw [getBang_found hl h (by omega) hrf]
    exact ⟨rfl, Rep.agrees hl h⟩
  | none =>
    have hg := getBang_inner hl hmv h k v inner hs (by omega) hW hrf
    revert hg
    cases getBang o t k (innerDefault o v inner) with
    | error e1 =>
      cases rbaseList o m inner with
      | error e2 =>
        intro hg
        have he : e1 = e2 := hg
        rw [he]
      | ok _ => exact fun hg => False.elim hg
    | ok p =>
      obtain ⟨r, t'⟩ := p
      cases rbaseList o m inner with
      | error _ => exact fun hg => False.elim hg
      | ok m' =>
        intro hg
        obtain ⟨hr1, hr2, -⟩ := hg
        exact ⟨hr1, m', rfl, Rep.agrees hl hr2⟩

theorem sizehintSmallAgrees_thm : SizehintSmallAgrees := by
  intro K V o hl hmv t m hR n shrink hn
  obtain ⟨h, hc⟩ := hR.rep hl hmv
  obtain ⟨t', h1, hi', hp', -⟩ := sizehint_spec hmv h.1 (by omega) n hn shrink
  exact ⟨t', h1, Rep.agrees hl ⟨hi', hp'.trans h.2⟩⟩

theorem emptyAgrees_thm : EmptyAgrees := by
  intro K V o hl hmv t m hR
  obtain ⟨h, -⟩ := hR.rep hl hmv
  exact Rep.agrees hl (emptyBang_spec h.1).1

theorem filterAgrees_thm : FilterAgrees := by
  intro K V o hl hmv t m hR pred
  obtain ⟨h, -⟩ := hR.rep hl hmv
  obtain ⟨t', h1, hi', htl, -⟩ := filterBang_spec hl h.1 pred
  refine ⟨t', h1, Rep.agrees hl ⟨hi', ?_⟩⟩
  rw [htl]
  exact h.2.filter _

theorem mergeAgrees_thm : MergeAgrees := by
  intro K V o hl hmv t m hR ps f hps
  obtain ⟨h, hc⟩ := hR.rep hl hmv
  obtain ⟨d2, hb, h2, hc2⟩ := buildDict_spec hl ps (by omega)
  obtain ⟨t1, h1, hr1, -⟩ := Rep.dictMerge hl hmv h h2 (by omega)
  obtain ⟨t2, h2', hr2, -⟩ := Rep.mergewith hl hmv f h h2 (by omega)
  exact ⟨d2, hb, ⟨t1, h1, Rep.agrees hl hr1⟩, ⟨t2, h2', Rep.agrees hl hr2⟩⟩

theorem popAnyAgrees_thm : PopAnyAgrees := by
  intro K V o hl hmv t m hR
  obtain ⟨h, -⟩ := hR.rep hl hmv
  cases m with
  | nil => exact popAny_empty h
  | cons e m' =>
    obtain ⟨k, v, t', h1, hmem, hr, -⟩ := h.popAny hl (List.cons_ne_nil e m')
    exact ⟨k, v, t', h1, hmem, Rep.agrees hl hr⟩

/-! ## `Float64` keys -/

theorem f64_isnan_of_bits {a b : Float.F64} (h : Float.F64.toBits a = Float.F64.toBits b) :
    Float.F64.isnan a = Float.F64.isnan b := by
  unfold Float.F64.isnan Float.F64.exponentField Float.F64.fraction
  rw [h]

theorem f64Ops_lawful (h : Float.F64 → JInt .u64)
    (hh : ∀ a b, Float.F64.isequal a b = true → h a = h b) : (f64Ops h).Lawful where
  refl a := by
    show Float.F64.isequal a a = true
    simp only [Float.F64.isequal, beq_self_eq_true, Bool.or_true]
  symm a b hab := by
    show Float.F64.isequal b a = true
    have hab' : Float.F64.isequal a b = true := hab
    simp only [Float.F64.isequal, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hab' ⊢
    rcases hab' with ⟨h1, h2⟩ | e
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr e.symm
  trans a b c hab hbc := by
    show Float.F64.isequal a c = true
    have hab' : Float.F64.isequal a b = true := hab
    have hbc' : Float.F64.isequal b c = true := hbc
    simp only [Float.F64.isequal, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hab' hbc' ⊢
    rcases hab' with ⟨a1, a2⟩ | e1 <;> rcases hbc' with ⟨b1, b2⟩ | e2
    · exact Or.inl ⟨a1, b2⟩
    · exact Or.inl ⟨a1, by rw [← f64_isnan_of_bits e2]; exact a2⟩
    · exact Or.inl ⟨by rw [f64_isnan_of_bits e1]; exact b1, b2⟩
    · exact Or.inr (e1.trans e2)
  hash_eq := hh

theorem floatKeysIsequal_thm : FloatKeysIsequal := by
  intro h hh V t m hR x y v w
  have hl := f64Ops_lawful h hh
  have hmv : MaxValuesOK (f64Ops h) := GenericMax.maxValuesOK rfl
  obtain ⟨hr, hc⟩ := hR.rep hl hmv
  obtain ⟨t1, h1, hr1, -⟩ := hr.setindex hl (by omega) x v
  have hc1 : t1.count ≤ t.count + 1 := by
    rw [hr1.count_eq, hr.count_eq]
    exact rset_length_le _ _ _ _
  obtain ⟨t2, h2, hr2, -⟩ := hr1.setindex hl (by omega) y w
  refine ⟨t1, t2, h1, h2, ?_, ?_, (Rep.agrees hl hr2).2.2.2⟩
  · rw [hr2.dictGet hl x, rlookup_rset hl, rlookup_rset hl, if_pos (hl.refl x)]
    show Except.ok (if Float.F64.isequal x y = true then some w else some v) = _
    cases Float.F64.isequal x y <;> rfl
  · rw [hr2.dictGet hl y, rlookup_rset hl, if_pos (hl.refl y)]

end JuliaLean.Dicts
