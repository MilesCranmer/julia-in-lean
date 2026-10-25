import JuliaLean.Dicts.ProofMerge
import JuliaLean.Dicts.ProofPop
import JuliaLean.Dicts.Props

/-!
# Every mutating call, and `get!` with a mutating `default`

Each call either leaves the slots and keys alone and `age` unchanged, or
advances `age` by at least one and at most `weight * (2 count + 21)`. A
`default` of total weight at most `2^30` on a table of at most `2^31` pairs
therefore moves `age` by less than `2^64` when it changes anything, so the
`age` test of `get!` (`base/dict.jl:462-468`) sees every change and re-probes.
-/

namespace JuliaLean.Dicts

variable {K V : Type}

theorem SameOutcome.mono {α β : Type} {A : DR α} {B : DR β} {R S : α → β → Prop}
    (h : SameOutcome A B R) (hRS : ∀ a b, R a b → S a b) : SameOutcome A B S := by
  cases A <;> cases B
  · exact h
  · exact False.elim h
  · exact False.elim h
  · exact hRS _ _ h

theorem rdel_length_le (o : KeyOps K) (m : RMap K V) (k : K) : (rdel o m k).length ≤ m.length :=
  List.length_filter_le _ _

theorem dr_pure_bind {α β : Type} (a : α) (f : α → DR β) : (pure a >>= f) = f a := rfl

/-! ## `get!` -/

/-- The `else` branch of `get!(default, h, key)`. -/
def gbTail (o : KeyOps K) (key : K) (default : Table K V → DR (V × Table K V)) (index : Int)
    (sh : Nat) (t : Table K V) : DR (V × Table K V) := do
  let age0 := t.age
  let (v, t) ← default t
  let (index, sh, t) ←
    if t.age.val != age0.val then keyindex2 o t (o.hash key) (o.eq key)
    else pure (index, sh, t)
  if index > 0 then pure (v, overwriteAt t v key index.toNat)
  else
    let t ← setindexAt o t v key (-index).toNat sh
    pure (v, t)

/-- The final store of `get!`. -/
def gbFin (o : KeyOps K) (key : K) (v : V) (r : Int × Nat × Table K V) : DR (V × Table K V) :=
  match r with
  | (index, sh, t) =>
    if index > 0 then pure (v, overwriteAt t v key index.toNat)
    else do
      let t ← setindexAt o t v key (-index).toNat sh
      pure (v, t)

theorem getBang_of {o : KeyOps K} {t t1 : Table K V} {key : K}
    {default : Table K V → DR (V × Table K V)} {idx : Int} {sh : Nat}
    (h : keyindex2 o t (o.hash key) (o.eq key) = .ok (idx, sh, t1)) :
    getBang o t key default = if idx > 0 then (valAt t1 idx.toNat >>= fun v => pure (v, t1))
      else gbTail o key default idx sh t1 := by
  unfold getBang
  rw [h] <;> rfl

theorem gbTail_eq {o : KeyOps K} {key : K} {default : Table K V → DR (V × Table K V)} {idx : Int}
    {sh : Nat} {t1 t2 : Table K V} {v : V} (hdef : default t1 = .ok (v, t2)) :
    gbTail o key default idx sh t1 =
      (if (t2.age.val != t1.age.val) = true then keyindex2 o t2 (o.hash key) (o.eq key) >>= gbFin o key v
        else pure (idx, sh, t2) >>= gbFin o key v) := by
  unfold gbTail
  rw [hdef] <;> rfl

theorem gbTail_err {o : KeyOps K} {key : K} {default : Table K V → DR (V × Table K V)} {idx : Int}
    {sh : Nat} {t1 : Table K V} {e : DErr} (hdef : default t1 = .error e) :
    gbTail o key default idx sh t1 = .error e := by
  unfold gbTail
  rw [hdef] <;> rfl

theorem gbFin_pos {o : KeyOps K} {key : K} {v : V} {idx : Int} {sh : Nat} {t : Table K V}
    (h : idx > 0) : gbFin o key v (idx, sh, t) = .ok (v, overwriteAt t v key idx.toNat) := by
  show (if idx > 0 then (pure (v, overwriteAt t v key idx.toNat) : DR (V × Table K V))
    else (setindexAt o t v key (-idx).toNat sh >>= fun t => pure (v, t))) = _
  rw [if_pos h] <;> rfl

theorem gbFin_neg {o : KeyOps K} {key : K} {v : V} {idx : Int} {sh : Nat} {t : Table K V}
    (h : ¬ idx > 0) :
    gbFin o key v (idx, sh, t) = (setindexAt o t v key (-idx).toNat sh >>= fun t => pure (v, t)) := by
  show (if idx > 0 then (pure (v, overwriteAt t v key idx.toNat) : DR (V × Table K V))
    else (setindexAt o t v key (-idx).toNat sh >>= fun t => pure (v, t))) = _
  rw [if_neg h]

/-- Re-probing and storing behaves like `setindex!`. -/
theorem gbFin_k2 {o : KeyOps K} (hl : o.Lawful) {t2 : Table K V} {m' : RMap K V} (h : Rep o t2 m')
    (hc : t2.count < 2 ^ 33) (k : K) (v : V) :
    ∃ t', (keyindex2 o t2 (o.hash k) (o.eq k) >>= gbFin o k v) = .ok (v, t') ∧
      Rep o t' (rset o m' k v) ∧ t'.count ≤ t2.count + 1 := by
  obtain ⟨t', hs, hr, -⟩ := h.setindex hl hc k v
  obtain ⟨idx, t3, -, hk2, -, -⟩ := keyindex2_spec hl h.1 hc k
  have hct : t'.count ≤ t2.count + 1 := by
    rw [hr.count_eq, h.count_eq]
    exact rset_length_le o m' k v
  rw [setindex_of_k2 hk2] at hs
  rw [hk2]
  refine ⟨t', ?_, hr, hct⟩
  show gbFin o k v (idx, shorthash7 (o.hash k), t3) = .ok (v, t')
  by_cases hi : idx > 0
  · rw [if_pos hi] at hs
    have he : overwriteAt t3 v k idx.toNat = t' := Except.ok.inj hs
    rw [gbFin_pos hi, he]
  · rw [if_neg hi] at hs
    rw [gbFin_neg hi, hs] <;> rfl

theorem getBang_found {o : KeyOps K} (hl : o.Lawful) {t : Table K V} {m : RMap K V} (h : Rep o t m)
    (hc : t.count < 2 ^ 33) {k : K} {e : K × V} (hrf : rfind o m k = some e)
    (default : Table K V → DR (V × Table K V)) : getBang o t k default = .ok (e.2, t) := by
  obtain ⟨i, h1, h2, he, hq⟩ := h.find_slot hrf
  obtain ⟨k0, w⟩ := e
  obtain ⟨idx, t1, n1, hk2, hn1, hout⟩ := keyindex2_spec hl h.1 hc k
  obtain ⟨hidx, ht1⟩ := hout.found i (k0, w) h1 h2 he hq
  rw [getBang_of hk2, hidx, ht1, if_pos (by omega), Int.toNat_natCast, valAt_of_ent he] <;> rfl

theorem getBangVal_absent {o : KeyOps K} (hl : o.Lawful) {t : Table K V} {m : RMap K V}
    (h : Rep o t m) (hc : t.count < 2 ^ 33) {k : K} (hrf : rfind o m k = none) (v : V) :
    ∃ t', getBangVal o t k v = .ok (v, t') ∧ Rep o t' (rset o m k v) ∧ t'.count ≤ t.count + 1 ∧
      ∃ n, n ≤ 2 * t.count + 21 ∧ AgeStep t t' n := by
  have habs := h.absent hrf
  obtain ⟨idx, t1, n1, hk2, hn1, hout⟩ := keyindex2_spec hl h.1 hc k
  obtain ⟨hneg, hslot⟩ := hout.absent habs
  have habs1 : Absent o t1 k := fun b hb => habs b (hout.perm.mem_iff.1 hb)
  obtain ⟨t', h1', hi', hp', hc', n2, -, hn2b, hage⟩ :=
    setindexAt_spec hl hout.inv v hslot habs1 (by rw [hout.count]; exact hc)
  have htail : gbTail o k (fun t => pure (v, t)) idx (shorthash7 (o.hash k)) t1 =
      gbFin o k v (idx, shorthash7 (o.hash k), t1) := by
    rw [gbTail_eq (default := fun t => pure (v, t)) (t1 := t1) (t2 := t1) (v := v) rfl,
      bne_self_eq_false, if_neg (by decide), dr_pure_bind]
  have hm : rdel o m k = m := rdel_of_absent fun b hb => habs b (h.2.mem_iff.2 hb)
  unfold getBangVal
  rw [getBang_of hk2, if_neg (by omega), htail, gbFin_neg (by omega), h1']
  refine ⟨t', rfl, ⟨hi', ?_⟩, by have := hout.count; omega, n1 + n2, by omega, hout.age.trans hage⟩
  show List.Perm (tlist t') ((k, v) :: rdel o m k)
  rw [hm]
  exact hp'.trans (List.Perm.cons _ (hout.perm.trans h.2))

/-! ## Each base call -/

/-- The result relation of one call: representation, count growth and `age` step. -/
def StepRel (o : KeyOps K) (t : Table K V) (w B : Nat) (t' : Table K V) (m' : RMap K V) : Prop :=
  Rep o t' m' ∧ t'.count ≤ t.count + w ∧ ∃ n, n ≤ w * B ∧ AgeStep t t' n

section BaseCalls

variable {o : KeyOps K} (hl : o.Lawful) {t : Table K V} {m : RMap K V} (h : Rep o t m) (B : Nat)
include hl h

theorem rb_set (k : K) (v : V) (hc : t.count + 1 ≤ 2 ^ 32) (hB : 2 * (t.count + 1) + 21 ≤ B) :
    SameOutcome (runBase o t (.set k v)) (rbase o m (.set k v)) (StepRel o t 1 B) := by
  have hct := h.count_eq
  obtain ⟨t', h1, hr, n, -, hn, ha⟩ := h.setindex hl (by omega) k v
  show SameOutcome (setindex o t v k) (pure (rset o m k v) : DR (RMap K V)) (StepRel o t 1 B)
  rw [h1]
  have := rset_length_le o m k v
  exact ⟨hr, by rw [hr.count_eq]; omega, n, by omega, ha⟩

theorem rb_del (k : K) (hB : 2 * (t.count + 1) + 21 ≤ B) :
    SameOutcome (runBase o t (.del k)) (rbase o m (.del k)) (StepRel o t 1 B) := by
  have hct := h.count_eq
  obtain ⟨t', h1, hr, n, hn, ha⟩ := h.dictDelete hl k
  show SameOutcome (dictDelete o t k) (pure (rdel o m k) : DR (RMap K V)) (StepRel o t 1 B)
  rw [h1]
  have := rdel_length_le o m k
  exact ⟨hr, by rw [hr.count_eq]; omega, n, by omega, ha⟩

theorem rb_pop (k : K) (hB : 2 * (t.count + 1) + 21 ≤ B) :
    SameOutcome (runBase o t (.pop k)) (rbase o m (.pop k)) (StepRel o t 1 B) := by
  have hct := h.count_eq
  show SameOutcome (popKey o t k >>= fun r => pure r.2)
    (match rfind o m k with
      | some _ => pure (rdel o m k)
      | none => throw .keyError : DR (RMap K V)) (StepRel o t 1 B)
  cases hrf : rfind o m k with
  | some e =>
    obtain ⟨t', h1, hr, ha⟩ := h.popKey_found hl hrf
    rw [h1]
    have := rdel_length_le o m k
    exact ⟨hr, by rw [hr.count_eq]; omega, 1, by omega, ha⟩
  | none =>
    rw [h.popKey_absent hrf]
    rfl

theorem rb_popd (k : K) (d : V) (hB : 2 * (t.count + 1) + 21 ≤ B) :
    SameOutcome (runBase o t (.popd k d)) (rbase o m (.popd k d)) (StepRel o t 1 B) := by
  have hct := h.count_eq
  obtain ⟨t', h1, hr, n, hn, ha⟩ := h.popKeyDefault hl k d
  show SameOutcome (popKeyDefault o t k d >>= fun r => pure r.2) (pure (rdel o m k) : DR (RMap K V))
    (StepRel o t 1 B)
  rw [h1]
  have := rdel_length_le o m k
  exact ⟨hr, by rw [hr.count_eq]; omega, n, by omega, ha⟩

theorem rb_getv (k : K) (v : V) (hc : t.count + 1 ≤ 2 ^ 32) (hB : 2 * (t.count + 1) + 21 ≤ B) :
    SameOutcome (runBase o t (.getv k v)) (rbase o m (.getv k v)) (StepRel o t 1 B) := by
  show SameOutcome (getBangVal o t k v >>= fun r => pure r.2)
    (match rfind o m k with
      | some _ => pure m
      | none => pure (rset o m k v) : DR (RMap K V)) (StepRel o t 1 B)
  cases hrf : rfind o m k with
  | some e =>
    have h1 : getBangVal o t k v = .ok (e.2, t) := getBang_found hl h (by omega) hrf _
    rw [h1]
    exact ⟨h, by show t.count ≤ _; omega, 0, Nat.zero_le _, AgeStep.refl t⟩
  | none =>
    obtain ⟨t', h1, hr, hc2, n, hn, ha⟩ := getBangVal_absent hl h (by omega) hrf v
    rw [h1]
    exact ⟨hr, hc2, n, by omega, ha⟩

theorem rb_hint (hmv : MaxValuesOK o) (n : JInt .i64) (s : Bool) (hn : n.val ≤ 2 ^ 61)
    (hc : t.count + 1 ≤ 2 ^ 32) (hB : 2 * (t.count + 1) + 21 ≤ B) :
    SameOutcome (runBase o t (.hint n s)) (rbase o m (.hint n s)) (StepRel o t 1 B) := by
  obtain ⟨t', h1, hi', hp', hc', k, hk, ha⟩ := sizehint_spec hmv h.1 (by omega) n hn s
  show SameOutcome (sizehint o t n s) (pure m : DR (RMap K V)) (StepRel o t 1 B)
  rw [h1]
  exact ⟨⟨hi', hp'.trans h.2⟩, by omega, k, by omega, ha⟩

theorem rb_empty (hB : 2 * (t.count + 1) + 21 ≤ B) :
    SameOutcome (runBase o t .empty) (rbase o m .empty) (StepRel o t 1 B) := by
  obtain ⟨hr, ha, hc0⟩ := emptyBang_spec h.1
  show SameOutcome (pure (emptyBang t) : DR (Table K V)) (pure [] : DR (RMap K V)) (StepRel o t 1 B)
  exact ⟨hr, by omega, 1, by omega, ha⟩

theorem rb_filter (p : K → V → Bool) (hB : 2 * (t.count + 1) + 21 ≤ B) :
    SameOutcome (runBase o t (.filter p)) (rbase o m (.filter p)) (StepRel o t 1 B) := by
  have hct := h.count_eq
  obtain ⟨t', h1, hi', htl, n, hn, ha⟩ := filterBang_spec hl h.1 p
  show SameOutcome (filterBang t p) (pure (m.filter fun e => p e.1 e.2) : DR (RMap K V))
    (StepRel o t 1 B)
  rw [h1]
  have hp' : List.Perm (tlist t') (m.filter fun e => p e.1 e.2) := by
    rw [htl]
    exact h.2.filter _
  have := List.length_filter_le (fun e : K × V => p e.1 e.2) m
  exact ⟨⟨hi', hp'⟩, by rw [hi'.count, hp'.length_eq]; omega, n, by omega, ha⟩

theorem rb_merge (hmv : MaxValuesOK o) (ps : List (K × V)) (hc : t.count + (1 + ps.length) ≤ 2 ^ 32)
    (hB : 2 * (t.count + (1 + ps.length)) + 21 ≤ B) :
    SameOutcome (runBase o t (.merge ps)) (rbase o m (.merge ps)) (StepRel o t (1 + ps.length) B) := by
  obtain ⟨d2, hb, h2, hc2⟩ := buildDict_spec hl ps (by omega)
  obtain ⟨t', h1, hr, hct', n, hn, ha⟩ := Rep.dictMerge hl hmv h h2 (by omega)
  have e : runBase o t (.merge ps) = .ok t' := by
    show (buildDict o ps >>= fun d2 => dictMerge o t d2) = _
    rw [hb, except_ok_bind, h1]
  rw [e]
  have hmul : (1 + d2.count) * (2 * (t.count + d2.count) + 21) ≤ (1 + ps.length) * B :=
    Nat.mul_le_mul (by omega) (by omega)
  exact ⟨hr, by omega, n, by omega, ha⟩

theorem rb_mergewith (hmv : MaxValuesOK o) (f : V → V → V) (ps : List (K × V))
    (hc : t.count + (1 + ps.length) ≤ 2 ^ 32) (hB : 2 * (t.count + (1 + ps.length)) + 21 ≤ B) :
    SameOutcome (runBase o t (.mergewith f ps)) (rbase o m (.mergewith f ps))
      (StepRel o t (1 + ps.length) B) := by
  obtain ⟨d2, hb, h2, hc2⟩ := buildDict_spec hl ps (by omega)
  obtain ⟨t', h1, hr, hct', n, hn, ha⟩ := Rep.mergewith hl hmv f h h2 (by omega)
  have e : runBase o t (.mergewith f ps) = .ok t' := by
    show (buildDict o ps >>= fun d2 => mergewith o f t d2) = _
    rw [hb, except_ok_bind, h1]
  rw [e]
  have hmul : (1 + d2.count) * (2 * (t.count + d2.count) + 21) ≤ (1 + ps.length) * B :=
    Nat.mul_le_mul (by omega) (by omega)
  exact ⟨hr, by omega, n, by omega, ha⟩

end BaseCalls

theorem runBase_spec {o : KeyOps K} (hl : o.Lawful) (hmv : MaxValuesOK o) {t : Table K V}
    {m : RMap K V} (h : Rep o t m) (b : BaseOp K V) (hs : baseHintSmall b = true) (B : Nat)
    (hc : t.count + baseWeight b ≤ 2 ^ 32) (hB : 2 * (t.count + baseWeight b) + 21 ≤ B) :
    SameOutcome (runBase o t b) (rbase o m b) (StepRel o t (baseWeight b) B) := by
  cases b with
  | set k v => exact rb_set hl h B k v hc hB
  | del k => exact rb_del hl h B k hB
  | pop k => exact rb_pop hl h B k hB
  | popd k d => exact rb_popd hl h B k d hB
  | getv k v => exact rb_getv hl h B k v hc hB
  | hint n s => exact rb_hint hl h B hmv n s (of_decide_eq_true hs) hc hB
  | empty => exact rb_empty hl h B hB
  | filter p => exact rb_filter hl h B p hB
  | merge ps => exact rb_merge hl h B hmv ps hc hB
  | mergewith f ps => exact rb_mergewith hl h B hmv f ps hc hB

theorem runBaseList_spec {o : KeyOps K} (hl : o.Lawful) (hmv : MaxValuesOK o) (B : Nat) :
    ∀ (l : List (BaseOp K V)) (t : Table K V) (m : RMap K V), Rep o t m →
      l.all baseHintSmall = true → t.count + baseListWeight l ≤ 2 ^ 32 →
      2 * (t.count + baseListWeight l) + 21 ≤ B →
      SameOutcome (runBaseList o t l) (rbaseList o m l) (StepRel o t (baseListWeight l) B)
  | [], t, _, h, _, _, _ => ⟨h, Nat.le_add_right _ _, 0, Nat.zero_le _, AgeStep.refl t⟩
  | b :: l, t, m, h, hs, hc, hB => by
    have hw : baseListWeight (b :: l) = baseWeight b + baseListWeight l := rfl
    rw [hw] at hc hB ⊢
    simp only [List.all_cons, Bool.and_eq_true] at hs
    have hb := runBase_spec hl hmv h b hs.1 B (by omega) (by omega)
    show SameOutcome (runBase o t b >>= fun t1 => runBaseList o t1 l)
      (rbase o m b >>= fun m1 => rbaseList o m1 l) _
    revert hb
    cases runBase o t b with
    | error e1 =>
      cases rbase o m b with
      | error e2 => exact fun hb => hb
      | ok _ => exact fun hb => False.elim hb
    | ok t1 =>
      cases rbase o m b with
      | error _ => exact fun hb => False.elim hb
      | ok m1 =>
        intro hb
        obtain ⟨hr1, hc1, n1, hn1, ha1⟩ := hb
        have ih := runBaseList_spec hl hmv B l t1 m1 hr1 hs.2 (by omega) (by omega)
        show SameOutcome (runBaseList o t1 l) (rbaseList o m1 l) _
        refine ih.mono fun t2 m2 hs2 => ?_
        obtain ⟨hr2, hc2, n2, hn2, ha2⟩ := hs2
        refine ⟨hr2, by omega, n1 + n2, ?_, ha1.trans ha2⟩
        rw [Nat.add_mul]
        omega

/-! ## `get!` with a mutating default -/

theorem innerDefault_eq (o : KeyOps K) (v : V) (inner : List (BaseOp K V)) (t : Table K V) :
    innerDefault o v inner t = (runBaseList o t inner >>= fun t => pure (v, t)) := rfl

theorem getBang_inner {o : KeyOps K} (hl : o.Lawful) (hmv : MaxValuesOK o) {t : Table K V}
    {m : RMap K V} (h : Rep o t m) (k : K) (v : V) (inner : List (BaseOp K V))
    (hs : inner.all baseHintSmall = true) (hc : t.count + baseListWeight inner ≤ 2 ^ 31)
    (hW : baseListWeight inner ≤ 2 ^ 30) (hrf : rfind o m k = none) :
    SameOutcome (getBang o t k (innerDefault o v inner)) (rbaseList o m inner)
      (fun r m' => r.1 = v ∧ Rep o r.2 (rset o m' k v) ∧
        r.2.count ≤ t.count + baseListWeight inner + 1) := by
  have habs := h.absent hrf
  obtain ⟨idx, t1, n1, hk2, hn1, hout⟩ := keyindex2_spec hl h.1 (by omega) k
  obtain ⟨hneg, hslot⟩ := hout.absent habs
  have habs1 : Absent o t1 k := fun b hb => habs b (hout.perm.mem_iff.1 hb)
  have hr1 : Rep o t1 m := ⟨hout.inv, hout.perm.trans h.2⟩
  have hc1 : t1.count = t.count := hout.count
  rw [getBang_of hk2, if_neg (by omega)]
  have hb := runBaseList_spec hl hmv (2 * (t.count + baseListWeight inner) + 21) inner t1 m hr1 hs
    (by omega) (by omega)
  revert hb
  cases hrun : runBaseList o t1 inner with
  | error e1 =>
    have hdef : innerDefault o v inner t1 = .error e1 := by rw [innerDefault_eq, hrun] <;> rfl
    rw [gbTail_err hdef]
    cases rbaseList o m inner with
    | error e2 => exact fun hb => hb
    | ok _ => exact fun hb => False.elim hb
  | ok t2 =>
    have hdef : innerDefault o v inner t1 = .ok (v, t2) := by rw [innerDefault_eq, hrun] <;> rfl
    rw [gbTail_eq hdef]
    cases rbaseList o m inner with
    | error _ => exact fun hb => False.elim hb
    | ok m' =>
      intro hb
      obtain ⟨hr2, hc2, N, hN, ha⟩ := hb
      by_cases hN0 : N = 0
      · -- nothing changed the slots: the old insertion slot is still free
        obtain ⟨hsz, hsl, hky, hmpl⟩ := ha.2 hN0
        have hage : t2.age = t1.age := by rw [ha.1, hN0, ageAdd_zero]
        have hbne : (t2.age.val != t1.age.val) = false := by simp [hage]
        rw [hbne, if_neg (by decide)]
        rw [dr_pure_bind]
        rw [gbFin_neg (by omega)]
        have hpow : IsPow t1.size := by
          rcases hout.inv.size with h0 | h0
          · have := hslot.2.1; have := hslot.1; omega
          · exact h0
        have hmp : t1.maxprobe < t1.size := by
          rcases hout.inv.maxprobe with h0 | h0
          · have := hslot.2.1; have := hslot.1; omega
          · exact h0
        have hslot2 : InsertSlot o t2 k (-idx).toNat :=
          ⟨hslot.1, by rw [hsz]; exact hslot.2.1, by rw [hsl]; exact hslot.2.2.1,
            Chain.mono (t := t1) hpow hmp hsz hmpl (fun p _ _ hp => by rw [hsl]; exact hp)
              hslot.2.2.2⟩
        have habs2 : Absent o t2 k := by
          intro e he
          obtain ⟨p, hp1, hp2, hpe⟩ := mem_tlist.1 he
          obtain ⟨hf, hk, -⟩ := ent_some hpe
          rw [hsl] at hf
          rw [hky] at hk
          rw [hsz] at hp2
          obtain ⟨k', v', hk', -, he', -, -⟩ := hout.inv.filled hp1 hp2 hf
          rw [hk] at hk'
          cases hk'
          exact habs1 (e.1, v') (mem_tlist.2 ⟨p, hp1, hp2, he'⟩)
        obtain ⟨t', h1', hi', hp', hc', -⟩ :=
          setindexAt_spec hl hr2.1 v hslot2 habs2 (by omega)
        rw [h1']
        have hm : rdel o m' k = m' := rdel_of_absent fun b hb => habs2 b (hr2.2.mem_iff.2 hb)
        refine ⟨rfl, ⟨hi', ?_⟩, by show t'.count ≤ _; omega⟩
        show List.Perm (tlist t') ((k, v) :: rdel o m' k)
        rw [hm]
        exact hp'.trans (List.Perm.cons _ hr2.2)
      · -- `age` moved by `0 < N < 2^64`, so the table is probed again
        have hB : 2 * (t.count + baseListWeight inner) + 21 ≤ 2 ^ 32 + 21 := by omega
        have hmul : baseListWeight inner * (2 * (t.count + baseListWeight inner) + 21) ≤
            2 ^ 30 * (2 ^ 32 + 21) := Nat.mul_le_mul hW hB
        have hne := ageAdd_ne t1.age (n := N) (by omega) (by omega)
        rw [← ha.1] at hne
        have hbne : (t2.age.val != t1.age.val) = true := by simp [hne]
        rw [hbne, if_pos rfl]
        obtain ⟨t', h1', hr', hc'⟩ := gbFin_k2 hl hr2 (by omega) k v
        rw [h1']
        exact ⟨rfl, hr', by show t'.count ≤ _; omega⟩

end JuliaLean.Dicts
