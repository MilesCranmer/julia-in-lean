import JuliaLean.DictsCov.DictProps

/-! Proofs of the `Dict` properties of `DictProps.lean`. -/

namespace JuliaLean.DictsCov

open JuliaLean.Dicts

variable {K V Q W : Type}

theorem bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    ((Except.ok a : Except ε α) >>= f) = f a := rfl

theorem bind_err {ε α β : Type} (e : ε) (f : α → Except ε β) :
    ((Except.error e : Except ε α) >>= f) = .error e := rfl

/-! ## Constructors -/

theorem empty_agrees {o : KeyOps K} (hl : o.Lawful) : Agrees o (Table.empty : Table K V) [] :=
  Rep.agrees hl (empty_rep o)

theorem hint_empty {o : KeyOps K} (hmv : MaxValuesOK o) (n : Nat) (hn : n ≤ 2 ^ 30)
    (shrink : Bool) :
    ∃ t', sizehint o (Table.empty : Table K V) (JInt.lit .i64 (n : Int)) shrink = .ok t' ∧
      Rep o t' [] ∧ t'.count = 0 := by
  have hi : Inv o (Table.empty : Table K V) := (empty_rep o).1
  have hv : (JInt.lit .i64 (n : Int)).val = n := lit_i64_val (by omega) (by omega)
  obtain ⟨t', h1, hI, hp, hc, -⟩ :=
    sizehint_spec hmv hi (Nat.zero_le _) (JInt.lit .i64 (n : Int)) (by rw [hv]; omega) shrink
  exact ⟨t', h1, ⟨hI, hp.trans (empty_rep o).2⟩, hc⟩

theorem dictKV_spec {o : KeyOps K} (hl : o.Lawful) (hmv : MaxValuesOK o) (kv : List (K × V))
    (hasLen : Bool) (hkv : kv.length ≤ 2 ^ 30) :
    ∃ t, dictKV o hasLen kv = .ok t ∧ Agrees o t (rbuild o kv) := by
  cases hasLen with
  | false =>
    obtain ⟨t', h1, h2, -⟩ := Rep.setFold hl (2 * (0 + kv.length) + 21) kv Table.empty []
      (empty_rep o) (by show 0 + kv.length ≤ 2 ^ 32; omega) (Nat.le_refl _)
    exact ⟨t', h1, Rep.agrees hl h2⟩
  | true =>
    obtain ⟨t0, h0, hr0, hc0⟩ := hint_empty (V := V) hmv kv.length hkv true
    obtain ⟨t', h1, h2, -⟩ := Rep.setFold hl (2 * (t0.count + kv.length) + 21) kv t0 []
      hr0 (by rw [hc0]; omega) (Nat.le_refl _)
    refine ⟨t', ?_, Rep.agrees hl h2⟩
    show (sizehint o (Table.empty : Table K V) (JInt.lit .i64 (kv.length : Int)) true >>= fun h =>
      kv.foldlM (fun h p => setindex o h p.2 p.1) h) = _
    rw [h0, bind_ok]
    exact h1

theorem dictConstructSpec_proven : DictConstructSpec := by
  intro K V o hl hmv
  refine ⟨empty_agrees hl, empty_agrees hl, fun t m hR => Rep.agrees hl (hR.rep hl hmv).1,
    fun _ _ _ _ _ _ _ _ _ _ => rfl, fun kv hasLen hkv => dictKV_spec hl hmv kv hasLen hkv,
    fun p => ?_, fun ps hps => dictKV_spec hl hmv ps true hps,
    fun ps hps => dictKV_spec hl hmv ps true hps⟩
  obtain ⟨k, v⟩ := p
  obtain ⟨t', h1, hr, -⟩ := (empty_rep o).setindex hl (by show (0 : Nat) < 2 ^ 33; decide) k v
  exact ⟨t', h1, Rep.agrees hl hr⟩

/-! ## Slot bytes -/

theorem lor_small : ∀ x, x < 128 → Nat.lor x 128 = x + 128 := by decide +kernel

theorem bytes_spec : ∀ b, b < 256 → ((isEmptyB b = true ↔ b = 0) ∧ (isMissingB b = true ↔ b = 127) ∧
    (isFilledB b = true ↔ 128 ≤ b)) := by decide +kernel

theorem shorthash7_eq (h : JInt .u64) : shorthash7 h = 128 + h.val.toNat / 2 ^ 57 := by
  have hr := u64_val_range h
  have h64 : h.val.toNat < 2 ^ 57 * 128 := by omega
  have hx : h.val.toNat / 2 ^ 57 < 128 := Nat.div_lt_of_lt_mul h64
  unfold shorthash7
  rw [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega), lor_small _ hx]
  omega

theorem dictSlotSpec_proven : DictSlotSpec := by
  refine ⟨fun h => ⟨shorthash7_filled h, shorthash7_eq h⟩, fun h p hp1 hp2 => ?_, bytes_spec⟩
  have hpow : IsPow (2 ^ p) := ⟨p, hp1, rfl⟩
  exact ⟨hashindex_fst hpow h, rfl, hashindex_range hpow h⟩

/-! ## Probing -/

theorem dictKeyindexSpec_proven : DictKeyindexSpec := by
  intro K V o hl hmv t m hR
  obtain ⟨h, hc⟩ := hR.rep hl hmv
  refine ⟨fun Q c hq q => Rep.keyindexQ hl hq h q, fun q => ?_, fun q v hrf => ?_⟩
  · obtain ⟨idx, t', n, hk2, -, hout⟩ := keyindex2_spec hl h.1 (by omega) q
    refine ⟨idx, t', n, hk2, ?_, hout⟩
    unfold keyindex2Bang
    rw [hk2]
    rfl
  · obtain ⟨idx, t1, n1, hk2, -, hout⟩ := keyindex2_spec hl h.1 (by omega) q
    have habs := h.absent hrf
    obtain ⟨hneg, hslot⟩ := hout.absent habs
    have habs1 : Absent o t1 q := fun b hb => habs b (hout.perm.mem_iff.1 hb)
    obtain ⟨t', h1', hi', hp', -, -⟩ :=
      setindexAt_spec hl hout.inv v hslot habs1 (by rw [hout.count]; omega)
    have hm : rdel o m q = m := rdel_of_absent fun b hb => habs b (h.2.mem_iff.2 hb)
    refine ⟨idx, t1, t', ?_, hneg, h1', Rep.agrees hl ⟨hi', ?_⟩⟩
    · unfold keyindex2Bang
      rw [hk2]
      rfl
    · show List.Perm (tlist t') ((q, v) :: rdel o m q)
      rw [hm]
      exact hp'.trans (List.Perm.cons _ (hout.perm.trans h.2))

/-! ## Conversion -/

theorem convKey_some (c : Conv Q K) (key0 : Q) (k : K) (h : c.isa key0 = some k) :
    convKey c key0 = .ok k := by
  unfold convKey
  rw [h]
  rfl

theorem convKey_err (c : Conv Q K) (key0 : Q) (e : DErr) (h : c.isa key0 = none)
    (h2 : c.convert key0 = .error e) : convKey c key0 = .error e := by
  unfold convKey
  rw [h, h2]
  rfl

theorem convKey_ok (c : Conv Q K) (key0 : Q) (k : K) (h : c.isa key0 = none)
    (h2 : c.convert key0 = .ok k) :
    convKey c key0 = if c.iseq key0 k then .ok k else .error .keyTypeError := by
  unfold convKey
  rw [h, h2]
  rfl

theorem setindexV_eq (o : KeyOps K) (cv : VConv W V) (t : Table K V) (v0 : W) (key : K) :
    setindexV o cv t v0 key = (convV cv v0 >>= fun v => setindex o t v key) := rfl

theorem dictSetindexSpec_proven : DictSetindexSpec := by
  intro K V Q W o c cv hl hmv t m hR
  obtain ⟨h, hc⟩ := hR.rep hl hmv
  refine ⟨fun v0 key => ?_, fun v key => ?_, fun v0 key0 => ?_⟩
  · cases hcv : convV cv v0 with
    | ok v =>
      obtain ⟨t', h1, hr, -⟩ := h.setindex hl (by omega) key v
      exact ⟨t', by rw [setindexV_eq, hcv, bind_ok]; exact h1, Rep.agrees hl hr⟩
    | error e =>
      show setindexV o cv t v0 key = .error e
      rw [setindexV_eq, hcv, bind_err]
  · obtain ⟨t', h1, hr, -⟩ := h.setindex hl (by omega) key v
    exact ⟨t', h1, Rep.agrees hl hr⟩
  · have e0 : setindexConvV o c cv t v0 key0 =
        (convKey c key0 >>= fun key => setindexV o cv t v0 key) := rfl
    cases hi : c.isa key0 with
    | some k =>
      rw [convKey_some c key0 k hi]
      exact ⟨by rw [e0, convKey_some c key0 k hi, bind_ok], fun h0 => by cases h0⟩
    | none =>
      cases hcv : c.convert key0 with
      | error e =>
        rw [convKey_err c key0 e hi hcv]
        exact ⟨by rw [e0, convKey_err c key0 e hi hcv, bind_err], rfl, Or.inl rfl⟩
      | ok k =>
        cases hq : c.iseq key0 k with
        | false =>
          have e1 : convKey c key0 = .error .keyTypeError := by rw [convKey_ok c key0 k hi hcv, hq]; rfl
          rw [e1]
          exact ⟨by rw [e0, e1, bind_err], rfl, Or.inr ⟨rfl, k, rfl, hq⟩⟩
        | true =>
          have e1 : convKey c key0 = .ok k := by rw [convKey_ok c key0 k hi hcv, hq]; rfl
          rw [e1]
          exact ⟨by rw [e0, e1, bind_ok], fun _ => ⟨rfl, hq⟩⟩

/-! ## `get!` -/

theorem dictGetBangSpec_proven : DictGetBangSpec := by
  intro K V Q W o c cv hl hmv t m hR
  obtain ⟨h, hc⟩ := hR.rep hl hmv
  refine ⟨fun key w => ?_, fun key0 default => ?_⟩
  · cases hrf : rfind o m key with
    | some e =>
      exact ⟨t, getBang_found hl h (by omega) hrf _, Rep.agrees hl h⟩
    | none =>
      cases hcv : convV cv w with
      | ok v =>
        have e1 : getBangV o cv t key (fun t => pure (w, t)) = getBangVal o t key v := by
          unfold getBangV getBangVal
          congr 1
          funext t1
          show (convV cv w >>= fun v => pure (v, t1)) = _
          rw [hcv]
          rfl
        obtain ⟨t', h1, hr, -⟩ := getBangVal_absent hl h (by omega) hrf v
        exact ⟨t', by rw [e1]; exact h1, Rep.agrees hl hr⟩
      | error e =>
        obtain ⟨idx, t1, n1, hk2, -, hout⟩ := keyindex2_spec hl h.1 (by omega) key
        obtain ⟨hneg, -⟩ := hout.absent (h.absent hrf)
        show getBang o t key _ = .error e
        rw [getBang_of hk2, if_neg (by omega)]
        exact gbTail_err (by show (convV cv w >>= fun v => pure (v, t1)) = .error e; rw [hcv]; rfl)
  · have e0 : getBangConv o c cv t key0 default =
        (convKey c key0 >>= fun key => getBangV o cv t key default) := rfl
    cases hk : convKey c key0 with
    | ok key => rw [e0, hk, bind_ok]
    | error e => rw [e0, hk, bind_err]

/-! ## Lookups -/

theorem getindexQ_of {c : Conv Q K} {t : Table K V} {q : Q} {idx : Int}
    (h : htKeyindex t (c.hash q) (c.iseq q) = .ok idx) :
    getindexQ c t q = if idx < 0 then .error .keyError else valAt t idx.toNat := by
  unfold getindexQ; rw [h]; rfl

theorem getQ_of {c : Conv Q K} {t : Table K V} {q : Q} {idx : Int} (d : V)
    (h : htKeyindex t (c.hash q) (c.iseq q) = .ok idx) :
    getQ c t q d = if idx < 0 then .ok d else valAt t idx.toNat := by
  unfold getQ; rw [h]; rfl

theorem getFQ_of {c : Conv Q K} {t : Table K V} {q : Q} {idx : Int} (f : Unit → DR V)
    (h : htKeyindex t (c.hash q) (c.iseq q) = .ok idx) :
    getFQ c t q f = if idx < 0 then f () else valAt t idx.toNat := by
  unfold getFQ; rw [h]; rfl

theorem haskeyQ_of {c : Conv Q K} {t : Table K V} {q : Q} {idx : Int}
    (h : htKeyindex t (c.hash q) (c.iseq q) = .ok idx) :
    haskeyQ c t q = .ok (decide (idx ≥ 0)) ∧ inKeySetQ c t q = .ok (decide (idx ≥ 0)) := by
  unfold haskeyQ inKeySetQ; rw [h]; exact ⟨rfl, rfl⟩

theorem getkeyQ_of {c : Conv Q K} {t : Table K V} {q : Q} {idx : Int} (d : K)
    (h : htKeyindex t (c.hash q) (c.iseq q) = .ok idx) :
    getkeyQ c t q d = if idx < 0 then .ok d else keyAt t idx.toNat := by
  unfold getkeyQ; rw [h]; rfl

theorem keyAt_of_ent {t : Table K V} {i : Nat} {k : K} {v : V} (he : ent t i = some (k, v)) :
    keyAt t i = .ok k := by
  unfold keyAt
  rw [(ent_some he).2.1]
  rfl

theorem dictLookupSpec_proven : DictLookupSpec := by
  intro K V Q o c hl hmv hq t m hR q dflt f kd
  have h := (hR.rep hl hmv).1
  have hk := Rep.keyindexQ hl hq h q
  revert hk
  cases hf : rfindQ c m q with
  | none =>
    intro hk
    have hh := haskeyQ_of hk
    refine ⟨by rw [getindexQ_of hk]; rfl, by rw [getQ_of dflt hk]; rfl, by rw [getFQ_of f hk]; rfl,
      by rw [hh.1]; rfl, by rw [hh.2]; rfl, by rw [getkeyQ_of kd hk]; rfl⟩
  | some e =>
    intro hk
    obtain ⟨i, hk, h1, h2, he⟩ := hk
    obtain ⟨k, v⟩ := e
    have hh := haskeyQ_of hk
    have hnn : ¬ ((i : Int) < 0) := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [getindexQ_of hk, if_neg hnn, Int.toNat_natCast, valAt_of_ent he]
    · rw [getQ_of dflt hk, if_neg hnn, Int.toNat_natCast, valAt_of_ent he]
    · rw [getFQ_of f hk, if_neg hnn, Int.toNat_natCast, valAt_of_ent he]
    · rw [hh.1]; simp
    · rw [hh.2]; simp
    · rw [getkeyQ_of kd hk, if_neg hnn, Int.toNat_natCast, keyAt_of_ent he]

/-! ## `pop!` and `delete!` -/

theorem popQ_of {c : Conv Q K} {t : Table K V} {q : Q} {idx : Int}
    (h : htKeyindex t (c.hash q) (c.iseq q) = .ok idx) :
    popQ c t q = if idx > 0 then popAt t idx.toNat else .error .keyError := by
  unfold popQ; rw [h]; rfl

theorem popDefaultQ_of {c : Conv Q K} {t : Table K V} {q : Q} {idx : Int} (d : V)
    (h : htKeyindex t (c.hash q) (c.iseq q) = .ok idx) :
    popDefaultQ c t q d = if idx > 0 then popAt t idx.toNat else .ok (d, t) := by
  unfold popDefaultQ; rw [h]; rfl

theorem deleteQ_of {c : Conv Q K} {t : Table K V} {q : Q} {idx : Int}
    (h : htKeyindex t (c.hash q) (c.iseq q) = .ok idx) :
    deleteQ c t q = if idx > 0 then .ok (deleteAt t idx.toNat) else .ok t := by
  unfold deleteQ; rw [h]; rfl

theorem popAt_of_ent {t : Table K V} {i : Nat} {e : K × V} (he : ent t i = some e) :
    popAt t i = .ok (e.2, deleteAt t i) := by
  obtain ⟨k, v⟩ := e
  unfold popAt
  rw [valAt_of_ent he]
  rfl

theorem dictPopSpec_proven : DictPopSpec := by
  intro K V Q o c hl hmv hq t m hR
  have h := (hR.rep hl hmv).1
  have hdel : ∀ (i : Nat) (e : K × V), 1 ≤ i → i ≤ t.size → ent t i = some e →
      Agrees o (deleteAt t i) (rdel o m e.1) ∧ popAt t i = .ok (e.2, deleteAt t i) :=
    fun i e h1 h2 he => ⟨Rep.agrees hl (h.deleteAt hl h1 h2 he (hl.refl e.1)).1, popAt_of_ent he⟩
  refine ⟨fun q dflt => ?_, hdel⟩
  have hk := Rep.keyindexQ hl hq h q
  revert hk
  cases hf : rfindQ c m q with
  | none =>
    intro hk
    refine ⟨?_, ?_, ?_⟩
    · rw [popQ_of hk]; rfl
    · rw [popDefaultQ_of dflt hk]; rfl
    · rw [deleteQ_of hk]; rfl
  | some e =>
    intro hk
    obtain ⟨i, hk, h1, h2, he⟩ := hk
    have hpos : (i : Int) > 0 := by omega
    obtain ⟨ha, hp⟩ := hdel i e h1 h2 he
    refine ⟨⟨deleteAt t i, ?_, ha⟩, ⟨deleteAt t i, ?_, ha⟩, ⟨deleteAt t i, ?_, ha⟩⟩
    · rw [popQ_of hk, if_pos hpos, Int.toNat_natCast, hp]
    · rw [popDefaultQ_of dflt hk, if_pos hpos, Int.toNat_natCast, hp]
    · rw [deleteQ_of hk, if_pos hpos, Int.toNat_natCast]

end JuliaLean.DictsCov
