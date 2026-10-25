import JuliaLean.Serialization.Leaves

/-!
Module references, `NamedTuple` names, `Tuple` types and the type data of
`Base.RefValue{Any}`, `UnitRange{Int64}` and `NamedTuple`s.
-/

namespace JuliaLean.Serialization

open JuliaLean

/-! ### Serializer steps -/

/-- A serializer step keeps the table well formed and extends it. -/
def Grows (es es' : ES) : Prop := Inv es → Inv es' ∧ Pres es es'

theorem grows_refl (es : ES) : Grows es es := fun h => ⟨h, pres_refl es⟩

theorem grows_trans {a b c : ES} (h1 : Grows a b) (h2 : Grows b c) : Grows a c := fun h => by
  obtain ⟨i1, p1⟩ := h1 h
  obtain ⟨i2, p2⟩ := h2 i1
  exact ⟨i2, pres_trans p1 p2⟩

theorem grows_register (es : ES) (key : Key) : Grows es (es.register key) :=
  fun h => ⟨inv_register h key, pres_register h key⟩

theorem serSym_grows (es : ES) (name : Bytes) : Grows es (serSym es name).2 := by
  unfold serSym
  cases sertagSym name with
  | some t => exact grows_refl es
  | none =>
    simp only
    split
    · cases es.tab.lookup (.sym name) with
      | some k => exact grows_refl es
      | none => exact grows_register es _
    · exact grows_refl es

theorem serModule_snd (es : ES) (name : Bytes) : (serModule es name).2 = (serSym es name).2 := rfl

theorem serSyms_grows : ∀ (es : ES) (ns : List Bytes), Grows es (serSyms es ns).2
  | es, [] => grows_refl es
  | es, n :: ns => grows_trans (serSym_grows es n) (serSyms_grows _ ns)

theorem serNames_grows (es : ES) (ns : List Bytes) : Grows es (serNames es ns).2 := by
  unfold serNames
  split
  · exact grows_refl es
  · exact serSyms_grows es ns

theorem serTypeData_grows (es : ES) (T : Ty) (name modName : Bytes) (np : Nat)
    (params : ES → Bytes × ES) (hp : ∀ e, Grows e (params e).2) :
    Grows es (serTypeData es T name modName np params).2 := by
  unfold serTypeData
  cases es.tab.lookup (.ty T) with
  | some k => exact grows_refl es
  | none =>
    simp only
    exact grows_trans (grows_register es _) (grows_trans (serSym_grows _ name)
      (grows_trans (by rw [serModule_snd]; exact serSym_grows _ modName) (hp _)))

theorem serTupleType_grows (es : ES) (fts : List Nat) : Grows es (serTupleType es fts).2 := by
  unfold serTupleType
  split
  · exact grows_refl es
  · exact serTypeData_grows _ _ _ _ _ _ (fun e => grows_refl e)

/-! ### Modules -/

theorem symOfTag_base : symOfTag 158 = nameBase := rfl
theorem symOfTag_core : symOfTag 155 = nameCore := rfl

theorem Dec.symTag {f t : Nat} (h1 : 79 ≤ t) (h2 : t ≤ 165) (E : List Nat) (es : ES) :
    Dec (Serialization.deser (f + 1)) E es [UInt8.ofNat t] (.v (.sym (symOfTag t))) E es := by
  refine Dec.deserTag (by omega) ?_
  rw [handle_value f t (by omega)]
  refine Dec.desertag ?_
  rw [desertag_eq]
  simp only [show ¬ (t = 0) from by omega, show ¬ (t < 68) from by omega,
    show ¬ (t = 68) from by omega, show ¬ (t = 74) from by omega,
    show ¬ (t < 76) from by omega, show ¬ (t = 76) from by omega,
    show ¬ (t = 77) from by omega, show ¬ (t = 78) from by omega,
    show (t < 190) from by omega, ↓reduceIte]

theorem Dec.emptyTuple {f : Nat} (E : List Nat) (es : ES) :
    Dec (Serialization.deser (f + 1)) E es [UInt8.ofNat EMPTYTUPLE_TAG] (.v (.tup [])) E es := by
  refine Dec.deserTag (by decide) ?_
  rw [handle_value f _ (by decide)]
  exact Dec.desertag (by rw [desertag_eq]; rfl)

/-- The bytes of a reference to `Base` or `Core`. -/
theorem serModule_eq (es : ES) (name : Bytes) (t : Nat) (h : sertagSym name = some t) :
    serModule es name = (UInt8.ofNat MODULE_TAG :: UInt8.ofNat NOTHING_TAG :: writeAsTag t ++
      [UInt8.ofNat EMPTYTUPLE_TAG], es) := by
  simp [serModule, serSym, h]

theorem Dec.module {f : Nat} {name : Bytes} {m : Md} {t : Nat} (ht : sertagSym name = some t)
    (hm : rootModule name = Pure.pure m) (E : List Nat) (es : ES) :
    Dec (Serialization.deser (f + 2)) E es (serModule es name).1 (.md m) E (serModule es name).2 := by
  obtain ⟨h1, h2, h3⟩ := sertagSym_spec ht
  rw [serModule_eq es name t ht]
  simp only [writeAsTag, VALUE_TAGS, show ¬ (t < 68) from by omega, ↓reduceIte]
  refine Dec.deserTag (by decide) ?_
  rw [handle_module]
  unfold deserModule
  refine Dec.bind (Dec.nothing (f := f) E es) ?_ rfl
  try dsimp only
  refine Dec.bind (Dec.symTag (f := f) h1 h2 E es) ?_ rfl
  try dsimp only
  rw [h3]
  refine Dec.bind (b1 := []) (Dec.pure _ E es) ?_ rfl
  rw [hm]
  refine Dec.bind (b1 := []) (Dec.pure _ E es) ?_ rfl
  refine Dec.bind (Dec.emptyTuple (f := f) E es) ?_ rfl
  exact Dec.pure _ E es

theorem Dec.moduleBase {f : Nat} (E : List Nat) (es : ES) :
    Dec (Serialization.deser (f + 2)) E es (serModule es nameBase).1 (.md .base) E
      (serModule es nameBase).2 :=
  Dec.module (t := 158) rfl rfl E es

theorem Dec.moduleCore {f : Nat} (E : List Nat) (es : ES) :
    Dec (Serialization.deser (f + 2)) E es (serModule es nameCore).1 (.md .core) E
      (serModule es nameCore).2 :=
  Dec.module (t := 155) rfl rfl E es

/-! ### Fuel -/

theorem Dec.fuel {f K : Nat} {E E' : List Nat} {es es' : ES} {bs : Bytes} {a : Obj}
    (h : ∀ g, Dec (Serialization.deser (g + K)) E es bs a E' es') (hf : K ≤ f) :
    Dec (Serialization.deser f) E es bs a E' es' := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + K := ⟨f - K, by omega⟩
  exact h g

/-! ### Lists -/

theorem Dec.readMany_nil {α : Type} (d : Dm α) (E : List Nat) (es : ES) :
    Dec (Serialization.readMany d 0) E es [] [] E es := Dec.pure _ E es

theorem Dec.readMany_cons {α : Type} {d : Dm α} {n : Nat} {E : List Nat} {es es1 es2 : ES}
    {b1 b2 : Bytes} {x : α} {xs : List α}
    (h1 : Dec d E es b1 x E es1) (h2 : Dec (Serialization.readMany d n) E es1 b2 xs E es2) :
    Dec (Serialization.readMany d (n + 1)) E es (b1 ++ b2) (x :: xs) E es2 := by
  show Dec (d >>= fun x => Serialization.readMany d n >>= fun xs => Pure.pure (x :: xs)) _ _ _ _ _ _
  exact Dec.bind h1 (Dec.bind (b2 := []) h2 (Dec.pure _ _ _) (by simp)) rfl

/-- A nested `deserialize(s)` whose result is used as a value. -/
theorem Dec.asV {f : Nat} {E E' : List Nat} {es es' : ES} {bs : Bytes} {x : V}
    (h : Dec (Serialization.deser f) E es bs (.v x) E' es') :
    Dec (do let o ← Serialization.deser f; Serialization.asV o) E es bs x E' es' :=
  Dec.bind (b2 := []) h (Dec.pure _ _ _) (by simp)

/-! ### Symbols in sequence -/

theorem emitBackref_ne (k : Nat) : 1 ≤ (emitBackref k).length := by
  unfold emitBackref
  split
  · simp
  · split <;> simp

theorem serSym_length_pos (es : ES) (n : Bytes) : 1 ≤ (serSym es n).1.length := by
  unfold serSym
  cases sertagSym n with
  | some t => simp only [writeAsTag]; split <;> simp
  | none =>
    simp only
    split
    · cases es.tab.lookup (.sym n) with
      | some k => exact emitBackref_ne k
      | none => simp only; split <;> simp
    · simp only; split <;> simp

/-- Pending slots never hold symbols, and lie below the counter. -/
def PendOK (E : List Nat) (es : ES) : Prop :=
  ∀ p ∈ E, p < es.counter ∧ ∀ n, encTable es p ≠ some (.sym n)

theorem PendOK.mono {E : List Nat} {es es' : ES} (h : PendOK E es) (hp : Pres es es') :
    PendOK E es' := fun p hp' => by
  obtain ⟨h1, h2⟩ := h p hp'
  exact ⟨Nat.lt_of_lt_of_le h1 hp.1, fun n => by rw [hp.2 p h1]; exact h2 n⟩

theorem Dec.symF {f : Nat} {name : Bytes} {E : List Nat} {es : ES} (hinv : Inv es)
    (h63 : es.counter ≤ 2 ^ 63) (hw : SymWF name) (hP : PendOK E es)
    (hf : (serSym es name).1.length ≤ f) :
    Dec (Serialization.deser f) E es (serSym es name).1 (.v (.sym name)) E (serSym es name).2 :=
  Dec.fuel (K := 1) (fun _ => Dec.sym hinv h63 hw (fun p hp => (hP p hp).2 name))
    (Nat.le_trans (serSym_length_pos es name) hf)

theorem Dec.syms : ∀ (ns : List Bytes) (f : Nat) (E : List Nat) (es : ES), Inv es →
    (serSyms es ns).2.counter ≤ 2 ^ 63 → (∀ n ∈ ns, SymWF n) → PendOK E es →
    (serSyms es ns).1.length ≤ f →
    Dec (Serialization.readMany (do let o ← Serialization.deser f; Serialization.asV o) ns.length)
      E es (serSyms es ns).1 (ns.map .sym) E (serSyms es ns).2
  | [], f, E, es, _, _, _, _, _ => Dec.readMany_nil _ E es
  | n :: ns, f, E, es, hinv, h63, hw, hP, hf => by
    obtain ⟨i1, p1⟩ := serSym_grows es n hinv
    obtain ⟨_, p2⟩ := serSyms_grows (serSym es n).2 ns i1
    simp only [serSyms, List.map_cons, List.length_cons]
    simp only [serSyms, List.length_append] at hf h63
    refine Dec.readMany_cons (Dec.asV (Dec.symF hinv ?_ (hw n (by simp)) hP (by omega)))
      (Dec.syms ns f E _ i1 h63 (fun m hm => hw m (by simp [hm])) (hP.mono p1) (by omega))
    have := p1.1; have := p2.1
    omega

/-! ### `NamedTuple` names -/

theorem symsOf_map : ∀ ns : List Bytes, symsOf (ns.map .sym) = some ns
  | [] => rfl
  | n :: ns => by simp [symsOf, symsOf_map ns]

theorem asNames_map (ns : List Bytes) :
    asNames (.v (.tup (ns.map .sym))) = Pure.pure ns := by
  simp [asNames, symsOf_map]

theorem serNames_ne (es : ES) (ns : List Bytes) (h : ns ≠ []) :
    serNames es ns = ((if ns.length ≤ 255 then [UInt8.ofNat TUPLE_TAG, UInt8.ofNat ns.length]
      else UInt8.ofNat LONGTUPLE_TAG :: le 4 ns.length) ++ (serSyms es ns).1, (serSyms es ns).2) := by
  simp [serNames, h]

theorem Dec.names {f : Nat} {ns : List Bytes} {E : List Nat} {es : ES} (hinv : Inv es)
    (h63 : (serNames es ns).2.counter ≤ 2 ^ 63) (hw : ∀ n ∈ ns, SymWF n) (hl : ns.length < 2 ^ 31)
    (hP : PendOK E es) (hf : (serNames es ns).1.length ≤ f) :
    Dec (Serialization.deser f) E es (serNames es ns).1 (.v (.tup (ns.map .sym))) E (serNames es ns).2 := by
  by_cases h0 : ns = []
  · subst h0
    simp only [serNames, ↓reduceIte, List.length_singleton] at hf ⊢
    exact Dec.fuel (K := 1) (fun g => Dec.emptyTuple E es) hf
  · rw [serNames_ne es ns h0] at hf h63 ⊢
    simp only at hf h63 ⊢
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by split at hf <;> simp at hf <;> omega⟩
    by_cases h255 : ns.length ≤ 255
    · simp only [h255, ↓reduceIte, List.cons_append, List.nil_append, List.length_cons] at hf ⊢
      refine Dec.deserTag (by decide) ?_
      rw [handle_tuple]
      refine Dec.bind (Dec.readU8 _ E es) ?_ rfl
      rw [tag_toNat (by omega)]
      unfold deserTuple
      exact Dec.bind (b2 := []) (Dec.syms ns g E es hinv h63 hw hP (by omega)) (Dec.pure _ _ _) (by simp)
    · simp only [h255, ↓reduceIte, List.cons_append, List.length_cons, List.length_append,
        le_length] at hf ⊢
      refine Dec.deserTag (by decide) ?_
      rw [handle_longtuple]
      have hr : InRange .i32 (ns.length : Int) := by
        simp only [InRange, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; simp; omega
      have hb : le 4 ns.length = le (nbytes .i32) (intBits .i32 (ns.length : Int)) := by
        congr 1; simp [intBits, IntTy.bits]; omega
      rw [hb]
      refine Dec.bind (Dec.readInt hr E es) ?_ rfl
      simp only [show ¬ ((ns.length : Int) < 0) from by omega, ↓reduceIte, Int.toNat_natCast]
      unfold deserTuple
      exact Dec.bind (b2 := []) (Dec.syms ns g E es hinv h63 hw hP (by omega)) (Dec.pure _ _ _) (by simp)

/-! ### Type data -/

theorem serModule_length (es : ES) (name : Bytes) (t : Nat) (h : sertagSym name = some t) :
    (serModule es name).1.length = 3 + (writeAsTag t).length := by
  rw [serModule_eq es name t h]; simp; omega

theorem serModule_state (es : ES) (name : Bytes) (t : Nat) (h : sertagSym name = some t) :
    (serModule es name).2 = es := by
  rw [serModule_eq es name t h]

theorem serTypeData_none (es : ES) (T : Ty) (name modName : Bytes) (np : Nat)
    (params : ES → Bytes × ES) (h : es.tab.lookup (.ty T) = none) :
    serTypeData es T name modName np params =
      (UInt8.ofNat DATATYPE_TAG :: (serSym (es.register (.ty T)) name).1 ++
        (serModule (serSym (es.register (.ty T)) name).2 modName).1 ++ le 4 np ++
        (params (serModule (serSym (es.register (.ty T)) name).2 modName).2).1,
       (params (serModule (serSym (es.register (.ty T)) name).2 modName).2).2) := by
  simp [serTypeData, h]

theorem serTypeData_some (es : ES) (T : Ty) (name modName : Bytes) (np : Nat)
    (params : ES → Bytes × ES) {k : Nat} (h : es.tab.lookup (.ty T) = some k) :
    serTypeData es T name modName np params = (emitBackref k, es) := by
  simp [serTypeData, h]

/-- `serialize_type_data` for a parametric type in `Base`/`Core` decodes to the type,
registering the same slots on both sides. -/
theorem Dec.typeData {f : Nat} {E : List Nat} {es : ES} {T : Ty} {name modName : Bytes} {np : Nat}
    {params : ES → Bytes × ES} {g : Global} {m : Md} {tm : Nat}
    (hinv : Inv es) (h63 : (serTypeData es T name modName np params).2.counter ≤ 2 ^ 63)
    (hP : PendOK E es) (hT : ∀ p ∈ E, encTable es p ≠ some (.ty T))
    (hname : SymWF name) (hnp : 0 < np) (hnp' : np < 2 ^ 31)
    (htm : sertagSym modName = some tm) (hroot : rootModule modName = Pure.pure m)
    (hg : getGlobal m name = Pure.pure g)
    (hpg : ∀ e, Grows e (params e).2)
    (hparams : ∀ (es' : ES) (f' : Nat), Inv es' → (params es').2.counter ≤ 2 ^ 63 →
      PendOK (es.counter :: E) es' → Pres es es' → encTable es' es.counter = some (.ty T) →
      (params es').1.length ≤ f' →
      Dec (readParams (Serialization.deser f') g (np : Int)) (es.counter :: E) es' (params es').1 T
        (es.counter :: E) (params es').2)
    (hf : (serTypeData es T name modName np params).1.length ≤ f) :
    Dec (Serialization.deser f) E es (serTypeData es T name modName np params).1 (.ty T) E
      (serTypeData es T name modName np params).2 := by
  cases hk : es.tab.lookup (.ty T) with
  | some k =>
    rw [serTypeData_some es T name modName np params hk] at h63 hf ⊢
    have hm := lookup_mem es.tab hk
    have hkt := encTable_of_mem hinv hm
    have hkE : k ∉ E := fun hm' => hT k hm' hkt
    have hlt := lt_of_mem hinv hm
    exact Dec.fuel (K := 1) (fun _ => Dec.backref (by simp at h63; omega) hkE hkt)
      (Nat.le_trans (emitBackref_ne k) hf)
  | none =>
    rw [serTypeData_none es T name modName np params hk] at h63 hf ⊢
    -- serializer states
    have i0 := hinv
    obtain ⟨i1, p1⟩ := grows_register es (.ty T) i0
    obtain ⟨i2, p2⟩ := serSym_grows (es.register (.ty T)) name i1
    have hms := serModule_state (serSym (es.register (.ty T)) name).2 modName tm htm
    obtain ⟨i3, p3⟩ := hpg (serModule (serSym (es.register (.ty T)) name).2 modName).2 (by rw [hms]; exact i2)
    rw [hms] at i3 p3 h63 hf ⊢
    simp only at h63
    simp only [List.cons_append, List.length_cons, List.length_append, le_length] at hf
    obtain ⟨g', rfl⟩ : ∃ g', f = g' + 1 := ⟨f - 1, by omega⟩
    have hP1 : PendOK (es.counter :: E) (es.register (.ty T)) := by
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · refine ⟨by simp [ES.register], fun n => ?_⟩
        rw [encTable_register hinv]; simp
      · exact (hP.mono p1) p hp
    have hslot : encTable (params (serSym (es.register (.ty T)) name).2).2 es.counter = some (.ty T) := by
      have e1 : encTable (es.register (.ty T)) es.counter = some (.ty T) := by
        rw [encTable_register hinv]; simp
      have hlt : es.counter < (es.register (.ty T)).counter := by simp [ES.register]
      rw [p3.2 _ (Nat.lt_of_lt_of_le hlt p2.1), p2.2 _ hlt, e1]
    refine Dec.deserTag (by decide) ?_
    rw [handle_datatype]
    unfold deserDatatype
    refine Dec.bind (b2 := (serSym (es.register (.ty T)) name).1 ++
        (serModule (serSym (es.register (.ty T)) name).2 modName).1 ++ le 4 np ++
        (params (serSym (es.register (.ty T)) name).2).1) (Dec.newSlot (.ty T) E es) ?_ (by simp)
    refine Dec.bind (b2 := (serModule (serSym (es.register (.ty T)) name).2 modName).1 ++ le 4 np ++
        (params (serSym (es.register (.ty T)) name).2).1)
      (Dec.symF i1 (by have := p2.1; have := p3.1; omega) hname hP1 (by omega)) ?_
      (by simp [List.append_assoc])
    refine Dec.bind (b1 := []) (Dec.pure _ _ _) ?_ (List.nil_append _).symm
    refine Dec.bind (b2 := le 4 np ++ (params (serSym (es.register (.ty T)) name).2).1)
      (Dec.fuel (K := 2) (fun _ => Dec.module (f := _) htm hroot _ _) (by
        rw [serModule_length _ _ tm htm] at hf; omega)) ?_ (List.append_assoc _ _ _)
    rw [hms]
    refine Dec.bind (b1 := []) (Dec.pure _ _ _) ?_ (List.nil_append _).symm
    rw [hg]
    refine Dec.bind (b1 := []) (Dec.pure _ _ _) ?_ (List.nil_append _).symm
    have hr : InRange .i32 (np : Int) := by
      simp only [InRange, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; simp; omega
    have hb : le 4 np = le (nbytes .i32) (intBits .i32 (np : Int)) := by
      congr 1; simp [intBits, IntTy.bits]; omega
    rw [hb]
    refine Dec.bind (Dec.readInt hr _ _) ?_ rfl
    simp only [show ¬ ((np : Int) = 0) from by omega, ↓reduceIte]
    have hslot2 : encTable (serSym (es.register (.ty T)) name).2 es.counter = some (.ty T) := by
      have hlt : es.counter < (es.register (.ty T)).counter := by simp [ES.register]
      rw [p2.2 _ hlt, encTable_register hinv]; simp
    refine Dec.bind (b2 := [])
      (hparams _ g' i2 (by omega) (hP1.mono p2) (pres_trans p1 p2) hslot2
        (by rw [serModule_length _ _ tm htm] at hf; omega))
      ?_ (by simp)
    exact Dec.bind (Dec.setBackref hslot) (Dec.pure _ _ _) rfl

/-! ### The types of the model -/

/-- Field type tags that decode as types (`TAGS` below `VALUE_TAGS`, or `Bool`/`Any`). -/
def TagOK (t : Nat) : Prop := t ≠ 0 ∧ t < 76 ∧ t ≠ 68 ∧ t ≠ 74

theorem serTagType_length (t : Nat) : 1 ≤ (serTagType t).length := by
  unfold serTagType writeAsTag; split <;> simp

theorem Dec.tagTypeF {f t : Nat} (ht : TagOK t) (hf : 1 ≤ f) (E : List Nat) (es : ES) :
    Dec (Serialization.deser f) E es (serTagType t) (.ty (.tagged t)) E es :=
  Dec.fuel (K := 1) (fun _ => Dec.tagType ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 E es) hf

theorem Dec.tagTypes {f : Nat} (hf : 1 ≤ f) (E : List Nat) (es : ES) :
    ∀ fts : List Nat, (∀ t ∈ fts, TagOK t) →
      Dec (Serialization.readMany (Serialization.deser f) fts.length) E es (fts.map serTagType).flatten
        (fts.map fun t => .ty (.tagged t)) E es
  | [], _ => Dec.readMany_nil _ E es
  | t :: ts, h => by
    simp only [List.map_cons, List.flatten_cons, List.length_cons]
    exact Dec.readMany_cons (Dec.tagTypeF (h t (by simp)) hf E es)
      (Dec.tagTypes hf E es ts (fun u hu => h u (by simp [hu])))

theorem taggedOf_map : ∀ fts : List Nat, taggedOf (fts.map fun t => .ty (.tagged t)) = some fts
  | [] => rfl
  | t :: ts => by simp [taggedOf, taggedOf_map ts]

theorem Dec.readParam {f want : Nat} {T : Ty} (ht : TagOK want) (hf : 1 ≤ f) (E : List Nat) (es : ES) :
    Dec (Serialization.readParam (Serialization.deser f) want T) E es (serTagType want) T E es := by
  unfold Serialization.readParam
  refine Dec.bind (b2 := []) (Dec.tagTypeF ht hf E es) ?_ (by simp)
  simp only [↓reduceIte]
  exact Dec.pure _ E es

/-- Pending slots hold mutable objects (the `RefValue` being read). -/
def PendObj (E : List Nat) (es : ES) : Prop :=
  ∀ p ∈ E, p < es.counter ∧ encTable es p = some .obj

theorem PendObj.pendOK {E : List Nat} {es : ES} (h : PendObj E es) : PendOK E es :=
  fun p hp => ⟨(h p hp).1, fun n => by rw [(h p hp).2]; simp⟩

theorem PendObj.noTy {E : List Nat} {es : ES} (h : PendObj E es) (T : Ty) :
    ∀ p ∈ E, encTable es p ≠ some (.ty T) := fun p hp => by rw [(h p hp).2]; simp

theorem paramsConst_grows (b : Bytes) : ∀ e : ES, Grows e ((fun es : ES => (b, es)) e).2 :=
  fun e => grows_refl e

/-- The type data of `Base.RefValue{Any}`. -/
theorem Dec.refAnyType {f : Nat} {E : List Nat} {es : ES} (hinv : Inv es)
    (h63 : (serTypeData es .refAny nameRefValue nameBase 1 (fun es => (serTagType ANY_TAG, es))).2.counter ≤ 2 ^ 63)
    (hO : PendObj E es)
    (hf : (serTypeData es .refAny nameRefValue nameBase 1 (fun es => (serTagType ANY_TAG, es))).1.length ≤ f) :
    Dec (Serialization.deser f) E es
      (serTypeData es .refAny nameRefValue nameBase 1 (fun es => (serTagType ANY_TAG, es))).1 (.ty .refAny) E
      (serTypeData es .refAny nameRefValue nameBase 1 (fun es => (serTagType ANY_TAG, es))).2 :=
  Dec.typeData (g := .refValue) (m := .base) (tm := 158) hinv h63 hO.pendOK (hO.noTy _)
    (by unfold SymWF nameRefValue; decide) (by decide) (by decide) rfl rfl rfl
    (paramsConst_grows _)
    (fun es' f' _ _ _ _ _ hl => by
      simp only [readParams, show ((1 : Nat) : Int) = 1 from rfl, ↓reduceIte]
      exact Dec.readParam (by unfold TagOK; decide) (Nat.le_trans (serTagType_length _) (by simpa using hl)) _ _)
    hf

/-- The type data of `UnitRange{Int64}`. -/
theorem Dec.urangeType {f : Nat} {E : List Nat} {es : ES} (hinv : Inv es)
    (h63 : (serTypeData es .urange nameUnitRange nameBase 1 (fun es => (serTagType INT64_TAG, es))).2.counter ≤ 2 ^ 63)
    (hO : PendObj E es)
    (hf : (serTypeData es .urange nameUnitRange nameBase 1 (fun es => (serTagType INT64_TAG, es))).1.length ≤ f) :
    Dec (Serialization.deser f) E es
      (serTypeData es .urange nameUnitRange nameBase 1 (fun es => (serTagType INT64_TAG, es))).1 (.ty .urange) E
      (serTypeData es .urange nameUnitRange nameBase 1 (fun es => (serTagType INT64_TAG, es))).2 :=
  Dec.typeData (g := .unitRange) (m := .base) (tm := 158) hinv h63 hO.pendOK (hO.noTy _)
    (by unfold SymWF nameUnitRange; decide) (by decide) (by decide) rfl rfl rfl
    (paramsConst_grows _)
    (fun es' f' _ _ _ _ _ hl => by
      simp only [readParams, show ((1 : Nat) : Int) = 1 from rfl, ↓reduceIte]
      exact Dec.readParam (by unfold TagOK; decide) (Nat.le_trans (serTagType_length _) (by simpa using hl)) _ _)
    hf

/-- The type `Tuple{fts...}` of a `NamedTuple`'s fields. -/
theorem Dec.tupleType {f : Nat} {fts : List Nat} {E : List Nat} {es : ES} (hinv : Inv es)
    (h63 : (serTupleType es fts).2.counter ≤ 2 ^ 63) (hP : PendOK E es)
    (hT : ∀ p ∈ E, encTable es p ≠ some (.ty (.tuple fts)))
    (hfts : ∀ t ∈ fts, TagOK t) (hl : fts.length < 2 ^ 31)
    (hf : (serTupleType es fts).1.length ≤ f) :
    Dec (Serialization.deser f) E es (serTupleType es fts).1
      (.ty (if fts = [] then .tagged EMPTYTUPLE_TYPE_TAG else .tuple fts)) E (serTupleType es fts).2 := by
  unfold serTupleType at h63 hf ⊢
  by_cases h0 : fts = []
  · simp only [h0, ↓reduceIte] at h63 hf ⊢
    exact Dec.tagTypeF (by unfold TagOK; decide) (Nat.le_trans (serTagType_length _) hf) E es
  · simp only [h0, ↓reduceIte] at h63 hf ⊢
    have hlen : 0 < fts.length := by
      cases fts with
      | nil => exact absurd rfl h0
      | cons => simp
    refine Dec.typeData (g := .tuple) (m := .core) (tm := 155) hinv h63 hP hT
      (by unfold SymWF nameTuple; decide) hlen hl rfl rfl rfl (fun e => grows_refl e) ?_ hf
    intro es' f' _ _ _ _ _ hl'
    unfold readParams
    simp only [Int.toNat_natCast]
    have hf1 : 1 ≤ f' := by
      cases fts with
      | nil => exact absurd rfl h0
      | cons t ts =>
        simp only [List.map_cons, List.flatten_cons, List.length_append] at hl'
        have := serTagType_length t
        omega
    refine Dec.bind (b2 := []) (Dec.tagTypes hf1 _ _ fts hfts) ?_ (by simp)
    simp only [taggedOf_map, h0, ↓reduceIte]
    exact Dec.pure _ _ _

theorem PendObj.mono {E : List Nat} {es es' : ES} (h : PendObj E es) (hp : Pres es es') :
    PendObj E es' := fun p hp' => by
  obtain ⟨h1, h2⟩ := h p hp'
  exact ⟨Nat.lt_of_lt_of_le h1 hp.1, by rw [hp.2 p h1]; exact h2⟩

/-- The parameters of a `NamedTuple` type: its names, then `Tuple{fts...}`. -/
def ntupParams (names : List Bytes) (fts : List Nat) (es : ES) : Bytes × ES :=
  let (b1, es) := serNames es names
  let (b2, es) := serTupleType es fts
  (b1 ++ b2, es)

theorem ntupParams_eq (names : List Bytes) (fts : List Nat) (e : ES) :
    ntupParams names fts e =
      ((serNames e names).1 ++ (serTupleType (serNames e names).2 fts).1,
        (serTupleType (serNames e names).2 fts).2) := rfl

theorem ntupParams_grows (names : List Bytes) (fts : List Nat) :
    ∀ e, Grows e (ntupParams names fts e).2 := fun e =>
  grows_trans (serNames_grows e names) (serTupleType_grows _ fts)

theorem ntupTypeES_eq (es : ES) (names : List Bytes) (fts : List Nat) :
    ntupTypeES es names fts =
      (serTypeData es (.ntup names fts) nameNamedTuple nameCore 2 (ntupParams names fts)).2 := rfl

/-- The type data of `NamedTuple{names, Tuple{fts...}}`. -/
theorem Dec.ntupType {f : Nat} {names : List Bytes} {fts : List Nat} {E : List Nat} {es : ES}
    (hinv : Inv es)
    (h63 : (serTypeData es (.ntup names fts) nameNamedTuple nameCore 2 (ntupParams names fts)).2.counter ≤ 2 ^ 63)
    (hO : PendObj E es) (hw : ∀ n ∈ names, SymWF n) (hnl : names.length < 2 ^ 31)
    (hlen : names.length = fts.length) (hfts : ∀ t ∈ fts, TagOK t)
    (hf : (serTypeData es (.ntup names fts) nameNamedTuple nameCore 2 (ntupParams names fts)).1.length ≤ f) :
    Dec (Serialization.deser f) E es
      (serTypeData es (.ntup names fts) nameNamedTuple nameCore 2 (ntupParams names fts)).1
      (.ty (.ntup names fts)) E
      (serTypeData es (.ntup names fts) nameNamedTuple nameCore 2 (ntupParams names fts)).2 := by
  refine Dec.typeData (g := .namedTuple) (m := .core) (tm := 155) hinv h63 hO.pendOK (hO.noTy _)
    (by unfold SymWF nameNamedTuple; decide) (by decide) (by decide) rfl rfl rfl
    (ntupParams_grows names fts) ?_ hf
  intro es' f' i' h63' hP' pr' hslot' hl'
  obtain ⟨i2, p2⟩ := serNames_grows es' names i'
  obtain ⟨_, p3⟩ := serTupleType_grows (serNames es' names).2 fts i2
  rw [ntupParams_eq] at h63' hl' ⊢
  dsimp only at h63' hl' ⊢
  simp only [List.length_append] at hl'
  unfold readParams
  simp only [show ((2 : Nat) : Int) = 2 from rfl, ↓reduceIte]
  have hP2 : PendOK (es.counter :: E) (serNames es' names).2 := hP'.mono p2
  refine Dec.bind (b2 := (serTupleType (serNames es' names).2 fts).1)
    (Dec.names i' (by have := p3.1; omega) hw hnl hP' (by omega)) ?_ (by simp [ntupParams])
  rw [asNames_map]
  refine Dec.bind (b1 := []) (Dec.pure _ _ _) ?_ (List.nil_append _).symm
  have hT2 : ∀ p ∈ es.counter :: E, encTable (serNames es' names).2 p ≠ some (.ty (.tuple fts)) := by
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · rw [p2.2 _ (by have := (hP' es.counter (by simp)).1; exact this), hslot']; simp
    · have hO' := hO.mono pr'
      have := (hO' p hp)
      rw [p2.2 _ this.1, this.2]; simp
  refine Dec.bind (b2 := []) (Dec.tupleType i2 h63' hP2 hT2 hfts (by omega) (by omega)) ?_ (by simp)
  by_cases hz : fts = []
  · subst hz
    simp only [↓reduceIte, asTupleTy]
    refine Dec.bind (b1 := []) (Dec.pure _ _ _) ?_ (List.nil_append _).symm
    simp only [hlen, List.length_nil, ↓reduceIte]
    exact Dec.pure _ _ _
  · simp only [hz, ↓reduceIte, asTupleTy]
    refine Dec.bind (b1 := []) (Dec.pure _ _ _) ?_ (List.nil_append _).symm
    simp only [hlen, ↓reduceIte]
    exact Dec.pure _ _ _

end JuliaLean.Serialization
