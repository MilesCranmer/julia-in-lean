import JuliaLean.Serialization.Values

/-!
Decoding of each composite value, given that its children decode (`ValueDec f`).
-/

namespace JuliaLean.Serialization

open JuliaLean

theorem pendOK_nil (es : ES) : PendOK [] es := fun _ hp => absurd hp (List.not_mem_nil)

theorem pendObj_nil (es : ES) : PendObj [] es := fun _ hp => absurd hp (List.not_mem_nil)

theorem i32_len {n : Nat} (h : n < 2 ^ 31) : InRange .i32 (n : Int) := by
  simp only [InRange, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; simp; omega

theorem le4_len {n : Nat} (h : n < 2 ^ 31) : le 4 n = le (nbytes .i32) (intBits .i32 (n : Int)) := by
  congr 1; simp [intBits, IntTy.bits]; omega

theorem i64_len {n : Nat} (h : n < 2 ^ 63) : InRange .i64 (n : Int) := by
  simp only [InRange, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; simp; omega

theorem asSym_sym (n : Bytes) : asSym (.v (.sym n)) = Pure.pure n := rfl

theorem tupHdr_length (l : Nat) : 2 ≤ (tupHdr l).length := by
  unfold tupHdr; split <;> simp [le_length]

theorem exprHdr_length (l : Nat) : 2 ≤ (exprHdr l).length := by
  unfold exprHdr; split <;> simp [le_length]

/-! ### Tuples -/

theorem Dec.tupCase {f : Nat} (ih : ValueDec f) {xs : List V} {es : ES} (hinv : Inv es)
    (hw : WF es (.tup xs)) (h63 : (ser es (.tup xs)).2.counter ≤ 2 ^ 63)
    (hf : (ser es (.tup xs)).1.length ≤ f + 1) :
    Dec (Serialization.deser (f + 1)) [] es (ser es (.tup xs)).1 (.v (.tup xs)) [] (ser es (.tup xs)).2 := by
  by_cases h0 : xs = []
  · subst h0; exact Dec.emptyTuple [] es
  · rw [ser_tup es xs h0] at h63 hf ⊢
    dsimp only at h63 hf ⊢
    simp only [WF] at hw
    simp only [List.length_append] at hf
    have := tupHdr_length xs.length
    have hd : Dec (deserTuple (Serialization.deser f) xs.length) [] es (serList es xs).1 (.v (.tup xs)) []
        (serList es xs).2 := by
      unfold deserTuple
      exact Dec.bind (b2 := []) (Dec.valueList ih xs es hinv hw.2 h63 (by omega)) (Dec.pure _ _ _)
        (by simp)
    unfold tupHdr
    by_cases hl : xs.length ≤ 255
    · simp only [hl, ↓reduceIte, List.cons_append, List.nil_append]
      refine Dec.deserTag (by decide) ?_
      rw [handle_tuple]
      refine Dec.bind (Dec.readU8 _ [] es) ?_ rfl
      rw [tag_toNat (by omega)]
      exact hd
    · simp only [hl, ↓reduceIte, List.cons_append]
      refine Dec.deserTag (by decide) ?_
      rw [handle_longtuple, le4_len hw.1]
      refine Dec.bind (Dec.readInt (i32_len hw.1) [] es) ?_ rfl
      simp only [show ¬ ((xs.length : Int) < 0) by omega, ↓reduceIte, Int.toNat_natCast]
      exact hd

/-! ### `Expr` -/

theorem Dec.exprCase {f : Nat} (ih : ValueDec f) {hd : Bytes} {args : List V} {es : ES} (hinv : Inv es)
    (hw : WF es (.expr hd args)) (h63 : (ser es (.expr hd args)).2.counter ≤ 2 ^ 63)
    (hf : (ser es (.expr hd args)).1.length ≤ f + 1) :
    Dec (Serialization.deser (f + 1)) [] es (ser es (.expr hd args)).1 (.v (.expr hd args)) []
      (ser es (.expr hd args)).2 := by
  rw [ser_expr] at h63 hf ⊢
  dsimp only at h63 hf ⊢
  simp only [WF] at hw
  simp only [ES.newObj] at h63 hf hw ⊢
  obtain ⟨hsym, hlen, hargs⟩ := hw
  simp only [List.length_append] at hf
  have := exprHdr_length args.length
  have i0 := inv_register hinv .obj
  obtain ⟨i1, p1⟩ := serSym_grows (es.register .obj) hd i0
  obtain ⟨_, p2⟩ := serList_grows (serSym (es.register .obj) hd).2 args i1
  have hbody : Dec (deserExpr (Serialization.deser f) (args.length : Int)) [] es
      ((serSym (es.register .obj) hd).1 ++ (serList (serSym (es.register .obj) hd).2 args).1) (.v (.expr hd args)) []
      (serList (serSym (es.register .obj) hd).2 args).2 := by
    unfold deserExpr
    refine Dec.bind (b1 := []) (Dec.resolveNow .obj [] es) ?_ (List.nil_append _).symm
    refine Dec.bind (Dec.symF i0 (by have := p1.1; have := p2.1; omega) hsym (pendOK_nil _)
      (by omega)) ?_ rfl
    rw [asSym_sym]
    refine Dec.bind (b1 := []) (Dec.pure _ _ _) ?_ (List.nil_append _).symm
    simp only [Int.toNat_natCast]
    exact Dec.bind (b2 := []) (Dec.valueList ih args _ i1 hargs h63 (by omega)) (Dec.pure _ _ _)
      (by simp)
  unfold exprHdr
  by_cases hl : args.length ≤ 255
  · simp only [hl, ↓reduceIte, List.cons_append, List.nil_append]
    refine Dec.deserTag (by decide) ?_
    rw [handle_expr]
    refine Dec.bind (Dec.readU8 _ [] es) ?_ rfl
    rw [tag_toNat (by omega)]
    exact hbody
  · simp only [hl, ↓reduceIte, List.cons_append, List.append_assoc]
    refine Dec.deserTag (by decide) ?_
    rw [handle_longexpr, le4_len hlen]
    exact Dec.bind (Dec.readInt (i32_len hlen) [] es) hbody rfl

/-! ### Arrays -/

theorem asLen_i64 (n : Int) : asLen (.v (.int .i64 n)) = Pure.pure (some n) := rfl

theorem serInt64_length (n : Int) : 1 ≤ (serInt64 n).length := serInt_length .i64 n

/-- The length of a vector, `serialize(s, length(a))`. -/
theorem Dec.len {f n : Nat} (hn : n < 2 ^ 63) (hf : 1 ≤ f) (E : List Nat) (es : ES) :
    Dec (Serialization.deser f) E es (serInt64 n) (.v (.int .i64 n)) E es :=
  Dec.fuel (K := 1) (fun _ => Dec.int (t := .i64) (i64_len hn) E es) hf

theorem encTable_newObj {es : ES} (hinv : Inv es) : encTable (es.register .obj) es.counter = some .obj := by
  rw [encTable_register hinv]; simp

theorem Dec.anyvecCase {f : Nat} (ih : ValueDec f) {xs : List (Option V)} {es : ES} (hinv : Inv es)
    (hw : WF es (.anyvec xs)) (h63 : (ser es (.anyvec xs)).2.counter ≤ 2 ^ 63)
    (hf : (ser es (.anyvec xs)).1.length ≤ f + 1) :
    Dec (Serialization.deser (f + 1)) [] es (ser es (.anyvec xs)).1 (.v (.anyvec xs)) []
      (ser es (.anyvec xs)).2 := by
  rw [ser_anyvec] at h63 hf ⊢
  dsimp only at h63 hf ⊢
  simp only [WF] at hw
  simp only [ES.newObj] at h63 hf hw ⊢
  obtain ⟨hlen, hel⟩ := hw
  simp only [List.length_cons, List.length_append] at hf
  have := serInt64_length xs.length
  have i0 := inv_register hinv .obj
  refine Dec.deserTag (by decide) ?_
  rw [handle_array]
  unfold deserArray
  refine Dec.bind (b1 := []) (Dec.newSlot .obj [] es) ?_ (List.nil_append _).symm
  refine Dec.bind (b1 := [UInt8.ofNat ANY_TAG]) (Dec.tagTypeF (t := ANY_TAG) (by unfold TagOK; decide)
    (by omega) _ _) ?_ rfl
  refine Dec.bind (b1 := serInt64 xs.length) (b2 := (serOptList (es.register .obj) xs).1)
    (Dec.bind (b2 := []) (Dec.len hlen (by omega) _ _) (Dec.pure (ArrKind.any, _) _ _) (by simp)) ?_ rfl
  rw [asLen_i64]
  refine Dec.bind (b1 := []) (Dec.pure _ _ _) ?_ (List.nil_append _).symm
  simp only [show ¬ ((xs.length : Int) < 0) by omega, ↓reduceIte, arrBody, Int.toNat_natCast]
  refine Dec.bind (b1 := []) (Dec.setBackref (encTable_newObj hinv)) ?_ (List.nil_append _).symm
  exact Dec.bind (b2 := []) (Dec.optList ih xs _ i0 hel h63 (by omega)) (Dec.pure _ _ _) (by simp)

theorem intTyOfTag_intTag (t : IntTy) : intTyOfTag (intTag t) = some t := by cases t <;> rfl

theorem intTag_ok (t : IntTy) : TagOK (intTag t) := by cases t <;> (unfold TagOK; decide)

theorem intTag_ne_any (t : IntTy) : intTag t ≠ ANY_TAG := by cases t <;> decide

theorem intTag_ne_bool (t : IntTy) : intTag t ≠ BOOL_TYPE_TAG := by cases t <;> decide

theorem ser_ivec (es : ES) (t : IntTy) (xs : List Int) :
    ser es (.ivec t xs) =
      (UInt8.ofNat ARRAY_TAG :: (if t = .u8 then [] else serTagType (intTag t)) ++ serInt64 xs.length ++
        (xs.map fun x => le (nbytes t) (intBits t x)).flatten, es.register .obj) := rfl

/-- The raw elements of a bits vector. -/
theorem Dec.ivecBody {t : IntTy} {xs : List Int} (hx : ∀ x ∈ xs, InRange t x) {E : List Nat} {es : ES}
    (slot : Nat) (hk : encTable es slot = some .obj) :
    Dec (arrBody h slot (.int t) (xs.length : Int)) (slot :: E) es
      (xs.map fun x => le (nbytes t) (intBits t x)).flatten (.v (.ivec t xs)) E es := by
  simp only [arrBody, Int.toNat_natCast]
  refine Dec.bind (b1 := []) (Dec.setBackref hk) ?_ (List.nil_append _).symm
  have hl := flatten_length (nbytes t) (fun x => le (nbytes t) (intBits t x)) (fun x => le_length _ _) xs
  rw [← hl]
  refine Dec.bind (b2 := []) (Dec.readN _ E es) (Dec.pure' E es ?_) (by simp)
  rw [chunks_flatten (nbytes t) (fun x => le (nbytes t) (intBits t x)) (fun x => le_length _ _) xs,
    List.map_map]
  congr 2
  conv => rhs; rw [← List.map_id xs]
  apply List.map_congr_left
  intro x hxm
  simp only [Function.comp, unle_le, Nat.mod_eq_of_lt (intBits_lt t x), id]
  exact ofBits_intBits t x (hx x hxm)

theorem Dec.ivecCase {f : Nat} {t : IntTy} {xs : List Int} {es : ES} (hinv : Inv es)
    (hw : WF es (.ivec t xs)) (hf : (ser es (.ivec t xs)).1.length ≤ f + 1) :
    Dec (Serialization.deser (f + 1)) [] es (ser es (.ivec t xs)).1 (.v (.ivec t xs)) []
      (ser es (.ivec t xs)).2 := by
  rw [ser_ivec] at hf ⊢
  dsimp only at hf ⊢
  simp only [WF] at hw
  obtain ⟨hlen, hx⟩ := hw
  have := serInt64_length xs.length
  refine Dec.deserTag (by decide) ?_
  rw [handle_array]
  unfold deserArray
  refine Dec.bind (b1 := []) (Dec.newSlot .obj [] es) ?_ (List.nil_append _).symm
  by_cases hu : t = .u8
  · subst hu
    simp only [↓reduceIte] at hf ⊢
    simp only [List.length_cons, List.length_append] at hf
    refine Dec.bind (Dec.len hlen (by omega) _ _) ?_ rfl
    refine Dec.bind (b1 := []) (Dec.pure (ArrKind.int .u8, _) _ _) ?_ (List.nil_append _).symm
    rw [asLen_i64]
    refine Dec.bind (b1 := []) (Dec.pure _ _ _) ?_ (List.nil_append _).symm
    simp only [show ¬ ((xs.length : Int) < 0) by omega, ↓reduceIte]
    exact Dec.ivecBody hx _ (encTable_newObj hinv)
  · simp only [hu, ↓reduceIte] at hf ⊢
    simp only [List.length_cons, List.length_append] at hf
    have := serTagType_length (intTag t)
    refine Dec.bind (b2 := serInt64 xs.length ++ (xs.map fun x => le (nbytes t) (intBits t x)).flatten)
      (Dec.tagTypeF (intTag_ok t) (by omega) _ _) ?_ (by simp)
    refine Dec.bind (b2 := (xs.map fun x => le (nbytes t) (intBits t x)).flatten)
      (Dec.bind (b2 := []) (Dec.len hlen (by omega) _ _)
        (by simp only [intTag_ne_any, intTag_ne_bool, ↓reduceIte, intTyOfTag_intTag]
            exact Dec.pure (ArrKind.int t, _) _ _) (by simp))
      ?_ rfl
    rw [asLen_i64]
    refine Dec.bind (b1 := []) (Dec.pure _ _ _) ?_ (List.nil_append _).symm
    simp only [show ¬ ((xs.length : Int) < 0) by omega, ↓reduceIte]
    exact Dec.ivecBody hx _ (encTable_newObj hinv)

theorem ser_bvec (es : ES) (xs : List Bool) :
    ser es (.bvec xs) =
      (UInt8.ofNat ARRAY_TAG :: UInt8.ofNat BOOL_TYPE_TAG :: serInt64 xs.length ++ rle xs,
        es.register .obj) := rfl

/-- The run-length coded elements of a `Vector{Bool}`. -/
theorem Dec.rleBody (xs : List Bool) (E : List Nat) (es : ES) :
    Dec (if (xs.length : Int).toNat > 0 then (do let s ← getS; rleRead (xs.length : Int).toNat (s.io.length + 1) [])
      else Pure.pure []) E es (rle xs) xs E es := by
  cases xs with
  | nil => exact Dec.pure _ E es
  | cons x ys =>
    simp only [Int.toNat_natCast, List.length_cons, show ys.length + 1 > 0 by omega, ↓reduceIte]
    intro ds rest ha hio
    refine ⟨{ ds with io := rest }, ?_, rfl, ha.congr rfl rfl, rfl, rfl⟩
    show rleRead (x :: ys).length (ds.io.length + 1) [] ds = _
    exact rleRead_rle (x :: ys) (List.cons_ne_nil _ _) ds rest _ hio (by rw [hio]; simp; omega)

theorem Dec.bvecCase {f : Nat} {xs : List Bool} {es : ES} (hinv : Inv es)
    (hw : WF es (.bvec xs)) (hf : (ser es (.bvec xs)).1.length ≤ f + 1) :
    Dec (Serialization.deser (f + 1)) [] es (ser es (.bvec xs)).1 (.v (.bvec xs)) []
      (ser es (.bvec xs)).2 := by
  rw [ser_bvec] at hf ⊢
  dsimp only at hf ⊢
  simp only [WF] at hw
  simp only [List.length_cons, List.length_append] at hf
  have := serInt64_length xs.length
  refine Dec.deserTag (by decide) ?_
  rw [handle_array]
  unfold deserArray
  refine Dec.bind (b1 := []) (Dec.newSlot .obj [] es) ?_ (List.nil_append _).symm
  refine Dec.bind (b1 := [UInt8.ofNat BOOL_TYPE_TAG]) (Dec.tagTypeF (t := BOOL_TYPE_TAG)
    (by unfold TagOK; decide) (by omega) _ _) ?_ rfl
  refine Dec.bind (b1 := serInt64 xs.length) (b2 := rle xs)
    (Dec.bind (b2 := []) (Dec.len hw (by omega) _ _) (Dec.pure (ArrKind.bool, _) _ _) (by simp)) ?_ rfl
  rw [asLen_i64]
  refine Dec.bind (b1 := []) (Dec.pure _ _ _) ?_ (List.nil_append _).symm
  simp only [show ¬ ((xs.length : Int) < 0) by omega, ↓reduceIte, arrBody]
  refine Dec.bind (b2 := []) (Dec.rleBody xs _ _) ?_ (by simp)
  exact Dec.bind (b1 := []) (Dec.setBackref (encTable_newObj hinv)) (Dec.pure _ _ _) rfl

/-! ### Structs -/

theorem checkField_i64 (n : Int) : checkField INT64_TAG (.int .i64 n) = Pure.pure (.int .i64 n) := rfl

theorem Dec.i64Opt {f : Nat} {n : Int} (hn : InRange .i64 n) (hf : 1 ≤ f) (E : List Nat) (es : ES) :
    Dec (readOpt (handle f)) E es (serInt64 n) (some (.int .i64 n)) E es :=
  Dec.readOpt_of (Dec.fuel (K := 1) (fun _ => Dec.int (t := .i64) hn E es) hf)

theorem Dec.urangeCase {f : Nat} {lo hi : Int} {es : ES} (hinv : Inv es)
    (hw : WF es (.urange lo hi)) (h63 : (ser es (.urange lo hi)).2.counter ≤ 2 ^ 63)
    (hf : (ser es (.urange lo hi)).1.length ≤ f + 1) :
    Dec (Serialization.deser (f + 1)) [] es (ser es (.urange lo hi)).1 (.v (.urange lo hi)) []
      (ser es (.urange lo hi)).2 := by
  rw [ser_urange] at h63 hf ⊢
  dsimp only at h63 hf ⊢
  simp only [WF] at hw
  simp only [List.length_cons, List.length_append] at hf
  have := serInt64_length lo
  have := serInt64_length hi
  simp only [urangeTD] at h63 hf ⊢
  refine Dec.deserTag (by decide) ?_
  rw [handle_object]
  refine Dec.bind (b2 := serInt64 lo ++ serInt64 hi)
    (Dec.urangeType hinv h63 (pendObj_nil es) (by omega)) ?_ (by simp)
  simp only [deserStruct]
  refine Dec.bind (Dec.i64Opt hw.1 (by omega) _ _) ?_ rfl
  refine Dec.bind (b2 := []) (Dec.i64Opt hw.2 (by omega) _ _) ?_ (by simp)
  simp only [checkField_i64]
  exact Dec.bind (b1 := []) (Dec.pure _ _ _)
    (Dec.bind (b1 := []) (Dec.pure _ _ _) (Dec.pure _ _ _) rfl) rfl

theorem ftsOf_length (xs : List V) : (ftsOf xs).length = xs.length := by simp [ftsOf]

theorem Dec.ntupCase {f : Nat} (ih : ValueDec f) {names : List Bytes} {xs : List V} {es : ES}
    (hinv : Inv es) (hw : WF es (.ntup names xs)) (h63 : (ser es (.ntup names xs)).2.counter ≤ 2 ^ 63)
    (hf : (ser es (.ntup names xs)).1.length ≤ f + 1) :
    Dec (Serialization.deser (f + 1)) [] es (ser es (.ntup names xs)).1 (.v (.ntup names xs)) []
      (ser es (.ntup names xs)).2 := by
  rw [ser_ntup] at h63 hf ⊢
  dsimp only at h63 hf ⊢
  simp only [WF] at hw
  obtain ⟨hlen, _, hnw, hnl, hts, hxs⟩ := hw
  simp only [List.length_cons, List.length_append] at hf
  obtain ⟨i1, _⟩ := serTypeData_grows es (.ntup names (ftsOf xs)) nameNamedTuple nameCore 2
    (ntupParams names (ftsOf xs)) (ntupParams_grows _ _) hinv
  obtain ⟨_, p2⟩ := serList_grows (ntupTD es names (ftsOf xs)).2 xs i1
  simp only [ntupTD] at h63 hf i1 p2 ⊢
  refine Dec.deserTag (by decide) ?_
  rw [handle_object]
  refine Dec.bind (Dec.ntupType hinv (by have := p2.1; omega) (pendObj_nil es) hnw hnl
    (by rw [ftsOf_length]; exact hlen) (ftsOf_ok xs hts) (by omega)) ?_ rfl
  simp only [deserStruct, ftsOf_length]
  refine Dec.bind (b2 := []) (Dec.someList ih xs _ i1 hxs h63 (by omega)) ?_ (by simp)
  simp only [allSome_map, fieldsOk_ftsOf xs hts, ↓reduceIte]
  exact Dec.pure _ _ _

/-! ### `Base.RefValue{Any}` -/

theorem Dec.optOf {f : Nat} (ih : ValueDec f) {x : Option V} {es : ES} (hinv : Inv es)
    (hw : WFOpt es x) (h63 : (serOpt es x).2.counter ≤ 2 ^ 63) (hf : (serOpt es x).1.length ≤ f) :
    Dec (readOpt (handle f)) [] es (serOpt es x).1 x [] (serOpt es x).2 := by
  cases x with
  | none => exact Dec.readOpt_none [] es
  | some x => exact Dec.readOpt_of (ih x es hinv hw h63 hf)

/-- `REF_OBJECT_TAG`: the slot is pushed on `pending_refs` while the type is read, and
`deserialize_cycle` fills it before the field is read, so the field may refer back to it. -/
theorem Dec.refvCase {f : Nat} (ih : ValueDec f) {x : Option V} {es : ES} (hinv : Inv es)
    (hw : WF es (.refv x)) (h63 : (ser es (.refv x)).2.counter ≤ 2 ^ 63)
    (hf : (ser es (.refv x)).1.length ≤ f + 1) :
    Dec (Serialization.deser (f + 1)) [] es (ser es (.refv x)).1 (.v (.refv x)) []
      (ser es (.refv x)).2 := by
  rw [ser_refv] at h63 hf ⊢
  dsimp only at h63 hf ⊢
  simp only [WF, refTypeES] at hw
  simp only [ES.newObj, refTD] at h63 hf hw ⊢
  simp only [List.length_cons, List.length_append] at hf
  have i0 := inv_register hinv .obj
  obtain ⟨iT, pT⟩ := serTypeData_grows (es.register .obj) .refAny nameRefValue nameBase 1
    (fun es => (serTagType ANY_TAG, es)) (paramsConst_grows _) i0
  obtain ⟨_, pX⟩ := serOpt_grows (serTypeData (es.register .obj) .refAny nameRefValue nameBase 1
    (fun es => (serTagType ANY_TAG, es))).2 x iT
  have hO : PendObj [es.counter] (es.register .obj) := by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨by simp [ES.register], encTable_newObj hinv⟩
  have hT := Dec.refAnyType (f := f) i0 (by have := pX.1; omega) hO (by omega)
  have hX := Dec.optOf ih iT hw h63 (by omega)
  have hslot : encTable (serTypeData (es.register .obj) .refAny nameRefValue nameBase 1
      (fun es => (serTagType ANY_TAG, es))).2 es.counter = some .obj := by
    rw [pT.2 _ (by simp [ES.register]), encTable_newObj hinv]
  generalize (serTypeData (es.register .obj) .refAny nameRefValue nameBase 1
    (fun es => (serTagType ANY_TAG, es))).1 = bT at hT hf ⊢
  generalize (serOpt (serTypeData (es.register .obj) .refAny nameRefValue nameBase 1
    (fun es => (serTagType ANY_TAG, es))).2 x).1 = bX at hX hf ⊢
  generalize (serTypeData (es.register .obj) .refAny nameRefValue nameBase 1
    (fun es => (serTagType ANY_TAG, es))).2 = TS at hT hX hslot ⊢
  intro ds rest ha hio
  simp only [List.cons_append, List.append_assoc] at hio
  rw [deser_eq, bind_run (readU8_run hio), tag_toNat (by decide), handle_refobject]
  let ds2 : DS := { ds with io := bT ++ (bX ++ rest), counter := ds.counter + 1 }
  let ds3 : DS := { ds2 with pending := ds.counter :: ds.pending }
  have a3 : AgreeOn [es.counter] (es.register .obj) ds3 :=
    (agree_push ha .obj).congr rfl rfl
  obtain ⟨ds4, r4, io4, a4, p4, v4⟩ := hT ds3 (bX ++ rest) a3 rfl
  let ds4' : DS := { ds4 with pending := ds.pending }
  let ds5 : DS := { ds4' with table := (fun j => if j = ds.counter then some Key.obj else ds4'.table j) }
  have a5 : AgreeOn [] TS ds5 := by
    have := agree_fill (E := []) (key := .obj) (a4.congr (ds' := ds4') rfl rfl) hslot
    rw [← ha.counter] at this
    exact this
  obtain ⟨ds6, r6, io6, a6, p6, v6⟩ := hX ds5 rest a5 io4
  refine ⟨ds6, ?_, io6, a6, by rw [p6], by rw [v6, v4]⟩
  have e1 : Serialization.newSlot { ds with io := bT ++ (bX ++ rest) } =
      .ok (ds.counter, ds2) := rfl
  rw [bind_run e1, bind_run (rfl : getS ds2 = .ok (ds2, ds2)), bind_run (rfl : setS ds3 ds2 = .ok ((), ds3)),
    bind_run r4]
  simp only [deserStruct]
  rw [bind_run (rfl : getS ds4 = .ok (ds4, ds4))]
  have hp4 : ds4.pending = ds.counter :: ds.pending := p4
  simp only [hp4]
  rw [bind_run (rfl : setS ds4' ds4 = .ok ((), ds4'))]
  rw [bind_run (rfl : Serialization.setBackref ds.counter .obj ds4' = .ok ((), ds5))]
  rw [bind_run r6]
  rfl

end JuliaLean.Serialization
