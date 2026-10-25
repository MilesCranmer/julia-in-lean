import JuliaLean.Serialization.Types

/-!
Decoding of composite values: equations of the serializer, growth of its state,
and the element loops of tuples, `Expr`s, `Vector{Any}` and `NamedTuple`s.
-/

namespace JuliaLean.Serialization

open JuliaLean

/-! ### Serializer equations -/

/-- The header of a non-empty tuple (`:283-295`). -/
def tupHdr (l : Nat) : Bytes :=
  if l ≤ 255 then [UInt8.ofNat TUPLE_TAG, UInt8.ofNat l] else UInt8.ofNat LONGTUPLE_TAG :: le 4 l

/-- The header of an `Expr` (`:447-454`). -/
def exprHdr (l : Nat) : Bytes :=
  if l ≤ 255 then [UInt8.ofNat EXPR_TAG, UInt8.ofNat l] else UInt8.ofNat LONGEXPR_TAG :: le 4 l

theorem ser_tup (es : ES) (xs : List V) (h : xs ≠ []) :
    ser es (.tup xs) = (tupHdr xs.length ++ (serList es xs).1, (serList es xs).2) := by
  unfold ser; rw [if_neg h]; rfl

theorem ser_expr (es : ES) (hd : Bytes) (args : List V) :
    ser es (.expr hd args) =
      (exprHdr args.length ++ (serSym es.newObj hd).1 ++ (serList (serSym es.newObj hd).2 args).1,
        (serList (serSym es.newObj hd).2 args).2) := rfl

theorem ser_anyvec (es : ES) (xs : List (Option V)) :
    ser es (.anyvec xs) =
      (UInt8.ofNat ARRAY_TAG :: UInt8.ofNat ANY_TAG :: serInt64 xs.length ++ (serOptList es.newObj xs).1,
        (serOptList es.newObj xs).2) := rfl

/-- The type data of `Base.RefValue{Any}` in state `es`. -/
abbrev refTD (es : ES) : Bytes × ES :=
  serTypeData es .refAny nameRefValue nameBase 1 (fun es => (serTagType ANY_TAG, es))

theorem ser_refv (es : ES) (x : Option V) :
    ser es (.refv x) =
      (UInt8.ofNat REF_OBJECT_TAG :: (refTD es.newObj).1 ++ (serOpt (refTD es.newObj).2 x).1,
        (serOpt (refTD es.newObj).2 x).2) := rfl

/-- The type data of `UnitRange{Int64}` in state `es`. -/
abbrev urangeTD (es : ES) : Bytes × ES :=
  serTypeData es .urange nameUnitRange nameBase 1 (fun es => (serTagType INT64_TAG, es))

theorem ser_urange (es : ES) (lo hi : Int) :
    ser es (.urange lo hi) =
      (UInt8.ofNat OBJECT_TAG :: (urangeTD es).1 ++ serInt64 lo ++ serInt64 hi, (urangeTD es).2) := rfl

/-- The field types of a `NamedTuple`'s values. -/
def ftsOf (xs : List V) : List Nat := xs.map fun x => (typeTag x).getD 0

/-- The type data of `NamedTuple{names, Tuple{fts...}}` in state `es`. -/
abbrev ntupTD (es : ES) (names : List Bytes) (fts : List Nat) : Bytes × ES :=
  serTypeData es (.ntup names fts) nameNamedTuple nameCore 2 (ntupParams names fts)

theorem ser_ntup (es : ES) (names : List Bytes) (xs : List V) :
    ser es (.ntup names xs) =
      (UInt8.ofNat OBJECT_TAG :: (ntupTD es names (ftsOf xs)).1 ++
          (serList (ntupTD es names (ftsOf xs)).2 xs).1,
        (serList (ntupTD es names (ftsOf xs)).2 xs).2) := rfl

theorem serList_cons (es : ES) (x : V) (xs : List V) :
    serList es (x :: xs) = ((ser es x).1 ++ (serList (ser es x).2 xs).1, (serList (ser es x).2 xs).2) :=
  rfl

theorem serOptList_cons (es : ES) (x : Option V) (xs : List (Option V)) :
    serOptList es (x :: xs) =
      ((serOpt es x).1 ++ (serOptList (serOpt es x).2 xs).1, (serOptList (serOpt es x).2 xs).2) :=
  rfl

/-! ### Growth of the serializer state -/

theorem grows_newObj (es : ES) : Grows es es.newObj := grows_register es .obj

mutual
theorem ser_grows (es : ES) : ∀ x : V, Grows es (ser es x).2
  | .int _ _ => grows_refl es
  | .flt _ _ => grows_refl es
  | .bool _ => grows_refl es
  | .char _ => grows_refl es
  | .nothing => grows_refl es
  | .back _ => grows_refl es
  | .sym n => serSym_grows es n
  | .str s => by
    rw [ser_str]
    split
    · exact grows_newObj es
    · exact grows_refl es
  | .tup xs => by
    by_cases h : xs = []
    · subst h; exact grows_refl es
    · rw [ser_tup es xs h]; exact serList_grows es xs
  | .expr hd args => by
    rw [ser_expr]
    exact grows_trans (grows_newObj es) (grows_trans (serSym_grows _ hd) (serList_grows _ args))
  | .anyvec xs => by
    rw [ser_anyvec]
    exact grows_trans (grows_newObj es) (serOptList_grows _ xs)
  | .ivec _ _ => grows_newObj es
  | .bvec _ => grows_newObj es
  | .refv x => by
    rw [ser_refv]
    exact grows_trans (grows_newObj es)
      (grows_trans (serTypeData_grows _ _ _ _ _ _ (paramsConst_grows _)) (serOpt_grows _ x))
  | .urange _ _ => by
    rw [ser_urange]
    exact serTypeData_grows _ _ _ _ _ _ (paramsConst_grows _)
  | .ntup names xs => by
    rw [ser_ntup]
    exact grows_trans (serTypeData_grows _ _ _ _ _ _ (ntupParams_grows _ _)) (serList_grows _ xs)

theorem serList_grows (es : ES) : ∀ xs : List V, Grows es (serList es xs).2
  | [] => grows_refl es
  | x :: xs => by
    rw [serList_cons]
    exact grows_trans (ser_grows es x) (serList_grows _ xs)

theorem serOpt_grows (es : ES) : ∀ x : Option V, Grows es (serOpt es x).2
  | none => grows_refl es
  | some x => ser_grows es x

theorem serOptList_grows (es : ES) : ∀ xs : List (Option V), Grows es (serOptList es xs).2
  | [] => grows_refl es
  | x :: xs => by
    rw [serOptList_cons]
    exact grows_trans (serOpt_grows es x) (serOptList_grows _ xs)
end

/-! ### `#undef`-aware reads -/

theorem handle_undef (f : Nat) (s : DS) : ∃ e, handle f UNDEFREF_TAG s = .error e := by
  cases f with
  | zero => exact ⟨_, rfl⟩
  | succ f => exact ⟨_, rfl⟩

/-- `readOpt` on a value that `deserialize` reads. -/
theorem Dec.readOpt_of {f : Nat} {E E' : List Nat} {es es' : ES} {bs : Bytes} {x : V}
    (h : Dec (Serialization.deser f) E es bs (.v x) E' es') :
    Dec (readOpt (handle f)) E es bs (some x) E' es' := by
  intro ds rest ha hio
  obtain ⟨ds', r, io', a', p', v'⟩ := h ds rest ha hio
  rw [deser_eq] at r
  refine ⟨ds', ?_, io', a', p', v'⟩
  cases hds : ds.io with
  | nil =>
    have : Serialization.readU8 ds = .error .eof := by simp [Serialization.readU8, hds]
    rw [bind_err this] at r
    cases r
  | cons b t =>
    have hr := readU8_run (s := ds) hds
    rw [bind_run hr] at r
    unfold readOpt
    rw [bind_run hr]
    by_cases hb : b.toNat = UNDEFREF_TAG
    · obtain ⟨e, he⟩ := handle_undef f { ds with io := t }
      rw [hb, he] at r
      cases r
    · rw [if_neg hb, bind_run r]
      rfl

/-- `readOpt` on `UNDEFREF_TAG`. -/
theorem Dec.readOpt_none {f : Nat} (E : List Nat) (es : ES) :
    Dec (readOpt (handle f)) E es [UInt8.ofNat UNDEFREF_TAG] none E es := by
  unfold readOpt
  refine Dec.bind (b2 := []) (Dec.readU8 _ E es) ?_ rfl
  rw [tag_toNat (by decide), if_pos rfl]
  exact Dec.pure _ E es

/-! ### Small facts -/

theorem strHdr_length (s : Bytes) : 2 ≤ (strHdr s).length := by
  unfold strHdr; split <;> simp [le_length]

theorem serInt_length (t : IntTy) (x : Int) : 1 ≤ (serInt t x).length := by
  cases t <;> simp only [serInt, serInt32, serInt64] <;> (try split) <;> (try split) <;> simp

theorem ser_length_pos (es : ES) : ∀ x : V, 1 ≤ (ser es x).1.length
  | .int t x => serInt_length t x
  | .flt _ _ => by simp [ser]
  | .bool _ => by simp [ser]
  | .char _ => by simp [ser]
  | .nothing => by simp only [ser]; unfold writeAsTag; split <;> simp
  | .sym n => serSym_length_pos es n
  | .str s => by
    rw [ser_str]; have := strHdr_length s
    split <;> simp <;> omega
  | .tup xs => by
    by_cases h : xs = []
    · subst h; simp [ser]
    · rw [ser_tup es xs h]; unfold tupHdr; split <;> simp
  | .expr _ _ => by rw [ser_expr]; unfold exprHdr; split <;> simp
  | .anyvec _ => by rw [ser_anyvec]; simp
  | .ivec _ _ => by simp [ser]
  | .bvec _ => by simp [ser]
  | .refv _ => by rw [ser_refv]; simp
  | .urange _ _ => by rw [ser_urange]; simp
  | .ntup _ _ => by rw [ser_ntup]; simp
  | .back k => emitBackref_ne k

theorem typeTag_ok : ∀ (x : V) (t : Nat), typeTag x = some t → TagOK t := by
  intro x t h
  cases x with
  | int u _ => cases u <;> (simp only [typeTag, intTag, Option.some.injEq] at h; subst h; unfold TagOK; decide)
  | flt w _ => cases w <;> (simp only [typeTag, FTy.tag, Option.some.injEq] at h; subst h; unfold TagOK; decide)
  | bool _ => simp only [typeTag, Option.some.injEq] at h; subst h; unfold TagOK; decide
  | char _ => simp only [typeTag, Option.some.injEq] at h; subst h; unfold TagOK; decide
  | str _ => simp only [typeTag, Option.some.injEq] at h; subst h; unfold TagOK; decide
  | sym _ => simp only [typeTag, Option.some.injEq] at h; subst h; unfold TagOK; decide
  | _ => simp [typeTag] at h

theorem ftsOf_ok (xs : List V) (h : ∀ x ∈ xs, (typeTag x).isSome) : ∀ t ∈ ftsOf xs, TagOK t := by
  intro t ht
  simp only [ftsOf, List.mem_map] at ht
  obtain ⟨x, hx, rfl⟩ := ht
  have hs := h x hx
  cases hc : typeTag x with
  | none => rw [hc] at hs; cases hs
  | some u => simp only [Option.getD_some]; exact typeTag_ok x u hc

theorem allSome_map : ∀ xs : List V, allSome (xs.map some) = some xs
  | [] => rfl
  | x :: xs => by simp [allSome, allSome_map xs]

theorem fieldsOk_ftsOf : ∀ xs : List V, (∀ x ∈ xs, (typeTag x).isSome) → fieldsOk (ftsOf xs) xs = true
  | [] => fun _ => rfl
  | x :: xs => fun h => by
    have hs := h x (by simp)
    have ih := fieldsOk_ftsOf xs (fun y hy => h y (by simp [hy]))
    simp only [ftsOf, List.map_cons] at ih ⊢
    simp only [fieldsOk, ih, Bool.and_true]
    cases hc : typeTag x with
    | none => rw [hc] at hs; cases hs
    | some u => simp

/-! ### Element loops -/

/-- `deserialize` reads back every well-formed value whose bytes fit in the budget `f`. -/
def ValueDec (f : Nat) : Prop :=
  ∀ (x : V) (es : ES), Inv es → WF es x → (ser es x).2.counter ≤ 2 ^ 63 → (ser es x).1.length ≤ f →
    Dec (Serialization.deser f) [] es (ser es x).1 (.v x) [] (ser es x).2

theorem Dec.valueList {f : Nat} (ih : ValueDec f) : ∀ (xs : List V) (es : ES), Inv es → WFList es xs →
    (serList es xs).2.counter ≤ 2 ^ 63 → (serList es xs).1.length ≤ f →
    Dec (Serialization.readMany (do let o ← Serialization.deser f; Serialization.asV o) xs.length)
      [] es (serList es xs).1 xs [] (serList es xs).2
  | [], es, _, _, _, _ => Dec.readMany_nil _ [] es
  | x :: xs, es, hinv, hw, h63, hf => by
    obtain ⟨i1, _⟩ := ser_grows es x hinv
    obtain ⟨_, p2⟩ := serList_grows (ser es x).2 xs i1
    simp only [WFList] at hw
    rw [serList_cons] at h63 hf ⊢
    dsimp only at h63 hf ⊢
    simp only [List.length_append] at hf
    exact Dec.readMany_cons (Dec.asV (ih x es hinv hw.1 (by have := p2.1; omega) (by omega)))
      (Dec.valueList ih xs _ i1 hw.2 h63 (by omega))

theorem Dec.someList {f : Nat} (ih : ValueDec f) : ∀ (xs : List V) (es : ES), Inv es → WFList es xs →
    (serList es xs).2.counter ≤ 2 ^ 63 → (serList es xs).1.length ≤ f →
    Dec (Serialization.readMany (readOpt (handle f)) xs.length)
      [] es (serList es xs).1 (xs.map some) [] (serList es xs).2
  | [], es, _, _, _, _ => Dec.readMany_nil _ [] es
  | x :: xs, es, hinv, hw, h63, hf => by
    obtain ⟨i1, _⟩ := ser_grows es x hinv
    obtain ⟨_, p2⟩ := serList_grows (ser es x).2 xs i1
    simp only [WFList] at hw
    rw [serList_cons] at h63 hf ⊢
    dsimp only at h63 hf ⊢
    simp only [List.length_append] at hf
    exact Dec.readMany_cons (Dec.readOpt_of (ih x es hinv hw.1 (by have := p2.1; omega) (by omega)))
      (Dec.someList ih xs _ i1 hw.2 h63 (by omega))

theorem Dec.optList {f : Nat} (ih : ValueDec f) : ∀ (xs : List (Option V)) (es : ES), Inv es →
    WFOptList es xs → (serOptList es xs).2.counter ≤ 2 ^ 63 → (serOptList es xs).1.length ≤ f →
    Dec (Serialization.readMany (readOpt (handle f)) xs.length)
      [] es (serOptList es xs).1 xs [] (serOptList es xs).2
  | [], es, _, _, _, _ => Dec.readMany_nil _ [] es
  | x :: xs, es, hinv, hw, h63, hf => by
    obtain ⟨i1, _⟩ := serOpt_grows es x hinv
    obtain ⟨_, p2⟩ := serOptList_grows (serOpt es x).2 xs i1
    simp only [WFOptList] at hw
    rw [serOptList_cons] at h63 hf ⊢
    dsimp only at h63 hf ⊢
    simp only [List.length_append] at hf
    refine Dec.readMany_cons ?_ (Dec.optList ih xs _ i1 hw.2 h63 (by omega))
    cases x with
    | none => exact Dec.readOpt_none [] es
    | some x =>
      simp only [WFOpt] at hw
      have hp := p2.1
      simp only [serOpt] at hp h63 hf ⊢
      exact Dec.readOpt_of (ih x es hinv hw.1 (by omega) (by omega))

end JuliaLean.Serialization
