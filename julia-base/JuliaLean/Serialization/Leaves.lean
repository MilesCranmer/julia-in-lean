import JuliaLean.Serialization.Handle

/-!
Decoding of the values without children: integers, floats, `Bool`, `nothing`,
`Char`, strings, symbols, backreferences and module references.
-/

namespace JuliaLean.Serialization

open JuliaLean

theorem Dec.pureV {o : Obj} (E : List Nat) (es : ES) : Dec (Pure.pure o : Dm Obj) E es [] o E es :=
  Dec.pure o E es

theorem Dec.deserTag {f n : Nat} {tail : Bytes} {E E' : List Nat} {es es' : ES} {a : Obj}
    (hn : n < 256) (h : Dec (handle f n) E es tail a E' es') :
    Dec (Serialization.deser f) E es (UInt8.ofNat n :: tail) a E' es' :=
  Dec.deser (tag_toNat hn) h

/-! ### Integers -/

theorem Dec.readIntV {t : IntTy} {x : Int} (hx : InRange t x) (E : List Nat) (es : ES)
    (g : Int → Obj) :
    Dec (do let y ← Serialization.readInt t; Pure.pure (g y)) E es (le (nbytes t) (intBits t x)) (g x) E es :=
  Dec.bind (b2 := []) (Dec.readInt hx E es) (Dec.pure _ E es) (by simp)

theorem intTag_lt (t : IntTy) : intTag t < 256 := by cases t <;> decide

theorem Dec.int {f : Nat} {t : IntTy} {x : Int} (hx : InRange t x) (E : List Nat) (es : ES) :
    Dec (Serialization.deser (f + 1)) E es (serInt t x) (.v (.int t x)) E es := by
  have generic : Dec (Serialization.deser (f + 1)) E es
      (UInt8.ofNat (intTag t) :: le (nbytes t) (intBits t x)) (.v (.int t x)) E es := by
    refine Dec.deserTag (intTag_lt t) ?_
    rw [handle_int]
    exact Dec.readIntV hx E es (fun y => .v (.int t y))
  cases t with
  | i32 =>
    unfold serInt serInt32
    by_cases hs : 0 ≤ x ∧ x ≤ 32
    · simp only [hs, and_self, ↓reduceIte, ZERO32_TAG]
      refine Dec.deserTag (by omega) ?_
      rw [handle_value f _ (by omega)]
      refine Dec.desertag ?_
      rw [desertag_eq]
      simp only [show ¬ (190 + x.toNat = 0) from by omega, show ¬ (190 + x.toNat < 68) from by omega,
        show ¬ (190 + x.toNat = 68) from by omega, show ¬ (190 + x.toNat = 74) from by omega,
        show ¬ (190 + x.toNat < 76) from by omega, show ¬ (190 + x.toNat = 76) from by omega,
        show ¬ (190 + x.toNat = 77) from by omega, show ¬ (190 + x.toNat = 78) from by omega,
        show ¬ (190 + x.toNat < 190) from by omega, show (190 + x.toNat < 223) from by omega,
        ↓reduceIte]
      congr 3
      omega
    · simp only [hs, ↓reduceIte]
      exact generic
  | i64 =>
    unfold serInt serInt64
    by_cases hs : 0 ≤ x ∧ x ≤ 32
    · simp only [hs, and_self, ↓reduceIte, ZERO64_TAG]
      refine Dec.deserTag (by omega) ?_
      rw [handle_value f _ (by omega)]
      refine Dec.desertag ?_
      rw [desertag_eq]
      simp only [show ¬ (223 + x.toNat = 0) from by omega, show ¬ (223 + x.toNat < 68) from by omega,
        show ¬ (223 + x.toNat = 68) from by omega, show ¬ (223 + x.toNat = 74) from by omega,
        show ¬ (223 + x.toNat < 76) from by omega, show ¬ (223 + x.toNat = 76) from by omega,
        show ¬ (223 + x.toNat = 77) from by omega, show ¬ (223 + x.toNat = 78) from by omega,
        show ¬ (223 + x.toNat < 190) from by omega, show ¬ (223 + x.toNat < 223) from by omega,
        show (223 + x.toNat ≤ 255) from by omega, ↓reduceIte]
      congr 3
      omega
    · simp only [hs, ↓reduceIte]
      by_cases hm : -2 ^ 31 ≤ x ∧ x ≤ 2 ^ 31 - 1
      · simp only [hm, and_self, ↓reduceIte, SHORTINT64_TAG]
        refine Dec.deserTag (by decide) ?_
        rw [handle_shortint64]
        have hr : InRange .i32 x := by
          simp only [InRange, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; simp; omega
        exact Dec.readIntV (t := .i32) hr E es (fun y => .v (.int .i64 y))
      · simp only [hm, ↓reduceIte]
        exact generic
  | i8 => exact generic
  | i16 => exact generic
  | i128 => exact generic
  | u8 => exact generic
  | u16 => exact generic
  | u32 => exact generic
  | u64 => exact generic
  | u128 => exact generic

/-! ### Floats, `Bool`, `nothing`, `Char` -/

theorem FTy.tag_lt (w : FTy) : w.tag < 256 := by cases w <;> decide

theorem Dec.flt {f : Nat} {w : FTy} {b : Nat} (hb : b < 256 ^ w.nbytes) (E : List Nat) (es : ES) :
    Dec (Serialization.deser (f + 1)) E es (UInt8.ofNat w.tag :: le w.nbytes b) (.v (.flt w b)) E es := by
  refine Dec.deserTag w.tag_lt ?_
  rw [handle_flt]
  refine Dec.bind (b2 := []) (Dec.readLE w.nbytes b E es) ?_ (by simp)
  rw [Nat.mod_eq_of_lt hb]
  exact Dec.pure _ E es

theorem Dec.bool {f : Nat} (b : Bool) (E : List Nat) (es : ES) :
    Dec (Serialization.deser (f + 1)) E es [UInt8.ofNat (if b then TRUE_TAG else FALSE_TAG)]
      (.v (.bool b)) E es := by
  cases b <;>
  · refine Dec.deserTag (by decide) ?_
    rw [handle_value f _ (by decide)]
    exact Dec.desertag (by rw [desertag_eq]; rfl)

theorem Dec.nothing {f : Nat} (E : List Nat) (es : ES) :
    Dec (Serialization.deser (f + 1)) E es (writeAsTag NOTHING_TAG) (.v .nothing) E es := by
  refine Dec.deserTag (by decide) ?_
  rw [handle_value f _ (by decide)]
  exact Dec.desertag (by rw [desertag_eq]; rfl)

theorem Dec.char {f : Nat} {c : Nat} (hc : CharWF c) (E : List Nat) (es : ES) :
    Dec (Serialization.deser (f + 1)) E es ([UInt8.ofNat CHAR_TAG] ++ writeChar c) (.v (.char c)) E es := by
  refine Dec.deserTag (by decide) ?_
  rw [handle_char]
  exact Dec.bind (b2 := []) (Dec.readChar hc E es) (Dec.pure _ E es) (by simp)

/-! ### Backreferences -/

theorem Dec.getBackref {k : Nat} {e : Key} {E : List Nat} {es : ES} (hE : k ∉ E)
    (hk : encTable es k = some e) :
    Dec (Serialization.getBackref (k : Int)) E es [] (ofEntry k e) E es := by
  intro ds rest ha hio
  refine ⟨ds, ?_, by simpa using hio, ha, rfl, rfl⟩
  have : ds.table k = some e := by rw [ha.table, if_neg hE, hk]
  simp [Serialization.getBackref, this]

theorem Dec.backref {f k : Nat} {e : Key} {E : List Nat} {es : ES} (hk63 : k < 2 ^ 63) (hE : k ∉ E)
    (hk : encTable es k = some e) :
    Dec (Serialization.deser (f + 1)) E es (emitBackref k) (ofEntry k e) E es := by
  unfold emitBackref
  by_cases h1 : k ≤ 65535
  · simp only [h1, ↓reduceIte]
    refine Dec.deserTag (by decide) ?_
    rw [handle_shortbackref]
    refine Dec.bind (b2 := []) (Dec.readLE 2 k E es) ?_ (by simp)
    rw [Nat.mod_eq_of_lt (by omega)]
    exact Dec.getBackref hE hk
  · simp only [h1, ↓reduceIte]
    by_cases h2 : k ≤ 2 ^ 31 - 1
    · simp only [h2, ↓reduceIte]
      refine Dec.deserTag (by decide) ?_
      rw [handle_backref]
      have hr : InRange .i32 (k : Int) := by
        simp only [InRange, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; simp; omega
      have hb : le 4 k = le (nbytes .i32) (intBits .i32 (k : Int)) := by
        congr 1; simp [intBits, IntTy.bits]; omega
      rw [hb]
      exact Dec.bind (b2 := []) (Dec.readInt hr E es) (Dec.getBackref hE hk) (by simp)
    · simp only [h2, ↓reduceIte]
      refine Dec.deserTag (by decide) ?_
      rw [handle_longbackref]
      have hr : InRange .i64 (k : Int) := by
        simp only [InRange, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; simp; omega
      have hb : le 8 k = le (nbytes .i64) (intBits .i64 (k : Int)) := by
        congr 1; simp [intBits, IntTy.bits]; omega
      rw [hb]
      exact Dec.bind (b2 := []) (Dec.readInt hr E es) (Dec.getBackref hE hk) (by simp)

/-! ### Strings -/

/-- The string header and bytes (`:416-423`). -/
def strHdr (s : Bytes) : Bytes :=
  if s.length ≤ 255 then [UInt8.ofNat STRING_TAG, UInt8.ofNat s.length]
  else UInt8.ofNat LONGSTRING_TAG :: le 8 s.length

theorem Dec.deserString {s : Bytes} (E : List Nat) (es : ES) :
    Dec (Serialization.deserString (s.length : Int)) E es s (.v (.str s)) E es := by
  unfold Serialization.deserString
  simp only [show ¬ ((s.length : Int) < 0) from by omega, ↓reduceIte, Int.toNat_natCast]
  exact Dec.bind (b2 := []) (Dec.readN s E es) (Dec.pure _ E es) (by simp)

theorem Dec.strBody {f : Nat} {s : Bytes} (hs : s.length < 2 ^ 63) (E : List Nat) (es : ES) :
    Dec (Serialization.deser (f + 1)) E es (strHdr s ++ s) (.v (.str s)) E es := by
  unfold strHdr
  by_cases hl : s.length ≤ 255
  · simp only [hl, ↓reduceIte, List.cons_append, List.nil_append]
    refine Dec.deserTag (by decide) ?_
    rw [handle_string]
    refine Dec.bind (Dec.readU8 _ E es) ?_ rfl
    rw [tag_toNat (by omega)]
    exact Dec.deserString E es
  · simp only [hl, ↓reduceIte, List.cons_append]
    refine Dec.deserTag (by decide) ?_
    rw [handle_longstring]
    have hr : InRange .i64 (s.length : Int) := by
      simp only [InRange, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; simp; omega
    have hb : le 8 s.length = le (nbytes .i64) (intBits .i64 (s.length : Int)) := by
      congr 1; simp [intBits, IntTy.bits]; omega
    rw [hb]
    exact Dec.bind (Dec.readInt hr E es) (Dec.deserString E es) rfl

theorem ser_str (es : ES) (s : Bytes) :
    ser es (.str s) = if s.length > 7 then (UInt8.ofNat SHARED_REF_TAG :: strHdr s ++ s, es.newObj)
      else (strHdr s ++ s, es) := by
  simp only [ser, strHdr]

theorem Dec.str {f : Nat} {s : Bytes} {E : List Nat} {es : ES} (hinv : Inv es) (hs : s.length < 2 ^ 63) :
    Dec (Serialization.deser (f + 2)) E es (ser es (.str s)).1 (.v (.str s)) E (ser es (.str s)).2 := by
  rw [ser_str]
  by_cases hl : s.length > 7
  · simp only [hl, ↓reduceIte]
    refine Dec.deserTag (by decide) ?_
    rw [handle_shared]
    refine Dec.bind (b2 := strHdr s ++ s) (Dec.newSlot .obj E es) ?_ (by simp)
    refine Dec.bind (b2 := []) (Dec.strBody (f := f) hs _ _) ?_ (by simp)
    refine Dec.bind (b2 := []) (Dec.setBackref ?_) (Dec.pure _ _ _) (by simp)
    rw [encTable_register hinv]
    simp
  · simp only [hl, ↓reduceIte]
    exact Dec.strBody (f := f + 1) hs E es

/-! ### Symbols -/

theorem findIdx_spec {name : Bytes} : ∀ (l : List Bytes) (i : Nat),
    l.findIdx? (· == name) = some i → i < l.length ∧ l.getD i [] = name
  | [], i, h => by simp at h
  | a :: l, i, h => by
    rw [List.findIdx?_cons] at h
    by_cases ha : (a == name) = true
    · simp only [ha, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp only [beq_iff_eq] at ha
      simp [ha]
    · simp only [ha, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h
      have := findIdx_spec l j hj
      have h2 := this.2
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this.1, Option.getD_some] at h2
      simp [this.1, h2]

theorem sertagSym_spec {name : Bytes} {t : Nat} (h : sertagSym name = some t) :
    79 ≤ t ∧ t ≤ 165 ∧ symOfTag t = name := by
  unfold sertagSym at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨i, hi, rfl⟩ := h
  obtain ⟨hlt, hget⟩ := findIdx_spec symTagNames i hi
  have hlen : symTagNames.length = 87 := rfl
  refine ⟨by omega, by omega, ?_⟩
  unfold symOfTag
  simp only [show i + 79 ≤ 165 from by omega, ↓reduceIte, Nat.add_sub_cancel]
  exact hget

/-- The symbol header (`:323-329`). -/
def symHdr (name : Bytes) : Bytes :=
  if name.length ≤ 255 then [UInt8.ofNat SYMBOL_TAG, UInt8.ofNat name.length]
  else UInt8.ofNat LONGSYMBOL_TAG :: le 4 name.length

theorem Dec.mkSymbol {name : Bytes} (h : 0 ∉ name) (E : List Nat) (es : ES) :
    Dec (Serialization.mkSymbol name) E es [] (.sym name) E es := by
  unfold Serialization.mkSymbol
  have : name.contains 0 = false := by simpa using h
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  exact Dec.pure _ E es

/-- `deserialize_symbol(s, len)` on the name. -/
theorem Dec.deserSymbol {name : Bytes} {E : List Nat} {es : ES} (h : 0 ∉ name) :
    Dec (Serialization.deserSymbol (name.length : Int)) E es name (.v (.sym name)) E
      (if name.length > 7 then es.register (.sym name) else es) := by
  unfold Serialization.deserSymbol
  simp only [show ¬ ((name.length : Int) < 0) from by omega, ↓reduceIte, Int.toNat_natCast]
  refine Dec.bind (b2 := []) (Dec.readN name E es) ?_ (by simp)
  refine Dec.bind (b2 := []) (Dec.mkSymbol h E es) ?_ (by simp)
  by_cases hl : name.length > 7
  · have : ((name.length : Int) > 7) := by omega
    simp only [this, hl, ↓reduceIte]
    exact Dec.bind (b2 := []) (Dec.resolveNow (.sym name) E es) (Dec.pure _ _ _) (by simp)
  · have : ¬ ((name.length : Int) > 7) := by omega
    simp only [this, hl, ↓reduceIte]
    exact Dec.pure _ E es

theorem Dec.symBody {f : Nat} {name : Bytes} {E : List Nat} {es : ES} (hw : SymWF name) :
    Dec (Serialization.deser (f + 1)) E es (symHdr name ++ name) (.v (.sym name)) E
      (if name.length > 7 then es.register (.sym name) else es) := by
  unfold symHdr
  by_cases hl : name.length ≤ 255
  · simp only [hl, ↓reduceIte, List.cons_append, List.nil_append]
    refine Dec.deserTag (by decide) ?_
    rw [handle_symbol]
    refine Dec.bind (Dec.readU8 _ E es) ?_ rfl
    rw [tag_toNat (by omega)]
    exact Dec.deserSymbol hw.1
  · simp only [hl, ↓reduceIte, List.cons_append]
    refine Dec.deserTag (by decide) ?_
    rw [handle_longsymbol]
    have hr : InRange .i32 (name.length : Int) := by
      have := hw.2
      simp only [InRange, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; simp; omega
    have hb : le 4 name.length = le (nbytes .i32) (intBits .i32 (name.length : Int)) := by
      have := hw.2
      congr 1; simp [intBits, IntTy.bits]; omega
    rw [hb]
    exact Dec.bind (Dec.readInt hr E es) (Dec.deserSymbol hw.1) rfl

/-- `serialize(s, ::Symbol)` decodes back to the symbol and registers the same slots. -/
theorem Dec.sym {f : Nat} {name : Bytes} {E : List Nat} {es : ES} (hinv : Inv es)
    (h63 : es.counter ≤ 2 ^ 63) (hw : SymWF name)
    (hE : ∀ p ∈ E, encTable es p ≠ some (.sym name)) :
    Dec (Serialization.deser (f + 1)) E es (serSym es name).1 (.v (.sym name)) E (serSym es name).2 := by
  unfold serSym
  cases ht : sertagSym name with
  | some t =>
    obtain ⟨h1, h2, h3⟩ := sertagSym_spec ht
    simp only [writeAsTag, VALUE_TAGS, show ¬ (t < 68) from by omega, ↓reduceIte]
    refine Dec.deserTag (by omega) ?_
    rw [handle_value f t (by omega)]
    refine Dec.desertag ?_
    rw [desertag_eq]
    simp only [show ¬ (t = 0) from by omega, show ¬ (t < 68) from by omega,
      show ¬ (t = 68) from by omega, show ¬ (t = 74) from by omega,
      show ¬ (t < 76) from by omega, show ¬ (t = 76) from by omega,
      show ¬ (t = 77) from by omega, show ¬ (t = 78) from by omega,
      show (t < 190) from by omega, ↓reduceIte, h3]
  | none =>
    simp only
    by_cases hl : name.length > 7
    · simp only [hl, ↓reduceIte]
      cases hk : es.tab.lookup (.sym name) with
      | some k =>
        simp only
        have hm := lookup_mem es.tab hk
        have hkt := encTable_of_mem hinv hm
        have hkE : k ∉ E := fun hm' => hE k hm' hkt
        exact Dec.backref (by have := lt_of_mem hinv hm; omega) hkE hkt
      | none =>
        simp only
        have := Dec.symBody (f := f) (E := E) (es := es) hw
        simp only [hl, ↓reduceIte] at this
        exact this
    · simp only [hl, ↓reduceIte]
      have := Dec.symBody (f := f) (E := E) (es := es) hw
      simp only [hl, ↓reduceIte] at this
      exact this

end JuliaLean.Serialization
