import JuliaLean.Serialization.Composite

/-!
The round trip: every well-formed value decodes back to itself, every slot agrees,
the header is accepted for every version up to `ser_version`, and backreferences
decode at every width.
-/

namespace JuliaLean.Serialization

open JuliaLean

theorem valueDec : ∀ f, ValueDec f
  | 0 => fun x es _ _ _ hf => absurd hf (by have := ser_length_pos es x; omega)
  | f + 1 => fun x es hinv hw h63 hf => by
    have ih := valueDec f
    cases x with
    | int t x => exact Dec.int hw [] es
    | flt w b => exact Dec.flt hw [] es
    | bool b => exact Dec.bool b [] es
    | char c => exact Dec.char hw [] es
    | nothing => exact Dec.nothing [] es
    | sym n =>
      have := (serSym_grows es n hinv).2.1
      exact Dec.sym hinv (by simp only [ser] at h63; omega) hw (fun p hp => absurd hp (List.not_mem_nil))
    | str s =>
      have hl : 2 ≤ (ser es (.str s)).1.length := by
        rw [ser_str]; have := strHdr_length s; split <;> simp <;> omega
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      exact Dec.str hinv hw
    | tup xs => exact Dec.tupCase ih hinv hw h63 hf
    | expr hd args => exact Dec.exprCase ih hinv hw h63 hf
    | anyvec xs => exact Dec.anyvecCase ih hinv hw h63 hf
    | ivec t xs => exact Dec.ivecCase hinv hw hf
    | bvec xs => exact Dec.bvecCase hinv hw hf
    | refv x => exact Dec.refvCase ih hinv hw h63 hf
    | urange lo hi => exact Dec.urangeCase hinv hw h63 hf
    | ntup names xs => exact Dec.ntupCase ih hinv hw h63 hf
    | back k =>
      have hk := lt_of_mem hinv hw
      exact Dec.backref (by simp only [ser] at h63; omega) (List.not_mem_nil) (encTable_of_mem hinv hw)

/-- The header bytes after `HEADER_TAG` for format version `ver`. -/
def hdrTail (ver : Nat) : Bytes := [0x4a, 0x4c, UInt8.ofNat ver, 0x04, 0, 0, 0]

theorem readHeader_ok {ver : Nat} (hv : ver < 256) (hle : ver ≤ serVersion) (s : DS) (rest : Bytes)
    (hio : s.io = hdrTail ver ++ rest) :
    readHeader s = .ok ((), { s with io := rest, version := ver }) := by
  have hv' : (UInt8.ofNat ver).toNat = ver := tag_toNat hv
  simp only [hdrTail, List.cons_append, List.nil_append] at hio
  unfold readHeader
  rw [bind_run (readU8_run hio), bind_run (readU8_run rfl)]
  simp only [show ¬ ((0x4a : UInt8) ≠ 0x4a ∨ (0x4c : UInt8) ≠ 0x4c) by decide, ↓reduceIte]
  rw [bind_run (readU8_run rfl), bind_run (readU8_run rfl), bind_run (readU8_run rfl),
    bind_run (readU8_run rfl), bind_run (readU8_run rfl)]
  simp only [show (4 : UInt8).toNat % 4 = 0 by decide, show (4 : UInt8).toNat / 4 % 4 = 1 by decide, hv',
    show ¬ (1 > 1) by decide, show ¬ (0 > 1) by decide, show ¬ ((0 : Nat) ≠ 0) by decide,
    show ¬ (ver > serVersion) by omega, ↓reduceIte]
  rfl

theorem readHeader_new {ver : Nat} (hv : ver < 256) (hgt : serVersion < ver) (s : DS) (rest : Bytes)
    (hio : s.io = hdrTail ver ++ rest) :
    readHeader s = .error (.errorEx "Cannot read stream serialized with a newer version of Julia") := by
  have hv' : (UInt8.ofNat ver).toNat = ver := tag_toNat hv
  simp only [hdrTail, List.cons_append, List.nil_append] at hio
  unfold readHeader
  rw [bind_run (readU8_run hio), bind_run (readU8_run rfl)]
  simp only [show ¬ ((0x4a : UInt8) ≠ 0x4a ∨ (0x4c : UInt8) ≠ 0x4c) by decide, ↓reduceIte]
  rw [bind_run (readU8_run rfl), bind_run (readU8_run rfl), bind_run (readU8_run rfl),
    bind_run (readU8_run rfl), bind_run (readU8_run rfl)]
  simp only [show (4 : UInt8).toNat % 4 = 0 by decide, show (4 : UInt8).toNat / 4 % 4 = 1 by decide, hv',
    show ¬ (1 > 1) by decide, show ¬ (0 > 1) by decide, show ¬ ((0 : Nat) ≠ 0) by decide,
    show ver > serVersion by omega, ↓reduceIte]
  rfl

/-- The decode of a stream with a header of version `ver ≤ ser_version`, then a value. -/
theorem decode_after_header {ver : Nat} (hv : ver < 256) (hle : ver ≤ serVersion) {x : V}
    (hw : WF ES.init x) (h63 : (ser ES.init x).2.counter ≤ 2 ^ 63) (rest : Bytes) :
    ∃ ds', deser ((UInt8.ofNat HEADER_TAG :: hdrTail ver ++ (ser ES.init x).1 ++ rest).length + 1)
        (DS.init (UInt8.ofNat HEADER_TAG :: hdrTail ver ++ (ser ES.init x).1 ++ rest)) = .ok (.v x, ds') ∧
      ds'.io = rest ∧ AgreeOn [] (ser ES.init x).2 ds' := by
  let io := UInt8.ofNat HEADER_TAG :: hdrTail ver ++ (ser ES.init x).1 ++ rest
  have hio : (DS.init io).io = UInt8.ofNat HEADER_TAG :: (hdrTail ver ++ ((ser ES.init x).1 ++ rest)) := by
    simp [io, DS.init, List.append_assoc]
  have hlen : (ser ES.init x).1.length ≤ io.length := by simp [io]; omega
  obtain ⟨n, hn⟩ : ∃ n, io.length + 1 = (n + 1) + 1 := ⟨io.length - 1, by simp [io]⟩
  show ∃ ds', deser (io.length + 1) (DS.init io) = _ ∧ _
  rw [hn, deser_eq, bind_run (readU8_run hio), tag_toNat (by decide), handle_header]
  let s1 : DS := { DS.init io with io := hdrTail ver ++ ((ser ES.init x).1 ++ rest) }
  rw [bind_run (readHeader_ok hv hle s1 _ rfl)]
  have ha : AgreeOn [] ES.init { s1 with io := (ser ES.init x).1 ++ rest, version := ver } :=
    (agree_init io).congr rfl rfl
  obtain ⟨ds', r, io', a', _, _⟩ := valueDec (n + 1) x ES.init inv_init hw h63 (by simp [io] at hn hlen; omega)
    _ rest ha rfl
  exact ⟨ds', r, io', a'⟩

theorem header_eq : header = UInt8.ofNat HEADER_TAG :: hdrTail serVersion := rfl

theorem headerVersions_proof : HeaderVersions := by
  intro ver hv x hw h63 rest
  by_cases hle : ver ≤ serVersion
  · rw [if_pos hle]
    obtain ⟨ds', r, io', _⟩ := decode_after_header hv hle hw h63 rest
    have : [UInt8.ofNat HEADER_TAG, 0x4a, 0x4c, UInt8.ofNat ver, 0x04, 0, 0, 0] ++ (ser ES.init x).1 ++ rest =
        UInt8.ofNat HEADER_TAG :: hdrTail ver ++ (ser ES.init x).1 ++ rest := rfl
    rw [this]
    unfold deserialize
    rw [r]
    show Except.ok (Obj.v x, ds'.io) = _
    rw [io']
  · rw [if_neg hle]
    let io := UInt8.ofNat HEADER_TAG :: hdrTail ver ++ (ser ES.init x).1 ++ rest
    have : [UInt8.ofNat HEADER_TAG, 0x4a, 0x4c, UInt8.ofNat ver, 0x04, 0, 0, 0] ++ (ser ES.init x).1 ++ rest =
        io := rfl
    rw [this]
    have hio : (DS.init io).io = UInt8.ofNat HEADER_TAG :: (hdrTail ver ++ ((ser ES.init x).1 ++ rest)) := by
      simp [io, DS.init, List.append_assoc]
    obtain ⟨n, hn⟩ : ∃ n, io.length + 1 = n + 1 := ⟨io.length, rfl⟩
    unfold deserialize
    rw [hn, deser_eq, bind_run (readU8_run hio), tag_toNat (by decide)]
    cases n with
    | zero => simp [io] at hn
    | succ n =>
      rw [handle_header, bind_err (readHeader_new hv (by omega) _ _ rfl)]

theorem roundTrip_proof : RoundTrip := by
  intro x hw h63 rest
  have := headerVersions_proof serVersion (by decide) x hw h63 rest
  rw [if_pos (Nat.le_refl _)] at this
  unfold serialize
  rw [header_eq]
  exact this

theorem slotAgreement_proof : SlotAgreement := by
  intro x hw h63 rest
  obtain ⟨ds', r, io', a'⟩ := decode_after_header (ver := serVersion) (by decide) (Nat.le_refl _) hw h63 rest
  refine ⟨ds', ?_, io', a'.counter, fun k => by rw [a'.table k]; simp⟩
  unfold deserializeState serialize
  rw [header_eq]
  exact r

theorem backrefDecode_proof : BackrefDecode := by
  intro k hk s e rest he hio
  have hg : ∀ s' : DS, s'.table k = some e → getBackref (k : Int) s' = .ok (ofEntry k e, s') := by
    intro s' h; simp [getBackref, h]
  unfold emitBackref at hio
  by_cases h1 : k ≤ 65535
  · simp only [h1, ↓reduceIte, List.cons_append] at hio
    rw [deser_eq, bind_run (readU8_run hio), tag_toNat (by decide),
      show handle 1 SHORTBACKREF_TAG = _ from handle_shortbackref 0, bind_run (readLE_run rfl),
      Nat.mod_eq_of_lt (by omega)]
    exact hg _ he
  · by_cases h2 : k ≤ 2 ^ 31 - 1
    · simp only [h1, h2, ↓reduceIte, List.cons_append] at hio
      rw [deser_eq, bind_run (readU8_run hio), tag_toNat (by decide),
        show handle 1 BACKREF_TAG = _ from handle_backref 0, le4_len (by omega),
        bind_run (readInt_run (i32_len (by omega)) rfl)]
      exact hg _ he
    · simp only [h1, h2, ↓reduceIte, List.cons_append] at hio
      have hb : le 8 k = le (nbytes .i64) (intBits .i64 (k : Int)) := by
        congr 1; simp [intBits, IntTy.bits]; omega
      rw [deser_eq, bind_run (readU8_run hio), tag_toNat (by decide),
        show handle 1 LONGBACKREF_TAG = _ from handle_longbackref 0, hb,
        bind_run (readInt_run (i64_len hk) rfl)]
      exact hg _ he

end JuliaLean.Serialization
