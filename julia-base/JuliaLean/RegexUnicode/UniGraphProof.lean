import JuliaLean.RegexUnicode.UniGraphemes

/-!
# Proofs: `titlecase(s; strict=false)` and `graphemes(s, m:n)`

`isgraphemebreak!` never throws on master: it converts only well-formed characters,
and `UInt32(c)` succeeds on them. The loops are proved for any functions they call
that satisfy the facts used (`GbTotal`, `Good`), and those facts are then proved for
the String functions.
-/

namespace JuliaLean.RegexUnicode.Uni

open JuliaLean JuliaLean.Strings

/-! ## `isgraphemebreak!` returns -/

theorem clo32_le (x : UInt32) : clo32 x ≤ 32 := by
  unfold clo32 clz32; split <;> omega

/-- `UInt32(c::Char)` succeeds on every well-formed character (master). -/
theorem codepoint_ok_of_wf (c : UInt32) (h : ismalformed c = false) : ∃ u, codepoint c = .ok u := by
  have hl := clo32_le c
  have e1 : (ix (Int.ofNat (clo32 c) * 8)).val = Int.ofNat (clo32 c) * 8 :=
    ix_val _ (by simp only [Int.ofNat_eq_coe]; omega) (by simp only [Int.ofNat_eq_coe]; omega)
  have e2 : ix (8 * Int.ofNat (clo32 c)) = ix (Int.ofNat (clo32 c) * 8) := by rw [Int.mul_comm]
  have hc : (decide (clo32 c = 1) ||
      decide ((ix (8 * Int.ofNat (clo32 c)) + ix (land56 (ctz32 c))).val > 32) ||
      (ushr32 ((c &&& 0x00c0c0c0) ^^^ 0x00808080) (land56 (ctz32 c)) != 0)) = false := by
    rw [e2]
    have hd : decide (clo32 c = 1) = decide ((ix (Int.ofNat (clo32 c) * 8)).val = 8) := by
      rw [e1]; simp only [decide_eq_decide, Int.ofNat_eq_coe]; omega
    rw [hd]; exact h
  unfold codepoint
  simp only [hc, Bool.false_eq_true, if_false]
  split <;> exact ⟨_, rfl⟩

/-- `isgraphemebreak!` never throws. -/
def GbTotal (gb : GbFn) : Prop := ∀ st c1 c2, ∃ r, gb st c1 c2 = .ok r

theorem gb_ok (P : Utf8proc) : GbTotal (isgraphemebreakBang P) := by
  intro st c1 c2
  unfold isgraphemebreakBang
  split
  · exact ⟨_, rfl⟩
  · rename_i hm
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hm
    obtain ⟨u1, h1⟩ := codepoint_ok_of_wf c1 hm.1
    obtain ⟨u2, h2⟩ := codepoint_ok_of_wf c2 hm.2
    simp only [h1, h2]
    exact ⟨_, rfl⟩

/-- The value `isgraphemebreak!` returns. -/
def gbV (gb : GbFn) (st : Int32) (c1 c2 : UInt32) : Bool × Int32 :=
  match gb st c1 c2 with
  | .ok r => r
  | .error _ => (true, 0)

theorem gbV_eq {gb : GbFn} (h : GbTotal gb) (st : Int32) (c1 c2 : UInt32) :
    gb st c1 c2 = .ok (gbV gb st c1 c2) := by
  obtain ⟨r, hr⟩ := h st c1 c2
  unfold gbV; rw [hr]

theorem gbV_of_eq {gb : GbFn} {st : Int32} {c1 c2 : UInt32} {r : Bool × Int32}
    (h : gb st c1 c2 = .ok r) : gbV gb st c1 c2 = r := by
  unfold gbV; rw [h]

theorem gbV_mal (P : Utf8proc) (st : Int32) (c1 c2 : UInt32)
    (h : (ismalformed c1 || ismalformed c2) = true) :
    gbV (isgraphemebreakBang P) st c1 c2 = (true, 0) := by
  have e : isgraphemebreakBang P st c1 c2 = .ok (true, 0) := by
    unfold isgraphemebreakBang; rw [if_pos h]
  exact gbV_of_eq e

theorem gbV_wf (P : Utf8proc) (st : Int32) (c1 c2 u1 u2 : UInt32) (h1 : ismalformed c1 = false)
    (h2 : ismalformed c2 = false) (e1 : codepoint c1 = .ok u1) (e2 : codepoint c2 = .ok u2) :
    gbV (isgraphemebreakBang P) st c1 c2 = P.gbStateful st u1 u2 := by
  have e : isgraphemebreakBang P st c1 c2 = .ok (P.gbStateful st u1 u2) := by
    unfold isgraphemebreakBang
    rw [if_neg (by rw [h1, h2]; decide), e1, e2]
  exact gbV_of_eq e

/-- The initial state on characters: a break before the first character, after which
the state is the one `c` starts from. -/
def GbInitV (gb : GbFn) : Prop :=
  ∀ c, (gbV gb 0 0 c).1 = true ∧ ∀ d, gbV gb (gbV gb 0 0 c).2 c d = gbV gb 0 c d

/-- `GbInit` at the level of `isgraphemebreak!` on characters. -/
theorem gbInitV (P : Utf8proc) (hP : GbInit P) : GbInitV (isgraphemebreakBang P) := by
  intro c
  by_cases hm : ismalformed c = true
  · rw [gbV_mal P 0 0 c (by simp [hm])]
    exact ⟨rfl, fun d => by rw [gbV_mal P 0 c d (by simp [hm])]⟩
  · have hm' : ismalformed c = false := by simpa using hm
    obtain ⟨u, hu⟩ := codepoint_ok_of_wf c hm'
    have h00 : ismalformed 0 = false := by decide
    have hz : codepoint 0 = .ok 0 := rfl
    rw [gbV_wf P 0 0 c 0 u h00 hm' hz hu]
    refine ⟨(hP u).1, fun d => ?_⟩
    by_cases hd : ismalformed d = true
    · rw [gbV_mal _ _ _ _ (by simp [hd]), gbV_mal _ _ _ _ (by simp [hd])]
    · have hd' : ismalformed d = false := by simpa using hd
      obtain ⟨v, hv⟩ := codepoint_ok_of_wf d hd'
      rw [gbV_wf P _ c d u v hm' hd' hu hv, gbV_wf P 0 c d u v hm' hd' hu hv]
      exact (hP u).2 v

/-! ## `titlecase(s; strict=false)` -/

theorem titleLoop_spec (gb : GbFn) (hgb : GbTotal gb) (tc lc : UInt32 → UJl UInt32)
    (ws : UInt32 → Bool) :
    ∀ (cs : List UInt32) (st : Int32) (c0 : UInt32), ∃ fl, sepFlags gb ws cs st c0 = .ok fl ∧
      ∀ sw, titleLoop gb tc lc ws false cs sw st c0 = wordStartMap tc cs fl sw := by
  intro cs
  induction cs with
  | nil => intro st c0; exact ⟨[], rfl, fun sw => by cases sw <;> rfl⟩
  | cons c cs ih =>
    intro st c0
    rcases hg : gbV gb st c0 c with ⟨b, st'⟩
    obtain ⟨fl, hfl, hloop⟩ := ih st' c
    have e : gb st c0 c = .ok (b, st') := by rw [gbV_eq hgb, hg]
    refine ⟨(b && ws c) :: fl, ?_, fun sw => ?_⟩
    · simp only [sepFlags, e, hfl, consM]
    · simp only [titleLoop, e]
      cases hb : (b && ws c)
      · cases sw
        · simp only [wordStartMap, hloop, if_false, Bool.false_eq_true]
        · rcases htc : tc c with e' | c'
          · simp only [wordStartMap, htc, if_true, if_false, Bool.false_eq_true]
          · simp only [wordStartMap, htc, hloop, if_true, if_false, Bool.false_eq_true]
      · simp only [wordStartMap, hloop, if_true]

theorem titlecaseOf_false (gb : GbFn) (hgb : GbTotal gb) (tc lc : UInt32 → UJl UInt32)
    (ws : UInt32 → Bool) (cs : List UInt32) :
    titlecaseOf gb tc lc ws false cs = titleSpecOf gb tc ws cs := by
  obtain ⟨fl, hfl, hloop⟩ := titleLoop_spec gb hgb tc lc ws cs 0 0
  rcases hw : wordStartMap tc cs fl true with e | cs'
  · simp only [titlecaseOf, titleSpecOf, hloop true, hfl, hw]
  · simp only [titlecaseOf, titleSpecOf, hloop true, hfl, hw]

theorem titlecaseNonstrict_proven : TitlecaseNonstrict := by
  intro P ws s
  exact titlecaseOf_false (isgraphemebreakBang P) (gb_ok P) (titlecaseChar P) (lowercaseChar P)
    ws (chars s)

/-! ## String iteration as a chain of `(char, index, next index)` -/

abbrev Tri := UInt32 × JInt64 × JInt64

/-- A segment `(first index, last index, index after)`. -/
abbrev Seg := JInt64 × JInt64 × JInt64

/-- Iterating `s` from `i` visits the triples in order: `iterate`, `getindex` and
`nextind` agree at each valid index, and the chain ends at `ncodeunits(s) + 1`. -/
def Chain (s : JStr) (O : GOps) : JInt64 → List Tri → Prop
  | i, [] => i.val = s.bytes.length + 1 ∧ O.it i = none
  | i, (c, p, q) :: r => p = i ∧ validZ s i.val ∧ O.it i = some (c, q) ∧
      O.gi i = .ok c ∧ O.nx i = .ok q ∧ i.val < q.val ∧
      q.val ≤ s.bytes.length + 1 ∧ Chain s O q r

/-- A segment: valid first and last index, in order, and the index after the last. -/
def Inv (s : JStr) (O : GOps) (a j k : JInt64) : Prop :=
  validZ s a.val ∧ validZ s j.val ∧ a.val ≤ j.val ∧ O.nx j = .ok k ∧ j.val < k.val ∧
    k.val ≤ s.bytes.length + 1

/-- `SubString(s, a, j)` for a segment. -/
def toSub (s : JStr) (g : Seg) : JSub := ⟨s, g.1 - ix 1, g.2.2 - g.1⟩

/-- The facts about the called functions that the proofs use. -/
structure Good (s : JStr) (O : GOps) : Prop where
  ncu : O.ncu.val = s.bytes.length
  fuel : O.fuel = s.bytes.length + 1
  ilast_le : O.ilast.val ≤ s.bytes.length
  ilast_ge : ∀ i : JInt64, validZ s i.val → i.val ≤ O.ilast.val
  sub : ∀ a j k, Inv s O a j k → O.sub a j = .ok (toSub s (a, j, k))
  gb : GbTotal O.gb
  init : GbInitV O.gb
  chain : ∃ T, Chain s O (ix 1) T

theorem chain_len (s : JStr) (O : GOps) : ∀ (T : List Tri) (i : JInt64), Chain s O i T →
    i.val + T.length ≤ s.bytes.length + 1
  | [], i, h => by
    have h' := h.1
    simp only [List.length_nil]; omega
  | (c, p, q) :: r, i, h => by
    obtain ⟨_, _, _, _, _, hq, _, hr⟩ := h
    have := chain_len s O r q hr
    simp only [List.length_cons]; omega

theorem chain_cons_le {s : JStr} {O : GOps} (hG : Good s O) {i : JInt64} {t : Tri}
    {r : List Tri} (h : Chain s O i (t :: r)) :
    i.val ≤ O.ilast.val ∧ i.val ≤ O.ncu.val := by
  obtain ⟨c, p, q⟩ := t
  obtain ⟨_, hv, _⟩ := h
  exact ⟨hG.ilast_ge i hv, by rw [hG.ncu]; exact hv.2.1⟩

theorem chain_nil_gt {s : JStr} {O : GOps} (hG : Good s O) {i : JInt64} (h : Chain s O i []) :
    ¬ i.val ≤ O.ilast.val ∧ ¬ i.val ≤ O.ncu.val := by
  have h' := h.1
  have := hG.ilast_le
  rw [hG.ncu]
  omega

/-! ## The grapheme-break sweep and its segments -/

/-- `isgraphemebreak!` along a chain, from state `st` and previous character `c0`. -/
def sweep (gb : GbFn) : Int32 → UInt32 → List Tri → List (Bool × Tri)
  | _, _, [] => []
  | st, c0, t :: r => ((gbV gb st c0 t.1).1, t) :: sweep gb (gbV gb st c0 t.1).2 t.1 r

/-- Segments `(first index, last index, index after)`: a new segment starts at each
break. `cur` is the open segment. -/
def grp : Seg → List (Bool × Tri) → List Seg
  | cur, [] => [cur]
  | cur, (b, (_, p, q)) :: r => if b then cur :: grp (p, p, q) r else grp (cur.1, p, q) r

/-- Number of breaks. -/
def ntrue : List (Bool × Tri) → Nat
  | [] => 0
  | (b, _) :: r => (if b then 1 else 0) + ntrue r

theorem sweep_congr (gb : GbFn) (st st' : Int32) (c0 : UInt32)
    (h : ∀ d, gbV gb st c0 d = gbV gb st' c0 d) : ∀ T, sweep gb st c0 T = sweep gb st' c0 T
  | [] => rfl
  | t :: r => by simp only [sweep, h t.1]

theorem grp_length : ∀ (F : List (Bool × Tri)) (cur : Seg), (grp cur F).length = 1 + ntrue F
  | [], _ => rfl
  | (b, (_, p, q)) :: r, cur => by
    cases b <;> simp only [grp, ntrue, if_true, if_false, Bool.false_eq_true, List.length_cons,
      grp_length r] <;> omega

/-- Consecutive segments: each is a segment and ends where the next starts. -/
def Tiling (s : JStr) (O : GOps) : List Seg → Prop
  | [] => True
  | [x] => Inv s O x.1 x.2.1 x.2.2
  | x :: y :: r => Inv s O x.1 x.2.1 x.2.2 ∧ x.2.2 = y.1 ∧ Tiling s O (y :: r)

theorem grp_head : ∀ (F : List (Bool × Tri)) (a j k : JInt64),
    ∃ y ys, grp (a, j, k) F = (a, y) :: ys
  | [], a, j, k => ⟨_, _, rfl⟩
  | (b, (_, p, q)) :: r, a, j, k => by
    cases b
    · simp only [grp, Bool.false_eq_true, if_false]; exact grp_head r a p q
    · simp only [grp, if_true]; exact ⟨_, _, rfl⟩

theorem grp_tiling (s : JStr) (O : GOps) : ∀ (rest : List Tri) (k : JInt64), Chain s O k rest →
    ∀ (st : Int32) (c0 : UInt32) (a j : JInt64), Inv s O a j k →
    Tiling s O (grp (a, j, k) (sweep O.gb st c0 rest))
  | [], _, _, _, _, _, _, hinv => hinv
  | (c, p, q) :: r, k, h, st, c0, a, j, hinv => by
    obtain ⟨hp, hv, _, _, hnx, hlt, hq, hr⟩ := h
    subst hp
    simp only [sweep, grp]
    cases hb : (gbV O.gb st c0 c).1
    · simp only [Bool.false_eq_true, if_false]
      exact grp_tiling s O r q hr _ c a p
        ⟨hinv.1, hv, by have := hinv.2.2.2.2.1; have := hinv.2.2.1; omega, hnx, hlt, hq⟩
    · simp only [if_true]
      obtain ⟨y, ys, hy⟩ := grp_head (sweep O.gb (gbV O.gb st c0 c).2 c r) p p q
      have ht := grp_tiling s O r q hr (gbV O.gb st c0 c).2 c p p
        ⟨hv, hv, Int.le_refl _, hnx, hlt, hq⟩
      rw [hy] at ht ⊢
      exact ⟨hinv, rfl, ht⟩

/-! ## `collect(graphemes(s))` -/

theorem gIterLoop_spec (s : JStr) (O : GOps) (hG : Good s O) :
    ∀ (rest : List Tri) (k : JInt64), Chain s O k rest → ∀ (f : Nat), rest.length < f →
    ∀ (st : Int32) (c0 : UInt32) (a j : JInt64), Inv s O a j k →
    ∃ st' j' k' rest', gIterLoop O f st c0 j k = .ok (st', j', k') ∧ Chain s O k' rest' ∧
      rest'.length ≤ rest.length ∧ Inv s O a j' k' ∧
      grp (a, j, k) (sweep O.gb st c0 rest) = (a, j', k') :: (match rest' with
        | [] => []
        | (c', p', q') :: r' => grp (p', p', q') (sweep O.gb st' c' r')) := by
  intro rest
  induction rest with
  | nil =>
    intro k h f hf st c0 a j hinv
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hgt := (chain_nil_gt hG h).2
    refine ⟨st, j, k, [], ?_, h, Nat.le_refl _, hinv, rfl⟩
    simp only [gIterLoop, hgt, if_false]
  | cons t r ih =>
    intro k h f hf st c0 a j hinv
    obtain ⟨c, p, q⟩ := t
    have hle := (chain_cons_le hG h).2
    obtain ⟨hp, hv, hit, hgi, hnx, hlt, hq, hr⟩ := h
    subst hp
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    rcases hg : gbV O.gb st c0 c with ⟨b, st''⟩
    have e : O.gb st c0 c = .ok (b, st'') := by rw [gbV_eq hG.gb, hg]
    cases b
    · obtain ⟨st', j', k', rest', e1, hc', hl', hinv', hgrp⟩ :=
        ih q hr f (by simp at hf; omega) st'' c a p
          ⟨hinv.1, hv, by have := hinv.2.2.2.2.1; have := hinv.2.2.1; omega, hnx, hlt, hq⟩
      refine ⟨st', j', k', rest', ?_, hc', by simp; omega, hinv', ?_⟩
      · simp only [gIterLoop, hle, if_true, hit, e]
        exact e1
      · simp only [sweep, hg, grp, Bool.false_eq_true, if_false]
        exact hgrp
    · refine ⟨st'', j, p, (c, p, q) :: r, ?_, ⟨rfl, hv, hit, hgi, hnx, hlt, hq, hr⟩,
        Nat.le_refl _, hinv, ?_⟩
      · simp only [gIterLoop, hle, if_true, hit, e]
      · simp only [sweep, hg, grp, if_true]

theorem gCollectFrom_spec (s : JStr) (O : GOps) (hG : Good s O) :
    ∀ (f : Nat) (c : UInt32) (p q : JInt64) (rest : List Tri) (st : Int32),
      Chain s O p ((c, p, q) :: rest) → rest.length + 1 < f →
      gCollectFrom O f st p = .ok ((grp (p, p, q) (sweep O.gb st c rest)).map (toSub s)) := by
  intro f
  induction f with
  | zero => intro _ _ _ _ _ _ hf; simp at hf
  | succ f ih =>
    intro c p q rest st h hf
    have hlen := chain_len s O _ p h
    obtain ⟨_, hv, hit, hgi, hnx, hlt, hq, hr⟩ := h
    obtain ⟨st', j', k', rest', e1, hc', hl', hinv', hgrp⟩ :=
      gIterLoop_spec s O hG rest q hr O.fuel (by rw [hG.fuel]; simp at hlen; omega) st c p p
        ⟨hv, hv, Int.le_refl _, hnx, hlt, hq⟩
    have hsub := hG.sub p j' k' hinv'
    have hit2 : gIterate O st p = .ok (some (toSub s (p, j', k'), st', k')) := by
      simp only [gIterate, hit, e1, hsub]
    simp only [gCollectFrom, hit2]
    rw [hgrp]
    cases rest' with
    | nil =>
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have : gIterate O st' k' = .ok none := by
        simp only [gIterate, hc'.2]
      simp only [gCollectFrom, this, consM, List.map_cons, List.map_nil]
    | cons t r' =>
      obtain ⟨c', p', q'⟩ := t
      have hp' : p' = k' := hc'.1
      subst hp'
      rw [ih c' p' q' r' st' hc' (by simp at hl'; omega)]
      simp only [consM, List.map_cons]

/-! ## `length(graphemes(s))` -/

theorem cnt_add (count : JInt64) (b : Bool) (h0 : 0 ≤ count.val) (h1 : count.val < 2 ^ 62) :
    (count + bInt b).val = count.val + (if b then 1 else 0) := by
  rw [add_val _ _ (by rw [bInt_val]; split <;> omega) (by rw [bInt_val]; split <;> omega), bInt_val]

theorem gLengthLoop_spec (s : JStr) (O : GOps) (hgb : GbTotal O.gb) :
    ∀ (T : List Tri) (i : JInt64), Chain s O i T → ∀ (f : Nat), T.length < f →
    ∀ (st : Int32) (c0 : UInt32) (n : JInt64), 0 ≤ n.val → n.val + T.length < 2 ^ 62 →
    ∃ len, gLengthLoop O f st c0 i n = .ok len ∧ len.val = n.val + ntrue (sweep O.gb st c0 T)
  | [], i, h, f, hf, st, c0, n, _, _ => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    exact ⟨n, by simp only [gLengthLoop, h.2], by simp [sweep, ntrue]⟩
  | (c, p, q) :: r, i, h, f, hf, st, c0, n, h0, hb => by
    obtain ⟨_, _, hit, _, _, _, _, hr⟩ := h
    simp only [List.length_cons] at hb hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rcases hg : gbV O.gb st c0 c with ⟨b, st'⟩
    have e : O.gb st c0 c = .ok (b, st') := by rw [gbV_eq hgb, hg]
    have hn := cnt_add n b h0 (by omega)
    obtain ⟨len, e', hl⟩ := gLengthLoop_spec s O hgb r q hr f (by omega) st' c (n + bInt b)
      (by rw [hn]; split <;> omega) (by rw [hn]; split <;> omega)
    refine ⟨len, ?_, ?_⟩
    · simp only [gLengthLoop, hit, e]; exact e'
    · rw [hl, hn]
      cases b <;> simp only [sweep, hg, ntrue, if_true, if_false, Bool.false_eq_true] <;> omega

/-! ## The two loops of `graphemes(s, m:n)` -/

theorem gFirst_stop (O : GOps) (m : JInt64) (f : Nat) (st : Int32)
    (c0 : UInt32) (count i iprev : JInt64) (h : ¬ (count.val < m.val ∧ i.val ≤ O.ilast.val)) :
    gFirst O m (f + 1) st c0 count i iprev = .ok (st, c0, count, i, iprev) := by
  simp only [gFirst]
  rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)]

theorem gFirst_spec (s : JStr) (O : GOps) (hG : Good s O) (m : JInt64) :
    ∀ (rest : List Tri) (i : JInt64), Chain s O i rest → ∀ (f : Nat), rest.length ≤ f →
    ∀ (st : Int32) (c0 : UInt32) (count iprev a : JInt64), Inv s O a iprev i →
    1 ≤ count.val → count.val < m.val → count.val < i.val →
    ∃ st1 c01 count1 i1 iprev1,
      gFirst O m (f + 1) st c0 count i iprev = .ok (st1, c01, count1, i1, iprev1) ∧
      ((m.val - count.val).toNat < (grp (a, iprev, i) (sweep O.gb st c0 rest)).length →
        count1.val = m.val ∧ ∃ r1, Chain s O i1 r1 ∧ Inv s O iprev1 iprev1 i1 ∧
          count1.val < i1.val ∧
          (grp (a, iprev, i) (sweep O.gb st c0 rest)).drop (m.val - count.val).toNat =
            grp (iprev1, iprev1, i1) (sweep O.gb st1 c01 r1)) ∧
      ((grp (a, iprev, i) (sweep O.gb st c0 rest)).length ≤ (m.val - count.val).toNat →
        count1.val < m.val) := by
  have hs := ncu_small s
  intro rest
  induction rest with
  | nil =>
    intro i h f hf st c0 count iprev a hinv h1 hm hi
    refine ⟨st, c0, count, i, iprev, gFirst_stop O m f st c0 count i iprev
      (by have := (chain_nil_gt hG h).1; omega), ?_, fun _ => hm⟩
    intro hlt
    simp only [sweep, grp, List.length_cons, List.length_nil] at hlt
    omega
  | cons t r ih =>
    intro i h f hf st c0 count iprev a hinv h1 hm hi
    obtain ⟨c, p, q⟩ := t
    have hle := (chain_cons_le hG h).1
    obtain ⟨hp, hv, hit, hgi, hnx, hlt, hq, hr⟩ := h
    subst hp
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    rcases hg : gbV O.gb st c0 c with ⟨b, st''⟩
    have e : O.gb st c0 c = .ok (b, st'') := by rw [gbV_eq hG.gb, hg]
    have hcnt := cnt_add count b (by omega) (by omega)
    have hstep : gFirst O m (f + 1 + 1) st c0 count p iprev =
        gFirst O m (f + 1) st'' c (count + bInt b) q p := by
      simp only [gFirst, hle, hm, decide_true, Bool.and_self, if_true, hgi, e, hnx]
    rw [hstep]
    have hsw : sweep O.gb st c0 ((c, p, q) :: r) = (b, (c, p, q)) :: sweep O.gb st'' c r := by
      simp only [sweep, hg]
    rw [hsw]
    cases b
    · have hc0 : count + bInt false = count := Subtype.ext (by rw [hcnt]; simp)
      rw [hc0]
      simp only [grp, Bool.false_eq_true, if_false]
      exact ih q hr f (by simp at hf; omega) st'' c count p a
        ⟨hinv.1, hv, by have := hinv.2.2.2.2.1; have := hinv.2.2.1; omega, hnx, hlt, hq⟩
        h1 hm (by omega)
    · simp only [if_true] at hcnt
      simp only [grp, if_true, List.length_cons]
      have hinvp : Inv s O p p q := ⟨hv, hv, Int.le_refl _, hnx, hlt, hq⟩
      by_cases hreach : count.val + 1 = m.val
      · refine ⟨st'', c, count + bInt true, q, p,
          gFirst_stop O m f st'' c _ q p (by omega), fun _ => ⟨by omega, r, hr, hinvp,
            by omega, ?_⟩, fun hl => ?_⟩
        · have e1 : (m.val - count.val).toNat = 1 := by omega
          rw [e1]; rfl
        · obtain ⟨y, ys, hy⟩ := grp_head (sweep O.gb st'' c r) p p q
          rw [hy] at hl; simp only [List.length_cons] at hl; omega
      · obtain ⟨st1, c01, count1, i1, iprev1, e1, hA, hB⟩ :=
          ih q hr f (by simp at hf; omega) st'' c (count + bInt true) p p hinvp (by omega)
            (by omega) (by omega)
        rw [hcnt] at hA hB
        have ek : (m.val - count.val).toNat = (m.val - (count.val + 1)).toNat + 1 := by omega
        refine ⟨st1, c01, count1, i1, iprev1, e1, fun hl => ?_, fun hl => ?_⟩
        · rw [ek] at hl ⊢
          simp only [List.drop_succ_cons]
          exact hA (by omega)
        · rw [ek] at hl
          exact hB (by omega)

theorem gSecond_spec (s : JStr) (O : GOps) (hG : Good s O) (n : JInt64) :
    ∀ (rest : List Tri) (i : JInt64), Chain s O i rest → ∀ (f : Nat), rest.length < f →
    ∀ (st : Int32) (c0 : UInt32) (count iprev a : JInt64), Inv s O a iprev i →
    0 ≤ count.val → count.val < i.val → count.val ≤ n.val →
    ∃ count' iprev', gSecond O n f st c0 count i iprev = .ok (count', iprev') ∧
      ((n.val - count.val).toNat < (grp (a, iprev, i) (sweep O.gb st c0 rest)).length →
        n.val ≤ count'.val ∧ ∃ x k',
          (grp (a, iprev, i) (sweep O.gb st c0 rest))[(n.val - count.val).toNat]? =
            some (x, iprev', k')) ∧
      ((grp (a, iprev, i) (sweep O.gb st c0 rest)).length ≤ (n.val - count.val).toNat →
        count'.val < n.val) := by
  have hs := ncu_small s
  intro rest
  induction rest with
  | nil =>
    intro i h f hf st c0 count iprev a hinv h0 hi hn
    have hgt := (chain_nil_gt hG h).1
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    refine ⟨count, iprev, by simp only [gSecond, hgt, if_false], fun hl => ?_, fun hl => ?_⟩
    · simp only [sweep, grp, List.length_cons, List.length_nil] at hl
      have e0 : (n.val - count.val).toNat = 0 := by omega
      rw [e0]
      simp only [sweep, grp, List.getElem?_cons_zero]
      exact ⟨by omega, a, i, rfl⟩
    · simp only [sweep, grp, List.length_cons, List.length_nil] at hl
      omega
  | cons t r ih =>
    intro i h f hf st c0 count iprev a hinv h0 hi hn
    obtain ⟨c, p, q⟩ := t
    have hle := (chain_cons_le hG h).1
    obtain ⟨hp, hv, hit, hgi, hnx, hlt, hq, hr⟩ := h
    subst hp
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    rcases hg : gbV O.gb st c0 c with ⟨b, st''⟩
    have e : O.gb st c0 c = .ok (b, st'') := by rw [gbV_eq hG.gb, hg]
    have hcnt := cnt_add count b h0 (by omega)
    have hsw : sweep O.gb st c0 ((c, p, q) :: r) = (b, (c, p, q)) :: sweep O.gb st'' c r := by
      simp only [sweep, hg]
    rw [hsw]
    cases b
    · have hc0 : count + bInt false = count := Subtype.ext (by rw [hcnt]; simp)
      have hstep : gSecond O n (f + 1) st c0 count p iprev =
          gSecond O n f st'' c count q p := by
        simp only [gSecond, hle, if_true, hgi, e, hc0, hnx]
        rw [if_neg (by omega)]
      rw [hstep]
      simp only [grp, Bool.false_eq_true, if_false]
      exact ih q hr f (by simp at hf; omega) st'' c count p a
        ⟨hinv.1, hv, by have := hinv.2.2.2.2.1; have := hinv.2.2.1; omega, hnx, hlt, hq⟩
        h0 (by omega) hn
    · simp only [if_true] at hcnt
      simp only [grp, if_true, List.length_cons]
      by_cases hover : count.val + 1 > n.val
      · have hstep : gSecond O n (f + 1) st c0 count p iprev = .ok (count + bInt true, iprev) := by
          simp only [gSecond, hle, if_true, hgi, e]
          rw [if_pos (by rw [hcnt]; omega)]
        refine ⟨_, _, hstep, fun _ => ?_, fun hl => by omega⟩
        have e0 : (n.val - count.val).toNat = 0 := by omega
        rw [e0]
        exact ⟨by omega, a, p, rfl⟩
      · have hstep : gSecond O n (f + 1) st c0 count p iprev =
            gSecond O n f st'' c (count + bInt true) q p := by
          simp only [gSecond, hle, if_true, hgi, e, hnx]
          rw [if_neg (by rw [hcnt]; omega)]
        rw [hstep]
        obtain ⟨count', iprev', e1, hA, hB⟩ := ih q hr f (by simp at hf; omega) st'' c
          (count + bInt true) p p ⟨hv, hv, Int.le_refl _, hnx, hlt, hq⟩ (by omega) (by omega)
          (by omega)
        rw [hcnt] at hA hB
        have ek : (n.val - count.val).toNat = (n.val - (count.val + 1)).toNat + 1 := by omega
        refine ⟨count', iprev', e1, fun hl => ?_, fun hl => ?_⟩
        · rw [ek] at hl ⊢
          simp only [List.getElem?_cons_succ]
          exact hA (by omega)
        · rw [ek] at hl
          exact hB (by omega)

/-! ## Concatenating consecutive segments -/

theorem toSub_bytes (s : JStr) (O : GOps) (g : Seg) (h : Inv s O g.1 g.2.1 g.2.2) :
    (toSub s g).view.bytes =
      (s.bytes.drop (g.1.val - 1).toNat).take (g.2.2.val - g.1.val).toNat := by
  have hs := ncu_small s
  obtain ⟨ha, _, haj, _, hjk, hk⟩ := h
  have e1 : (g.1 - ix 1).val = g.1.val - 1 := sub_val _ _ (by simp; omega) (by simp; omega)
  have e2 : (g.2.2 - g.1).val = g.2.2.val - g.1.val := sub_val _ _ (by omega) (by omega)
  simp only [toSub, JSub.view, JStr.slice, e1, e2]

theorem take_drop_append (l : List UInt8) (x y z : Nat) :
    (l.drop x).take y ++ (l.drop (x + y)).take z = (l.drop x).take (y + z) := by
  rw [List.take_add, List.drop_drop]

theorem tiling_head (s : JStr) (O : GOps) {x : Seg} {L : List Seg} (h : Tiling s O (x :: L)) :
    Inv s O x.1 x.2.1 x.2.2 := by
  cases L with
  | nil => exact h
  | cons _ _ => exact h.1

theorem tiling_mono (s : JStr) (O : GOps) : ∀ (L : List Seg) (x y : Seg) (k : Nat),
    Tiling s O (x :: L) → (x :: L)[k]? = some y → x.1.val ≤ y.2.1.val ∧ Inv s O y.1 y.2.1 y.2.2
  | _, x, y, 0, ht, hk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    have hx := tiling_head s O ht
    exact ⟨hx.2.2.1, hx⟩
  | [], _, _, _ + 1, _, hk => by simp at hk
  | w :: L, x, y, k + 1, ht, hk => by
    simp only [List.getElem?_cons_succ] at hk
    obtain ⟨hx, hxw, ht'⟩ := ht
    obtain ⟨ih1, ih2⟩ := tiling_mono s O L w y k ht' hk
    obtain ⟨_, _, haj, _, hjk, _⟩ := hx
    rw [hxw] at hjk
    have hw := tiling_head s O ht'
    exact ⟨by have := hw.2.2.1; omega, ih2⟩

theorem tiling_concat (s : JStr) (O : GOps) : ∀ (L : List Seg) (x z : Seg), Tiling s O (x :: L) →
    (x :: L)[L.length]? = some z →
    ((x :: L).map (fun g => (toSub s g).view.bytes)).flatten =
      (s.bytes.drop (x.1.val - 1).toNat).take (z.2.2.val - x.1.val).toNat
  | [], x, z, ht, hz => by
    simp only [List.length_nil, List.getElem?_cons_zero, Option.some.injEq] at hz
    subst hz
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact toSub_bytes s O _ ht
  | w :: L, x, z, ht, hz => by
    obtain ⟨hx, hxw, ht'⟩ := ht
    have hz' : (w :: L)[L.length]? = some z := by simpa using hz
    have ih := tiling_concat s O L w z ht' hz'
    obtain ⟨hwz, hinvz⟩ := tiling_mono s O L w z L.length ht' hz'
    rw [List.map_cons, List.flatten_cons, ih, toSub_bytes s O _ hx, ← hxw]
    obtain ⟨hv, _, haj, _, hjk, _⟩ := hx
    have hzz := hinvz.2.2.2.2.1
    have e := take_drop_append s.bytes (x.1.val - 1).toNat (x.2.2.val - x.1.val).toNat
      (z.2.2.val - x.2.2.val).toNat
    have e1 : (x.1.val - 1).toNat + (x.2.2.val - x.1.val).toNat = (x.2.2.val - 1).toNat := by
      have := hv.1; omega
    have hw2 : x.2.2.val = w.1.val := by rw [hxw]
    have e2 : (x.2.2.val - x.1.val).toNat + (z.2.2.val - x.2.2.val).toNat =
        (z.2.2.val - x.1.val).toNat := by
      omega
    rw [e1, e2] at e
    exact e

theorem tiling_drop (s : JStr) (O : GOps) : ∀ (L : List Seg) (d : Nat), Tiling s O L →
    Tiling s O (L.drop d)
  | [], _, _ => by simp [Tiling]
  | _ :: _, 0, h => h
  | [_], _ + 1, _ => by simp [Tiling]
  | _ :: y :: r, d + 1, h => by
    simp only [List.drop_succ_cons]
    exact tiling_drop s O (y :: r) d h.2.2

theorem tiling_take (s : JStr) (O : GOps) : ∀ (L : List Seg) (d : Nat), Tiling s O L →
    Tiling s O (L.take d)
  | [], _, _ => by simp [Tiling]
  | _ :: _, 0, _ => by simp [Tiling]
  | [_], _ + 1, h => by simpa using h
  | _ :: _ :: _, 1, h => h.1
  | x :: y :: r, d + 2, h => by
    have ih := tiling_take s O (y :: r) (d + 1) h.2.2
    simp only [List.take_succ_cons] at ih ⊢
    exact ⟨h.1, h.2.1, ih⟩

/-! ## `graphemes(s, m:n)` for any functions satisfying `Good` -/

theorem rangeOf_spec (s : JStr) (O : GOps) (hG : Good s O) (m n : JInt64) (hm : 1 ≤ m.val)
    (hmn : m.val ≤ n.val) :
    ∃ G len, gCollectFrom O (s.bytes.length + 1) 0 (ix 1) = .ok G ∧
      gLengthLoop O (s.bytes.length + 1) 0 0 (ix 1) (ix 0) = .ok len ∧ len.val = G.length ∧
      (n.val ≤ len.val → ∃ r, graphemesRangeOf O m n = .ok r ∧ r.str = s ∧
        r.view.bytes = (((G.drop (m.val.toNat - 1)).take ((n.val - m.val).toNat + 1)).map
          (fun g => g.view.bytes)).flatten) ∧
      (len.val < n.val → graphemesRangeOf O m n = .error (.str boundsErr)) := by
  have hs := ncu_small s
  have hix1 : (ix 1).val = 1 := ix1
  obtain ⟨T, hT⟩ := hG.chain
  have hm0 : (0 : Int) < m.val := by omega
  cases T with
  | nil =>
    have hN : s.bytes.length = 0 := by
      have h' := hT.1
      rw [hix1] at h'; omega
    have hcol : gCollectFrom O (s.bytes.length + 1) 0 (ix 1) = .ok [] := by
      rw [hN]
      simp only [gCollectFrom, gIterate, hT.2]
    have hlen : gLengthLoop O (s.bytes.length + 1) 0 0 (ix 1) (ix 0) = .ok (ix 0) := by
      rw [hN]
      simp only [gLengthLoop, hT.2]
    refine ⟨[], ix 0, hcol, hlen, by simp, fun h => absurd h (by simp; omega), fun _ => ?_⟩
    have hgt := (chain_nil_gt hG hT).1
    unfold graphemesRangeOf
    rw [hG.fuel, if_neg (by simp; omega), if_neg (by omega), hN,
      gFirst_stop O m 0 0 0 (ix 0) (ix 1) (ix 1) (by omega)]
    simp only [ix0, hm0, if_true]
  | cons t rest =>
    obtain ⟨c1, p1, q1⟩ := t
    have hlenT := chain_len s O _ _ hT
    simp only [hix1, List.length_cons] at hlenT
    obtain ⟨hp1, hv1, hit1, hgi1, hnx1, hlt1, hq1, hr⟩ := hT
    subst hp1
    have hinv1 : Inv s O (ix 1) (ix 1) q1 := ⟨hv1, hv1, Int.le_refl _, hnx1, hlt1, hq1⟩
    obtain ⟨hb1, hσ⟩ := hG.init c1
    have hsweq := sweep_congr O.gb (gbV O.gb 0 0 c1).2 0 c1 hσ rest
    have hcol : gCollectFrom O (s.bytes.length + 1) 0 (ix 1) =
        .ok ((grp (ix 1, ix 1, q1) (sweep O.gb 0 c1 rest)).map (toSub s)) :=
      gCollectFrom_spec s O hG _ c1 (ix 1) q1 rest 0 ⟨rfl, hv1, hit1, hgi1, hnx1, hlt1, hq1, hr⟩
        (by omega)
    generalize hG' : grp (ix 1, ix 1, q1) (sweep O.gb 0 c1 rest) = G at hcol
    have htile : Tiling s O G := by
      rw [← hG']; exact grp_tiling s O rest q1 hr 0 c1 (ix 1) (ix 1) hinv1
    obtain ⟨len, hlen, hlenv⟩ := gLengthLoop_spec s O hG.gb ((c1, ix 1, q1) :: rest) (ix 1)
      ⟨rfl, hv1, hit1, hgi1, hnx1, hlt1, hq1, hr⟩ (s.bytes.length + 1)
      (by simp only [List.length_cons]; omega) 0 0 (ix 0)
      (by simp) (by simp only [ix0, List.length_cons]; omega)
    have hGlen : G.length = 1 + ntrue (sweep O.gb 0 c1 rest) := by rw [← hG', grp_length]
    have hlenG : len.val = G.length := by
      rw [hlenv, hGlen]
      simp only [sweep, hb1, ntrue, if_true, ix0]
      rw [hsweq]; omega
    refine ⟨G.map (toSub s), len, hcol, hlen, by simp [hlenG], ?_⟩
    have hstep : gFirst O m (s.bytes.length + 1) 0 0 (ix 0) (ix 1) (ix 1) =
        gFirst O m s.bytes.length (gbV O.gb 0 0 c1).2 c1 (ix 0 + bInt true) q1 (ix 1) := by
      have hle := hG.ilast_ge (ix 1) hv1
      have e : O.gb 0 0 c1 = .ok (true, (gbV O.gb 0 0 c1).2) := by
        rw [gbV_eq hG.gb, ← hb1]
      simp only [gFirst, hle, ix0, hm0, decide_true, Bool.and_self, if_true, hgi1, e, hnx1]
    have hone : (ix 0 + bInt true).val = 1 := by
      rw [cnt_add (ix 0) true (by rw [ix0]; omega) (by rw [ix0]; omega), ix0]; simp
    obtain ⟨len', hlen'⟩ : ∃ l, s.bytes.length = l + 1 := ⟨s.bytes.length - 1, by omega⟩
    have key : ∃ st1 c01 count1 i1 iprev1,
        gFirst O m (s.bytes.length + 1) 0 0 (ix 0) (ix 1) (ix 1) =
          .ok (st1, c01, count1, i1, iprev1) ∧
        ((m.val - 1).toNat < G.length → count1.val = m.val ∧ ∃ r1, Chain s O i1 r1 ∧
          Inv s O iprev1 iprev1 i1 ∧ count1.val < i1.val ∧
          G.drop (m.val - 1).toNat = grp (iprev1, iprev1, i1) (sweep O.gb st1 c01 r1)) ∧
        (G.length ≤ (m.val - 1).toNat → count1.val < m.val) := by
      rw [hstep, hlen']
      by_cases hm1 : m.val = 1
      · refine ⟨_, _, _, _, _, gFirst_stop O m len' _ c1 _ q1 (ix 1) (by omega),
          fun _ => ⟨by omega, rest, hr, hinv1, by omega, ?_⟩, fun hl => ?_⟩
        · rw [show (m.val - 1).toNat = 0 by omega, List.drop_zero, ← hG', hsweq]
        · obtain ⟨y, ys, hy⟩ := grp_head (sweep O.gb 0 c1 rest) (ix 1) (ix 1) q1
          rw [← hG', hy] at hl
          simp only [List.length_cons] at hl
          omega
      · obtain ⟨st1, c01, count1, i1, iprev1, e1, hA, hB⟩ := gFirst_spec s O hG m rest q1 hr
          len' (by omega) (gbV O.gb 0 0 c1).2 c1 (ix 0 + bInt true) (ix 1) (ix 1) hinv1
          (by omega) (by omega) (by omega)
        rw [hone, hsweq, hG'] at hA hB
        exact ⟨st1, c01, count1, i1, iprev1, e1, hA, hB⟩
    obtain ⟨st1, c01, count1, i1, iprev1, e1, hA, hB⟩ := key
    by_cases hmG : (m.val - 1).toNat < G.length
    · obtain ⟨hc1, r1, hr1, hinvi, hci, hdrop⟩ := hA hmG
      have hlen1 := chain_len s O _ _ hr1
      obtain ⟨count', iprev', e2, hA2, hB2⟩ := gSecond_spec s O hG n r1 i1 hr1
        (s.bytes.length + 1) (by omega) st1 c01 count1 iprev1 iprev1 hinvi (by omega) hci (by omega)
      rw [← hdrop, hc1] at hA2 hB2
      have hdl : (G.drop (m.val - 1).toNat).length = G.length - (m.val - 1).toNat :=
        List.length_drop
      obtain ⟨w, ys, hy⟩ := grp_head (sweep O.gb st1 c01 r1) iprev1 iprev1 i1
      rw [hy] at hdrop
      have hR : graphemesRangeOf O m n = (if count'.val < n.val then .error (.str boundsErr)
          else liftS (O.sub iprev1 iprev')) := by
        unfold graphemesRangeOf
        rw [hG.fuel, if_neg (by simp; omega), if_neg (by omega), e1]
        simp only [show ¬ count1.val < m.val by omega, if_false, e2]
      rw [hR]
      constructor
      · intro hnl
        have hnl' : (n.val - m.val).toNat < (G.drop (m.val - 1).toNat).length := by
          rw [hdl]; omega
        obtain ⟨hn', x, k', hx⟩ := hA2 hnl'
        rw [if_neg (by omega)]
        have htile2 : Tiling s O ((iprev1, w) :: ys) := by
          rw [← hdrop]; exact tiling_drop s O G _ htile
        rw [hdrop] at hx hnl'
        obtain ⟨hle', hinvx⟩ := tiling_mono s O ys (iprev1, w) (x, iprev', k') _ htile2 hx
        have hinvr : Inv s O iprev1 iprev' k' := ⟨hinvi.1, hinvx.2.1, hle', hinvx.2.2.2⟩
        rw [hG.sub iprev1 iprev' k' hinvr]
        refine ⟨toSub s (iprev1, iprev', k'), rfl, rfl, ?_⟩
        have hmn : m.val.toNat - 1 = (m.val - 1).toNat := by omega
        have hmap : (((G.map (toSub s)).drop (m.val.toNat - 1)).take
            ((n.val - m.val).toNat + 1)).map (fun g => g.view.bytes) =
            ((((iprev1, w) :: ys).take ((n.val - m.val).toNat + 1)).map
              (fun g => (toSub s g).view.bytes)) := by
          rw [hmn, ← List.map_drop, hdrop, ← List.map_take, List.map_map]
          rfl
        rw [hmap, List.take_succ_cons]
        simp only [List.length_cons] at hnl'
        have htl : (ys.take (n.val - m.val).toNat).length = (n.val - m.val).toNat := by
          rw [List.length_take]; omega
        have hz : ((iprev1, w) :: ys.take (n.val - m.val).toNat)[
            (ys.take (n.val - m.val).toNat).length]? = some (x, iprev', k') := by
          rw [htl, ← List.take_succ_cons, List.getElem?_take, if_pos (by omega)]
          exact hx
        have hLt : Tiling s O ((iprev1, w) :: ys.take (n.val - m.val).toNat) := by
          rw [← List.take_succ_cons]; exact tiling_take s O _ _ htile2
        rw [tiling_concat s O _ (iprev1, w) (x, iprev', k') hLt hz,
          toSub_bytes s O (iprev1, iprev', k') hinvr]
      · intro hnl
        rw [if_pos (hB2 (by rw [hdl]; omega))]
    · have hc1 := hB (by omega)
      refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
      unfold graphemesRangeOf
      rw [hG.fuel, if_neg (by simp; omega), if_neg (by omega), e1]
      simp only [hc1, if_true]

/-! ## The String functions satisfy `Good` -/

theorem getindex_of_iterate (s : JStr) (i : JInt64) (hv : validZ s i.val) {c : UInt32}
    {q : JInt64} (hit : iterate s i = some (c, q)) : getindex s i = .ok c := by
  obtain ⟨h1, h2, h3⟩ := hv
  rw [iterate_eq s i h1 h2] at hit
  have hcu : codeunit s i = .ok (cu s i) := by
    unfold codeunit; rw [if_pos ⟨h1, by rw [ncu_val]; exact h2⟩]
  have hval : isvalidAt s i = true := (isvalidAt_iff s i).2 ⟨h1, h2, h3⟩
  have hg : getindex s i = (if !between (cu s i) 0x80 0xf7 then .ok ((cu s i).toUInt32 <<< 24)
      else getindexContinued s i ((cu s i).toUInt32 <<< 24)) := by
    unfold getindex; rw [hcu]; rfl
  rw [hg]
  by_cases hb : (!between (cu s i) 0x80 0xf7) = true
  · rw [if_pos hb] at hit; rw [if_pos hb]
    simp only [Option.some.injEq, Prod.mk.injEq] at hit
    rw [hit.1]
  · rw [if_neg hb] at hit; rw [if_neg hb]
    by_cases hu : (cu s i).toUInt32 <<< 24 < 0xc0000000
    · have hgc : getindexContinued s i ((cu s i).toUInt32 <<< 24) =
          .ok ((cu s i).toUInt32 <<< 24) := by
        unfold getindexContinued; rw [if_pos hu, if_pos hval]
      have hic : iterateContinued s i ((cu s i).toUInt32 <<< 24) =
          ((cu s i).toUInt32 <<< 24, i + ix 1) := by
        unfold iterateContinued; rw [if_pos hu]
      rw [hgc]; rw [hic] at hit
      simp only [Option.some.injEq, Prod.mk.injEq] at hit
      rw [hit.1]
    · have hgc : getindexContinued s i ((cu s i).toUInt32 <<< 24) =
          .ok (iterateContinued s i ((cu s i).toUInt32 <<< 24)).1 := by
        unfold getindexContinued; rw [if_neg hu]
      rw [hgc, Option.some.inj hit]

theorem gops_it (P : Utf8proc) (s : JStr) : (gops P s).it = iterate s := by simp only [gops]
theorem gops_gi (P : Utf8proc) (s : JStr) : (gops P s).gi = getindex s := by simp only [gops]
theorem gops_nx (P : Utf8proc) (s : JStr) : (gops P s).nx = nextind s := by simp only [gops]
theorem gops_sub (P : Utf8proc) (s : JStr) :
    (gops P s).sub = fun i j => substring s i j := by simp only [gops]
theorem gops_gb (P : Utf8proc) (s : JStr) : (gops P s).gb = isgraphemebreakBang P := by
  simp only [gops]
theorem gops_ncu (P : Utf8proc) (s : JStr) : (gops P s).ncu = ncodeunits s := by simp only [gops]
theorem gops_ilast (P : Utf8proc) (s : JStr) :
    (gops P s).ilast = lastOf (thisind s (ncodeunits s)) := by simp only [gops]
theorem gops_fuel (P : Utf8proc) (s : JStr) : (gops P s).fuel = s.bytes.length + 1 := by
  simp only [gops]

theorem chain_exists (P : Utf8proc) (s : JStr) : ∀ (k : Nat) (i : JInt64), 1 ≤ i.val →
    i.val ≤ s.bytes.length + 1 → (k : Int) = s.bytes.length + 1 - i.val →
    (i.val ≤ s.bytes.length → validZ s i.val) → ∃ T, Chain s (gops P s) i T := by
  have hs := ncu_small s
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro i h1 h2 hk hv
    by_cases hend : i.val = s.bytes.length + 1
    · exact ⟨[], hend, by rw [gops_it]; exact iterate_end s i hend⟩
    · have hv' := hv (by omega)
      obtain ⟨c, j, hit, hj⟩ := iterate_valid s i hv'
      obtain ⟨j', hnx, hj'⟩ := nextind_mid s i h1 (by omega)
      have hjj : j' = j := Subtype.ext (by omega)
      rw [hjj] at hnx
      obtain ⟨q1, q2, q3, q4⟩ := nextZ_nextValid s i.val h1 (by omega)
      rw [← hj] at q1 q2 q3 q4
      obtain ⟨T, hT⟩ := ih (s.bytes.length + 1 - j.val).toNat (by omega) j (by omega) q2
        (by omega) q4
      exact ⟨(c, i, j) :: T, rfl, hv', by rw [gops_it]; exact hit,
        by rw [gops_gi]; exact getindex_of_iterate s i hv' hit, by rw [gops_nx]; exact hnx, q1, q2,
        hT⟩

theorem lastOf_le (s : JStr) : (lastOf (thisind s (ncodeunits s))).val ≤ s.bytes.length := by
  by_cases hN : 1 ≤ s.bytes.length
  · obtain ⟨j, hj, hjv⟩ := thisind_mid s (ncodeunits s) (by rw [ncu_val]; omega)
      (by rw [ncu_val]; exact Int.le_refl _)
    rw [hj]
    simp only [lastOf]
    rw [hjv, ncu_val]
    exact (thisZ_le s _).1
  · have h0 : (ncodeunits s).val = 0 := by rw [ncu_val]; omega
    have : thisind s (ncodeunits s) = .ok (ix 0) := by unfold thisind; rw [if_pos h0]
    rw [this]
    simp only [lastOf, ix0]
    omega

theorem lastOf_ge (s : JStr) (i : JInt64) (hv : validZ s i.val) :
    i.val ≤ (lastOf (thisind s (ncodeunits s))).val := by
  obtain ⟨h1, h2, h3⟩ := hv
  obtain ⟨j, hj, hjv⟩ := thisind_mid s (ncodeunits s) (by rw [ncu_val]; omega)
    (by rw [ncu_val]; exact Int.le_refl _)
  rw [hj]
  simp only [lastOf]
  rw [hjv, ncu_val]
  have ht := thisZ_le s s.bytes.length
  by_cases heq : thisZ s s.bytes.length = s.bytes.length
  · omega
  · have hcov := leadZ_covers s s.bytes.length (by omega) (Int.le_refl _) (by omega)
    by_cases hlt : i.val ≤ thisZ s s.bytes.length
    · exact hlt
    · have := leadZ_inside s (thisZ s s.bytes.length) i.val hcov.2.2.1 ⟨hcov.1, hcov.2.1⟩
        (by omega) (by omega)
      omega

theorem substring_seg (s : JStr) (a j k : JInt64) (ha : validZ s a.val) (hj : validZ s j.val)
    (haj : a.val ≤ j.val) (hk : nextind s j = .ok k) :
    substring s a j = .ok (toSub s (a, j, k)) := by
  have hva : isvalidAt s a = true := (isvalidAt_iff s a).2 ha
  have hvj : isvalidAt s j = true := (isvalidAt_iff s j).2 hj
  have h1 : (1 : Int) ≤ a.val := ha.1
  have h2 : j.val ≤ (ncodeunits s).val := by rw [ncu_val]; exact hj.2.1
  unfold substring
  simp only [haj, h1, h2, hva, hvj, hk, decide_true, Bool.not_true, Bool.and_self,
    Bool.false_eq_true, if_false, toSub]

theorem good_gops (P : Utf8proc) (hP : GbInit P) (s : JStr) : Good s (gops P s) where
  ncu := by rw [gops_ncu]; exact ncu_val s
  fuel := gops_fuel P s
  ilast_le := by rw [gops_ilast]; exact lastOf_le s
  ilast_ge := fun i hv => by rw [gops_ilast]; exact lastOf_ge s i hv
  sub := fun a j k h => by
    have hk := h.2.2.2.1
    rw [gops_nx] at hk
    simp only [gops_sub]
    exact substring_seg s a j k h.1 h.2.1 h.2.2.1 hk
  gb := by rw [gops_gb]; exact gb_ok P
  init := by rw [gops_gb]; exact gbInitV P hP
  chain := by
    have hs := ncu_small s
    have hix1 : (ix 1).val = 1 := ix1
    exact chain_exists P s s.bytes.length (ix 1) (by rw [hix1]; omega) (by rw [hix1]; omega)
      (by rw [hix1]; omega) (fun h => by rw [hix1]; exact valid_one s (by rw [hix1] at h; omega))

/-! ## `graphemes(s, m:n)` -/

theorem graphemesRange_proven : GraphemesRangeProp := by
  intro P hP s m n hm hmn
  exact rangeOf_spec s (gops P s) (good_gops P hP s) m n hm hmn

end JuliaLean.RegexUnicode.Uni
