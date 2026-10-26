import JuliaLean.BitSetsCov.BitSetChunk

/-!
# `_matched_map!` on `BitSet`s

Every vector primitive used by `_matched_map!(f, a1, b1, a2, b2, ...)` is
described by its effect on the global chunk view `Cg`; composing the views
shows that the result holds `f(chunk of s1, chunk of s2)` at every global chunk
index, which gives the elementwise specification of `union!`, `intersect!`,
`setdiff!` and `symdiff!`.
-/

namespace JuliaLean.BitSetsCov

open JuliaLean JuliaLean.BitArrays JuliaLean.BitArrays.BitSetProof

namespace BS

/-! ## `getD` on list operations -/

theorem getD_app (a b : List U64) : ∀ i : Nat,
    (a ++ b).getD i 0 = if i < a.length then a.getD i 0 else b.getD (i - a.length) 0 := by
  induction a with
  | nil => intro i; simp
  | cons x xs ih =>
    intro i
    cases i with
    | zero => simp
    | succ i =>
      rw [List.cons_append, List.getD_cons_succ, List.getD_cons_succ, ih, List.length_cons]
      by_cases h : i < xs.length
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega), show i + 1 - (xs.length + 1) = i - xs.length by omega]

theorem getD_rep (d : U64) : ∀ (n i : Nat), (List.replicate n d).getD i 0 = if i < n then d else 0
  | 0, i => by simp
  | n + 1, 0 => by simp
  | n + 1, i + 1 => by
    rw [List.replicate_succ, List.getD_cons_succ, getD_rep d n i]
    by_cases h : i < n
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

theorem getD_tk (a : List U64) : ∀ (n i : Nat), (a.take n).getD i 0 = if i < n then a.getD i 0 else 0 := by
  induction a with
  | nil => intro n i; simp
  | cons x xs ih =>
    intro n i
    cases n with
    | zero => simp
    | succ n =>
      cases i with
      | zero => simp
      | succ i =>
        rw [List.take_succ_cons, List.getD_cons_succ, List.getD_cons_succ, ih]
        by_cases h : i < n
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]

theorem getD_dr (a : List U64) : ∀ (n i : Nat), (a.drop n).getD i 0 = a.getD (i + n) 0 := by
  induction a with
  | nil => intro n i; simp
  | cons x xs ih =>
    intro n i
    cases n with
    | zero => simp
    | succ n =>
      rw [List.drop_succ_cons, ih, show i + (n + 1) = (i + n) + 1 by omega, List.getD_cons_succ]

theorem length_vset (a : List U64) (i : Nat) (x : U64) : (vset a i x).length = a.length := by
  unfold vset; simp

theorem getD_vset (a : List U64) (i j : Nat) (x : U64) (hi : 1 ≤ i) (hl : i - 1 < a.length) :
    (vset a i x).getD j 0 = if j = i - 1 then x else a.getD j 0 := by
  unfold vset; exact getD_set x a (i - 1) j hl

/-- A loop writing `F i a[i]` at the consecutive 1-based indices `lo, …, lo+n-1`. -/
def vfold (lo : Nat) (F : Nat → U64 → U64) (n : Nat) (a : List U64) : List U64 :=
  (List.range n).foldl (fun a k => vset a (lo + k) (F (lo + k) (vget a (lo + k)))) a

theorem vfold_succ (lo : Nat) (F : Nat → U64 → U64) (n : Nat) (a : List U64) :
    vfold lo F (n + 1) a = vset (vfold lo F n a) (lo + n) (F (lo + n) (vget (vfold lo F n a) (lo + n))) := by
  unfold vfold; rw [List.range_succ, List.foldl_append]; rfl

theorem fold_vset (a : List U64) (lo : Nat) (hlo : 1 ≤ lo) (F : Nat → U64 → U64) : ∀ n, (n ≠ 0 → lo - 1 + n ≤ a.length) →
    (vfold lo F n a).length = a.length ∧
    ∀ i : Nat, (vfold lo F n a).getD i 0 =
      if lo - 1 ≤ i ∧ i < lo - 1 + n then F (i + 1) (a.getD i 0) else a.getD i 0
  | 0, _ => ⟨rfl, fun i => by rw [if_neg (by omega)]; rfl⟩
  | n + 1, hn => by
    have hn' := hn (by omega)
    obtain ⟨hl, hg⟩ := fold_vset a lo hlo F n (fun _ => by omega)
    rw [vfold_succ]
    generalize vfold lo F n a = r at hl hg ⊢
    refine ⟨by rw [length_vset, hl], fun i => ?_⟩
    rw [getD_vset _ _ _ _ (by omega) (by rw [hl]; omega)]
    unfold vget
    rw [hg, hg]
    by_cases hi : i = lo + n - 1
    · rw [if_pos hi, if_neg (by omega), if_pos (by omega), hi, show lo + n - 1 + 1 = lo + n by omega]
    · rw [if_neg hi]
      by_cases h2 : lo - 1 ≤ i ∧ i < lo - 1 + n
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

/-! ## The chunk view of each primitive -/

theorem Cg_def (a : List U64) (B c : Int) :
    Cg a B c = if 0 ≤ c - B then a.getD (c - B).toNat 0 else 0 := rfl

theorem Cg_out (a : List U64) (B c : Int) (h : c < B ∨ B + a.length ≤ c) : Cg a B c = 0 := by
  rw [Cg_def]
  split
  · exact getD_ge _ _ (by omega)
  · rfl

theorem Cg_growend (a : List U64) (n : Nat) (d : U64) (B c : Int) :
    Cg (growend a n d) B c = if B + a.length ≤ c ∧ c < B + a.length + n then d else Cg a B c := by
  unfold growend
  rw [Cg_def, Cg_def]
  split
  · rw [getD_app, getD_rep]
    by_cases h1 : (c - B).toNat < a.length
    · rw [if_pos h1, if_neg (by omega)]
    · rw [if_neg h1, getD_ge _ _ (by omega)]
      by_cases h2 : (c - B).toNat - a.length < n
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]
  · rw [if_neg (by omega)]

theorem Cg_growbeg (a : List U64) (n : Nat) (d : U64) (B c : Int) :
    Cg (growbeg a n d) (B - n) c = if B - n ≤ c ∧ c < B then d else Cg a B c := by
  unfold growbeg
  rw [Cg_def, Cg_def]
  split
  · rw [getD_app, getD_rep, List.length_replicate]
    by_cases h1 : (c - (B - n)).toNat < n
    · rw [if_pos h1, if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega), if_pos (by omega),
        show (c - (B - n)).toNat - n = (c - B).toNat by omega]
  · rw [if_neg (by omega), if_neg (by omega)]

theorem Cg_deleteend (a : List U64) (n : Nat) (B c : Int) :
    Cg (deleteend a n) B c = if B + a.length - n ≤ c then 0 else Cg a B c := by
  unfold deleteend
  by_cases hc : 0 ≤ c - B
  · have e1 : ∀ a : List U64, Cg a B c = a.getD (c - B).toNat 0 := fun a => by rw [Cg_def, if_pos hc]
    rw [e1, e1, getD_tk]
    by_cases h1 : (c - B).toNat < a.length - n
    · rw [if_pos h1, if_neg (by omega)]
    · rw [if_neg h1]
      by_cases h2 : B + a.length - n ≤ c
      · rw [if_pos h2]
      · rw [if_neg h2, getD_ge _ _ (by omega)]
  · rw [Cg_out _ _ _ (Or.inl (by omega)), Cg_out a _ _ (Or.inl (by omega))]
    try (split <;> rfl)

theorem Cg_deletebeg (a : List U64) (n : Nat) (B c : Int) :
    Cg (deletebeg a n) (B + n) c = if c < B + n then 0 else Cg a B c := by
  unfold deletebeg
  rw [Cg_def, Cg_def]
  split
  · rw [if_neg (by omega), if_pos (by omega), getD_dr, show (c - (B + n)).toNat + n = (c - B).toNat by omega]
  · rw [if_pos (by omega)]

theorem length_growend (a : List U64) (n : Nat) (d : U64) : (growend a n d).length = a.length + n := by
  unfold growend; simp

theorem length_growbeg (a : List U64) (n : Nat) (d : U64) : (growbeg a n d).length = n + a.length := by
  unfold growbeg; simp

theorem length_deleteend (a : List U64) (n : Nat) : (deleteend a n).length = a.length - n := by
  unfold deleteend; simp

theorem length_deletebeg (a : List U64) (n : Nat) : (deletebeg a n).length = a.length - n := by
  unfold deletebeg; simp

def mcF (f : MapOp) (a2 : List U64) (bdiff : Int) (i : Nat) (v : U64) : U64 :=
  f.chunk v (vget a2 ((i : Int) - bdiff).toNat)

def zF (_i : Nat) (_v : U64) : U64 := 0

def cpF (src : List U64) (doffs soffs : Nat) (i : Nat) (_v : U64) : U64 := vget src (i - doffs + soffs)

theorem mapCommon_eq (f : MapOp) (a1 a2 : List U64) (bdiff lo hi : Int) (hlo : 0 ≤ lo) :
    mapCommon f a1 a2 bdiff lo hi = vfold lo.toNat (mcF f a2 bdiff) (hi - lo + 1).toNat a1 := by
  unfold mapCommon vfold mcF
  congr 1
  funext a k
  rw [show (lo + (k : Int)).toNat = lo.toNat + k by omega,
    show lo + (k : Int) - bdiff = ((lo.toNat + k : Nat) : Int) - bdiff by omega]

theorem length_mapCommon (f : MapOp) (a1 a2 : List U64) (bdiff lo hi : Int) (hlo : 1 ≤ lo)
    (hhi : hi ≤ a1.length) : (mapCommon f a1 a2 bdiff lo hi).length = a1.length := by
  rw [mapCommon_eq _ _ _ _ _ _ (by omega)]
  exact (fold_vset a1 lo.toNat (by omega) _ (hi - lo + 1).toNat (fun _ => by omega)).1

/-- `mapCommon` with `b2 = b1 + bdiff`: the chunks `lo..hi` become `f(s1 chunk, s2 chunk)`. -/
theorem Cg_mapCommon (f : MapOp) (a1 a2 : List U64) (b1 b2 lo hi c : Int) (hlo : 1 ≤ lo)
    (hlo2 : 1 + (b2 - b1) ≤ lo) (hhi : hi ≤ a1.length) :
    Cg (mapCommon f a1 a2 (b2 - b1) lo hi) b1 c =
      if b1 + lo - 1 ≤ c ∧ c ≤ b1 + hi - 1 then f.chunk (Cg a1 b1 c) (Cg a2 b2 c) else Cg a1 b1 c := by
  rw [mapCommon_eq _ _ _ _ _ _ (by omega)]
  have hf := (fold_vset a1 lo.toNat (by omega) (mcF f a2 (b2 - b1)) (hi - lo + 1).toNat (fun _ => by omega)).2
  by_cases hc : 0 ≤ c - b1
  · have e1 : ∀ a : List U64, Cg a b1 c = a.getD (c - b1).toNat 0 := fun a => by rw [Cg_def, if_pos hc]
    rw [e1, e1, hf]
    by_cases hr : b1 + lo - 1 ≤ c ∧ c ≤ b1 + hi - 1
    · rw [if_pos (by omega), if_pos hr]
      unfold mcF vget
      rw [Cg_def, if_pos (by omega), show (((c - b1).toNat + 1 : Nat) : Int) - (b2 - b1) = c - b2 + 1 by omega,
        show (c - b2 + 1).toNat - 1 = (c - b2).toNat by omega]
    · rw [if_neg (by omega), if_neg hr]
  · rw [Cg_out _ _ _ (Or.inl (by omega)), Cg_out a1 _ _ (Or.inl (by omega)), if_neg (by omega)]

theorem zeroRange_eq (a : List U64) (lo hi : Int) (hlo : 0 ≤ lo) :
    zeroRange a lo hi = vfold lo.toNat zF (hi - lo + 1).toNat a := by
  unfold zeroRange vfold zF
  congr 1
  funext a k
  rw [show (lo + (k : Int)).toNat = lo.toNat + k by omega]

theorem Cg_zeroRange (a : List U64) (B lo hi c : Int) (hlo : 1 ≤ lo) (hhi : hi ≤ a.length) :
    Cg (zeroRange a lo hi) B c = if B + lo - 1 ≤ c ∧ c ≤ B + hi - 1 then 0 else Cg a B c := by
  rw [zeroRange_eq _ _ _ (by omega)]
  have hf := (fold_vset a lo.toNat (by omega) zF (hi - lo + 1).toNat (fun _ => by omega)).2
  by_cases hc : 0 ≤ c - B
  · have e1 : ∀ a : List U64, Cg a B c = a.getD (c - B).toNat 0 := fun a => by rw [Cg_def, if_pos hc]
    rw [e1, e1, hf]
    by_cases hr : B + lo - 1 ≤ c ∧ c ≤ B + hi - 1
    · rw [if_pos (by omega), if_pos hr]; rfl
    · rw [if_neg (by omega), if_neg hr]
  · rw [Cg_out _ _ _ (Or.inl (by omega)), Cg_out a _ _ (Or.inl (by omega)), if_neg (by omega)]

theorem length_zeroRange (a : List U64) (lo hi : Int) (hlo : 1 ≤ lo) (hhi : hi ≤ a.length) :
    (zeroRange a lo hi).length = a.length := by
  rw [zeroRange_eq _ _ _ (by omega)]
  exact (fold_vset a lo.toNat (by omega) zF (hi - lo + 1).toNat (fun _ => by omega)).1

theorem vunsafeCopyto_eq (dest : List U64) (doffs : Nat) (src : List U64) (soffs n : Nat) :
    vunsafeCopyto dest doffs src soffs n = vfold doffs (cpF src doffs soffs) n dest := by
  unfold vunsafeCopyto vfold cpF
  congr 1
  funext a k
  rw [show doffs + k - doffs + soffs = soffs + k by omega]

theorem length_copy (dest : List U64) (doffs : Nat) (src : List U64) (soffs n : Nat) (hd : 1 ≤ doffs)
    (hn : doffs - 1 + n ≤ dest.length) : (vunsafeCopyto dest doffs src soffs n).length = dest.length := by
  rw [vunsafeCopyto_eq]
  exact (fold_vset dest doffs hd (cpF src doffs soffs) n (fun _ => hn)).1

/-- `unsafe_copyto!(dest, doffs, src, soffs, n)` with `dest` at offset `B` and
`src` at offset `Bs = B + doffs - soffs`. -/
theorem Cg_copy (dest : List U64) (doffs : Nat) (src : List U64) (soffs n : Nat) (B Bs c : Int)
    (hd : 1 ≤ doffs) (hs : 1 ≤ soffs) (hn : doffs - 1 + n ≤ dest.length) (hB : Bs = B + doffs - soffs) :
    Cg (vunsafeCopyto dest doffs src soffs n) B c =
      if B + doffs - 1 ≤ c ∧ c < B + doffs - 1 + n then Cg src Bs c else Cg dest B c := by
  rw [vunsafeCopyto_eq]
  have hf := (fold_vset dest doffs hd (cpF src doffs soffs) n (fun _ => hn)).2
  by_cases hc : 0 ≤ c - B
  · have e1 : ∀ a : List U64, Cg a B c = a.getD (c - B).toNat 0 := fun a => by rw [Cg_def, if_pos hc]
    rw [e1, e1, hf]
    by_cases hr : B + doffs - 1 ≤ c ∧ c < B + doffs - 1 + n
    · rw [if_pos (by omega), if_pos hr]
      unfold cpF vget
      rw [Cg_def, if_pos (by omega), show (c - B).toNat + 1 - doffs + soffs - 1 = (c - Bs).toNat by omega]
    · rw [if_neg (by omega), if_neg hr]
  · rw [Cg_out _ _ _ (Or.inl (by omega)), Cg_out dest _ _ (Or.inl (by omega)), if_neg (by omega)]

end BS

end JuliaLean.BitSetsCov

namespace JuliaLean.BitSetsCov

open JuliaLean JuliaLean.BitArrays JuliaLean.BitArrays.BitSetProof

namespace BS

theorem Cg_growbeg' (a : List U64) (n : Nat) (d : U64) (B B' c : Int) (h : B' = B - n) :
    Cg (growbeg a n d) B' c = if B - n ≤ c ∧ c < B then d else Cg a B c := by
  subst h; exact Cg_growbeg a n d B c

theorem Cg_deletebeg' (a : List U64) (n : Nat) (B B' c : Int) (h : B' = B + n) :
    Cg (deletebeg a n) B' c = if c < B + n then 0 else Cg a B c := by
  subst h; exact Cg_deletebeg a n B c

theorem Cg_nil (B c : Int) : Cg [] B c = 0 := Cg_out _ _ _ (by simp; omega)


set_option hygiene false in
/-- Closes one region of a chunk-view case split. -/
macro "mmclose" : tactic => `(tactic| first
  | rfl
  | (exfalso; omega)
  | (rw [Cg_out a1 b1 c (by omega), Cg_out a2 b2 c (by omega), hf.zz])
  | (rw [Cg_out a1 b1 c (by omega), hy])
  | (rw [Cg_out a2 b2 c (by omega), hx])
  | (rw [Cg_out a1 b1 c (by omega)])
  | (rw [Cg_out a2 b2 c (by omega)])
  | (rw [Cg_out a2 b2 c (by omega), Cg_out a1 b1 c (by omega), hf.zz]))

/-- The end-adjusting half of `_matched_map!` (`base/bitset.jl:219-238`) after the common loop. -/
def stB (A a2 : List U64) (b1 b2 l1 l2 : Int) (lff rff : Bool) (dirty : U64) : List U64 × Int :=
  let bdiff := b2 - b1
  let e1 := l1 + b1
  let e2 := l2 + b2
  let ediff := e2 - e1
  if ediff > 0 then
    if lff then (A, l1)
    else
      let a1 := growend A ediff.toNat dirty
      let (a1, l1) := if l1 + 1 ≤ bdiff then (zeroRange a1 (l1 + 1) bdiff, bdiff) else (a1, l1)
      let ediff := e2 - l1 - b1
      let a1 := vunsafeCopyto a1 (l1 + 1).toNat a2 (l2 + 1 - ediff).toNat ediff.toNat
      (a1, (a1.length : Int))
  else if ediff < 0 then
    if rff then (deleteend A (min l1 (-ediff)).toNat, l1) else (A, l1)
  else (A, l1)

/-- The start-adjusting half (`base/bitset.jl:240-252`). -/
def stC (aB : List U64) (lB : Int) (a2 : List U64) (b1 b2 l2 : Int) (lff rff : Bool) (dirty : U64) :
    List U64 × Int :=
  let bdiff := b2 - b1
  if bdiff < 0 then
    if lff then (aB, b1)
    else
      let a1 := growbeg aB (-bdiff).toNat dirty
      let a1 := zeroRange a1 (l2 + 1) (-bdiff)
      let b1 := b1 + bdiff
      (vunsafeCopyto a1 1 a2 1 (min (-bdiff) l2).toNat, b1)
  else if bdiff > 0 then
    if rff then (deletebeg aB (min lB bdiff).toNat, b1 + bdiff) else (aB, b1)
  else (aB, b1)

theorem matchedMapBits_eq (f : MapOp) (a1 : List U64) (b1 : Int) (a2 : List U64) (b2 : Int)
    (lff rff : Bool) (dirty : U64) :
    matchedMapBits f a1 b1 a2 b2 lff rff dirty =
      match stB (mapCommon f a1 a2 (b2 - b1) (max 1 (1 + (b2 - b1))) (min (a1.length : Int) ((a2.length : Int) + (b2 - b1))))
          a2 b1 b2 a1.length a2.length lff rff dirty with
      | (aB, lB) => stC aB lB a2 b1 b2 a2.length lff rff dirty := rfl

/-- What the four `MapOp`s do with a zero argument. -/
structure OpFacts (f : MapOp) (lff rff : Bool) : Prop where
  zz : f.chunk 0 0 = 0
  l1 : lff = true → ∀ y, f.chunk 0 y = 0
  l0 : lff = false → ∀ y, f.chunk 0 y = y
  r1 : rff = true → ∀ x, f.chunk x 0 = 0
  r0 : rff = false → ∀ x, f.chunk x 0 = x
  rl : rff = true → lff = true

theorem stB_spec (f : MapOp) (a1 A a2 : List U64) (b1 b2 : Int) (lff rff : Bool) (dirty : U64)
    (hf : OpFacts f lff rff) (hAl : A.length = a1.length)
    (hAv : ∀ c, Cg A b1 c = if b1 + max 1 (1 + (b2 - b1)) - 1 ≤ c ∧
        c ≤ b1 + min (a1.length : Int) ((a2.length : Int) + (b2 - b1)) - 1
      then f.chunk (Cg a1 b1 c) (Cg a2 b2 c) else Cg a1 b1 c)
    (aB : List U64) (lB : Int) (h : stB A a2 b1 b2 a1.length a2.length lff rff dirty = (aB, lB)) :
    (∀ c, b1 ≤ c → b2 ≤ c → Cg aB b1 c = f.chunk (Cg a1 b1 c) (Cg a2 b2 c)) ∧
    (∀ c, b1 ≤ c → c < b2 → Cg aB b1 c = Cg a1 b1 c) ∧
    (lff = true → lB = a1.length ∧ aB.length ≤ a1.length) := by
  unfold stB at h
  simp only [] at h
  by_cases he : (a2.length : Int) + b2 - ((a1.length : Int) + b1) > 0
  · rw [if_pos he] at h
    cases hl : lff
    · rw [hl] at h
      simp only [Bool.false_eq_true, if_false] at h
      have hy := hf.l0 hl
      by_cases hz : (a1.length : Int) + 1 ≤ b2 - b1
      · rw [if_pos hz] at h
        simp only [] at h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        subst h1 h2
        refine ⟨?_, ?_, fun h => absurd h (by simp)⟩
        · intro c hc1 hc2
          rw [Cg_copy _ _ _ _ _ _ b2 _ (by omega) (by omega)
              (by rw [length_zeroRange _ _ _ (by omega) (by rw [length_growend, hAl]; omega), length_growend, hAl]; omega)
              (by omega),
            Cg_zeroRange _ _ _ _ _ (by omega) (by rw [length_growend, hAl]; omega), Cg_growend, hAv, hAl]
          repeat' split
          all_goals mmclose
        · intro c hc1 hc2
          rw [Cg_copy _ _ _ _ _ _ b2 _ (by omega) (by omega)
              (by rw [length_zeroRange _ _ _ (by omega) (by rw [length_growend, hAl]; omega), length_growend, hAl]; omega)
              (by omega),
            Cg_zeroRange _ _ _ _ _ (by omega) (by rw [length_growend, hAl]; omega), Cg_growend, hAv, hAl]
          repeat' split
          all_goals mmclose
      · rw [if_neg hz] at h
        simp only [] at h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        subst h1 h2
        refine ⟨?_, ?_, fun h => absurd h (by simp)⟩
        · intro c hc1 hc2
          rw [Cg_copy _ _ _ _ _ _ b2 _ (by omega) (by omega) (by rw [length_growend, hAl]; omega) (by omega),
            Cg_growend, hAv, hAl]
          repeat' split
          all_goals mmclose
        · intro c hc1 hc2
          rw [Cg_copy _ _ _ _ _ _ b2 _ (by omega) (by omega) (by rw [length_growend, hAl]; omega) (by omega),
            Cg_growend, hAv, hAl]
          repeat' split
          all_goals mmclose
    · rw [hl] at h
      simp only [if_true] at h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      subst h1 h2
      have hy := hf.l1 hl
      refine ⟨?_, ?_, fun _ => ⟨rfl, by omega⟩⟩
      · intro c hc1 hc2
        rw [hAv]
        repeat' split
        all_goals mmclose
      · intro c hc1 hc2
        rw [hAv]
        repeat' split
        all_goals mmclose
  · rw [if_neg he] at h
    by_cases he2 : (a2.length : Int) + b2 - ((a1.length : Int) + b1) < 0
    · rw [if_pos he2] at h
      cases hr : rff
      · rw [hr] at h
        simp only [Bool.false_eq_true, if_false] at h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        subst h1 h2
        have hx := hf.r0 hr
        refine ⟨?_, ?_, fun _ => ⟨rfl, by omega⟩⟩
        · intro c hc1 hc2
          rw [hAv]
          repeat' split
          all_goals mmclose
        · intro c hc1 hc2
          rw [hAv]
          repeat' split
          all_goals mmclose
      · rw [hr] at h
        simp only [if_true] at h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        subst h1 h2
        have hx := hf.r1 hr
        refine ⟨?_, ?_, fun _ => ⟨rfl, by rw [length_deleteend, hAl]; omega⟩⟩
        · intro c hc1 hc2
          rw [Cg_deleteend, hAv, hAl]
          repeat' split
          all_goals mmclose
        · intro c hc1 hc2
          rw [Cg_deleteend, hAv, hAl]
          repeat' split
          all_goals mmclose
    · rw [if_neg he2] at h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      subst h1 h2
      refine ⟨?_, ?_, fun _ => ⟨rfl, by omega⟩⟩
      · intro c hc1 hc2
        rw [hAv]
        repeat' split
        all_goals mmclose
      · intro c hc1 hc2
        rw [hAv]
        repeat' split
        all_goals mmclose

theorem Cg_matchedMapBits (f : MapOp) (a1 : List U64) (b1 : Int) (a2 : List U64) (b2 : Int)
    (lff rff : Bool) (dirty : U64) (hf : OpFacts f lff rff) (c : Int) :
    Cg (matchedMapBits f a1 b1 a2 b2 lff rff dirty).1 (matchedMapBits f a1 b1 a2 b2 lff rff dirty).2 c =
      f.chunk (Cg a1 b1 c) (Cg a2 b2 c) := by
  have hAl := length_mapCommon f a1 a2 (b2 - b1) (max 1 (1 + (b2 - b1)))
    (min (a1.length : Int) ((a2.length : Int) + (b2 - b1))) (by omega) (by omega)
  have hAv := fun c => Cg_mapCommon f a1 a2 b1 b2 (max 1 (1 + (b2 - b1)))
    (min (a1.length : Int) ((a2.length : Int) + (b2 - b1))) c (by omega) (by omega) (by omega)
  rw [matchedMapBits_eq]
  generalize mapCommon f a1 a2 (b2 - b1) (max 1 (1 + (b2 - b1)))
    (min (a1.length : Int) ((a2.length : Int) + (b2 - b1))) = A at hAl hAv ⊢
  rcases hB : stB A a2 b1 b2 a1.length a2.length lff rff dirty with ⟨aB, lB⟩
  obtain ⟨P1, P2, P3⟩ := stB_spec f a1 A a2 b1 b2 lff rff dirty hf hAl hAv aB lB hB
  simp only []
  unfold stC
  simp only []
  by_cases hb : b2 - b1 < 0
  · rw [if_pos hb]
    cases hl : lff
    · simp only [Bool.false_eq_true, if_false]
      have hy := hf.l0 hl
      have hgl : (growbeg aB (-(b2 - b1)).toNat dirty).length = (-(b2 - b1)).toNat + aB.length := length_growbeg _ _ _
      rw [Cg_copy _ _ _ _ _ _ b2 _ (by omega) (by omega)
          (by rw [length_zeroRange _ _ _ (by omega) (by rw [hgl]; omega), hgl]; omega) (by omega),
        Cg_zeroRange _ _ _ _ _ (by omega) (by rw [hgl]; omega),
        Cg_growbeg' _ _ _ b1 _ _ (by omega)]
      by_cases hc : b1 ≤ c
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), P1 c hc (by omega)]
      · rw [Cg_out aB b1 c (by omega), Cg_out a1 b1 c (by omega), hy]
        repeat' split
        all_goals mmclose
    · simp only [if_true]
      have hy := hf.l1 hl
      by_cases hc : b1 ≤ c
      · exact P1 c hc (by omega)
      · rw [Cg_out aB b1 c (by omega), Cg_out a1 b1 c (by omega), hy]
  · rw [if_neg hb]
    by_cases hb2 : b2 - b1 > 0
    · rw [if_pos hb2]
      cases hr : rff
      · simp only [Bool.false_eq_true, if_false]
        have hx := hf.r0 hr
        by_cases hc : b1 ≤ c
        · by_cases hc2 : b2 ≤ c
          · exact P1 c hc hc2
          · rw [P2 c hc (by omega), Cg_out a2 b2 c (by omega), hx]
        · rw [Cg_out aB b1 c (by omega), Cg_out a1 b1 c (by omega), Cg_out a2 b2 c (by omega), hf.zz]
      · simp only [if_true]
        have hx := hf.r1 hr
        have hlff : lff = true := hf.rl hr
        obtain ⟨hlB, hlen⟩ := P3 hlff
        by_cases hm : (a1.length : Int) ≤ b2 - b1
        · have hnil : deletebeg aB (min lB (b2 - b1)).toNat = [] := by
            unfold deletebeg; rw [List.drop_eq_nil_of_le]; omega
          rw [hnil, Cg_nil]
          by_cases hc2 : b2 ≤ c
          · rw [Cg_out a1 b1 c (by omega), hf.l1 hlff]
          · rw [Cg_out a2 b2 c (by omega), hx]
        · rw [Cg_deletebeg' _ _ b1 _ _ (by omega)]
          split
          · rw [Cg_out a2 b2 c (by omega), hx]
          · exact P1 c (by omega) (by omega)
    · rw [if_neg hb2]
      by_cases hc : b1 ≤ c
      · exact P1 c hc (by omega)
      · rw [Cg_out aB b1 c (by omega), Cg_out a1 b1 c (by omega), Cg_out a2 b2 c (by omega), hf.zz]

end BS

end JuliaLean.BitSetsCov
