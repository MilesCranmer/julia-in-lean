import JuliaLean.Core

/-!
Binary searches on vectors, `base/sort.jl:184-238` (master `bbfa0ce4150`),
and `issorted(itr, order)`, `base/sort.jl:48-60`.

The searches take the window `lo::T`, `hi::T` of an arbitrary integer type `T`.
Their locals change type as the source runs: `m + 1` and `half_len + 1` add
the `Int` literal `1` and so are computed in `promote_type(T, Int)`, while
`midpoint`, `T(1)` and the sentinels stay in `T`. `SearchIndex` records the
current Julia type of each local. The keyword methods (`sort.jl:304-311`) call
these with `lo = firstindex(v) = 1` and `hi = lastindex(v)`, both `Int`.
-/

namespace JuliaLean.Sort

open JuliaLean

/-- An integer local together with its current Julia type. -/
structure SearchIndex where
  ty : IntTy
  word : JInt ty

def searchIndex (t : IntTy) (x : Int) : SearchIndex := ⟨t, JInt.wrap t x⟩

def SearchIndex.val (x : SearchIndex) : Int := x.word.val

/-- `x + y` and `x - y` after promotion (`base/int.jl`), wrapping in the promoted type. -/
def indexAdd (x y : SearchIndex) : SearchIndex :=
  searchIndex (IntTy.promote x.ty y.ty) (x.val + y.val)

def indexSub (x y : SearchIndex) : SearchIndex :=
  searchIndex (IntTy.promote x.ty y.ty) (x.val - y.val)

/-- `x >>> 0x01` (logical shift of the bit pattern), `base/sort.jl:188`. -/
def indexHalf (x : SearchIndex) : SearchIndex :=
  searchIndex x.ty ((x.val % (2 ^ x.ty.bits)) / 2)

/-- `midpoint(lo::T, hi::T) = lo +% ((hi -% lo) >>> 0x01)`, `base/array.jl:2288`. -/
def indexMidpoint (lo hi : SearchIndex) : SearchIndex :=
  indexAdd lo (indexHalf (indexSub hi lo))

/-- Outcome of a search. `invalidAccess i` is an `@inbounds` read of `v[i]`
outside the vector (undefined behaviour in Julia: it reads arbitrary memory);
`exhausted` is the model's fuel running out, never a Julia outcome. -/
inductive SearchResult (α : Type) where
  | returned (value : α)
  | invalidAccess (index : Int)
  | exhausted
  deriving DecidableEq

/-- One-based read `v[i]`; `none` outside the vector. -/
def vectorRead (v : Array α) (i : Int) : Option α :=
  if 1 ≤ i then v[i.toNat - 1]? else none

/-- Loop of `searchsortedfirst`, `base/sort.jl:187-197`. `hi = m` is dead
(the loop reads only `lo` and `len`) and is omitted. -/
def firstSearchLoop (lt : α → α → Bool) (v : Array α) (x : α) :
    Nat → SearchIndex → SearchIndex → SearchResult Int
  | 0, _, _ => .exhausted
  | fuel + 1, lo, len =>
    if len.val = 0 then .returned lo.val else
    let half := indexHalf len
    let m := indexAdd lo half
    match vectorRead v m.val with
    | none => .invalidAccess m.val
    | some a =>
      if lt a x then
        firstSearchLoop lt v x fuel (indexAdd m (searchIndex .i64 1))
          (indexSub len (indexAdd half (searchIndex .i64 1)))
      else firstSearchLoop lt v x fuel lo half

/-- `searchsortedfirst(v, x, lo::T, hi::T, o)`, `base/sort.jl:184-199`. -/
def searchsortedfirst (lt : α → α → Bool) (v : Array α) (x : α) {t : IntTy}
    (lo hi : JInt t) (fuel : Nat := v.size + 2) : SearchResult Int :=
  let l : SearchIndex := ⟨t, lo⟩
  let h := indexAdd ⟨t, hi⟩ (searchIndex t 1)
  firstSearchLoop lt v x fuel l (indexSub h l)

/-- Loop of `searchsortedlast`, `base/sort.jl:207-214`. -/
def lastSearchLoop (lt : α → α → Bool) (v : Array α) (x : α) (u : SearchIndex) :
    Nat → SearchIndex → SearchIndex → SearchResult Int
  | 0, _, _ => .exhausted
  | fuel + 1, lo, hi =>
    if lo.val = (indexSub hi u).val then .returned lo.val else
    let m := indexMidpoint lo hi
    match vectorRead v m.val with
    | none => .invalidAccess m.val
    | some a =>
      if lt x a then lastSearchLoop lt v x u fuel lo m
      else lastSearchLoop lt v x u fuel m hi

/-- `searchsortedlast(v, x, lo::T, hi::T, o)`, `base/sort.jl:203-216`. -/
def searchsortedlast (lt : α → α → Bool) (v : Array α) (x : α) {t : IntTy}
    (lo hi : JInt t) (fuel : Nat := v.size + 2) : SearchResult Int :=
  let u := searchIndex t 1
  lastSearchLoop lt v x u fuel (indexSub ⟨t, lo⟩ u) (indexAdd ⟨t, hi⟩ u)

/-- Loop of `searchsorted`, `base/sort.jl:225-237`: `v[m] < x` is tested before
`x < v[m]`; on a match the first and last searches run on `lo+u:m` and `m:hi-u`. -/
def equalSearchLoop (lt : α → α → Bool) (v : Array α) (x : α) (u : SearchIndex) :
    Nat → SearchIndex → SearchIndex → SearchResult (Int × Int)
  | 0, _, _ => .exhausted
  | fuel + 1, lo, hi =>
    if lo.val = (indexSub hi u).val then
      .returned ((indexAdd lo (searchIndex .i64 1)).val, (indexSub hi (searchIndex .i64 1)).val)
    else
      let m := indexMidpoint lo hi
      match vectorRead v m.val with
      | none => .invalidAccess m.val
      | some a =>
        if lt a x then equalSearchLoop lt v x u fuel m hi
        else if lt x a then equalSearchLoop lt v x u fuel lo m
        else
          let start := indexAdd lo u
          match firstSearchLoop lt v x (v.size + 2) start
              (indexSub (indexAdd m (searchIndex m.ty 1)) start) with
          | .invalidAccess i => .invalidAccess i
          | .exhausted => .exhausted
          | .returned a =>
            match lastSearchLoop lt v x (searchIndex m.ty 1) (v.size + 2)
                (indexSub m (searchIndex m.ty 1)) (indexAdd (indexSub hi u) (searchIndex m.ty 1)) with
            | .returned b => .returned (a, b)
            | .invalidAccess i => .invalidAccess i
            | .exhausted => .exhausted

/-- `searchsorted(v, x, ilo::T, ihi::T, o)`, `base/sort.jl:221-238`. -/
def searchsorted (lt : α → α → Bool) (v : Array α) (x : α) {t : IntTy}
    (lo hi : JInt t) (fuel : Nat := v.size + 2) : SearchResult (Int × Int) :=
  let u := searchIndex t 1
  equalSearchLoop lt v x u fuel (indexSub ⟨t, lo⟩ u) (indexAdd ⟨t, hi⟩ u)

/-- `issorted(itr, order)`, `base/sort.jl:48-60`, on a finite list. -/
def issorted (lt : α → α → Bool) : List α → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => if lt b a then false else issorted lt (b :: rest)

/-! ### Specifications -/

/-- `lt` is a strict weak order (`sort!` docstring, sort.jl): irreflexive and
negatively transitive (`lt a c → lt a b ∨ lt b c`). -/
def NegTransOrder (lt : α → α → Bool) : Prop :=
  (∀ a, lt a a = false) ∧ (∀ a b c, lt a c = true → lt a b = true ∨ lt b c = true)

/-- `v` is sorted under `lt`: no later element is ordered before an earlier one. -/
def VecSorted (lt : α → α → Bool) (v : Array α) : Prop :=
  ∀ (i j : Int) (a b : α), i ≤ j → vectorRead v i = some a → vectorRead v j = some b →
    lt b a = false

/-- The `1`-based exact boundary `r` of a predicate on the window `[L, H)`. -/
def SearchPartition (p : Int → Bool) (L H r : Int) : Prop :=
  L ≤ r ∧ r ≤ H ∧ (∀ i, L ≤ i → i < r → p i = true) ∧ (∀ i, r ≤ i → i < H → p i = false)

/-- `v[i]` is ordered before `x`. -/
def before (lt : α → α → Bool) (v : Array α) (x : α) (i : Int) : Bool :=
  match vectorRead v i with
  | some a => lt a x
  | none => false

/-- `v[i]` is not ordered after `x`. -/
def notAfter (lt : α → α → Bool) (v : Array α) (x : α) (i : Int) : Bool :=
  match vectorRead v i with
  | some a => !(lt x a)
  | none => false

/-- `searchsortedfirst(v, x; lt, by, rev, order)` and `searchsortedlast` return the
docstring answers (sort.jl:353-357, 392-396) for every vector sorted under a
strict weak order (the keyword methods search the `Int` window `1:length(v)`). -/
def VectorSearchCorrect : Prop :=
  ∀ (α : Type) (lt : α → α → Bool) (v : Array α) (x : α),
    NegTransOrder lt → VecSorted lt v → v.size < 2 ^ 62 →
    (∃ r, searchsortedfirst lt v x (JInt.lit .i64 1) (JInt.lit .i64 v.size) = .returned r ∧
        SearchPartition (before lt v x) 1 (v.size + 1) r) ∧
    (∃ r, searchsortedlast lt v x (JInt.lit .i64 1) (JInt.lit .i64 v.size) = .returned r ∧
        SearchPartition (notAfter lt v x) 1 (v.size + 1) (r + 1))

/-- The positional methods `searchsortedlast(v, x, lo::T, hi::T, o)` never read
outside `lo:hi` for a valid window `1 ≤ lo ≤ hi ≤ length(v)` of any integer type. -/
def WindowSearchInBounds : Prop :=
  ∀ (α : Type) (lt : α → α → Bool) (v : Array α) (x : α) (t : IntTy) (lo hi : JInt t),
    1 ≤ lo.val → lo.val ≤ hi.val → hi.val ≤ v.size →
    ∀ i, searchsortedlast lt v x lo hi ≠ .invalidAccess i

/-! ### Proofs for `Int` windows -/

private abbrev I (x : Int) : SearchIndex := searchIndex .i64 x

private theorem I_val {x : Int} (h0 : -(2 ^ 62) ≤ x) (h1 : x ≤ 2 ^ 62) : (I x).val = x :=
  wrapInt_of_inRange .i64 x ⟨by simp [IntTy.min, IntTy.signed, IntTy.bits]; omega,
    by simp [IntTy.max, IntTy.signed, IntTy.bits]; omega⟩

private theorem I_ty (x : Int) : (I x).ty = .i64 := rfl

private theorem add_I {a b : Int} (ha0 : -(2 ^ 62) ≤ a) (ha1 : a ≤ 2 ^ 62)
    (hb0 : -(2 ^ 62) ≤ b) (hb1 : b ≤ 2 ^ 62) : indexAdd (I a) (I b) = I (a + b) := by
  unfold indexAdd
  rw [I_val ha0 ha1, I_val hb0 hb1]
  rfl

private theorem sub_I {a b : Int} (ha0 : -(2 ^ 62) ≤ a) (ha1 : a ≤ 2 ^ 62)
    (hb0 : -(2 ^ 62) ≤ b) (hb1 : b ≤ 2 ^ 62) : indexSub (I a) (I b) = I (a - b) := by
  unfold indexSub
  rw [I_val ha0 ha1, I_val hb0 hb1]
  rfl

private theorem half_I {a : Int} (ha0 : 0 ≤ a) (ha1 : a ≤ 2 ^ 62) : indexHalf (I a) = I (a / 2) := by
  unfold indexHalf
  rw [I_val (by omega) ha1]
  show searchIndex .i64 ((a % 2 ^ 64) / 2) = _
  rw [Int.emod_eq_of_lt ha0 (by omega)]

private theorem mid_I {a b : Int} (h0 : 0 ≤ a) (h1 : a ≤ b) (h2 : b ≤ 2 ^ 62) :
    indexMidpoint (I a) (I b) = I (a + (b - a) / 2) := by
  unfold indexMidpoint
  rw [sub_I (by omega) (by omega) (by omega) (by omega), half_I (by omega) (by omega),
    add_I (by omega) (by omega) (by omega) (by omega)]

private theorem read_some {v : Array α} {i : Int} (h1 : 1 ≤ i) (h2 : i ≤ v.size) :
    ∃ a, vectorRead v i = some a := by
  unfold vectorRead
  rw [if_pos h1]
  exact ⟨v[i.toNat - 1]'(by omega), Array.getElem?_eq_getElem (by omega)⟩

private theorem before_of {lt : α → α → Bool} {v : Array α} {x a : α} {i : Int}
    (h : vectorRead v i = some a) : before lt v x i = lt a x := by
  unfold before; rw [h]

private theorem notAfter_of {lt : α → α → Bool} {v : Array α} {x a : α} {i : Int}
    (h : vectorRead v i = some a) : notAfter lt v x i = !(lt x a) := by
  unfold notAfter; rw [h]

/-- The first-search loop returns the exact boundary of a monotone predicate. -/
private theorem firstLoop_correct (lt : α → α → Bool) (v : Array α) (x : α)
    (hsz : v.size < 2 ^ 62)
    (mono : ∀ i j : Int, 1 ≤ i → i ≤ j → j ≤ v.size → before lt v x j = true → before lt v x i = true) :
    ∀ (fuel len : Nat) (lo : Int), len < fuel → 1 ≤ lo → lo + len ≤ v.size + 1 →
      ∃ r, firstSearchLoop lt v x fuel (I lo) (I len) = .returned r ∧
        SearchPartition (before lt v x) lo (lo + len) r := by
  intro fuel
  induction fuel with
  | zero => intro len lo h; omega
  | succ fuel ih =>
    intro len lo hfuel hlo hhi
    unfold firstSearchLoop
    rw [I_val (by omega) (by omega)]
    by_cases hz : (len : Int) = 0
    · rw [if_pos hz]
      refine ⟨_, rfl, ?_⟩
      rw [I_val (by omega) (by omega)]
      refine ⟨by omega, by omega, fun i h1 h2 => by omega, fun i h1 h2 => by omega⟩
    · rw [if_neg hz]
      have hhalf : indexHalf (I len) = I ((len : Int) / 2) := half_I (by omega) (by omega)
      have hm : indexAdd (I lo) (I ((len : Int) / 2)) = I (lo + (len : Int) / 2) :=
        add_I (by omega) (by omega) (by omega) (by omega)
      have hmv : (I (lo + (len : Int) / 2)).val = lo + (len : Int) / 2 := I_val (by omega) (by omega)
      simp only [hhalf, hm, hmv]
      obtain ⟨a, ha⟩ := read_some (v := v) (i := lo + (len : Int) / 2) (by omega) (by omega)
      rw [ha]
      simp only
      cases hc : lt a x
      · -- `hi = m; len = half_len`
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hl2 : ((len : Int) / 2) = (((len / 2 : Nat)) : Int) := by omega
        rw [hl2]
        obtain ⟨r, hr, hp⟩ := ih (len / 2) lo (by omega) hlo (by omega)
        refine ⟨r, hr, ?_⟩
        obtain ⟨h1, h2, h3, h4⟩ := hp
        have hmb : before lt v x (lo + (len : Int) / 2) = false := by rw [before_of ha, hc]
        refine ⟨h1, by omega, h3, ?_⟩
        intro i hi1 hi2
        by_cases hi : i < lo + ((len / 2 : Nat) : Int)
        · exact h4 i hi1 hi
        · cases hb : before lt v x i with
          | false => rfl
          | true =>
            have := mono (lo + (len : Int) / 2) i (by omega) (by omega) (by omega) hb
            rw [hmb] at this; exact absurd this (by decide)
      · -- `lo = m + 1; len -= half_len + 1`
        simp only [↓reduceIte]
        have e1 : indexAdd (I (lo + (len : Int) / 2)) (I 1) = I (lo + (len : Int) / 2 + 1) :=
          add_I (by omega) (by omega) (by omega) (by omega)
        have e2 : indexAdd (I ((len : Int) / 2)) (I 1) = I ((len : Int) / 2 + 1) :=
          add_I (by omega) (by omega) (by omega) (by omega)
        have e3 : indexSub (I len) (I ((len : Int) / 2 + 1)) = I ((len : Int) - ((len : Int) / 2 + 1)) :=
          sub_I (by omega) (by omega) (by omega) (by omega)
        rw [e1, e2, e3]
        have hl2 : (len : Int) - ((len : Int) / 2 + 1) = (((len - len / 2 - 1 : Nat)) : Int) := by omega
        rw [hl2]
        obtain ⟨r, hr, hp⟩ := ih (len - len / 2 - 1) (lo + (len : Int) / 2 + 1)
          (by omega) (by omega) (by omega)
        refine ⟨r, hr, ?_⟩
        obtain ⟨h1, h2, h3, h4⟩ := hp
        have hmb : before lt v x (lo + (len : Int) / 2) = true := by rw [before_of ha, hc]
        refine ⟨by omega, by omega, ?_, fun i hi1 hi2 => h4 i hi1 (by omega)⟩
        intro i hi1 hi2
        by_cases hi : lo + (len : Int) / 2 + 1 ≤ i
        · exact h3 i hi hi2
        · exact mono i (lo + (len : Int) / 2) (by omega) (by omega) (by omega) hmb

/-- The last-search loop returns the exact boundary of a monotone predicate. -/
private theorem lastLoop_correct (lt : α → α → Bool) (v : Array α) (x : α)
    (hsz : v.size < 2 ^ 62)
    (mono : ∀ i j : Int, 1 ≤ i → i ≤ j → j ≤ v.size → notAfter lt v x j = true → notAfter lt v x i = true) :
    ∀ (fuel gap : Nat) (lo : Int), gap < fuel → 0 ≤ lo → lo + gap + 1 ≤ v.size + 1 →
      ∃ r, lastSearchLoop lt v x (I 1) fuel (I lo) (I (lo + gap + 1)) = .returned r ∧
        SearchPartition (notAfter lt v x) (lo + 1) (lo + gap + 1) (r + 1) := by
  intro fuel
  induction fuel with
  | zero => intro gap lo h; omega
  | succ fuel ih =>
    intro gap lo hfuel hlo hhi
    unfold lastSearchLoop
    have e0 : indexSub (I (lo + gap + 1)) (I 1) = I (lo + gap + 1 - 1) :=
      sub_I (by omega) (by omega) (by omega) (by omega)
    rw [e0, I_val (by omega) (by omega), I_val (by omega) (by omega)]
    by_cases hz : (gap : Int) = 0
    · rw [if_pos (by omega)]
      refine ⟨lo, rfl, ?_⟩
      refine ⟨by omega, by omega, fun i h1 h2 => by omega, fun i h1 h2 => by omega⟩
    · rw [if_neg (by omega)]
      have em : indexMidpoint (I lo) (I (lo + gap + 1)) = I (lo + (lo + gap + 1 - lo) / 2) :=
        mid_I (by omega) (by omega) (by omega)
      have emv : (I (lo + (lo + gap + 1 - lo) / 2)).val = lo + (lo + gap + 1 - lo) / 2 :=
        I_val (by omega) (by omega)
      simp only [em, emv]
      obtain ⟨a, ha⟩ := read_some (v := v) (i := lo + (lo + gap + 1 - lo) / 2) (by omega) (by omega)
      rw [ha]
      simp only
      have hmr : lo < lo + (lo + gap + 1 - lo) / 2 ∧ lo + (lo + gap + 1 - lo) / 2 < lo + gap + 1 := by
        omega
      generalize hmd : lo + (lo + gap + 1 - lo) / 2 = m at *
      cases hc : lt x a
      · -- `lo = m`
        simp only [Bool.false_eq_true, ↓reduceIte]
        have he : lo + ↑gap + 1 = m + (((lo + gap - m : Int).toNat : Nat) : Int) + 1 := by omega
        rw [he]
        obtain ⟨r, hr, hp⟩ := ih (lo + gap - m).toNat m (by omega) (by omega) (by omega)
        refine ⟨r, hr, ?_⟩
        obtain ⟨h1, h2, h3, h4⟩ := hp
        have hmv : notAfter lt v x m = true := by rw [notAfter_of ha, hc]; rfl
        refine ⟨by omega, by omega, ?_, fun i hi1 hi2 => h4 i hi1 (by omega)⟩
        intro i hi1 hi2
        by_cases hi : m + 1 ≤ i
        · exact h3 i hi hi2
        · exact mono i m (by omega) (by omega) (by omega) hmv
      · -- `hi = m`
        simp only [↓reduceIte]
        have he : m = lo + (((m - lo - 1 : Int).toNat : Nat) : Int) + 1 := by omega
        obtain ⟨r, hr, hp⟩ := ih (m - lo - 1).toNat lo (by omega) hlo (by omega)
        rw [← he] at hr hp
        refine ⟨r, hr, ?_⟩
        obtain ⟨h1, h2, h3, h4⟩ := hp
        have hmv : notAfter lt v x m = false := by rw [notAfter_of ha, hc]; rfl
        refine ⟨h1, by omega, h3, ?_⟩
        intro i hi1 hi2
        by_cases hi : i < m
        · exact h4 i hi1 hi
        · cases hb : notAfter lt v x i with
          | false => rfl
          | true =>
            have := mono m i (by omega) (by omega) (by omega) hb
            rw [hmv] at this; exact absurd this (by decide)

theorem vectorSearchCorrect : VectorSearchCorrect := by
  intro α lt v x ⟨hirr, hneg⟩ hs hsz
  have monoB : ∀ i j : Int, 1 ≤ i → i ≤ j → j ≤ v.size →
      before lt v x j = true → before lt v x i = true := by
    intro i j hi hij hj hb
    obtain ⟨a, ha⟩ := read_some (v := v) (i := i) hi (by omega)
    obtain ⟨b, hb'⟩ := read_some (v := v) (i := j) (by omega) hj
    rw [before_of hb'] at hb
    rw [before_of ha]
    rcases hneg b a x hb with h | h
    · rw [hs i j a b hij ha hb'] at h; exact absurd h (by decide)
    · exact h
  have monoN : ∀ i j : Int, 1 ≤ i → i ≤ j → j ≤ v.size →
      notAfter lt v x j = true → notAfter lt v x i = true := by
    intro i j hi hij hj hb
    obtain ⟨a, ha⟩ := read_some (v := v) (i := i) hi (by omega)
    obtain ⟨b, hb'⟩ := read_some (v := v) (i := j) (by omega) hj
    rw [notAfter_of hb'] at hb
    rw [notAfter_of ha]
    cases hxa : lt x a with
    | false => rfl
    | true =>
      rcases hneg x b a hxa with h | h
      · rw [h] at hb; exact absurd hb (by decide)
      · rw [hs i j a b hij ha hb'] at h; exact absurd h (by decide)
  constructor
  · unfold searchsortedfirst
    have e1 : (⟨.i64, JInt.lit .i64 1⟩ : SearchIndex) = I 1 := rfl
    have e2 : indexAdd ⟨.i64, JInt.lit .i64 v.size⟩ (searchIndex .i64 1) = I (v.size + 1) := by
      show indexAdd (I v.size) (I 1) = _
      exact add_I (by omega) (by omega) (by omega) (by omega)
    simp only
    rw [e1, e2, sub_I (by omega) (by omega) (by omega) (by omega)]
    have e3 : (v.size : Int) + 1 - 1 = ((v.size : Nat) : Int) := by omega
    rw [e3]
    obtain ⟨r, hr, hp⟩ := firstLoop_correct lt v x hsz monoB (v.size + 2) v.size 1 (by omega)
      (by omega) (by omega)
    exact ⟨r, hr, by rw [Int.add_comm]; exact hp⟩
  · unfold searchsortedlast
    have e1 : indexSub ⟨.i64, JInt.lit .i64 1⟩ (searchIndex .i64 1) = I 0 := by
      show indexSub (I 1) (I 1) = _
      exact sub_I (by omega) (by omega) (by omega) (by omega)
    have e2 : indexAdd ⟨.i64, JInt.lit .i64 v.size⟩ (searchIndex .i64 1) = I (0 + v.size + 1) := by
      show indexAdd (I v.size) (I 1) = _
      rw [add_I (by omega) (by omega) (by omega) (by omega)]
      congr 1; omega
    simp only
    rw [e1, e2]
    obtain ⟨r, hr, hp⟩ := lastLoop_correct lt v x hsz monoN (v.size + 2) v.size 0 (by omega)
      (by omega) (by omega)
    refine ⟨r, hr, ?_⟩
    have e4 : (0 : Int) + ↑v.size + 1 = ↑v.size + 1 := by omega
    rw [e4] at hp
    simpa using hp

/-! ### Refutation: the `UInt8` window `1:255` -/

/-- `searchsortedlast(v, x, 0x01, 0xff, o)`: `hi + 0x01` wraps to `0x00`, so both
sentinels are `0x00`, `lo != hi - u` holds, and `midpoint(0x00, 0x00) = 0x00` is read. -/
theorem u8WindowReadsZero :
    searchsortedlast (fun a b => decide (a < b)) (Array.replicate 255 (0 : Int)) 0
      (JInt.lit .u8 1) (JInt.lit .u8 255) = .invalidAccess 0 := by
  decide +kernel

theorem windowSearchInBounds_refuted : ¬ WindowSearchInBounds := by
  intro h
  exact h Int (fun a b => decide (a < b)) (Array.replicate 255 0) 0 .u8 (JInt.lit .u8 1)
    (JInt.lit .u8 255) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0 u8WindowReadsZero

/-! ### `issorted` -/

/-- `issorted(xs, o)` holds iff no element is ordered before its predecessor. -/
def IssortedAdjacent : Prop := ∀ (α : Type) (lt : α → α → Bool) (xs : List α),
  issorted lt xs = true ↔ ∀ (i : Nat) (h : i + 1 < xs.length),
    lt (xs[i + 1]'h) (xs[i]'(by omega)) = false

theorem issortedAdjacent : IssortedAdjacent := by
  intro α lt xs
  induction xs with
  | nil => simp [issorted]
  | cons a xs ih =>
    cases xs with
    | nil => simp [issorted]
    | cons b rest =>
      unfold issorted
      cases hba : lt b a
      · simp only [Bool.false_eq_true, if_false]
        rw [ih]
        constructor
        · intro h i hi
          cases i with
          | zero => simpa using hba
          | succ i =>
            have := h i (by simp at hi ⊢; omega)
            simp only [List.getElem_cons_succ] at this ⊢
            exact this
        · intro h i hi
          have := h (i + 1) (by simp at hi ⊢; omega)
          simp only [List.getElem_cons_succ] at this ⊢
          exact this
      · simp only [if_true]
        constructor
        · intro h; exact absurd h (by decide)
        · intro h
          have := h 0 (by simp)
          simp [hba] at this

end JuliaLean.Sort
