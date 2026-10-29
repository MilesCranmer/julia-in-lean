import JuliaLean.MultidimCov.ArrayV2Copy

/-!
`reverse`, `reverse!`, `reverseind` and `midpoint` on `Vector`
(master `base/array.jl:2253-2333`).
-/

namespace JuliaLean.MultidimCov.ArrayV2

/-- Signed `w`-bit wrapping (`x % T` for a signed `T` of `w` bits). -/
def wrapS (w : Nat) (x : Int) : Int := (x + 2 ^ (w - 1)) % 2 ^ w - 2 ^ (w - 1)

/-- base/array.jl:2288 `midpoint(lo::T, hi::T) = lo +% ((hi -% lo) >>> 0x01)` for a
`w`-bit `T` (`signed` or not): `>>>` shifts the bit pattern as unsigned. -/
def m2288 (signed : Bool) (w : Nat) (lo hi : Int) : Int :=
  if signed then wrapS w (lo + ((wrapS w (hi - lo)) % 2 ^ w) / 2)
  else (lo + ((hi - lo) % 2 ^ w) / 2) % 2 ^ w

/-- base/array.jl:2289 `midpoint(lo::Integer, hi::Integer) = midpoint(promote(lo, hi)...)`:
both values are promoted to the common type (`signed`, `w` bits), in which both fit. -/
def m2289 (signed : Bool) (w : Nat) (lo hi : Int) : Int := m2288 signed w lo hi

theorem emod_self_range {x M : Int} (h0 : 0 ≤ x) (h1 : x < M) : x % M = x := Int.emod_eq_of_lt h0 h1

theorem wrapS_id {w : Nat} {x : Int} (hw : 1 ≤ w) (h0 : -(2 ^ (w - 1)) ≤ x) (h1 : x < 2 ^ (w - 1)) :
    wrapS w x = x := by
  unfold wrapS
  have hp : (2 : Int) ^ w = 2 ^ (w - 1) * 2 := by
    rw [← Int.pow_succ]; congr 1; omega
  rw [hp, Int.emod_eq_of_lt (by omega) (by omega)]; omega

theorem wrapS_emod (w : Nat) (x : Int) : wrapS w x % 2 ^ w = x % 2 ^ w := by
  unfold wrapS
  rw [Int.emod_def (x + 2 ^ (w - 1)) (2 ^ w)]
  rw [show x + 2 ^ (w - 1) - 2 ^ w * ((x + 2 ^ (w - 1)) / 2 ^ w) - 2 ^ (w - 1) =
    x + 2 ^ w * (-((x + 2 ^ (w - 1)) / 2 ^ w)) by rw [Int.mul_neg]; omega]
  exact Int.add_mul_emod_self_left _ _ _

/-- `midpoint(lo, hi)` for `lo ≤ hi` (both representable in the type) is
`fld(lo + hi, 2)` with no intermediate overflow — the use in `reverse!` and
binary searches. -/
def P2288 : Prop := ∀ (signed : Bool) (w : Nat), 1 ≤ w → ∀ lo hi : Int,
    (if signed then -(2 ^ (w - 1)) ≤ lo ∧ hi < 2 ^ (w - 1) else 0 ≤ lo ∧ hi < 2 ^ w) → lo ≤ hi →
    m2288 signed w lo hi = (lo + hi) / 2 ∧ m2289 signed w lo hi = (lo + hi) / 2

theorem p2288 : P2288 := by
  intro signed w hw lo hi hr hle
  have hp : (2 : Int) ^ w = 2 ^ (w - 1) * 2 := by
    rw [← Int.pow_succ]; congr 1; omega
  have hpos : (0 : Int) < 2 ^ (w - 1) := Int.pow_pos (by omega)
  suffices h : m2288 signed w lo hi = (lo + hi) / 2 from ⟨h, h⟩
  unfold m2288
  cases signed
  · simp only [Bool.false_eq_true, if_false] at hr ⊢
    rw [Int.emod_eq_of_lt (a := hi - lo) (by omega) (by omega)]
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  · simp only [if_true] at hr ⊢
    rw [wrapS_emod, Int.emod_eq_of_lt (a := hi - lo) (by omega) (by omega)]
    rw [wrapS_id hw (by omega) (by omega)]
    omega

/-- The swap loop `for i in s:mid; v[i], v[r] = v[r], v[i]; r -= 1; end`
(`@inbounds`; each read throws `UndefRefError` on an unset slot). -/
def swapLoop (v : Arr α) : Nat → Int → Int → R (Arr α)
  | 0, _, _ => .ok v
  | k + 1, i, r => do
    let x ← getU v r
    let y ← getU v i
    let v := setU v i (some x)
    let v := setU v r (some y)
    swapLoop v k (i + 1) (r - 1)

/-- base/array.jl:2317 `reverse!(v::AbstractVector, start, stop=lastindex(v))` for a `Vector`. -/
def m2317 (v : Arr α) (start stop : Int) : R (Arr α) := do
  let s ← toInt start
  let n ← toInt stop
  if n > s then
    if ¬ (1 ≤ s ∧ s ≤ length v) then .error .bounds
    else if ¬ (1 ≤ n ∧ n ≤ length v) then .error .bounds
    else swapLoop v (m2288 true 64 s (n - 1) - s + 1).toNat s n
  else .ok v

/-- `for i = lo:hi; B[i] = A[f(i)]; end` with checked `getindex`/`setindex!`. -/
def copyLoop (a : Arr α) (f : Int → Int) (b : Arr α) : Nat → Int → R (Arr α)
  | 0, _ => .ok b
  | k + 1, i => do
    let x ← getL a (f i)
    let b ← m1036 b x i
    copyLoop a f b k (i + 1)

/-- base/array.jl:2253 `reverse(A::AbstractVector, start, stop=lastindex(A))` for a `Vector`. -/
def m2253 (a : Arr α) (start stop : Int) : R (Arr α) := do
  let s ← toInt start
  let n ← toInt stop
  let b ← m414 a
  let b ← copyLoop a id b (s - 1).toNat 1
  let b ← copyLoop a (fun i => n + s - i) b (n - s + 1).toNat s
  copyLoop a id b (length a - n).toNat (n + 1)

/-- The `dims` keyword of `reverse`/`reverse!`. -/
inductive DimsArg where
  | colon
  | tuple (d : Int)
  | int (d : Int)

/-- base/array.jl:2272 `_reverse(A, ::Colon) = reverse(A, firstindex(A), lastindex(A))`
(and the `reverse!` twin), given the `(A, start, stop)` method `f`. -/
def revColon (f : Arr α → Int → Int → R (Arr α)) (a : Arr α) : R (Arr α) := f a 1 (length a)

/-- base/array.jl:2274 `_reverse(A, dim::Integer)`: `dim == 1 || _throw_argerror(...)`. -/
def revInt (f : Arr α → Int → Int → R (Arr α)) (a : Arr α) (d : Int) : R (Arr α) :=
  if d = 1 then revColon f a else m321 "invalid dimension"

/-- Dispatch of `_reverse`/`_reverse!` on `dims` (base/array.jl:2272-2274); a
`Tuple{Integer}` forwards `first(dim)` to the `Integer` method. -/
def revDims (f : Arr α → Int → Int → R (Arr α)) (a : Arr α) : DimsArg → R (Arr α)
  | .colon => revColon f a
  | .tuple d => revInt f a d
  | .int d => revInt f a d

/-- base/array.jl:2272 `_reverse(A, ::Colon)` / `_reverse!(A, ::Colon)`. -/
def m2272 (f : Arr α → Int → Int → R (Arr α)) (a : Arr α) : R (Arr α) := revDims f a .colon
/-- base/array.jl:2273 `_reverse(A, dim::Tuple{Integer})` and its `reverse!` twin. -/
def m2273 (f : Arr α → Int → Int → R (Arr α)) (a : Arr α) (d : Int) : R (Arr α) := revDims f a (.tuple d)
/-- base/array.jl:2274 `_reverse(A, dim::Integer)` and its `reverse!` twin. -/
def m2274 (f : Arr α → Int → Int → R (Arr α)) (a : Arr α) (d : Int) : R (Arr α) := revDims f a (.int d)
/-- base/array.jl:2271 `reverse(A; dims=:)` / `reverse!(A; dims=:)`. -/
def m2271 (f : Arr α → Int → Int → R (Arr α)) (a : Arr α) (dims : DimsArg) : R (Arr α) := revDims f a dims

/-- base/array.jl:2281 `reverseind(a, i) = first(li) + last(li) - i`. -/
def m2281 (a : Arr α) (i : Int) : Int := wrap64 (wrap64 (1 + length a) - i)

/-! ### Proofs -/

/-- Slot values of the reversal of window `s:e`. -/
def revAt (v : Arr α) (s e k : Int) : Option α := if s ≤ k ∧ k ≤ e then v.at (s + e - k) else v.at k

theorem swapLoop_spec (v0 : Arr α) (s e : Int) :
    ∀ (k : Nat) (v : Arr α) (j : Int), 0 ≤ j → s + j + k ≤ e - j - k + 1 →
      v.dims = v0.dims → v.off = v0.off →
      (∀ t, v.at t = if (s ≤ t ∧ t < s + j) ∨ (e - j < t ∧ t ≤ e) then v0.at (s + e - t) else v0.at t) →
      (∀ t, s ≤ t → t ≤ e → (v0.at t).isSome) →
      ∃ v', swapLoop v k (s + j) (e - j) = .ok v' ∧ v'.dims = v0.dims ∧ v'.off = v0.off ∧
        ∀ t, v'.at t = if (s ≤ t ∧ t < s + j + k) ∨ (e - j - k < t ∧ t ≤ e) then v0.at (s + e - t) else v0.at t
  | 0, v, j, _, _, hd, ho, hv, _ => ⟨v, rfl, hd, ho, fun t => by simpa using hv t⟩
  | k + 1, v, j, hj, hk, hd, ho, hv, ha => by
    have gr : ∃ x, v.at (e - j) = some x ∧ v0.at (e - j) = some x := by
      rw [hv, if_neg (by omega)]
      have := ha (e - j) (by omega) (by omega)
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp this
      exact ⟨x, hx, hx⟩
    have gi : ∃ y, v.at (s + j) = some y ∧ v0.at (s + j) = some y := by
      rw [hv, if_neg (by omega)]
      have := ha (s + j) (by omega) (by omega)
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp this
      exact ⟨y, hy, hy⟩
    obtain ⟨x, hx1, hx2⟩ := gr
    obtain ⟨y, hy1, hy2⟩ := gi
    unfold swapLoop
    simp only [getU, hx1, hy1, bind_ok]
    have := swapLoop_spec v0 s e k (setU (setU v (s + j) (some x)) (e - j) (some y)) (j + 1) (by omega)
      (by omega) (by simp [hd]) (by simp [ho]) (fun t => ?_) ha
    · rw [show s + (j + 1) = s + j + 1 by omega, show e - (j + 1) = e - j - 1 by omega] at this
      obtain ⟨v', e', hd', ho', hp⟩ := this
      refine ⟨v', e', hd', ho', fun t => ?_⟩
      rw [hp t]
      by_cases h1 : (s ≤ t ∧ t < s + j + 1 + k) ∨ (e - j - 1 - k < t ∧ t ≤ e)
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]
    · simp only [setU_at]
      by_cases h1 : t = e - j
      · subst h1; rw [if_pos rfl, if_pos (by omega), show s + e - (e - j) = s + j by omega, hy2]
      · rw [if_neg h1]
        by_cases h2 : t = s + j
        · subst h2; rw [if_pos rfl, if_pos (by omega), show s + e - (s + j) = e - j by omega, hx2]
        · rw [if_neg h2, hv t]
          by_cases h3 : (s ≤ t ∧ t < s + j) ∨ (e - j < t ∧ t ≤ e)
          · rw [if_pos h3, if_pos (by omega)]
          · rw [if_neg h3, if_neg (by omega)]

theorem m2317_spec {v : Arr α} {s e : Int} (h1 : 1 ≤ s) (h2 : s < e) (h3 : e ≤ length v)
    (hl : length v ≤ 2 ^ 60) (ha : ∀ t, s ≤ t → t ≤ e → (v.at t).isSome) :
    ∃ v', m2317 v s e = .ok v' ∧ v'.dims = v.dims ∧ v'.off = v.off ∧ ∀ t, v'.at t = revAt v s e t := by
  unfold m2317
  rw [toInt_ok (by omega) (by omega), bind_ok, toInt_ok (by omega) (by omega), bind_ok,
    if_pos h2, if_neg (by omega), if_neg (by omega)]
  have hm : m2288 true 64 s (e - 1) = (s + (e - 1)) / 2 :=
    (p2288 true 64 (by omega) s (e - 1) (by simp; omega) (by omega)).1
  rw [hm]
  have := swapLoop_spec v s e ((s + (e - 1)) / 2 - s + 1).toNat v 0 (by omega) (by omega) rfl rfl
    (fun t => by rw [if_neg (by omega)]) ha
  simp only [Int.add_zero, Int.sub_zero] at this
  obtain ⟨v', e', hd, ho, hp⟩ := this
  refine ⟨v', e', hd, ho, fun t => ?_⟩
  rw [hp t]; unfold revAt
  by_cases h : s ≤ t ∧ t ≤ e
  · rw [if_pos h]
    by_cases h' : (s ≤ t ∧ t < s + ((s + (e - 1)) / 2 - s + 1).toNat) ∨
        (e - ((s + (e - 1)) / 2 - s + 1).toNat < t ∧ t ≤ e)
    · rw [if_pos h']
    · rw [if_neg h']; congr 1; omega
  · rw [if_neg h, if_neg (by omega)]

theorem contents_revAt {v w : Arr α} {n s e : Int} (hn : length v = n) (hw : length w = n)
    (h1 : 1 ≤ s) (h2 : s ≤ e + 1) (h3 : e ≤ n) (hp : ∀ t, 1 ≤ t → t ≤ n → w.at t = revAt v s e t) :
    contents w = (contents v).take (s - 1).toNat ++
      (((contents v).drop (s - 1).toNat).take (e - s + 1).toNat).reverse ++ (contents v).drop e.toNat := by
  apply List.ext_getElem
  · simp; omega
  · intro j hj1 hj2
    simp only [contents_length] at hj1
    rw [getElem_contents, hp _ (by omega) (by omega)]
    unfold revAt
    simp only [List.getElem_append, List.getElem_take, List.getElem_drop, List.getElem_reverse,
      List.length_take, List.length_drop, List.length_reverse, List.length_append, contents_length,
      getElem_contents]
    repeat' split
    all_goals first | rfl | omega | (congr 1; omega)

/-- `reverse!(v, start, stop)` (docstring `base/array.jl:2292`): an empty or
one-element window leaves `v` unchanged; otherwise both ends must lie in
`1:length(v)` (`BoundsError`), and the window `v[start:stop]` is reversed in place
with every other element unchanged (all window elements assigned). -/
def P2317 : Prop := ∀ {α : Type} (v : Arr α) (n s e : Int), VecOK v n →
    (typeminInt ≤ s → s ≤ typemaxInt → typeminInt ≤ e → e ≤ typemaxInt → e ≤ s → m2317 v s e = .ok v) ∧
    (typeminInt ≤ s → s ≤ typemaxInt → typeminInt ≤ e → e ≤ typemaxInt → s < e →
      (s < 1 ∨ n < s ∨ n < e) → m2317 v s e = .error .bounds) ∧
    (1 ≤ s → s < e → e ≤ n → (∀ t, s ≤ t → t ≤ e → (v.at t).isSome) →
      ∃ v', m2317 v s e = .ok v' ∧ IsVec v' n ∧ contents v' = (contents v).take (s - 1).toNat ++
        (((contents v).drop (s - 1).toNat).take (e - s + 1).toNat).reverse ++ (contents v).drop e.toNat)

theorem p2317 : P2317 := by
  intro α v n s e hv
  obtain ⟨hn, ho, hn0, hw, hs, hvd⟩ := vecOK_unpack hv
  refine ⟨fun a b c d h => ?_, fun a b c d h h' => ?_, fun h1 h2 h3 ha => ?_⟩
  · unfold m2317; rw [toInt_ok' a b, bind_ok, toInt_ok' c d, bind_ok, if_neg (by omega)]
  · unfold m2317; rw [toInt_ok' a b, bind_ok, toInt_ok' c d, bind_ok, if_pos h]
    simp only [hn]
    by_cases hs1 : 1 ≤ s ∧ s ≤ n
    · rw [if_neg (by simpa using hs1), if_pos (by omega)]
    · rw [if_pos hs1]
  · obtain ⟨v', e', hd, ho', hp⟩ := m2317_spec (v := v) h1 h2 (by omega) (by omega) ha
    refine ⟨v', e', hd.trans hvd, ?_⟩
    exact contents_revAt hn (by simp [length, hd, hvd]) h1 (by omega) h3 (fun t _ _ => hp t)

theorem copyLoop_spec (a : Arr α) (f : Int → Int) :
    ∀ (k : Nat) (b : Arr α) (i : Int), 1 ≤ i → i - 1 + k ≤ length b →
      (∀ t, i ≤ t → t < i + k → 1 ≤ f t ∧ f t ≤ length a ∧ (a.at (f t)).isSome) →
      ∃ b', copyLoop a f b k i = .ok b' ∧ b'.dims = b.dims ∧ b'.off = b.off ∧ b'.mem.len = b.mem.len ∧
        ∀ t, b'.at t = if i ≤ t ∧ t < i + k then a.at (f t) else b.at t
  | 0, b, i, _, _, _ => ⟨b, rfl, rfl, rfl, rfl, fun t => by rw [if_neg (by omega)]⟩
  | k + 1, b, i, h1, h2, ha => by
    obtain ⟨r1, r2, r3⟩ := ha i (by omega) (by omega)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp r3
    unfold copyLoop
    rw [getL_def, if_pos (by rw [inBounds_iff]; exact ⟨r1, r2⟩)]
    simp only [hx, bind_ok]
    unfold m1036
    rw [if_neg (by rw [inBounds_iff]; simp; omega), bind_ok]
    obtain ⟨b', e, hd, ho, hm, hp⟩ := copyLoop_spec a f k (setU b i (some x)) (i + 1) (by omega)
      (by rw [length_setU]; omega) (fun t t1 t2 => ha t (by omega) (by omega))
    refine ⟨b', e, hd, ho, hm, fun t => ?_⟩
    rw [hp t, setU_at]
    by_cases h : t = i
    · subst h; rw [if_neg (by omega), if_pos rfl, if_pos (by omega), hx]
    · rw [if_neg h]
      by_cases h' : i + 1 ≤ t ∧ t < i + 1 + k
      · rw [if_pos h', if_pos (by omega)]
      · rw [if_neg h', if_neg (by omega)]

theorem m2253_spec {a : Arr α} {n s e : Int} (hv : VecOK a n) (h1 : 1 ≤ s) (h2 : s ≤ e + 1) (h3 : e ≤ n)
    (ha : ∀ t, 1 ≤ t → t ≤ n → (a.at t).isSome) :
    ∃ b, m2253 a s e = .ok b ∧ IsVec b n ∧ Valid b ∧ ∀ t, 1 ≤ t → t ≤ n → b.at t = revAt a s e t := by
  obtain ⟨hn, ho, hn0, hw, hs, hvd⟩ := vecOK_unpack hv
  unfold m2253
  rw [toInt_ok (by omega) (by omega), bind_ok, toInt_ok (by omega) (by omega), bind_ok]
  obtain ⟨b0, e0, hb0, hvb0, _⟩ := (p414 (β := α) a []).1 n hvd hn0 (by unfold typemaxInt; omega) |>.1
  rw [e0, bind_ok]
  have hl0 : length b0 = n := by simp [length, hb0]
  obtain ⟨b1, e1, hd1, ho1, hm1, hp1⟩ := copyLoop_spec a id (s - 1).toNat b0 1 (by omega) (by omega)
    (fun t t1 t2 => ⟨by simp only [id]; omega, by simp only [id]; omega, ha t (by omega) (by omega)⟩)
  rw [e1, bind_ok]
  have hl1 : length b1 = n := by simp [length, hd1, hb0]
  obtain ⟨b2, e2, hd2, ho2, hm2, hp2⟩ := copyLoop_spec a (fun i => e + s - i) (e - s + 1).toNat b1 s h1
    (by omega) (fun t t1 t2 => ⟨by omega, by omega, ha _ (by omega) (by omega)⟩)
  rw [e2, bind_ok]
  have hl2 : length b2 = n := by simp [length, hd2, hd1, hb0]
  obtain ⟨b3, e3, hd3, ho3, hm3, hp3⟩ := copyLoop_spec a id (length a - e).toNat b2 (e + 1) (by omega)
    (by omega) (fun t t1 t2 => ⟨by simp only [id]; omega, by simp only [id]; omega, ha t (by omega) (by omega)⟩)
  have hl3 : length b3 = n := by simp [length, hd3, hd2, hd1, hb0]
  obtain ⟨vb1, vb2, vb3⟩ := hvb0
  refine ⟨b3, e3, show b3.dims = [n] by rw [hd3, hd2, hd1, hb0], ⟨by rw [ho3, ho2, ho1]; exact vb1, by omega,
    by rw [ho3, ho2, ho1, hm3, hm2, hm1, hl3]; omega⟩, fun t t1 t2 => ?_⟩
  rw [hp3, hp2, hp1]
  unfold revAt
  simp only [id]
  repeat' split
  all_goals first | rfl | omega | (congr 1; omega)

/-- `reverse(v, start, stop)` (docstring `base/array.jl:2235`): for `1 ≤ start`,
`stop ≤ length(v)` and `start ≤ stop + 1` (all elements assigned), a new vector
equal to `v` with `v[start:stop]` reversed; an empty window gives a copy. -/
def P2253 : Prop := ∀ {α : Type} (v : Arr α) (n s e : Int), VecOK v n →
    (∀ t, 1 ≤ t → t ≤ n → (v.at t).isSome) → 1 ≤ s → s ≤ e + 1 → e ≤ n →
    ∃ b, m2253 v s e = .ok b ∧ IsVec b n ∧ Valid b ∧ contents b = (contents v).take (s - 1).toNat ++
      (((contents v).drop (s - 1).toNat).take (e - s + 1).toNat).reverse ++ (contents v).drop e.toNat

theorem p2253 : P2253 := by
  intro α v n s e hv ha h1 h2 h3
  obtain ⟨b, eb, hb, hvb, hp⟩ := m2253_spec hv h1 h2 h3 ha
  exact ⟨b, eb, hb, hvb, contents_revAt (vecOK_unpack hv).1 (length_vec b n hb) h1 h2 h3 hp⟩

theorem full_reverse {l : List α} : l.take ((1 : Int) - 1).toNat ++
    ((l.drop ((1 : Int) - 1).toNat).take ((l.length : Int) - 1 + 1).toNat).reverse ++
      l.drop (l.length : Int).toNat = l.reverse := by
  simp

/-- `reverse(v; dims)` and `reverse!(v; dims)` on a `Vector` (docstrings
`base/array.jl:2214`, `2292`): `dims` may be `:`, `1` or `(1,)`, each reversing the
whole vector (all elements assigned); any other dimension is an `ArgumentError`. -/
def P2271 : Prop := ∀ {α : Type} (v : Arr α) (n : Int), VecOK v n → (∀ t, 1 ≤ t → t ≤ n → (v.at t).isSome) →
    (∀ dims, (dims = DimsArg.colon ∨ dims = .int 1 ∨ dims = .tuple 1) →
      (∃ b, m2271 m2253 v dims = .ok b ∧ IsVec b n ∧ contents b = (contents v).reverse) ∧
      (∃ b, m2271 m2317 v dims = .ok b ∧ IsVec b n ∧ contents b = (contents v).reverse)) ∧
    (∀ d, d ≠ 1 → m2271 m2253 v (.int d) = .error .argument ∧ m2271 m2253 v (.tuple d) = .error .argument ∧
      m2271 m2317 v (.int d) = .error .argument ∧ m2271 m2317 v (.tuple d) = .error .argument) ∧
    (∃ b, m2272 m2253 v = .ok b ∧ contents b = (contents v).reverse) ∧
    (∀ d, m2273 m2253 v d = m2274 m2253 v d ∧ m2273 m2317 v d = m2274 m2317 v d)

theorem colon_reverse {v : Arr α} {n : Int} (hv : VecOK v n) (ha : ∀ t, 1 ≤ t → t ≤ n → (v.at t).isSome) :
    (∃ b, revColon m2253 v = .ok b ∧ IsVec b n ∧ contents b = (contents v).reverse) ∧
    (∃ b, revColon m2317 v = .ok b ∧ IsVec b n ∧ contents b = (contents v).reverse) := by
  obtain ⟨hn, ho, hn0, hw, hs, hvd⟩ := vecOK_unpack hv
  have hl : ((contents v).length : Int) = n := by simp; omega
  unfold revColon
  rw [hn]
  refine ⟨?_, ?_⟩
  · obtain ⟨b, eb, hb, _, hc⟩ := p2253 v n 1 n hv ha (by omega) (by omega) (by omega)
    refine ⟨b, eb, hb, ?_⟩
    rw [hc, ← hl]; exact full_reverse
  · by_cases h : 1 < n
    · obtain ⟨_, _, h3⟩ := p2317 v n 1 n hv
      obtain ⟨b, eb, hb, hc⟩ := h3 (by omega) h (by omega) (fun t t1 t2 => ha t t1 t2)
      refine ⟨b, eb, hb, ?_⟩
      rw [hc, ← hl]; exact full_reverse
    · obtain ⟨h1, _, _⟩ := p2317 v n 1 n hv
      refine ⟨v, h1 (by unfold typeminInt; omega) (by unfold typemaxInt; omega)
        (by unfold typeminInt; omega) (by unfold typemaxInt; omega) (by omega), hvd, ?_⟩
      have hle : (contents v).length ≤ 1 := by simp; omega
      match hcv : contents v, hle with
      | [], _ => rfl
      | [_], _ => rfl

theorem p2271 : P2271 := by
  intro α v n hv ha
  obtain ⟨c1, c2⟩ := colon_reverse hv ha
  refine ⟨fun dims hd => ?_, fun d hd => ?_, ?_, fun d => ⟨rfl, rfl⟩⟩
  · rcases hd with rfl | rfl | rfl <;> exact ⟨c1, c2⟩
  · simp [m2271, revDims, revInt, hd, m321]
  · obtain ⟨b, e, _, c⟩ := c1; exact ⟨b, e, c⟩

/-- `reverseind(v, i)` (docstring `base/array.jl:2276`): for `i ∈ 1:n` it is
`n + 1 - i`, again in `1:n`, an involution, and `v[reverseind(v, i)] == reverse(v)[i]`. -/
def P2281 : Prop := ∀ {α : Type} (v : Arr α) (n i : Int), VecOK v n → 1 ≤ i → i ≤ n →
    m2281 v i = n + 1 - i ∧ 1 ≤ m2281 v i ∧ m2281 v i ≤ n ∧ m2281 v (m2281 v i) = i ∧
    (contents v)[(m2281 v i - 1).toNat]? = (contents v).reverse[(i - 1).toNat]?

theorem p2281 : P2281 := by
  intro α v n i hv h1 h2
  obtain ⟨hn, ho, hn0, hw, hs, hvd⟩ := vecOK_unpack hv
  have hr : ∀ j, 1 ≤ j → j ≤ n → m2281 v j = n + 1 - j := by
    intro j j1 j2
    unfold m2281; rw [hn, wrap64_id (x := 1 + n) (by omega) (by omega), wrap64_id (by omega) (by omega)]; omega
  rw [hr i h1 h2, hr (n + 1 - i) (by omega) (by omega)]
  refine ⟨rfl, by omega, by omega, by omega, ?_⟩
  rw [List.getElem?_reverse (by simp; omega)]
  congr 1; simp; omega

end JuliaLean.MultidimCov.ArrayV2
