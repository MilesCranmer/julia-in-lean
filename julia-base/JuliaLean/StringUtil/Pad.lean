import JuliaLean.StringUtil.Strip
import JuliaLean.StringUtil.Width

/-!
# `lpad` and `rpad` on `String`

`base/strings/util.jl:511-584` (master `bbfa0ce4150`) for `s::String`, `n::Int` and a pad
`p::String`, with `textwidth` from `JuliaLean/StringUtil/Width.lean` (the utf8proc width table
is the parameter `cw`).
-/

namespace JuliaLean.StringUtil.Pad

open JuliaLean JuliaLean.Strings JuliaLean.StringUtil.Strip

/-! ## Models -/

/-- The loop of `_pad_remainder(p::AbstractString, r::Int)`, `base/strings/util.jl:516-523`:
`width = 0; for (i, c) in pairs(p); width += Int(textwidth(c))::Int; width >= r && return
@view p[begin:i]; end; return SubString(p)`, with `next = iterate(p, ·)` (the key of
`pairs(p)` is the iteration state, `base/iterators.jl:1725`). `@view p[begin:i]` is the
checked `SubString(p, 1, i)` (`base/strings/substring.jl:122`). The first argument bounds the
remaining iterations as in `Strip.lstripStrLoop`. -/
def padRemLoop (cw : UInt32 → Int) (p : JStr) (next : JInt64 → Option (UInt32 × JInt64))
    (r : JInt64) : Nat → JInt64 → JInt64 → SJl JSub
  | 0, _, _ => .ok (wholeSub p)
  | k + 1, i, width =>
    match next i with
    | none => .ok (wholeSub p)
    | some (c, i') =>
      let width := width + ix (textwidthChar cw c)
      if width.val ≥ r.val then substring p (ix 1) i else padRemLoop cw p next r k i' width

/-- `_pad_remainder(p::AbstractString, r::Int)`, `base/strings/util.jl:516-523`. -/
def padRemainder (cw : UInt32 → Int) (p : JStr) (r : JInt64) : SJl JSub :=
  padRemLoop cw p (iterate p) r (p.bytes.length + 1) (ix 1) (ix 0)

/-- `string(a...)` for `String`/`SubString{String}` pieces, `base/strings/substring.jl:254-283`:
`_string_n(n)` for the summed code units, then each piece's bytes in order. -/
def stringConcat (pieces : List (List UInt8)) : SJl JStr :=
  stringN (pieces.map List.length).sum fun _ => pieces.flatten

/-- `lpad(s::String, n::Int, p::String)`, `base/strings/util.jl:526-544`:
`m = signed(n) - Int(textwidth(s))` (wrapping), `m ≤ 0 && return string(s)`,
`l = textwidth(p)`, `ArgumentError` if `l == 0`, `q, r = divrem(m, l)` (`div`, `rem`,
`base/div.jl:273-279`), then `string(p^q, s)` or `string(p^q, _pad_remainder(p, r), s)`.
`p^q` is `repeat(p, q)` (`base/strings/basic.jl:771`). -/
def lpadStr (cw : UInt32 → Int) (s : JStr) (n : JInt64) (p : JStr) : SJl JStr :=
  let m := n - ix (textwidth cw s)
  if m.val ≤ 0 then .ok s
  else
    let l := ix (textwidth cw p)
    if l.val = 0 then .error (.jl (.argumentError "pad has zero textwidth"))
    else
      match JInt.div m l, JInt.remInt m l with
      | .ok q, .ok r =>
        match repeatStr p q with
        | .error e => .error e
        | .ok pq =>
          if r.val = 0 then stringConcat [pq.bytes, s.bytes]
          else
            match padRemainder cw p r with
            | .error e => .error e
            | .ok rem => stringConcat [pq.bytes, rem.view.bytes, s.bytes]
      | _, _ => .error (.jl .divideError)

/-- `rpad(s::String, n::Int, p::String)`, `base/strings/util.jl:566-584`: as `lpadStr`, with
`string(s, p^q)` or `string(s, p^q, _pad_remainder(p, r))`. -/
def rpadStr (cw : UInt32 → Int) (s : JStr) (n : JInt64) (p : JStr) : SJl JStr :=
  let m := n - ix (textwidth cw s)
  if m.val ≤ 0 then .ok s
  else
    let l := ix (textwidth cw p)
    if l.val = 0 then .error (.jl (.argumentError "pad has zero textwidth"))
    else
      match JInt.div m l, JInt.remInt m l with
      | .ok q, .ok r =>
        match repeatStr p q with
        | .error e => .error e
        | .ok pq =>
          if r.val = 0 then stringConcat [s.bytes, pq.bytes]
          else
            match padRemainder cw p r with
            | .error e => .error e
            | .ok rem => stringConcat [s.bytes, pq.bytes, rem.view.bytes]
      | _, _ => .error (.jl .divideError)

/-! ## Widths -/

/-- The summed width of a list of characters. -/
def wsum (cw : UInt32 → Int) (cs : List UInt32) : Int :=
  cs.foldl (fun acc c => acc + textwidthChar cw c) 0

theorem textwidth_eq (cw : UInt32 → Int) (s : JStr) : textwidth cw s = wsum cw (chars s) := rfl

theorem foldl_add (g : UInt32 → Int) : ∀ (cs : List UInt32) (a : Int),
    cs.foldl (fun acc c => acc + g c) a = a + cs.foldl (fun acc c => acc + g c) 0
  | [], a => by simp
  | c :: cs, a => by
    simp only [List.foldl_cons]
    rw [foldl_add g cs (a + g c), foldl_add g cs (0 + g c)]
    omega

theorem wsum_append (cw : UInt32 → Int) (xs ys : List UInt32) :
    wsum cw (xs ++ ys) = wsum cw xs + wsum cw ys := by
  unfold wsum
  rw [List.foldl_append, foldl_add _ ys]

theorem wsum_cons (cw : UInt32 → Int) (c : UInt32) (cs : List UInt32) :
    wsum cw (c :: cs) = textwidthChar cw c + wsum cw cs := by
  unfold wsum
  rw [List.foldl_cons, foldl_add _ cs]
  omega

theorem wsum_single (cw : UInt32 → Int) (c : UInt32) : wsum cw [c] = textwidthChar cw c := by
  rw [wsum_cons]; simp [wsum]

theorem twc_bounds (cw : UInt32 → Int) (hcw : ∀ u, 0 ≤ cw u ∧ cw u ≤ 2) (c : UInt32) :
    0 ≤ textwidthChar cw c ∧ textwidthChar cw c ≤ 2 := by
  unfold textwidthChar
  dsimp only
  repeat' split
  all_goals first | omega | exact hcw _

theorem wsum_bounds (cw : UInt32 → Int) (hcw : ∀ u, 0 ≤ cw u ∧ cw u ≤ 2) :
    ∀ cs : List UInt32, 0 ≤ wsum cw cs ∧ wsum cw cs ≤ 2 * cs.length
  | [] => by simp [wsum]
  | c :: cs => by
    rw [wsum_cons]
    have := twc_bounds cw hcw c
    have := wsum_bounds cw hcw cs
    simp only [List.length_cons]
    omega

theorem chars_length (s : JStr) : (chars s).length ≤ s.bytes.length := by
  have hseg := trace_seg_end (collect_trace s) (ve_one s)
  have hl := (seg_ve hseg (ve_one s)).2.1
  rw [ix1, ncu1_val] at hl
  unfold chars
  rw [List.length_map]
  omega

theorem tw_bounds (cw : UInt32 → Int) (hcw : ∀ u, 0 ≤ cw u ∧ cw u ≤ 2) (s : JStr) :
    0 ≤ textwidth cw s ∧ textwidth cw s ≤ 2 * s.bytes.length := by
  rw [textwidth_eq]
  have h1 := wsum_bounds cw hcw (chars s)
  have h2 := chars_length s
  omega

/-! ## `_pad_remainder` -/

theorem seg_snoc {s : JStr} {b b' : JInt64} {c : UInt32} (hit : iterate s b = some (c, b')) :
    ∀ {a : JInt64} {A : List (UInt32 × JInt64)}, Seg s b a A → Seg s b' a (A ++ [(c, b)]) := by
  intro a A h
  induction h with
  | nil => exact .cons hit .nil
  | cons hit' _ ih => exact .cons hit' ih

theorem padRemLoop_spec (cw : UInt32 → Int) (hcw : ∀ u, 0 ≤ cw u ∧ cw u ≤ 2) (p : JStr)
    (next : JInt64 → Option (UInt32 × JInt64)) (hnext : ∀ i, next i = iterate p i) (r : JInt64)
    (hrl : r.val ≤ wsum cw ((collectPairs p).map (·.1))) :
    ∀ (k : Nat) (i w : JInt64) (pre post : List (UInt32 × JInt64)),
      Seg p i (ix 1) pre → Seg p (ncodeunits p + ix 1) i post → VE p i →
      collectPairs p = pre ++ post → w.val = wsum cw (pre.map (·.1)) →
      wsum cw (pre.map (·.1)) < r.val → post.length < k →
      ∃ pre' c j rest i', padRemLoop cw p next r k i w = .ok ⟨p, ix 1 - ix 1, i' - ix 1⟩ ∧
        collectPairs p = pre' ++ [(c, j)] ++ rest ∧ Seg p i' (ix 1) (pre' ++ [(c, j)]) ∧
        wsum cw (pre'.map (·.1)) < r.val ∧ r.val ≤ wsum cw (pre'.map (·.1)) + textwidthChar cw c := by
  have hs := ncu_small p
  have e1 := ix1
  have hcl := chars_length p
  intro k
  induction k with
  | zero => intro i w pre post _ _ _ _ _ _ hk; exact absurd hk (Nat.not_lt_zero _)
  | succ k ih =>
    intro i w pre post hpre hpost hv hcp hw hlt hk
    cases post with
    | nil =>
      rw [List.append_nil] at hcp
      rw [← hcp] at hlt
      exact absurd hrl (Int.not_le.mpr hlt)
    | cons x rest =>
      obtain ⟨hx, i', hit, hseg'⟩ := seg_cons_inv hpost
      obtain ⟨c, i0⟩ := x
      simp only at hx hit
      subst hx
      obtain ⟨hvi, hnv, hve'⟩ := iter_step hv hit
      have hn : next i0 = some (c, i') := by rw [hnext]; exact hit
      have htc := twc_bounds cw hcw c
      obtain ⟨t, ht⟩ : ∃ t, textwidthChar cw c = t := ⟨_, rfl⟩
      rw [ht] at htc
      have hpl : (pre.map (·.1)).length + 1 ≤ p.bytes.length := by
        have h1 : (pre.map (·.1)).length + 1 ≤ (chars p).length := by
          unfold chars; rw [hcp]
          simp only [List.map_append, List.map_cons, List.length_append, List.length_cons,
            List.length_map]
          omega
        exact Nat.le_trans h1 hcl
      have hwb := wsum_bounds cw hcw (pre.map (·.1))
      have htw : (ix t).val = t := ix_val _ (by omega) (by omega)
      have hw' : (w + ix t).val = wsum cw (pre.map (·.1)) + t := by
        rw [add_val _ _ (by omega) (by omega), htw, hw]
      have hseg2 : Seg p i' (ix 1) (pre ++ [(c, i0)]) := seg_snoc hit hpre
      have hcp2 : collectPairs p = pre ++ [(c, i0)] ++ rest := by simp [hcp]
      by_cases hge : (w + ix t).val ≥ r.val
      · have hv1 : validZ p (ix 1).val := by rw [e1]; exact valid_one p (by have := hvi.2.1; have := hvi.1; omega)
        have hsub := substring_ok p (ix 1) i0 i' true hv1 hvi (by rw [e1]; exact hvi.1)
          (nextind_to p i0 i' hvi hnv)
        refine ⟨pre, c, i0, rest, i', ?_, hcp2, hseg2, hlt, by rw [ht]; omega⟩
        simp only [padRemLoop, hn, ht, hge, ↓reduceIte]
        exact hsub
      · have hw2 : (w + ix t).val = wsum cw ((pre ++ [(c, i0)]).map (·.1)) := by
          rw [hw', List.map_append, wsum_append]
          simp only [List.map_cons, List.map_nil, wsum_single]
          rw [ht]
        obtain ⟨pre', c', j, rest', i'', h1, h2, h3, h4, h5⟩ :=
          ih i' _ (pre ++ [(c, i0)]) rest hseg2 hseg' hve' (by simp [hcp]) hw2 (by rw [← hw2]; omega)
            (by simp only [List.length_cons] at hk; omega)
        refine ⟨pre', c', j, rest', i'', ?_, h2, h3, h4, h5⟩
        simp only [padRemLoop, hn, ht, hge, ↓reduceIte]
        exact h1

theorem padRemainder_eq (cw : UInt32 → Int) (p : JStr) (r : JInt64) :
    padRemainder cw p r = padRemLoop cw p (iterate p) r (p.bytes.length + 1) (ix 1) (ix 0) := rfl

/-- `_pad_remainder(p, r)` for `0 < r < textwidth(p)` returns the shortest prefix of `p` (in
characters) whose width reaches `r`. -/
theorem padRemainder_spec (cw : UInt32 → Int) (hcw : ∀ u, 0 ≤ cw u ∧ cw u ≤ 2) (p : JStr)
    (r : JInt64) (hr0 : 0 < r.val) (hrl : r.val < textwidth cw p) :
    ∃ rem cs, padRemainder cw p r = .ok rem ∧ rem.str = p ∧ rem.offset.val = 0 ∧
      subChars rem = .ok cs ∧ cs <+: chars p ∧ r.val ≤ wsum cw cs ∧
      ∀ cs' c, cs = cs' ++ [c] → wsum cw cs' < r.val := by
  have e1 := ix1
  have hs := ncu_small p
  have tr := collect_trace p
  have hseg := trace_seg_end tr (ve_one p)
  have hl := (seg_ve hseg (ve_one p)).2.1
  rw [textwidth_eq] at hrl
  obtain ⟨pre', c, j, rest, i', hloop, hcp, hsg, h1, h2⟩ :=
    padRemLoop_spec cw hcw p (iterate p) (fun _ => rfl) r (by unfold chars at hrl; exact Int.le_of_lt hrl)
      (p.bytes.length + 1) (ix 1) (ix 0) [] (collectPairs p) .nil hseg (ve_one p) (List.nil_append _).symm
      (by rw [ix0]; simp [wsum]) (by simp only [List.map_nil, wsum, List.foldl_nil]; exact hr0)
      (by rw [ix1, ncu1_val] at hl; omega)
  have hl2 := (seg_ve hsg (ve_one p)).2.1
  simp only [List.length_append, List.length_singleton] at hl2
  have hvi' := (seg_ve hsg (ve_one p)).1
  have ei : (i' - ix 1).val = i'.val - 1 := by
    have := hvi'.1; have := hvi'.2.1
    rw [sub_val _ _ (by omega) (by omega)]; omega
  have eo : (ix 1 - ix 1).val = 0 := rfl
  refine ⟨⟨p, ix 1 - ix 1, i' - ix 1⟩, (pre' ++ [(c, j)]).map (·.1), by rw [padRemainder_eq]; exact hloop,
    rfl, eo, ?_, ?_, ?_, ?_⟩
  · exact subChars_seg p _ _ i' (ix 1) _ hsg (ve_one p) (by omega) (by omega) (by omega) (by omega)
  · refine ⟨rest.map (·.1), ?_⟩
    unfold chars
    rw [hcp]
    exact (List.map_append ..).symm
  · rw [List.map_append, wsum_append]; simp only [List.map_cons, List.map_nil, wsum_single]
    exact h2
  · intro cs' c' hc
    rw [List.map_append] at hc
    have := (List.append_inj' hc (by simp)).1
    rw [← this]
    exact h1

/-! ## `divrem`, `repeat` and `string` -/

theorem jint64_bounds (x : JInt64) : -(2 ^ 63) ≤ x.val ∧ x.val ≤ 2 ^ 63 - 1 := by
  have h := x.property
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at h
  omega

theorem divrem_vals (M L q r : JInt64) (hM : 0 < M.val) (hL : 0 < L.val)
    (hq : JInt.div M L = .ok q) (hr : JInt.remInt M L = .ok r) :
    q.val = M.val / L.val ∧ r.val = M.val % L.val := by
  have h0 : ¬ L.val = 0 := by omega
  have h1 : ¬ (IntTy.signed .i64 = true ∧ M.val = IntTy.min .i64 ∧ L.val = -1) :=
    fun ⟨_, _, h⟩ => by omega
  unfold JInt.div at hq
  unfold JInt.remInt at hr
  rw [if_neg h0, if_neg h1] at hq
  rw [if_neg h0] at hr
  cases hq
  cases hr
  have hd0 := Int.ediv_nonneg (show 0 ≤ M.val by omega) (show 0 ≤ L.val by omega)
  have hd1 := Int.ediv_le_self L.val (show 0 ≤ M.val by omega)
  have hm0 := Int.emod_nonneg M.val (show L.val ≠ 0 by omega)
  have hm1 := Int.emod_lt_of_pos M.val hL
  have hMb := (jint64_bounds M).2
  have hLb := (jint64_bounds L).2
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega), Int.tmod_eq_emod_of_nonneg (by omega)]
  exact ⟨wrap64_val _ (by omega) (by omega), wrap64_val _ (by omega) (by omega)⟩

theorem repeat_bytes (p : JStr) (q : JInt64) (pq : JStr) (h : repeatStr p q = .ok pq) :
    pq.bytes = (List.replicate q.val.toNat p.bytes).flatten := by
  unfold repeatStr at h
  by_cases hr : q.val < 0
  · rw [if_pos hr] at h; cases h
  rw [if_neg hr] at h
  have hu := u64_val q (by omega)
  simp only [] at h
  split at h
  · rename_i h0; cases h; rw [hu] at h0; simp [JStr.empty, h0]
  split at h
  · rename_i h1; cases h; rw [hu] at h1; simp [h1]
  split at h
  · rename_i hn; cases h; simp [JStr.empty, List.eq_nil_of_length_eq_zero hn]
  split at h
  · cases h
  rw [stringN_ok h, hu]

theorem concat_bytes {pieces : List (List UInt8)} {out : JStr} (h : stringConcat pieces = .ok out) :
    out.bytes = pieces.flatten :=
  stringN_ok h

/-! ## Properties -/

/-- The pad pieces: `p^q` and the remainder SubString `rem` of `p` (whose characters are `cs`)
cover exactly the missing width `n - textwidth(s)`, with no whole copy of `p` too many, and
dropping the last character of `rem` would leave the result short (widths measured piece by
piece). -/
def PadPieces (cw : UInt32 → Int) (s p : JStr) (n : JInt64) (q : Nat) (rem : JSub)
    (cs : List UInt32) : Prop :=
  rem.str = p ∧ rem.offset.val = 0 ∧ subChars rem = .ok cs ∧ cs <+: chars p ∧
    q * textwidth cw p ≤ n.val - textwidth cw s ∧
    n.val - textwidth cw s ≤ q * textwidth cw p + wsum cw cs ∧
    ∀ cs' c, cs = cs' ++ [c] → q * textwidth cw p + wsum cw cs' < n.val - textwidth cw s

/-- For widths `0 ≤ cw ≤ 2`, a pad of positive width and `n - textwidth(s)` not wrapping,
`lpad(s, n, p)` returns `s` when `n ≤ textwidth(s)`, and otherwise the bytes of
`p^q * rem * s` for pieces as in `PadPieces`. -/
def LpadPieces : Prop :=
  ∀ (cw : UInt32 → Int), (∀ u, 0 ≤ cw u ∧ cw u ≤ 2) →
  ∀ (s p : JStr) (n : JInt64) (out : JStr), 0 < textwidth cw p →
    -(2 ^ 63) ≤ n.val - textwidth cw s → lpadStr cw s n p = .ok out →
    (n.val ≤ textwidth cw s ∧ out = s) ∨
    ∃ q rem cs, out.bytes = (List.replicate q p.bytes).flatten ++ rem.view.bytes ++ s.bytes ∧
      PadPieces cw s p n q rem cs

/-- As `LpadPieces` for `rpad(s, n, p)`, whose bytes are `s * p^q * rem`. -/
def RpadPieces : Prop :=
  ∀ (cw : UInt32 → Int), (∀ u, 0 ≤ cw u ∧ cw u ≤ 2) →
  ∀ (s p : JStr) (n : JInt64) (out : JStr), 0 < textwidth cw p →
    -(2 ^ 63) ≤ n.val - textwidth cw s → rpadStr cw s n p = .ok out →
    (n.val ≤ textwidth cw s ∧ out = s) ∨
    ∃ q rem cs, out.bytes = s.bytes ++ (List.replicate q p.bytes).flatten ++ rem.view.bytes ∧
      PadPieces cw s p n q rem cs

/-- The shared arithmetic: `q, r = divrem(m, l)` with `m = n - textwidth(s) > 0` and
`l = textwidth(p) > 0`. -/
theorem pieces_of (cw : UInt32 → Int) (hcw : ∀ u, 0 ≤ cw u ∧ cw u ≤ 2) (s p : JStr) (n q r : JInt64)
    (hm : 0 < n.val - textwidth cw s) (hl : 0 < textwidth cw p)
    (hqv : q.val = (n.val - textwidth cw s) / textwidth cw p)
    (hrv : r.val = (n.val - textwidth cw s) % textwidth cw p) :
    (r.val = 0 → PadPieces cw s p n q.val.toNat ⟨p, ix 0, ix 0⟩ []) ∧
    (r.val ≠ 0 → ∃ rem cs, padRemainder cw p r = .ok rem ∧ PadPieces cw s p n q.val.toNat rem cs) := by
  unfold PadPieces
  generalize textwidth cw s = A at hm hqv hrv ⊢
  obtain ⟨B, hB⟩ : ∃ B, textwidth cw p = B := ⟨_, rfl⟩
  rw [hB] at hl hqv hrv ⊢
  have he := Int.mul_ediv_add_emod (n.val - A) B
  have hm0 := Int.emod_nonneg (n.val - A) (Int.ne_of_gt hl)
  have hm1 := Int.emod_lt_of_pos (n.val - A) hl
  have hq0 := Int.ediv_nonneg (Int.le_of_lt hm) (Int.le_of_lt hl)
  rw [← hqv, ← hrv] at he
  rw [← hrv] at hm0 hm1
  rw [← hqv] at hq0
  have hqn : ((q.val.toNat : Nat) : Int) = q.val := Int.toNat_of_nonneg hq0
  rw [Int.mul_comm] at he
  rw [hqn]
  generalize q.val * B = P at he ⊢
  constructor
  · intro hr0
    refine ⟨rfl, rfl, subChars_empty p _ _ rfl rfl, ⟨chars p, List.nil_append _⟩, by omega, ?_, ?_⟩
    · simp only [wsum, List.foldl_nil]; omega
    · intro cs' c h; simp at h
  · intro hr0
    obtain ⟨rem, cs, hrem, hstr, hoff, hch, hpre, hw, hmin⟩ :=
      padRemainder_spec cw hcw p r (by omega) (by rw [hB]; omega)
    refine ⟨rem, cs, hrem, hstr, hoff, hch, hpre, by omega, by omega, ?_⟩
    intro cs' c h
    have := hmin cs' c h
    omega

theorem view_empty (p : JStr) : (JSub.view ⟨p, ix 0, ix 0⟩).bytes = [] := rfl

/-- The steps shared by `lpad` and `rpad` up to the pad pieces. -/
theorem pad_common (cw : UInt32 → Int) (hcw : ∀ u, 0 ≤ cw u ∧ cw u ≤ 2) (s p : JStr) (n : JInt64)
    (hp : 0 < textwidth cw p) (hn : -(2 ^ 63) ≤ n.val - textwidth cw s) :
    (n - ix (textwidth cw s)).val = n.val - textwidth cw s ∧ (ix (textwidth cw p)).val = textwidth cw p := by
  have hts := tw_bounds cw hcw s
  have htp := tw_bounds cw hcw p
  have hs := ncu_small s
  have hps := ncu_small p
  have hnb := (jint64_bounds n).2
  generalize textwidth cw s = A at hts hn ⊢
  generalize textwidth cw p = B at htp hp ⊢
  have hix : (ix A).val = A := ix_val _ (by omega) (by omega)
  refine ⟨?_, ix_val _ (by omega) (by omega)⟩
  rw [sub_val _ _ (by rw [hix]; omega) (by rw [hix]; omega), hix]

theorem lpadPieces_proven : LpadPieces := by
  intro cw hcw s p n out hp hn h
  obtain ⟨hM, hL⟩ := pad_common cw hcw s p n hp hn
  unfold lpadStr at h
  generalize hMd : n - ix (textwidth cw s) = M at h hM
  generalize hLd : ix (textwidth cw p) = L at h hL
  simp only [] at h
  by_cases hle : M.val ≤ 0
  · rw [if_pos hle] at h
    cases h
    exact Or.inl ⟨by rw [hM] at hle; exact Int.le_of_sub_nonpos hle, rfl⟩
  rw [if_neg hle] at h
  have hl0 : ¬ L.val = 0 := by rw [hL]; exact Int.ne_of_gt hp
  rw [if_neg hl0] at h
  split at h
  next q r hq hr =>
    obtain ⟨hqv, hrv⟩ := divrem_vals M L q r (Int.not_le.mp hle) (by rw [hL]; exact hp) hq hr
    rw [hM, hL] at hqv hrv
    have hpc := pieces_of cw hcw s p n q r (by rw [← hM]; exact Int.not_le.mp hle) hp hqv hrv
    split at h
    next e _ => cases h
    next pq hpq =>
      have hpqb := repeat_bytes p q pq hpq
      right
      by_cases hr0 : r.val = 0
      · rw [if_pos hr0] at h
        refine ⟨q.val.toNat, ⟨p, ix 0, ix 0⟩, [], ?_, hpc.1 hr0⟩
        rw [concat_bytes h, view_empty, hpqb]
        simp
      · rw [if_neg hr0] at h
        obtain ⟨rem, cs, hrem, hpp⟩ := hpc.2 hr0
        rw [hrem] at h
        simp only [] at h
        refine ⟨q.val.toNat, rem, cs, ?_, hpp⟩
        rw [concat_bytes h, hpqb]
        simp
  next => cases h

theorem rpadPieces_proven : RpadPieces := by
  intro cw hcw s p n out hp hn h
  obtain ⟨hM, hL⟩ := pad_common cw hcw s p n hp hn
  unfold rpadStr at h
  generalize hMd : n - ix (textwidth cw s) = M at h hM
  generalize hLd : ix (textwidth cw p) = L at h hL
  simp only [] at h
  by_cases hle : M.val ≤ 0
  · rw [if_pos hle] at h
    cases h
    exact Or.inl ⟨by rw [hM] at hle; exact Int.le_of_sub_nonpos hle, rfl⟩
  rw [if_neg hle] at h
  have hl0 : ¬ L.val = 0 := by rw [hL]; exact Int.ne_of_gt hp
  rw [if_neg hl0] at h
  split at h
  next q r hq hr =>
    obtain ⟨hqv, hrv⟩ := divrem_vals M L q r (Int.not_le.mp hle) (by rw [hL]; exact hp) hq hr
    rw [hM, hL] at hqv hrv
    have hpc := pieces_of cw hcw s p n q r (by rw [← hM]; exact Int.not_le.mp hle) hp hqv hrv
    split at h
    next e _ => cases h
    next pq hpq =>
      have hpqb := repeat_bytes p q pq hpq
      right
      by_cases hr0 : r.val = 0
      · rw [if_pos hr0] at h
        refine ⟨q.val.toNat, ⟨p, ix 0, ix 0⟩, [], ?_, hpc.1 hr0⟩
        rw [concat_bytes h, view_empty, hpqb]
        simp
      · rw [if_neg hr0] at h
        obtain ⟨rem, cs, hrem, hpp⟩ := hpc.2 hr0
        rw [hrem] at h
        simp only [] at h
        refine ⟨q.val.toNat, rem, cs, ?_, hpp⟩
        rw [concat_bytes h, hpqb]
        simp
  next => cases h

end JuliaLean.StringUtil.Pad

namespace JuliaLean.StringUtil

open JuliaLean JuliaLean.Strings

/-- For widths `0 ≤ cw ≤ 2` and a pad of positive width, `lpad(s, n, p)` is at least `n`
columns wide and ends with `s` ("pad the resulting string on the left with `p` to make it `n`
characters (in `textwidth`) long", `base/strings/util.jl:494-498`). -/
def LpadWidthSuffix : Prop :=
  ∀ (cw : UInt32 → Int), (∀ u, 0 ≤ cw u ∧ cw u ≤ 2) →
  ∀ (s p : JStr) (n : JInt64) (out : JStr), 0 < textwidth cw p →
    Pad.lpadStr cw s n p = .ok out →
    n.val ≤ textwidth cw out ∧ Strings.endswith out s = .ok true

/-- `"\x80"`, `"\xe0"` and `"\xe0\xe0\x80"`. -/
def str80 : JStr := ⟨[0x80], by decide⟩
def strE0 : JStr := ⟨[0xe0], by decide⟩
def strE0E080 : JStr := ⟨[0xe0, 0xe0, 0x80], by decide⟩

theorem lpadWidthSuffix_refuted : ¬ LpadWidthSuffix := by
  intro h
  have hl : Pad.lpadStr (fun _ => 1) str80 (ix 3) strE0 = .ok strE0E080 :=
    of_okSat_eq _ _ (by decide)
  have hw : textwidth (fun _ => 1) strE0E080 = 2 := by decide
  have := (h (fun _ => 1) (fun _ => ⟨by decide, by decide⟩) str80 strE0 (ix 3) strE0E080
    (by decide) hl).1
  rw [hw] at this
  revert this
  decide

open JuliaLean.Registry

/-- Registry entries of `lpad` and `rpad`. -/
def padEntries : List Entry := []

end JuliaLean.StringUtil
