import JuliaLean.IteratorsCov.Leaves
import JuliaLean.IteratorsCov.Traits

/-!
# `Iterators.Take` and `Iterators.Drop` (base/iterators.jl:776-892)
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- `iterate(it, rest...)` for a state tail `rest` that is empty or one state. -/
def innerIter (it : It) : List V → Step
  | [] => it.first
  | [s] => it.next s
  | _ => jthrow (.methodError "iterate")

/-- `isdone(it, rest...)` for a state tail `rest`. -/
def innerDone (it : It) : List V → R (Option Bool)
  | [] => it.done0
  | [s] => it.doneS s
  | _ => jthrow (.methodError "isdone")

/-- Julia's `|` on `Union{Bool, Missing}` (`none` is `missing`). -/
def or3 : Option Bool → Option Bool → Option Bool
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

/-! ## `Take` -/

/-- The tail of `iterate(it::Take, state)` after `n <= 0` was ruled out:
`y === nothing && return nothing; return y[1], (n - 1, y[2])`. -/
def takeCont (n : Int) : Step → Step
  | .ok none => .ok none
  | .ok (some (y, s)) => .ok (some (y, .tup [.int (i64 n - i64 1).val, s]))
  | .error e => .error e

/-- `iterate(it::Take, state=(it.n,))`, base/iterators.jl:827-833. -/
def takeNext (xs : It) : V → Step
  | .tup (.int n :: rest) => if n ≤ 0 then .ok none else takeCont n (innerIter xs rest)
  | _ => jthrow (.methodError "iterate")

/-- `take_iteratorsize`, base/iterators.jl:820-821. -/
def takeIsz : Isz → Isz
  | .sizeUnknown => .sizeUnknown
  | _ => .hasLength

/-- `isdone(t::Take, state) = (state[1] <= 0) | isdone(t.xs, tail(state)...)`,
base/iterators.jl:825. -/
def takeDoneS (xs : It) : V → R (Option Bool)
  | .tup (.int n :: rest) => do
    let d ← innerDone xs rest
    pure (or3 (some (decide (n ≤ 0))) d)
  | _ => jthrow (.methodError "isdone")

/-- The object `Take(xs, n)` with its methods: `eltype` and `IteratorEltype`
of the wrapped type (818-819), `IteratorSize` (822), `length` (823,
`_min_length(t.xs, 1:t.n, IteratorSize(t.xs), HasLength())` with
`length(1:n) == n`), the two `isdone` methods (824-825) and `iterate`
(827-833). -/
def takeIt (xs : It) (n : JInt64) : It where
  first := takeNext xs (.tup [.int n.val])
  next := takeNext xs
  isz := takeIsz xs.isz
  iel := xs.iel
  elt := xs.elt
  len := minLength xs.len (.ok n) xs.isz .hasLength
  done0 := xs.done0
  doneS := takeDoneS xs

/-- The inner constructor `Take(xs, n)`, base/iterators.jl:781-784. -/
def mkTake (xs : It) (n : JInt64) : R It :=
  if n < i64 0 then jthrow (.argumentError "Take length must be non-negative") else .ok (takeIt xs n)

/-- `take(xs, n::Integer) = Take(xs, Int(n))`, base/iterators.jl:815, for an
`Int` count. -/
def take (xs : It) (n : JInt64) : R It := mkTake xs n

/-- `take(xs::Take, n) = Take(xs.xs, min(Int(n), xs.n))`, base/iterators.jl:816:
`inner` is `xs.xs` and `m` is `xs.n`. -/
def takeTake (inner : It) (m : JInt64) (n : JInt64) : R It := mkTake inner (jmin n m)

/-! ## `Drop` -/

/-- The loop `for _ in 1:it.n; y === nothing && return y; y = iterate(it.xs, y[2]); end`
of `iterate(it::Drop)`, base/iterators.jl:885-888. -/
def dropLoop (xs : It) : Nat → Step → Step
  | 0, y => y
  | k + 1, .ok none => .ok none
  | k + 1, .ok (some (_, s)) => dropLoop xs k (xs.next s)
  | _ + 1, .error e => .error e

/-- `drop_iteratorsize`, base/iterators.jl:877-879. -/
def dropIsz : Isz → Isz
  | .sizeUnknown => .sizeUnknown
  | .hasShape _ => .hasLength
  | .hasLength => .hasLength
  | .isInfinite => .isInfinite

/-- The object `Drop(xs, n)` with its methods: `eltype`, `IteratorEltype`
(875-876), `IteratorSize` (880), `length` (881,
`_diff_length(d.xs, 1:d.n, IteratorSize(d.xs), HasLength())`), `iterate(it::Drop)`
(883-890), `iterate(it::Drop, state)` (891) and `isdone(it::Drop, state)` (892).
There is no `isdone(::Drop)` method: the fallback answers `missing`. -/
def dropIt (xs : It) (n : JInt64) : It where
  first := dropLoop xs n.val.toNat xs.first
  next := xs.next
  isz := dropIsz xs.isz
  iel := xs.iel
  elt := xs.elt
  len := diffLength xs.len (.ok n) xs.isz .hasLength
  done0 := .ok none
  doneS := xs.doneS

/-- The inner constructor `Drop(xs, n)`, base/iterators.jl:840-843. -/
def mkDrop (xs : It) (n : JInt64) : R It :=
  if n < i64 0 then jthrow (.argumentError "Drop length must be non-negative") else .ok (dropIt xs n)

/-! ## Lemmas -/

theorem i64_toNat {n : JInt64} (h : 0 ≤ n.val) : i64 (n.val.toNat : Nat) = n := by
  apply Subtype.ext
  have := n.property
  rw [Int.toNat_of_nonneg h]
  exact i64_val (by simp [IntTy.min, IntTy.signed, IntTy.bits] at this; omega)
    (by simp [IntTy.max, IntTy.signed, IntTy.bits] at this; omega)

theorem jint64_lt (n : JInt64) : n.val < 2 ^ 63 := by
  have := n.property; simp [IntTy.max, IntTy.signed, IntTy.bits] at this; omega

theorem take_YF (xs : It) {y : Step} {l : List V} (h : YF xs.next y l) :
    ∀ k : Nat, k < 2 ^ 63 →
      YF (takeNext xs) (if (k : Int) ≤ 0 then .ok none else takeCont k y) (l.take k) := by
  induction h with
  | nil => intro k _; rw [List.take_nil]; split <;> exact .nil
  | @cons x s l _ ih =>
    intro k hk
    cases k with
    | zero => rw [if_pos (by simp), List.take_zero]; exact .nil
    | succ k =>
      have h1 : ¬ ((k + 1 : Nat) : Int) ≤ 0 := by omega
      rw [if_neg h1]
      simp only [takeCont, List.take_succ_cons]
      have hp : (i64 ((k + 1 : Nat) : Int) - i64 1).val = (k : Int) := by
        rw [i64_pred (by omega) (by omega)]; omega
      rw [hp]
      exact .cons (ih k (by omega))

theorem take_PF_YF (xs : It) {y : Step} {l : List V} (h : PF xs.next y l) :
    ∀ k : Nat, l.length = k → k < 2 ^ 63 →
      YF (takeNext xs) (if (k : Int) ≤ 0 then .ok none else takeCont k y) l := by
  induction h with
  | nil => intro k hk _; subst hk; rw [if_pos (by simp)]; exact .nil
  | @cons x s l _ ih =>
    intro k hk hk2
    cases k with
    | zero => simp at hk
    | succ k =>
      have h1 : ¬ ((k + 1 : Nat) : Int) ≤ 0 := by omega
      rw [if_neg h1]
      simp only [takeCont]
      have hp : (i64 ((k + 1 : Nat) : Int) - i64 1).val = (k : Int) := by
        rw [i64_pred (by omega) (by omega)]; omega
      rw [hp]
      exact .cons (ih k (by simpa using hk) (by omega))

theorem take_PF_inner (xs : It) : ∀ (l : List V) (k : Nat) (y : Step),
    PF (takeNext xs) (if (k : Int) ≤ 0 then .ok none else takeCont k y) l → k < 2 ^ 63 →
      PF xs.next y l := by
  intro l
  induction l with
  | nil => intro _ _ _ _; exact .nil
  | cons z zs ih =>
    intro k y h hk
    generalize hw : (if (k : Int) ≤ 0 then .ok none else takeCont k y) = w at h
    cases h with
    | @cons _ s' _ h' =>
      split at hw
      · cases hw
      · rename_i hk0
        match y, hw with
        | .ok (some (a, s)), hw =>
          simp only [takeCont, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          refine .cons ?_
          have hp : (i64 (k : Int) - i64 1).val = ((k - 1 : Nat) : Int) := by
            rw [i64_pred (by omega) (by omega)]; omega
          rw [hp] at h'
          exact ih (k - 1) (xs.next s) h' (by omega)

theorem take_RF (xs : It) {y : Step} {k : Nat} {st : V}
    (h : RF (takeNext xs) (if (k : Int) ≤ 0 then .ok none else takeCont k y) st) (hk : k < 2 ^ 63) :
    ∃ (m : Nat) (s : V), st = .tup [.int m, s] ∧ RF xs.next y s ∧ m < 2 ^ 63 := by
  generalize hw : (if (k : Int) ≤ 0 then .ok none else takeCont k y) = w at h
  induction h with
  | @here x s =>
    split at hw
    · cases hw
    · match y, hw with
      | .ok (some (a, s0)), hw =>
        simp only [takeCont, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        refine ⟨k - 1, s0, ?_, .here, by omega⟩
        rw [i64_pred (by omega) (by omega)]
        congr; omega
  | @step _ s x s' _ hn ih =>
    obtain ⟨m, s0, rfl, hr, hm⟩ := ih hw
    have hn' : (if (m : Int) ≤ 0 then .ok none else takeCont m (xs.next s0)) = .ok (some (x, s')) := hn
    split at hn'
    · cases hn'
    · rename_i hm0
      generalize hq : xs.next s0 = q at hn'
      match q, hn' with
      | .ok (some (a, s1)), hn' =>
        simp only [takeCont, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hn'
        obtain ⟨rfl, rfl⟩ := hn'
        refine ⟨m - 1, s1, ?_, .step hr hq, by omega⟩
        rw [i64_pred (by omega) (by omega)]
        congr; omega

/-! ## `Drop` lemmas -/

theorem drop_YF (xs : It) : ∀ (k : Nat) {y : Step} {l : List V}, YF xs.next y l →
    YF xs.next (dropLoop xs k y) (l.drop k) := by
  intro k
  induction k with
  | zero => intro y l h; exact h
  | succ k ih =>
    intro y l h
    cases h with
    | nil => exact .nil
    | cons h' => exact ih h'

theorem drop_PF (xs : It) : ∀ (k : Nat) {y : Step} {l : List V}, PF xs.next y l → k ≤ l.length →
    PF xs.next (dropLoop xs k y) (l.drop k) := by
  intro k
  induction k with
  | zero => intro y l h _; exact h
  | succ k ih =>
    intro y l h hk
    cases h with
    | nil => simp at hk
    | cons h' => exact ih h' (by simp at hk; omega)

theorem drop_PF_inner (xs : It) : ∀ (k : Nat) {y : Step} {l : List V},
    PF xs.next (dropLoop xs k y) l → ∃ pre, PF xs.next y (pre ++ l) := by
  intro k
  induction k with
  | zero => intro y l h; exact ⟨[], h⟩
  | succ k ih =>
    intro y l h
    match y, h with
    | .ok none, h =>
      cases l with
      | nil => exact ⟨[], .nil⟩
      | cons _ _ => cases h
    | .ok (some (a, s)), h =>
      obtain ⟨pre, hp⟩ := ih h
      exact ⟨a :: pre, .cons hp⟩
    | .error e, h =>
      cases l with
      | nil => exact ⟨[], .nil⟩
      | cons _ _ => cases h

theorem RF.some_of {nx : V → Step} {y : Step} {s : V} (h : RF nx y s) :
    ∃ x s0, y = .ok (some (x, s0)) := by
  induction h with
  | here => exact ⟨_, _, rfl⟩
  | step _ _ ih => exact ih

theorem RF.prepend {nx : V → Step} {a s0 s : V} (h : RF nx (nx s0) s) :
    RF nx (.ok (some (a, s0))) s := by
  generalize hq : nx s0 = q at h
  induction h with
  | here => exact .step .here hq
  | step _ hn ih => exact .step (ih hq) hn

theorem drop_RF (xs : It) : ∀ (k : Nat) {y : Step} {s : V},
    RF xs.next (dropLoop xs k y) s → RF xs.next y s := by
  intro k
  induction k with
  | zero => intro y s h; exact h
  | succ k ih =>
    intro y s h
    obtain ⟨x0, s1, hy0⟩ := RF.some_of h
    match y, h, hy0 with
    | .ok (some (a, s0)), h, _ => exact RF.prepend (ih h)
    | .ok none, _, hy0 => simp [dropLoop] at hy0
    | .error e, _, hy0 => simp [dropLoop] at hy0

/-! ## Properties -/

/-- `Iterators.take(itr, n)` for an `Int` count: the constructor rejects
`n < 0`; otherwise the iterator yields the first `min(n, length)` elements of
a finite `itr` and the first `n` of an infinite one, its `IteratorSize`,
`length` and `eltype` are truthful whenever `itr`'s are, and
`isdone(t, state)` agrees with `iterate(t, state)` whenever `isdone(itr, s)`
agrees with `iterate(itr, s)` (base/iterators.jl:790-833). -/
def TakeSound : Prop :=
  ∀ (it : It) (n : JInt64),
    (n.val < 0 → mkTake it n = jthrow (.argumentError "Take length must be non-negative")) ∧
    (0 ≤ n.val →
      take it n = .ok (takeIt it n) ∧
      (∀ xs, it.Yields xs → (takeIt it n).Yields (xs.take n.val.toNat)) ∧
      (it.Endless → ∃ xs, xs.length = n.val.toNat ∧ it.Pre xs ∧ (takeIt it n).Yields xs) ∧
      (it.SizeSound → (takeIt it n).SizeSound) ∧
      (it.EltSound → (takeIt it n).EltSound) ∧
      (it.DoneSSound → (takeIt it n).DoneSSound))

theorem takeIt_first (it : It) (n : JInt64) (h : 0 ≤ n.val) :
    (takeIt it n).first =
      if ((n.val.toNat : Nat) : Int) ≤ 0 then .ok none else takeCont (n.val.toNat : Nat) it.first := by
  show takeNext it (.tup [.int n.val]) = _
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h
  rw [hk, Int.toNat_natCast]
  rfl

theorem i64_zero_val : (i64 0).val = 0 := by decide

theorem i64_sub_nat {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) (h : b ≤ a) :
    i64 a - i64 b = i64 (a - b : Nat) := by
  apply Subtype.ext
  show wrapInt .i64 ((i64 a).val - (i64 b).val) = (i64 ((a - b : Nat) : Int)).val
  rw [i64_nat_val' ha, i64_nat_val' hb, i64_nat_val' (by omega)]
  rw [wrapInt_of_inRange .i64 _ ⟨by simp [IntTy.min, IntTy.signed, IntTy.bits]; omega,
    by simp [IntTy.max, IntTy.signed, IntTy.bits]; omega⟩]
  omega

theorem takeSound : TakeSound := by
  intro it n
  constructor
  · intro hn
    unfold mkTake
    rw [if_pos (show n < i64 0 by show n.val < (i64 0).val; rw [i64_zero_val]; exact hn)]
  · intro hn
    have hnl := jint64_lt n
    have hnot : ¬ n < i64 0 := by show ¬ n.val < (i64 0).val; rw [i64_zero_val]; omega
    have hk : (n.val.toNat : Nat) < 2 ^ 63 := by omega
    have hfirst := takeIt_first it n hn
    have hyield : ∀ xs, it.Yields xs → (takeIt it n).Yields (xs.take n.val.toNat) := by
      intro xs hy
      unfold It.Yields
      rw [hfirst]
      exact take_YF it hy _ hk
    have hend : it.Endless → ∃ xs, xs.length = n.val.toNat ∧ it.Pre xs ∧ (takeIt it n).Yields xs := by
      intro hE
      obtain ⟨ps, hlen, hpre⟩ := hE n.val.toNat
      refine ⟨ps, hlen, hpre, ?_⟩
      unfold It.Yields
      rw [hfirst]
      exact take_PF_YF it hpre _ hlen hk
    refine ⟨by unfold take mkTake; rw [if_neg hnot], hyield, hend, ?_, ?_, ?_⟩
    · intro hS
      obtain ⟨hS1, _, hS3⟩ := hS
      refine ⟨?_, ?_, ?_⟩
      · intro hf
        cases hiz : it.isz with
        | sizeUnknown =>
          simp [takeIt, hiz, takeIsz, Isz.finite] at hf
        | isInfinite =>
          obtain ⟨ps, hlen, _, hy⟩ := hend (hS3 hiz)
          refine ⟨ps, hy, by omega, ?_⟩
          show minLength it.len (.ok n) it.isz .hasLength = _
          rw [hiz, hlen, i64_toNat hn]
          rfl
        | hasLength | hasShape _ =>
          obtain ⟨xs, hy, hlt, hlen⟩ := hS1 (by simp [hiz, Isz.finite])
          refine ⟨xs.take n.val.toNat, hyield xs hy, by simp; omega, ?_⟩
          show minLength it.len (.ok n) it.isz .hasLength = _
          rw [minLength_ff _ _ (by simp [hiz, Isz.finite]) rfl, hlen]
          show Except.ok (jmin (i64 xs.length) n) = _
          conv => lhs; rw [← i64_toNat hn]
          rw [jmin_i64 hlt hk, List.length_take, Nat.min_comm]
      · intro m hm
        cases hiz : it.isz <;> simp [takeIt, hiz, takeIsz] at hm
      · intro hm
        cases hiz : it.isz <;> simp [takeIt, hiz, takeIsz] at hm
    · intro hE hiel xs hpre x hx
      unfold It.Pre at hpre
      rw [hfirst] at hpre
      exact hE hiel xs (take_PF_inner it xs _ _ hpre hk) x hx
    · intro hD st hr
      rw [hfirst] at hr
      obtain ⟨m, s, rfl, hrs, hm⟩ := take_RF it hr hk
      obtain ⟨hD1, hD2⟩ := hD s hrs
      have hds : (takeIt it n).doneS (.tup [.int m, s]) =
          (it.doneS s).bind (fun d => .ok (or3 (some (decide ((m : Int) ≤ 0))) d)) := rfl
      have hnx : (takeIt it n).next (.tup [.int m, s]) =
          if (m : Int) ≤ 0 then .ok none else takeCont m (it.next s) := rfl
      rw [hds, hnx]
      cases hd : it.doneS s with
      | error e => simp [Except.bind]
      | ok d =>
        show (Except.ok (or3 (some (decide ((m : Int) ≤ 0))) d) = Except.ok (some true) → _) ∧
          (Except.ok (or3 (some (decide ((m : Int) ≤ 0))) d) = Except.ok (some false) → _)
        by_cases hm0 : (m : Int) ≤ 0
        · rw [if_pos hm0, decide_eq_true hm0]
          refine ⟨fun _ => rfl, fun h => ?_⟩
          cases d with
          | none => simp [or3] at h
          | some b => cases b <;> simp [or3] at h
        · rw [if_neg hm0, decide_eq_false hm0]
          constructor
          · intro h
            cases d with
            | none => simp [or3] at h
            | some b =>
              cases b with
              | false => simp [or3] at h
              | true => rw [hD1 (by rw [hd])]; rfl
          · intro h
            cases d with
            | none => simp [or3] at h
            | some b =>
              cases b with
              | true => simp [or3] at h
              | false =>
                obtain ⟨⟨a, b⟩, hp⟩ := hD2 (by rw [hd])
                rw [hp]
                exact ⟨_, rfl⟩

/-- `Iterators.drop(itr, n)` for an `Int` count: the constructor rejects
`n < 0`; otherwise the iterator yields all but the first `n` elements of a
finite `itr`, stays infinite for an infinite one, its `IteratorSize`,
`length` and `eltype` are truthful whenever `itr`'s are, and
`isdone(d, state)` agrees with `iterate(d, state)` whenever `itr`'s
`isdone` agrees with its `iterate` (base/iterators.jl:849-892). -/
def DropSound : Prop :=
  ∀ (it : It) (n : JInt64),
    (n.val < 0 → mkDrop it n = jthrow (.argumentError "Drop length must be non-negative")) ∧
    (0 ≤ n.val →
      mkDrop it n = .ok (dropIt it n) ∧
      (∀ xs, it.Yields xs → (dropIt it n).Yields (xs.drop n.val.toNat)) ∧
      (it.Endless → (dropIt it n).Endless) ∧
      (it.SizeSound → (dropIt it n).SizeSound) ∧
      (it.EltSound → (dropIt it n).EltSound) ∧
      (it.DoneSSound → (dropIt it n).DoneSSound))

theorem dropSound : DropSound := by
  intro it n
  constructor
  · intro hn
    unfold mkDrop
    rw [if_pos (show n < i64 0 by show n.val < (i64 0).val; rw [i64_zero_val]; exact hn)]
  · intro hn
    have hnl := jint64_lt n
    have hnot : ¬ n < i64 0 := by show ¬ n.val < (i64 0).val; rw [i64_zero_val]; omega
    have hk : (n.val.toNat : Nat) < 2 ^ 63 := by omega
    have hyield : ∀ xs, it.Yields xs → (dropIt it n).Yields (xs.drop n.val.toNat) :=
      fun xs hy => drop_YF it _ hy
    have hend : it.Endless → (dropIt it n).Endless := by
      intro hE m
      obtain ⟨ps, hlen, hpre⟩ := hE (n.val.toNat + m)
      exact ⟨ps.drop n.val.toNat, by simp; omega, drop_PF it _ hpre (by omega)⟩
    refine ⟨by unfold mkDrop; rw [if_neg hnot], hyield, hend, ?_, ?_, ?_⟩
    · intro hS
      obtain ⟨hS1, _, hS3⟩ := hS
      refine ⟨?_, ?_, ?_⟩
      · intro hf
        cases hiz : it.isz with
        | sizeUnknown => simp [dropIt, hiz, dropIsz, Isz.finite] at hf
        | isInfinite => simp [dropIt, hiz, dropIsz, Isz.finite] at hf
        | hasLength | hasShape _ =>
          obtain ⟨xs, hy, hlt, hlen⟩ := hS1 (by simp [hiz, Isz.finite])
          refine ⟨xs.drop n.val.toNat, hyield xs hy, by simp; omega, ?_⟩
          show diffLength it.len (.ok n) it.isz .hasLength = _
          rw [diffLength_ff _ _ (by simp [hiz, Isz.finite]) rfl, hlen]
          show Except.ok (if i64 xs.length > n then i64 xs.length - n else i64 0) = _
          conv => lhs; rw [← i64_toNat hn]
          have hlt' := i64_lt (x := (n.val.toNat : Nat)) (y := (xs.length : Nat))
            (by omega) (by omega) (by omega) (by omega)
          rw [List.length_drop]
          split
          · rename_i h
            have : n.val.toNat < xs.length := by exact_mod_cast hlt'.mp h
            rw [i64_sub_nat hlt hk (by omega)]
          · rename_i h
            have : ¬ n.val.toNat < xs.length := fun hc => h (hlt'.mpr (by exact_mod_cast hc))
            have : xs.length - n.val.toNat = 0 := by omega
            rw [this]; rfl
      · intro m hm
        cases hiz : it.isz <;> simp [dropIt, hiz, dropIsz] at hm
      · intro hm
        have : it.isz = .isInfinite := by
          cases hiz : it.isz <;> simp [dropIt, hiz, dropIsz] at hm ⊢
        exact hend (hS3 this)
    · intro hE hiel xs hpre x hx
      obtain ⟨pre, hp⟩ := drop_PF_inner it _ hpre
      exact hE hiel _ hp x (List.mem_append_right _ hx)
    · intro hD st hr
      exact hD st (drop_RF it _ hr)

end JuliaLean.IteratorsCov
