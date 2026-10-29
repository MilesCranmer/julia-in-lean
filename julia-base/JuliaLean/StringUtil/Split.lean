import JuliaLean.Strings.Props
import JuliaLean.Registry.Types

/-!
# `split` and `rsplit`, `base/strings/util.jl:772-1009`

Master `bbfa0ce4150`. The iterators `SplitIterator` and `RSplitIterator` are
modelled over an arbitrary splitter, given as the function
`k ↦ findnext(splitter, str, k)` (resp. `findprev`) that the iterators call. A
`findnext` result `j::Int` (a character predicate) is the range `j:j`.

`while` loops carry an explicit iteration bound (`fuel`); each docstring states
why the bound is never reached for a splitter whose `findnext` returns ranges
starting at or after `k` (resp. ending at or before the search position).
-/

namespace JuliaLean.StringUtil

open JuliaLean.Strings JuliaLean.Registry

/-- `k ↦ findnext(splitter, str, k)` or `findprev`: `nothing` or a range `first:last`. -/
abbrev Finder := JInt64 → SJl (Option (JInt64 × JInt64))

/-- `findnext(isequal(c), s, k)` for a `Char` `c`, as a range `j:j`. -/
def charFinder (c : UInt32) (s : JStr) : Finder :=
  fun k => (findnextChar c s k).map (Option.map fun j => (j, j))

/-- `findnext(t, s, k)` for a String delimiter `t`. -/
def strFinder (t s : JStr) : Finder :=
  fun k => (findnextStr t s k).map (Option.map fun p => (ix p.1, ix p.2))

/-- `findprev(t, s, k)` for a String delimiter `t`. -/
def strFinderPrev (t s : JStr) : Finder :=
  fun k => (findprevStr t s k).map (Option.map fun p => (ix p.1, ix p.2))

abbrev SplitState := JInt64 × JInt64 × JInt64
abbrev SplitStep := SJl (Option (JSub × SplitState))

/-- `lastindex(s::String) = thisind(s, ncodeunits(s))`, `base/strings/string.jl:249`;
the same function as `Strings.lastindex`, written without a `match` so that
proofs can unfold it on a symbolic string (unfolding `Strings.lastindex` makes
Lean evaluate `thisind` on the symbolic length). -/
def lastIdx (s : JStr) : JInt64 := (thisind s (ncodeunits s)).toOption.getD (ix 0)

/-- After the `while` loop of `iterate(::SplitIterator, (i, k, n))`,
`base/strings/util.jl:805-806`. -/
def splitTail (s : JStr) (keepempty : Bool) (i k n : JInt64) : SplitStep :=
  if !keepempty && !decide (i.val ≤ (ncodeunits s).val) then .ok none
  else (substring s i (lastIdx s) false).map fun sub => some (sub, (ncodeunits s + ix 2, k, n + ix 1))

/-- The `while` loop of `iterate(::SplitIterator, (i, k, n))`,
`base/strings/util.jl:794-804`; `r` is the pending `findnext` result. Every pass
that does not return sets `k` to `k_ > first(r) ≥ k`, so for a splitter whose
ranges start at or after `k` the loop exits after at most `ncodeunits(s) + 1`
passes (once `first(r) > ncodeunits(s)`); the bound `ncodeunits(s) + 2` is never
reached. -/
def splitLoop (s : JStr) (fnext : Finder) (limit : JInt64) (keepempty : Bool) :
    Nat → JInt64 → JInt64 → JInt64 → Option (JInt64 × JInt64) → SplitStep
  | 0, i, k, n, _ => splitTail s keepempty i k n
  | _ + 1, i, k, n, none => splitTail s keepempty i k n
  | fuel + 1, i, k, n, some (a, b) =>
    if !(decide (n.val ≠ (limit - ix 1).val) && decide (a.val ≤ (ncodeunits s).val)) then
      splitTail s keepempty i k n
    else
      match nextind s b with
      | .error e => .error e
      | .ok k1 =>
        match (if k1.val ≤ a.val then nextind s a else .ok k1) with
        | .error e => .error e
        | .ok k_ =>
          if i.val < k1.val then
            match prevind s a with
            | .error e => .error e
            | .ok pj =>
              match substring s i pj false with
              | .error e => .error e
              | .ok sub =>
                if keepempty || decide (i.val < a.val) then .ok (some (sub, (k1, k_, n + ix 1)))
                else
                  match fnext k_ with
                  | .error e => .error e
                  | .ok r => splitLoop s fnext limit keepempty fuel k1 k_ n r
          else
            match fnext k_ with
            | .error e => .error e
            | .ok r => splitLoop s fnext limit keepempty fuel i k_ n r

/-- `iterate(iter::SplitIterator, (i, k, n))`, `base/strings/util.jl:791-807`. -/
def splitIterate (s : JStr) (fnext : Finder) (limit : JInt64) (keepempty : Bool)
    (i k n : JInt64) : SplitStep :=
  if (i - ix 1).val > (ncodeunits s).val then .ok none
  else
    match fnext k with
    | .error e => .error e
    | .ok r => splitLoop s fnext limit keepempty (s.bytes.length + 2) i k n r

/-- `collect` of a `SplitIterator`. Every yielded piece either consumes at least
one code unit of a delimiter occurrence or ends the iteration, so
`ncodeunits(s) + 2` calls suffice for such splitters. -/
def splitAll (s : JStr) (fnext : Finder) (limit : JInt64) (keepempty : Bool) :
    Nat → SplitState → SJl (List JSub)
  | 0, _ => .ok []
  | fuel + 1, st =>
    match splitIterate s fnext limit keepempty st.1 st.2.1 st.2.2 with
    | .error e => .error e
    | .ok none => .ok []
    | .ok (some (sub, st')) => (splitAll s fnext limit keepempty fuel st').map (sub :: ·)

/-- `split(str, splitter; limit, keepempty) = collect(eachsplit(str, splitter; limit,
keepempty))` (`base/strings/util.jl:958-961`) for `limit::Int`; the iterator starts
at `(firstindex(str), firstindex(str), 0)` (`:791`). -/
def splitGen (s : JStr) (fnext : Finder) (limit : JInt64) (keepempty : Bool) : SJl (List JSub) :=
  splitAll s fnext limit keepempty (s.bytes.length + 2) (ix 1, ix 1, ix 0)

/-- `eachsplit(str, splitter; limit::Integer, keepempty)` collected
(`base/strings/util.jl:820-821,958-961`) for a `limit` of integer type `t`: the call
`SplitIterator(str, splitter, limit, keepempty)` reaches the default constructor,
whose `limit` field is `Int` (`:776-781`); default constructors do not convert, so
any other integer type is a `MethodError`. -/
def eachsplitTyped (s : JStr) (fnext : Finder) (t : IntTy) (limit : JInt t) (keepempty : Bool) :
    SJl (List JSub) :=
  match t, limit with
  | .i64, l => splitGen s fnext l keepempty
  | _, _ => .error (.jl (.methodError "SplitIterator"))

/-- The `while !iszero(remaining_splits)` loop of `iterate(::RSplitIterator, (to,
remaining_splits))`, `base/strings/util.jl:902-924`, entered with
`remaining_splits ≠ 0` (which the loop never changes). Returns `(from, next_to,
to)`. Only `continue` (`from > to && !keepempty`) loops, setting `to =
prevind(str, first(pos)) < to` for a splitter whose ranges end at or before
`to`; the bound `to + 1` is never reached for such splitters. -/
def rsplitLoop (s : JStr) (fprev : Finder) (keepempty : Bool) :
    Nat → JInt64 → SJl (JInt64 × JInt64 × JInt64)
  | fuel, to =>
    match fprev to with
    | .error e => .error e
    | .ok none => .ok (ix 1, ix (-1), to)
    | .ok (some (a, b)) =>
      match nextind s b with
      | .error e => .error e
      | .ok frm =>
        match (if decide (b.val < a.val) && decide (to.val < 2) then .ok (ix (-1)) else prevind s a) with
        | .error e => .error e
        | .ok nextTo =>
          if decide (frm.val > to.val) && !keepempty then
            match fuel with
            | 0 => .ok (frm, nextTo, to)
            | fuel + 1 => rsplitLoop s fprev keepempty fuel nextTo
          else .ok (frm, nextTo, to)

/-- `from`, `next_to` and `to` after the loop of `base/strings/util.jl:900-924`. -/
def rsplitRes (s : JStr) (fprev : Finder) (keepempty : Bool) (to rem : JInt64) :
    SJl (JInt64 × JInt64 × JInt64) :=
  if rem.val = 0 then .ok (ix 1, ix (-1), to)
  else rsplitLoop s fprev keepempty (to.val.toNat + 1) to

/-- `iterate(it::RSplitIterator, (to, remaining_splits))`, `base/strings/util.jl:898-927`.
The final `SubString(it.str, from, to)` is checked (no `@inbounds`). -/
def rsplitIterate (s : JStr) (fprev : Finder) (keepempty : Bool) (to rem : JInt64) :
    SJl (Option (JSub × (JInt64 × JInt64))) :=
  if to.val < 0 then .ok none
  else
    match rsplitRes s fprev keepempty to rem with
    | .error e => .error e
    | .ok (frm, nextTo, to') =>
      if decide (frm.val > to'.val) && !keepempty then .ok none
      else (substring s frm to').map fun sub => some (sub, (nextTo, rem - ix 1))

/-- `collect` of an `RSplitIterator`; each piece decreases `to` for splitters as
in `rsplitLoop`, so `ncodeunits(s) + 2` calls suffice. -/
def rsplitAll (s : JStr) (fprev : Finder) (keepempty : Bool) :
    Nat → JInt64 × JInt64 → SJl (List JSub)
  | 0, _ => .ok []
  | fuel + 1, st =>
    match rsplitIterate s fprev keepempty st.1 st.2 with
    | .error e => .error e
    | .ok none => .ok []
    | .ok (some (sub, st')) => (rsplitAll s fprev keepempty fuel st').map (sub :: ·)

/-- `rsplit(str, splitter; limit, keepempty) = reverse!(collect(eachrsplit(...)))`,
`base/strings/util.jl:1001-1004`, from the state `(lastindex(str), limit - 1)` (`:898`). -/
def rsplitGen (s : JStr) (fprev : Finder) (limit : JInt64) (keepempty : Bool) : SJl (List JSub) :=
  (rsplitAll s fprev keepempty (s.bytes.length + 2) (lastIdx s, limit - ix 1)).map List.reverse

/-! ## Splitter contracts and joins -/

/-- `join(pieces, d)` as bytes. -/
def joinBytes (d : List UInt8) : List (List UInt8) → List UInt8
  | [] => []
  | [p] => p
  | p :: q :: ps => p ++ d ++ joinBytes d (q :: ps)

/-- `findnext` of the delimiter `d` in `s`: for every search start `k` it returns,
and any range `a:b` it returns starts at or after `k`, has valid character indices
`a ≤ b`, and covers exactly the bytes of `d` (from `a` up to `nextind(s, b) - 1`). -/
def FinderNext (s d : JStr) (fnext : Finder) : Prop :=
  ∀ k : JInt64, 1 ≤ k.val → k.val ≤ s.bytes.length + 1 → ∃ r, fnext k = .ok r ∧
    ∀ a b, r = some (a, b) → k.val ≤ a.val ∧ a.val ≤ b.val ∧ isvalidAt s a = true ∧
      isvalidAt s b = true ∧
      ∀ e, nextind s b = .ok e → (s.bytes.drop (a.val - 1).toNat).take (e.val - a.val).toNat = d.bytes

/-- `findprev` of the delimiter `d` in `s`: for every search position `0 ≤ t ≤
ncodeunits(s)` it returns, and any range `a:b` it returns ends at or before `t`,
has valid character indices `a ≤ b`, and covers exactly the bytes of `d`. -/
def FinderPrev (s d : JStr) (fprev : Finder) : Prop :=
  ∀ t : JInt64, 0 ≤ t.val → t.val ≤ s.bytes.length → ∃ r, fprev t = .ok r ∧
    ∀ a b, r = some (a, b) → b.val ≤ t.val ∧ a.val ≤ b.val ∧ isvalidAt s a = true ∧
      isvalidAt s b = true ∧
      ∀ e, nextind s b = .ok e → (s.bytes.drop (a.val - 1).toNat).take (e.val - a.val).toNat = d.bytes

/-! ## Lemmas -/

theorem valid_le_thisZ (s : JStr) (q r : Int) (hq : validZ s q) (h1 : q ≤ r) : q ≤ thisZ s r := by
  obtain ⟨hq1, hq2, hq3⟩ := hq
  rcases thisZ_cases s r with h | h | h | h
  · omega
  · refine Classical.byContradiction fun hc => ?_
    have e : q = r := by omega
    subst e; omega
  · refine Classical.byContradiction fun hc => ?_
    rcases (show q = r ∨ q = r - 1 by omega) with e | e
    · subst e; omega
    · have := thisZ_lead1 s (r - 2) q (by omega) (by omega) ⟨by omega, by omega⟩ (by rw [e]; omega)
      omega
  · refine Classical.byContradiction fun hc => ?_
    rcases (show q = r ∨ q = r - 1 ∨ q = r - 2 by omega) with e | e | e
    · subst e; omega
    · have := thisZ_lead2 s (r - 3) q (by omega) (by omega) ⟨by omega, by omega⟩
        (by rw [show r - 3 + 1 = r - 2 by omega]; omega) (by rw [e]; omega)
      omega
    · have := thisZ_lead1 s (r - 3) q (by omega) (by omega) ⟨by omega, by omega⟩ (by rw [e]; omega)
      omega

theorem lastIdx_zero (s : JStr) (h : s.bytes.length = 0) : (lastIdx s).val = 0 := by
  have e : (ncodeunits s).val = 0 := by rw [ncu_val, h]; rfl
  have ht : thisind s (ncodeunits s) = .ok (ix 0) := by unfold thisind; rw [if_pos e]
  unfold lastIdx
  rw [ht]
  exact ix0

theorem lastIdx_pos (s : JStr) (h : 1 ≤ s.bytes.length) :
    (lastIdx s).val = thisZ s s.bytes.length ∧ validZ s (thisZ s s.bytes.length) ∧
      ∃ e, nextind s (lastIdx s) = .ok e ∧ e.val = s.bytes.length + 1 := by
  have hsm := ncu_small s
  obtain ⟨j, hj, hjv⟩ := thisind_mid s (ncodeunits s) (by rw [ncu_val]; omega)
    (by rw [ncu_val]; exact Int.le_refl _)
  rw [ncu_val] at hjv
  have hl : lastIdx s = j := by unfold lastIdx; rw [hj] <;> rfl
  have hr := thisZ_range s s.bytes.length (by omega)
  have hv : validZ s (thisZ s s.bytes.length) := ⟨hr.1, hr.2, thisZ_idem s _⟩
  rw [hl, hjv]
  refine ⟨rfl, hv, ?_⟩
  obtain ⟨e, he, hev⟩ := nextind_mid s j (by omega) (by omega)
  refine ⟨e, he, ?_⟩
  have hn := nextZ_nextValid s j.val (by omega) (by omega)
  rw [← hev] at hn
  obtain ⟨n1, n2, _, n4⟩ := hn
  refine Classical.byContradiction fun hc => ?_
  have hv' := n4 (by omega)
  have := valid_le_thisZ s e.val s.bytes.length hv' (by omega)
  omega

theorem view_bytes (s : JStr) (off n : JInt64) :
    (JSub.view ⟨s, off, n⟩).bytes = (s.bytes.drop off.val.toNat).take n.val.toNat := rfl

theorem split_view_empty (s : JStr) : (JSub.view ⟨s, ix 0, ix 0⟩).bytes = [] := rfl

theorem split_substring_empty (s : JStr) (i j : JInt64) (c : Bool) (h : j.val < i.val) :
    substring s i j c = .ok ⟨s, ix 0, ix 0⟩ := by
  unfold substring
  rw [if_pos (by simp only [Bool.not_eq_true', decide_eq_false_iff_not]; omega)]

theorem substring_unchecked (s : JStr) (i j e : JInt64) (hij : i.val ≤ j.val)
    (he : nextind s j = .ok e) : substring s i j false = .ok ⟨s, i - ix 1, e - i⟩ := by
  unfold substring
  rw [if_neg (by simp only [Bool.not_eq_true', decide_eq_false_iff_not]; omega)]
  simp only [Bool.not_false, ↓reduceIte, he] <;> rfl

theorem substring_checked (s : JStr) (i j e : JInt64) (h1 : 1 ≤ i.val) (hij : i.val ≤ j.val)
    (hj : j.val ≤ s.bytes.length) (hvi : isvalidAt s i = true) (hvj : isvalidAt s j = true)
    (he : nextind s j = .ok e) : substring s i j = .ok ⟨s, i - ix 1, e - i⟩ := by
  unfold substring
  have hb : (!(decide (1 ≤ i.val) && decide (j.val ≤ (ncodeunits s).val))) = false := by
    rw [ncu_val]; simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq]; omega
  rw [if_neg (by simp only [Bool.not_eq_true', decide_eq_false_iff_not]; omega)]
  simp only [Bool.not_true, hb, hvi, hvj, Bool.false_eq_true, ↓reduceIte, he] <;> rfl

theorem prevind_valid (s : JStr) (a : JInt64) (ha : validZ s a.val) :
    ∃ pj, prevind s a = .ok pj ∧ ((a.val = 1 ∧ pj.val = 0) ∨
      (2 ≤ a.val ∧ PrevValid s a.val pj.val ∧ nextind s pj = .ok a)) := by
  obtain ⟨pj, hp, hpv⟩ := previndN_one s a ha.1 (by have := ha.2.1; omega)
  refine ⟨pj, hp, ?_⟩
  rcases hpv with h | ⟨h2, hpv⟩
  · exact Or.inl h
  · right
    refine ⟨h2, hpv, ?_⟩
    obtain ⟨j, hj, hn⟩ := nextindAfterPrevind_proven s a h2 (Or.inl ((isvalidAt_iff s a).2 ha))
    have e : j = pj := Except.ok.inj (hj.symm.trans hp)
    rw [← e]; exact hn

theorem seg_drop {α : Type} (l : List α) (x y : Nat) (h : x ≤ y) :
    (l.drop x).take (y - x) ++ l.drop y = l.drop x := by
  have e : (l.drop x).drop (y - x) = l.drop y := by rw [List.drop_drop]; congr 1; omega
  rw [← e]; exact List.take_append_drop _ _

theorem take_seg {α : Type} (l : List α) (x y : Nat) (h : x ≤ y) :
    l.take x ++ (l.drop x).take (y - x) = l.take y := by
  have := (List.take_add : l.take (x + (y - x)) = _)
  rw [show x + (y - x) = y by omega] at this
  exact this.symm

theorem joinBytes_snoc (d : List UInt8) :
    ∀ (xs : List (List UInt8)) (p : List UInt8), xs ≠ [] →
      joinBytes d (xs ++ [p]) = joinBytes d xs ++ d ++ p := by
  intro xs
  induction xs with
  | nil => intro p h; exact absurd rfl h
  | cons x xs ih =>
    intro p _
    cases xs with
    | nil => rfl
    | cons y ys =>
      have := ih p (List.cons_ne_nil _ _)
      simp only [List.cons_append] at this ⊢
      simp only [joinBytes, this, List.append_assoc]

/-! ## `split`: joining the pieces with the delimiter gives the string back -/

/-- A piece start: a valid index or `ncodeunits(s) + 1`. -/
abbrev Good (s : JStr) (i : Int) : Prop :=
  1 ≤ i ∧ i ≤ s.bytes.length + 1 ∧ (i ≤ s.bytes.length → validZ s i)

theorem tail_bytes (s : JStr) (i : JInt64) (hg : Good s i.val) :
    ∃ sub, substring s i (lastIdx s) false = .ok sub ∧
      sub.view.bytes = s.bytes.drop (i.val - 1).toNat := by
  have hsm := ncu_small s
  by_cases hn : s.bytes.length = 0
  · refine ⟨_, split_substring_empty s i _ false (by rw [lastIdx_zero s hn]; omega), ?_⟩
    rw [split_view_empty]; exact (List.drop_eq_nil_iff.mpr (by omega)).symm
  · obtain ⟨hL, hLv, e, he, hev⟩ := lastIdx_pos s (by omega)
    by_cases hi : i.val = s.bytes.length + 1
    · refine ⟨_, split_substring_empty s i _ false (by rw [hL]; have := hLv.2.1; omega), ?_⟩
      rw [split_view_empty]; exact (List.drop_eq_nil_iff.mpr (by omega)).symm
    · have hv := hg.2.2 (by omega)
      have hle := valid_le_thisZ s i.val s.bytes.length hv (by omega)
      refine ⟨_, substring_unchecked s i (lastIdx s) e (by rw [hL]; exact hle) he, ?_⟩
      rw [view_bytes, sub_val i (ix 1) (by rw [ix1]; omega) (by rw [ix1]; omega),
        sub_val e i (by omega) (by omega), ix1, hev]
      apply List.take_of_length_le
      simp only [List.length_drop]; omega

theorem splitTail_true (s : JStr) (i k n : JInt64) (hg : Good s i.val) :
    ∃ sub, splitTail s true i k n = .ok (some (sub, (ncodeunits s + ix 2, k, n + ix 1))) ∧
      sub.view.bytes = s.bytes.drop (i.val - 1).toNat := by
  obtain ⟨sub, hs, hb⟩ := tail_bytes s i hg
  refine ⟨sub, ?_, hb⟩
  unfold splitTail
  rw [if_neg (by simp), hs]
  rfl

theorem splitLoop_none (s : JStr) (fnext : Finder) (limit : JInt64) (ke : Bool) (fuel : Nat)
    (i k n : JInt64) : splitLoop s fnext limit ke fuel i k n none = splitTail s ke i k n := by
  cases fuel <;> rfl

theorem ncu2_val (s : JStr) : (ncodeunits s + ix 2).val = s.bytes.length + 2 := by
  have hsm := ncu_small s
  rw [add_val _ _ (by rw [ncu_val, ix2]; omega) (by rw [ncu_val, ix2]; omega), ncu_val, ix2]

theorem loop_step (s d : JStr) (fnext : Finder) (limit : JInt64) (f : Nat) (i n : JInt64)
    (hg : Good s i.val) (r : Option (JInt64 × JInt64))
    (hrc : ∀ a b, r = some (a, b) → i.val ≤ a.val ∧ a.val ≤ b.val ∧ isvalidAt s a = true ∧
      isvalidAt s b = true ∧
      ∀ e, nextind s b = .ok e → (s.bytes.drop (a.val - 1).toNat).take (e.val - a.val).toNat = d.bytes) :
    ∃ sub st', splitLoop s fnext limit true (f + 1) i i n r = .ok (some (sub, st')) ∧
      ((st'.1.val = s.bytes.length + 2 ∧ sub.view.bytes = s.bytes.drop (i.val - 1).toNat) ∨
       (st'.2.1 = st'.1 ∧ i.val < st'.1.val ∧ Good s st'.1.val ∧
        sub.view.bytes ++ d.bytes ++ s.bytes.drop (st'.1.val - 1).toNat =
          s.bytes.drop (i.val - 1).toNat)) := by
  have hsm := ncu_small s
  cases r with
  | none =>
    obtain ⟨sub, h1, h2⟩ := splitTail_true s i i n hg
    exact ⟨sub, (ncodeunits s + ix 2, i, n + ix 1), by rw [splitLoop_none, h1],
      Or.inl ⟨ncu2_val s, h2⟩⟩
  | some p =>
    obtain ⟨a, b⟩ := p
    obtain ⟨hia, hab, hva, hvb, hd⟩ := hrc a b rfl
    have hva' := (isvalidAt_iff s a).1 hva
    have hvb' := (isvalidAt_iff s b).1 hvb
    by_cases hlim : n.val = (limit - ix 1).val
    · have hc : (!(decide (n.val ≠ (limit - ix 1).val) && decide (a.val ≤ (ncodeunits s).val))) = true := by
        simp [hlim]
      obtain ⟨sub, h1, h2⟩ := splitTail_true s i i n hg
      refine ⟨sub, (ncodeunits s + ix 2, i, n + ix 1), ?_, Or.inl ⟨ncu2_val s, h2⟩⟩
      simp only [splitLoop, hc, ↓reduceIte, h1]
    · have hc : (!(decide (n.val ≠ (limit - ix 1).val) && decide (a.val ≤ (ncodeunits s).val))) = false := by
        rw [ncu_val]; simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hlim, by omega⟩
      obtain ⟨e, he, hev⟩ := nextind_mid s b hvb'.1 hvb'.2.1
      have hnv := nextZ_nextValid s b.val hvb'.1 hvb'.2.1
      rw [← hev] at hnv
      obtain ⟨n1, n2, _, n4⟩ := hnv
      obtain ⟨pj, hpj, hpjc⟩ := prevind_valid s a hva'
      have hsub : ∃ sub, substring s i pj false = .ok sub ∧
          sub.view.bytes = (s.bytes.drop (i.val - 1).toNat).take (a.val - i.val).toNat := by
        by_cases hia' : i.val = a.val
        · refine ⟨_, split_substring_empty s i pj false ?_, ?_⟩
          · rcases hpjc with ⟨_, h0⟩ | ⟨_, hp, _⟩
            · omega
            · have := hp.2.1; omega
          · rw [split_view_empty, hia']; simp
        · rcases hpjc with ⟨h1, _⟩ | ⟨_, hp, hnx⟩
          · omega
          · have hipj : i.val ≤ pj.val := by
              refine Classical.byContradiction fun hc' => ?_
              exact hp.2.2.2 i.val (by omega) (by omega) (hg.2.2 (by omega))
            refine ⟨_, substring_unchecked s i pj a hipj hnx, ?_⟩
            rw [view_bytes, sub_val i (ix 1) (by rw [ix1]; omega) (by rw [ix1]; omega), ix1,
              sub_val a i (by omega) (by omega)]
      obtain ⟨sub, hs, hsb⟩ := hsub
      have hke : ¬ e.val ≤ a.val := by omega
      have hik : i.val < e.val := by omega
      refine ⟨sub, (e, e, n + ix 1), ?_, Or.inr ⟨rfl, hik, (⟨by omega, n2, n4⟩ : Good s e.val), ?_⟩⟩
      · simp only [splitLoop, hc, Bool.false_eq_true, ↓reduceIte, he, hke, hik, hpj, hs,
          Bool.true_or]
      · simp only
        rw [hsb, ← hd e he, show (a.val - i.val).toNat = (a.val - 1).toNat - (i.val - 1).toNat by omega,
          show (e.val - a.val).toNat = (e.val - 1).toNat - (a.val - 1).toNat by omega,
          List.append_assoc, seg_drop s.bytes (a.val - 1).toNat (e.val - 1).toNat (by omega),
          seg_drop s.bytes (i.val - 1).toNat (a.val - 1).toNat (by omega)]

theorem split_step (s d : JStr) (fnext : Finder) (limit : JInt64) (hc : FinderNext s d fnext)
    (i n : JInt64) (hg : Good s i.val) :
    ∃ sub st', splitIterate s fnext limit true i i n = .ok (some (sub, st')) ∧
      ((st'.1.val = s.bytes.length + 2 ∧ sub.view.bytes = s.bytes.drop (i.val - 1).toNat) ∨
       (st'.2.1 = st'.1 ∧ i.val < st'.1.val ∧ Good s st'.1.val ∧
        sub.view.bytes ++ d.bytes ++ s.bytes.drop (st'.1.val - 1).toNat =
          s.bytes.drop (i.val - 1).toNat)) := by
  have hsm := ncu_small s
  obtain ⟨r, hr, hrc⟩ := hc i hg.1 hg.2.1
  have e1 : (i - ix 1).val = i.val - 1 := sub_val i (ix 1) (by rw [ix1]; omega) (by rw [ix1]; omega)
  obtain ⟨sub, st', h, hP⟩ := loop_step s d fnext limit (s.bytes.length + 1) i n hg r hrc
  refine ⟨sub, st', ?_, hP⟩
  unfold splitIterate
  rw [if_neg (by rw [e1, ncu_val]; omega), hr]
  exact h

theorem splitAll_done (s : JStr) (fnext : Finder) (limit : JInt64) (ke : Bool) (fuel : Nat)
    (st : SplitState) (h : st.1.val = s.bytes.length + 2) : splitAll s fnext limit ke fuel st = .ok [] := by
  have hsm := ncu_small s
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have e : (st.1 - ix 1).val = s.bytes.length + 1 := by
      rw [sub_val _ _ (by rw [ix1]; omega) (by rw [ix1]; omega), ix1, h]; omega
    simp only [splitAll]
    unfold splitIterate
    rw [if_pos (by rw [e, ncu_val]; omega)]

theorem split_all (s d : JStr) (fnext : Finder) (limit : JInt64) (hc : FinderNext s d fnext) :
    ∀ (fuel : Nat) (i n : JInt64), Good s i.val → (s.bytes.length : Int) + 2 - i.val < fuel →
      ∃ ps, splitAll s fnext limit true fuel (i, i, n) = .ok ps ∧ ps ≠ [] ∧
        joinBytes d.bytes (ps.map fun p => p.view.bytes) = s.bytes.drop (i.val - 1).toNat := by
  intro fuel
  induction fuel with
  | zero => intro i n hg hf; omega
  | succ fuel ih =>
    intro i n hg hf
    obtain ⟨sub, st', hst, hcase⟩ := split_step s d fnext limit hc i n hg
    simp only [splitAll, hst]
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · rw [splitAll_done s fnext limit true fuel st' h1]
      exact ⟨[sub], rfl, List.cons_ne_nil _ _, h2⟩
    · obtain ⟨e, k', n'⟩ := st'
      simp only at h1 h2 h3 h4
      subst h1
      obtain ⟨ps, hps, hne, hj⟩ := ih k' n' h3 (by omega)
      rw [hps]
      refine ⟨sub :: ps, rfl, List.cons_ne_nil _ _, ?_⟩
      obtain ⟨q, qs, rfl⟩ := List.exists_cons_of_ne_nil hne
      simp only [List.map_cons, joinBytes] at hj ⊢
      rw [hj]; exact h4

/-- For a delimiter `d` and a splitter whose `findnext` satisfies `FinderNext`,
`join(split(s, d; limit, keepempty=true), d) == s` for every `limit`. -/
def SplitJoin : Prop :=
  ∀ (s d : JStr) (fnext : Finder) (limit : JInt64), FinderNext s d fnext →
    ∃ ps, splitGen s fnext limit true = .ok ps ∧
      joinBytes d.bytes (ps.map fun p => p.view.bytes) = s.bytes

theorem splitJoin_proven : SplitJoin := by
  intro s d fnext limit hc
  have hsm := ncu_small s
  obtain ⟨ps, hps, _, hj⟩ := split_all s d fnext limit hc (s.bytes.length + 2) (ix 1) (ix 0)
    ⟨by simp, by rw [ix1]; omega, fun h => by rw [ix1] at h ⊢; exact valid_one s (by omega)⟩
    (by rw [ix1]; omega)
  exact ⟨ps, hps, by rw [hj]; rfl⟩

/-! ## `split` with `limit ≥ 1` returns at most `limit` pieces -/

theorem splitTail_n (s : JStr) (ke : Bool) (i k n : JInt64) (sub : JSub) (st' : SplitState)
    (h : splitTail s ke i k n = .ok (some (sub, st'))) :
    st'.1 = ncodeunits s + ix 2 ∧ st'.2.2 = n + ix 1 := by
  unfold splitTail at h
  split at h
  · cases h
  · cases hs : substring s i (lastIdx s) false with
    | error e => rw [hs] at h; simp [Except.map] at h
    | ok x =>
      rw [hs] at h
      simp only [Except.map, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨rfl, rfl⟩

theorem splitLoop_n (s : JStr) (fnext : Finder) (limit : JInt64) (ke : Bool) (hl : 1 ≤ limit.val) :
    ∀ (fuel : Nat) (i k n : JInt64) (r : Option (JInt64 × JInt64)) (sub : JSub) (st' : SplitState),
      0 ≤ n.val → n.val ≤ limit.val - 1 →
      splitLoop s fnext limit ke fuel i k n r = .ok (some (sub, st')) →
      st'.2.2.val = n.val + 1 ∧ (n.val + 1 ≤ limit.val - 1 ∨ st'.1.val = s.bytes.length + 2) := by
  have hlim := limit.property.2
  simp only [IntTy.max, IntTy.signed, IntTy.bits] at hlim
  have e1 : (limit - ix 1).val = limit.val - 1 :=
    sub_val _ _ (by rw [ix1]; omega) (by rw [ix1]; simp at hlim; omega)
  have hn1 : ∀ n : JInt64, 0 ≤ n.val → n.val ≤ limit.val - 1 → (n + ix 1).val = n.val + 1 :=
    fun n h1 h2 => add_val _ _ (by rw [ix1]; omega) (by rw [ix1]; simp at hlim; omega)
  have tail : ∀ (i k n : JInt64) (sub : JSub) (st' : SplitState), 0 ≤ n.val → n.val ≤ limit.val - 1 →
      splitTail s ke i k n = .ok (some (sub, st')) →
      st'.2.2.val = n.val + 1 ∧ (n.val + 1 ≤ limit.val - 1 ∨ st'.1.val = s.bytes.length + 2) := by
    intro i k n sub st' h1 h2 h
    obtain ⟨hs1, hs2⟩ := splitTail_n s ke i k n sub st' h
    rw [hs1, hs2]
    exact ⟨hn1 n h1 h2, Or.inr (ncu2_val s)⟩
  intro fuel
  induction fuel with
  | zero => intro i k n r sub st' h1 h2 h; exact tail i k n sub st' h1 h2 h
  | succ fuel ih =>
    intro i k n r sub st' h1 h2 h
    cases r with
    | none => rw [splitLoop_none] at h; exact tail i k n sub st' h1 h2 h
    | some p =>
      obtain ⟨a, b⟩ := p
      simp only [splitLoop] at h
      split at h
      · exact tail i k n sub st' h1 h2 h
      · rename_i hc
        have hne : n.val ≠ limit.val - 1 := by
          intro heq; apply hc; rw [e1]; simp [heq]
        repeat' split at h
        all_goals first
          | (simp at h; done)
          | exact ih _ _ _ _ _ _ h1 h2 h
          | (simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
             obtain ⟨-, rfl⟩ := h
             exact ⟨hn1 n h1 h2, Or.inl (by omega)⟩)

theorem splitIterate_some (s : JStr) (fnext : Finder) (limit : JInt64) (ke : Bool) (i k n : JInt64)
    (sub : JSub) (st' : SplitState) (h : splitIterate s fnext limit ke i k n = .ok (some (sub, st'))) :
    (i - ix 1).val ≤ s.bytes.length ∧
      ∃ r, splitLoop s fnext limit ke (s.bytes.length + 2) i k n r = .ok (some (sub, st')) := by
  unfold splitIterate at h
  split at h
  · cases h
  · rename_i hc
    rw [ncu_val] at hc
    cases hf : fnext k with
    | error e => rw [hf] at h; simp at h
    | ok r => rw [hf] at h; exact ⟨by omega, r, h⟩

theorem splitAll_len (s : JStr) (fnext : Finder) (limit : JInt64) (ke : Bool) (hl : 1 ≤ limit.val) :
    ∀ (fuel : Nat) (st : SplitState) (ps : List JSub), 0 ≤ st.2.2.val →
      (st.2.2.val ≤ limit.val - 1 ∨ (st.2.2.val ≤ limit.val ∧ st.1.val = s.bytes.length + 2)) →
      splitAll s fnext limit ke fuel st = .ok ps → (ps.length : Int) + st.2.2.val ≤ limit.val := by
  have hsm := ncu_small s
  intro fuel
  induction fuel with
  | zero =>
    intro st ps h0 hinv h
    simp only [splitAll] at h
    cases h
    rw [List.length_nil]; omega
  | succ fuel ih =>
    intro st ps h0 hinv h
    simp only [splitAll] at h
    cases hit : splitIterate s fnext limit ke st.1 st.2.1 st.2.2 with
    | error e => rw [hit] at h; simp at h
    | ok o =>
      cases o with
      | none => rw [hit] at h; simp only at h; cases h; rw [List.length_nil]; omega
      | some p =>
        obtain ⟨sub, st'⟩ := p
        rw [hit] at h; simp only at h
        obtain ⟨hle, r, hr⟩ := splitIterate_some s fnext limit ke _ _ _ sub st' hit
        have hn : st.2.2.val ≤ limit.val - 1 := by
          rcases hinv with h' | ⟨_, h'⟩
          · exact h'
          · rw [sub_val _ _ (by rw [ix1]; omega) (by rw [ix1]; omega), ix1, h'] at hle; omega
        obtain ⟨hn', hor⟩ := splitLoop_n s fnext limit ke hl _ _ _ _ r sub st' h0 hn hr
        cases hrest : splitAll s fnext limit ke fuel st' with
        | error e => rw [hrest] at h; simp [Except.map] at h
        | ok ps' =>
          rw [hrest] at h
          simp only [Except.map, Except.ok.injEq] at h
          subst h
          have := ih st' ps' (by omega)
            (by rcases hor with h' | h'
                · exact Or.inl (by omega)
                · exact Or.inr ⟨by omega, h'⟩) hrest
          rw [List.length_cons]; omega

/-- `split(s, dlm; limit, keepempty)` with `limit ≥ 1` returns at most `limit`
pieces, for every splitter and every `keepempty`. -/
def SplitLimit : Prop :=
  ∀ (s : JStr) (fnext : Finder) (limit : JInt64) (keepempty : Bool) (ps : List JSub),
    1 ≤ limit.val → splitGen s fnext limit keepempty = .ok ps → (ps.length : Int) ≤ limit.val

theorem splitLimit_proven : SplitLimit := by
  intro s fnext limit ke ps hl h
  have := splitAll_len s fnext limit ke hl _ _ ps (by simp) (Or.inl (by simp; omega)) h
  simp only [ix0] at this
  omega

/-! ## `rsplit`: joining the pieces with the delimiter gives the string back -/

/-- A position `to` of the right-to-left iteration: `0` or a valid index. -/
abbrev GoodTo (s : JStr) (t : Int) : Prop := t = 0 ∨ validZ s t

/-- One past the last byte of the character at `t` (`1` for `t = 0`). -/
def Ez (s : JStr) (t : Int) : Int := if t = 0 then 1 else nextZ s t

theorem prefix_sub (s : JStr) (to : JInt64) (hg : GoodTo s to.val) :
    ∃ sub, substring s (ix 1) to = .ok sub ∧ sub.view.bytes = s.bytes.take (Ez s to.val - 1).toNat := by
  have hsm := ncu_small s
  rcases hg with h0 | hv
  · refine ⟨_, split_substring_empty s (ix 1) to true (by rw [h0]; simp), ?_⟩
    rw [split_view_empty]; simp [Ez, h0]
  · obtain ⟨e, he, hev⟩ := nextind_mid s to hv.1 hv.2.1
    have hb := (nextZ_spec s to.val hv.1 hv.2.1).2.1
    have hlo := (nextZ_spec s to.val hv.1 hv.2.1).1
    rw [← hev] at hb hlo
    refine ⟨_, substring_checked s (ix 1) to e (by simp) (by rw [ix1]; exact hv.1) hv.2.1
      ((isvalidAt_iff s _).2 (by rw [ix1]; exact valid_one s (by have := hv.2.1; omega)))
      ((isvalidAt_iff s to).2 hv) he, ?_⟩
    have hE : Ez s to.val = e.val := by simp only [Ez]; rw [if_neg (by omega), hev]
    rw [view_bytes, sub_val (ix 1) (ix 1) (by simp) (by simp),
      sub_val e (ix 1) (by rw [ix1]; omega) (by rw [ix1]; omega), ix1, hE]
    simp

theorem rsplitIterate_of_res (s : JStr) (fprev : Finder) (to rem frm nt : JInt64) (sub : JSub)
    (h0 : 0 ≤ to.val) (hres : rsplitRes s fprev true to rem = .ok (frm, nt, to))
    (hsub : substring s frm to = .ok sub) :
    rsplitIterate s fprev true to rem = .ok (some (sub, (nt, rem - ix 1))) := by
  unfold rsplitIterate
  rw [if_neg (by omega), hres]
  simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hsub] <;> rfl

theorem rsplit_step (s d : JStr) (fprev : Finder) (hc : FinderPrev s d fprev) (to rem : JInt64)
    (hg : GoodTo s to.val) :
    ∃ sub nt, rsplitIterate s fprev true to rem = .ok (some (sub, (nt, rem - ix 1))) ∧
      ((nt.val = -1 ∧ sub.view.bytes = s.bytes.take (Ez s to.val - 1).toNat) ∨
       (GoodTo s nt.val ∧ nt.val < to.val ∧
        s.bytes.take (Ez s nt.val - 1).toNat ++ d.bytes ++ sub.view.bytes =
          s.bytes.take (Ez s to.val - 1).toNat)) := by
  have hsm := ncu_small s
  have hto0 : 0 ≤ to.val ∧ to.val ≤ s.bytes.length := by
    rcases hg with h | h
    · omega
    · exact ⟨by have := h.1; omega, h.2.1⟩
  obtain ⟨sub0, hs0, hb0⟩ := prefix_sub s to hg
  have whole : rsplitRes s fprev true to rem = .ok (ix 1, ix (-1), to) →
      ∃ sub nt, rsplitIterate s fprev true to rem = .ok (some (sub, (nt, rem - ix 1))) ∧
      ((nt.val = -1 ∧ sub.view.bytes = s.bytes.take (Ez s to.val - 1).toNat) ∨
       (GoodTo s nt.val ∧ nt.val < to.val ∧
        s.bytes.take (Ez s nt.val - 1).toNat ++ d.bytes ++ sub.view.bytes =
          s.bytes.take (Ez s to.val - 1).toNat)) := fun hres =>
    ⟨sub0, ix (-1), rsplitIterate_of_res s fprev to rem _ _ _ hto0.1 hres hs0, Or.inl ⟨rfl, hb0⟩⟩
  by_cases hrem : rem.val = 0
  · exact whole (by unfold rsplitRes; rw [if_pos hrem])
  · obtain ⟨r, hr, hrc⟩ := hc to hto0.1 hto0.2
    cases r with
    | none => exact whole (by unfold rsplitRes; rw [if_neg hrem, rsplitLoop, hr])
    | some p =>
      obtain ⟨a, b⟩ := p
      obtain ⟨hbt, hab, hva, hvb, hd⟩ := hrc a b rfl
      have hva' := (isvalidAt_iff s a).1 hva
      have hvb' := (isvalidAt_iff s b).1 hvb
      obtain ⟨e, he, hev⟩ := nextind_mid s b hvb'.1 hvb'.2.1
      have hnv := nextZ_nextValid s b.val hvb'.1 hvb'.2.1
      rw [← hev] at hnv
      obtain ⟨n1, n2, n3, n4⟩ := hnv
      obtain ⟨pa, hpa, hpac⟩ := prevind_valid s a hva'
      have hc1 : (decide (b.val < a.val) && decide (to.val < 2)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      have hres : rsplitRes s fprev true to rem = .ok (e, pa, to) := by
        unfold rsplitRes; rw [if_neg hrem, rsplitLoop, hr]
        simp only [he, hc1, Bool.false_eq_true, ↓reduceIte, hpa, Bool.not_true, Bool.and_false] <;> rfl
      have hEpa : Ez s pa.val = a.val ∧ GoodTo s pa.val ∧ pa.val < a.val := by
        rcases hpac with ⟨h1, h0⟩ | ⟨_, hp, hnx⟩
        · exact ⟨by simp [Ez, h0, h1], Or.inl h0, by omega⟩
        · obtain ⟨j, hj, hjv⟩ := nextind_mid s pa hp.2.2.1.1 hp.2.2.1.2.1
          have ej : j = a := Except.ok.inj (hj.symm.trans hnx)
          refine ⟨?_, Or.inr hp.2.2.1, hp.2.1⟩
          simp only [Ez]; rw [if_neg (by have := hp.1; omega), ← hjv, ej]
      have hto1 : to.val ≠ 0 := by omega
      have hvto : validZ s to.val := hg.elim (fun h => absurd h hto1) id
      have hd' := hd e he
      by_cases hgt : e.val > to.val
      · have hteq : to.val = b.val := by
          refine Classical.byContradiction fun hne => ?_
          exact n3 to.val (by omega) hgt hvto
        have hEto : Ez s to.val = e.val := by simp only [Ez]; rw [if_neg hto1, hteq, hev]
        refine ⟨_, pa, rsplitIterate_of_res s fprev to rem e pa _ hto0.1 hres
          (split_substring_empty s e to true hgt), Or.inr ⟨hEpa.2.1, by omega, ?_⟩⟩
        rw [split_view_empty, List.append_nil, hEpa.1, hEto, ← hd',
          show (e.val - a.val).toNat = (e.val - 1).toNat - (a.val - 1).toNat by omega,
          take_seg _ _ _ (by omega)]
      · obtain ⟨e', he', hev'⟩ := nextind_mid s to hvto.1 hvto.2.1
        have hb' := (nextZ_spec s to.val hvto.1 hvto.2.1).2.1
        have hlo' := (nextZ_spec s to.val hvto.1 hvto.2.1).1
        rw [← hev'] at hb' hlo'
        have hEto : Ez s to.val = e'.val := by simp only [Ez]; rw [if_neg hto1, hev']
        have hsub := substring_checked s e to e' (by omega) (by omega) hvto.2.1
          ((isvalidAt_iff s e).2 (n4 (by omega))) ((isvalidAt_iff s to).2 hvto) he'
        refine ⟨_, pa, rsplitIterate_of_res s fprev to rem e pa _ hto0.1 hres hsub,
          Or.inr ⟨hEpa.2.1, by omega, ?_⟩⟩
        rw [view_bytes, sub_val e (ix 1) (by rw [ix1]; omega) (by rw [ix1]; omega), ix1,
          sub_val e' e (by omega) (by omega), hEpa.1, hEto, ← hd',
          show (e.val - a.val).toNat = (e.val - 1).toNat - (a.val - 1).toNat by omega,
          show (e'.val - e.val).toNat = (e'.val - 1).toNat - (e.val - 1).toNat by omega,
          take_seg _ _ _ (by omega), take_seg _ _ _ (by omega)]

theorem rsplitAll_done (s : JStr) (fprev : Finder) (ke : Bool) (fuel : Nat) (st : JInt64 × JInt64)
    (h : st.1.val < 0) : rsplitAll s fprev ke fuel st = .ok [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    simp only [rsplitAll]
    unfold rsplitIterate
    rw [if_pos h]

theorem rsplit_all (s d : JStr) (fprev : Finder) (hc : FinderPrev s d fprev) :
    ∀ (fuel : Nat) (to rem : JInt64), GoodTo s to.val → to.val + 1 < fuel →
      ∃ ps, rsplitAll s fprev true fuel (to, rem) = .ok ps ∧ ps ≠ [] ∧
        joinBytes d.bytes (ps.reverse.map fun p => p.view.bytes) =
          s.bytes.take (Ez s to.val - 1).toNat := by
  intro fuel
  induction fuel with
  | zero => intro to rem hg hf; rcases hg with h | h <;> omega
  | succ fuel ih =>
    intro to rem hg hf
    obtain ⟨sub, nt, hst, hcase⟩ := rsplit_step s d fprev hc to rem hg
    simp only [rsplitAll, hst]
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · rw [rsplitAll_done s fprev true fuel (nt, rem - ix 1) (by simp only; omega)]
      exact ⟨[sub], rfl, List.cons_ne_nil _ _, h2⟩
    · obtain ⟨ps, hps, hne, hj⟩ := ih nt (rem - ix 1) h1 (by omega)
      rw [hps]
      refine ⟨sub :: ps, rfl, List.cons_ne_nil _ _, ?_⟩
      rw [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        joinBytes_snoc d.bytes ((ps.reverse).map fun p => p.view.bytes) sub.view.bytes
          (by simpa using hne), hj, h3]

/-- For a delimiter `d` and a splitter whose `findprev` satisfies `FinderPrev`,
`join(rsplit(s, d; limit, keepempty=true), d) == s` for every `limit`. -/
def RsplitJoin : Prop :=
  ∀ (s d : JStr) (fprev : Finder) (limit : JInt64), FinderPrev s d fprev →
    ∃ ps, rsplitGen s fprev limit true = .ok ps ∧
      joinBytes d.bytes (ps.map fun p => p.view.bytes) = s.bytes

theorem rsplitJoin_proven : RsplitJoin := by
  intro s d fprev limit hc
  have hsm := ncu_small s
  have hlast : GoodTo s (lastIdx s).val ∧ (lastIdx s).val ≤ s.bytes.length ∧
      Ez s (lastIdx s).val = s.bytes.length + 1 := by
    by_cases hn : s.bytes.length = 0
    · rw [lastIdx_zero s hn]; exact ⟨Or.inl rfl, by omega, by simp [Ez, hn]⟩
    · obtain ⟨hL, hLv, e, he, hev⟩ := lastIdx_pos s (by omega)
      have h1 := hLv.1
      obtain ⟨j, hj, hjv⟩ := nextind_mid s (lastIdx s) (by omega) (by rw [hL]; exact hLv.2.1)
      have ej : j = e := Except.ok.inj (hj.symm.trans he)
      refine ⟨Or.inr (by rw [hL]; exact hLv), by rw [hL]; exact hLv.2.1, ?_⟩
      simp only [Ez]; rw [if_neg (by omega), ← hjv, ej, hev]
  obtain ⟨ps, hps, _, hj⟩ := rsplit_all s d fprev hc (s.bytes.length + 2) (lastIdx s)
    (limit - ix 1) hlast.1 (by omega)
  refine ⟨ps.reverse, by unfold rsplitGen; rw [hps]; rfl, ?_⟩
  rw [hj, hlast.2.2]
  apply List.take_of_length_le
  omega

/-! ## Refuted: integer types for `limit` -/

/-- `split(s, dlm; limit)` accepts every integer type for `limit`
(`limit::Integer`, `base/strings/util.jl:930,958-959`): a `limit` of integer type
`t` whose value fits in `Int` behaves as `Int(limit)`. -/
def SplitLimitInteger : Prop :=
  ∀ (s : JStr) (fnext : Finder) (t : IntTy) (limit : JInt t) (keepempty : Bool),
    -(2 ^ 63) ≤ limit.val → limit.val < 2 ^ 63 →
    eachsplitTyped s fnext t limit keepempty = splitGen s fnext (ix limit.val) keepempty

/-- `"a,b,c"`. -/
def strACommas : JStr := ⟨[0x61, 0x2c, 0x62, 0x2c, 0x63], by decide⟩

theorem splitLimitInteger_refuted : ¬ SplitLimitInteger := by
  intro h
  have := congrArg (okSat fun _ => true)
    (h strACommas (charFinder 0x2c000000 strACommas) .u64 (JInt.lit .u64 2) true (by decide) (by decide))
  revert this; decide

/-- Registry entries of `split`/`rsplit`. -/
def splitEntries : List Entry := []

end JuliaLean.StringUtil
