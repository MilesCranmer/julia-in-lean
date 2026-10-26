import JuliaLean.IteratorsCov.TakeDrop

/-!
# `Filter`, `Accumulate`, `Rest`, `TakeWhile`, `DropWhile`
(base/iterators.jl:528-739, 895-990)

Predicates are Julia functions returning `Bool` (`V → Bool`); the model's
`fuel` bounds the `while` loops of `Filter` and `DropWhile` (running out is
`E.fuel`, never a Julia result).
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-! ## `Filter` -/

/-- The loop of `iterate(f::Filter, state...)`, base/iterators.jl:578-592:
`while y !== nothing; v, s = y; f.flt(v) && return (v, s); y = iterate(f.itr, s); end`. -/
def filterLoop (p : V → Bool) (nx : V → Step) : Nat → Step → Step
  | _, .ok none => .ok none
  | _, .error e => .error e
  | 0, .ok (some _) => .error .fuel
  | k + 1, .ok (some (v, s)) => if p v then .ok (some (v, s)) else filterLoop p nx k (nx s)

/-- The object `filter(flt, itr) = Filter(flt, itr)` (576) with `iterate`
(578-592), `eltype` and `IteratorEltype` of `I` (594-595) and `IteratorSize`
`SizeUnknown()` (596). -/
def filterIt (fuel : Nat) (p : V → Bool) (it : It) : It where
  first := filterLoop p it.next fuel it.first
  next := fun s => filterLoop p it.next fuel (it.next s)
  isz := .sizeUnknown
  iel := it.iel
  elt := it.elt

/-- `reverse(f::Filter) = Filter(f.flt, reverse(f.itr))` (598) given the
reversed wrapped iterator `rit`, and `last(f::Filter) = first(reverse(f))` (599). -/
def filterLast (fuel : Nat) (p : V → Bool) (rit : It) : R V :=
  (filterIt fuel p rit).first.bind fun
    | some (x, _) => .ok x
    | none => jthrow (.argumentError "collection must be non-empty")

theorem filter_YF (p : V → Bool) (nx : V → Step) (k : Nat) {y : Step} {xs : List V}
    (h : YF nx y xs) : ∀ j, xs.length < j → j ≤ k →
      YF (fun s => filterLoop p nx k (nx s)) (filterLoop p nx j y) (xs.filter p) := by
  induction h with
  | nil => intro j _ _; cases j <;> exact .nil
  | @cons x s xs _ ih =>
    intro j hj hjk
    simp only [List.length_cons] at hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    show YF _ (if p x then .ok (some (x, s)) else filterLoop p nx j (nx s)) _
    by_cases hp : p x
    · rw [if_pos hp, List.filter_cons_of_pos hp]
      exact .cons (ih k (by omega) (Nat.le_refl _))
    · rw [if_neg hp, List.filter_cons_of_neg hp]
      exact ih j (by omega) (by omega)

theorem filter_PF_inner (p : V → Bool) (nx : V → Step) (k : Nat) :
    ∀ (zs : List V) (j : Nat) (y : Step),
      PF (fun s => filterLoop p nx k (nx s)) (filterLoop p nx j y) zs →
        ∃ xs, PF nx y xs ∧ ∀ z ∈ zs, z ∈ xs := by
  intro zs
  induction zs with
  | nil => intro _ _ _; exact ⟨[], .nil, by simp⟩
  | cons z zs ih =>
    intro j
    induction j with
    | zero =>
      intro y h
      match y, h with
      | .ok none, h => cases h
      | .error _, h => cases h
      | .ok (some _), h => cases h
    | succ j ihj =>
      intro y h
      match y, h with
      | .ok none, h => cases h
      | .error _, h => cases h
      | .ok (some (v, s)), h =>
        by_cases hp : p v
        · have h' : PF (fun s => filterLoop p nx k (nx s)) (.ok (some (v, s))) (z :: zs) := by
            have : filterLoop p nx (j + 1) (.ok (some (v, s))) = .ok (some (v, s)) := by
              simp [filterLoop, hp]
            rw [← this]; exact h
          have h3 : z = v ∧ PF (fun s => filterLoop p nx k (nx s)) (filterLoop p nx k (nx s)) zs := by
            cases h' with
            | cons h'' => exact ⟨rfl, h''⟩
          obtain ⟨rfl, h''⟩ := h3
          obtain ⟨xs, hxs, hm⟩ := ih k (nx s) h''
          refine ⟨_ :: xs, .cons hxs, ?_⟩
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (hm w hw)
        · have : filterLoop p nx (j + 1) (.ok (some (v, s))) = filterLoop p nx j (nx s) := by
            simp [filterLoop, hp]
          rw [this] at h
          obtain ⟨xs, hxs, hm⟩ := ihj (nx s) h
          exact ⟨v :: xs, .cons hxs, fun w hw => List.mem_cons_of_mem _ (hm w hw)⟩

/-- `Iterators.filter(flt, itr)` yields the elements of `itr` for which `flt`
is true, in order (base/iterators.jl:536-575), its `eltype` is truthful
whenever `itr`'s is, and `last(filter(flt, itr))` is the last such element
when `Iterators.reverse(itr)` yields `itr` backwards. -/
def FilterSound : Prop :=
  ∀ (p : V → Bool) (it : It) (fuel : Nat),
    (∀ xs, it.Yields xs → xs.length < fuel → (filterIt fuel p it).Yields (xs.filter p)) ∧
    (it.EltSound → (filterIt fuel p it).EltSound) ∧
    (∀ (rit : It) (xs : List V) (x : V), rit.Yields xs.reverse → xs.length < fuel →
      (xs.filter p).getLast? = some x →
      filterLast fuel p rit = .ok x)

theorem filterSound : FilterSound := by
  intro p it fuel
  refine ⟨?_, ?_, ?_⟩
  · intro xs hy hl
    exact filter_YF p it.next fuel hy fuel hl (Nat.le_refl _)
  · intro hE hiel zs hp z hz
    obtain ⟨xs, hxs, hm⟩ := filter_PF_inner p it.next fuel zs fuel it.first hp
    exact hE hiel xs hxs z (hm z hz)
  · intro rit xs x hr hl hx
    have hy := filter_YF p rit.next fuel hr fuel (by simpa using hl) (Nat.le_refl _)
    have e : (xs.reverse.filter p) = x :: ((xs.filter p).dropLast).reverse := by
      rw [List.filter_reverse]
      obtain ⟨l, hl'⟩ : ∃ l, xs.filter p = l ++ [x] := by
        exact List.getLast?_eq_some_iff.mp hx
      rw [hl']; simp
    rw [e] at hy
    show (filterLoop p rit.next fuel rit.first).bind _ = _
    generalize filterLoop p rit.next fuel rit.first = y at hy ⊢
    cases hy with
    | cons _ => rfl

/-! ## `Accumulate` -/

/-- `Base.BottomRF(op)(acc, x)`: `reduce_first(op, x)` (here `rf x`) when there
is no `init` (`acc` is `Base._InitialValue()`), otherwise `op(acc, x)`
(base/reduce.jl:85-90). -/
def bottomRF (op : V → V → V) (rf : V → V) : Option V → V → V
  | none, x => rf x
  | some a, x => op a x

/-- `iterate(itr::Accumulate)`, base/iterators.jl:643-650. -/
def accFirst (op : V → V → V) (rf : V → V) (init : Option V) : Step → Step
  | .ok none => .ok none
  | .ok (some (x, s)) => let v := bottomRF op rf init x; .ok (some (v, .tup [v, s]))
  | .error e => .error e

/-- The tail of `iterate(itr::Accumulate, state)`, base/iterators.jl:652-659,
on `nxt = iterate(itr.itr, state[2])`: `val = itr.f(state[1], nxt[1])`. -/
def accCont (op : V → V → V) (a : V) : Step → Step
  | .ok none => .ok none
  | .ok (some (x, s')) => let v := op a x; .ok (some (v, .tup [v, s']))
  | .error e => .error e

/-- `iterate(itr::Accumulate, state)`, base/iterators.jl:652-659. -/
def accNext (op : V → V → V) (it : It) : V → Step
  | .tup [a, s] => accCont op a (it.next s)
  | _ => jthrow (.methodError "iterate")

/-- `Iterators.accumulate(f, itr; init)` (641) with `iterate` (643-659),
`length` (661), `size` (662), `IteratorSize` of `I` (664) and
`IteratorEltype` `EltypeUnknown()` (665). -/
def accIt (op : V → V → V) (rf : V → V) (init : Option V) (it : It) : It where
  first := accFirst op rf init it.first
  next := accNext op it
  isz := it.isz
  iel := false
  len := it.len
  size := it.size

/-- Running reductions from accumulator `a`. -/
def accFrom (op : V → V → V) : V → List V → List V
  | _, [] => []
  | a, x :: xs => op a x :: accFrom op (op a x) xs

/-- The documented elements of `Iterators.accumulate`. -/
def accSpec (op : V → V → V) (rf : V → V) : Option V → List V → List V
  | _, [] => []
  | init, x :: xs => bottomRF op rf init x :: accFrom op (bottomRF op rf init x) xs

theorem acc_YF (op : V → V → V) (it : It) {y : Step} {xs : List V} (h : YF it.next y xs) :
    ∀ a, YF (accNext op it) (accCont op a y) (accFrom op a xs) := by
  induction h with
  | nil => intro a; exact .nil
  | @cons x s xs _ ih => intro a; exact .cons (ih (op a x))

/-- `Iterators.accumulate(f, itr; init)` yields the running reductions: the
first element is `Base.BottomRF(f)(init, x₁)` (`reduce_first(f, x₁)` without
`init`, `f(init, x₁)` with it) and each further element is `f(previous, xᵢ)`
(base/iterators.jl:612-641); its `IteratorSize`, `length` and `size` are
those of `itr`, so they stay truthful. -/
def AccumulateSound : Prop :=
  ∀ (op : V → V → V) (rf : V → V) (init : Option V) (it : It),
    (∀ xs, it.Yields xs → (accIt op rf init it).Yields (accSpec op rf init xs)) ∧
    (it.SizeSound → ∀ xs, it.Yields xs → (accIt op rf init it).isz.finite = true →
      (accIt op rf init it).len = .ok (i64 (accSpec op rf init xs).length))

theorem accSpec_length (op : V → V → V) (rf : V → V) (init : Option V) (xs : List V) :
    (accSpec op rf init xs).length = xs.length := by
  have : ∀ a (ys : List V), (accFrom op a ys).length = ys.length := by
    intro a ys
    induction ys generalizing a with
    | nil => rfl
    | cons y ys ih => simp [accFrom, ih]
  cases xs with
  | nil => rfl
  | cons x xs => simp [accSpec, this]

theorem accumulateSound : AccumulateSound := by
  intro op rf init it
  refine ⟨?_, ?_⟩
  · intro xs hy
    unfold It.Yields at hy ⊢
    show YF _ (accFirst op rf init it.first) _
    generalize it.first = y at hy ⊢
    cases hy with
    | nil => exact .nil
    | @cons x s xs h => exact .cons (acc_YF op it h _)
  · intro hS xs hy hf
    obtain ⟨ys, hys, _, hl⟩ := hS.1 hf
    rw [YF.unique hy hys, accSpec_length]
    exact hl

/-! ## `Rest` -/

/-- An `Iterators.Rest` object: the wrapped iterator and the start state. -/
structure RestObj where
  itr : It
  st : V

/-- `rest(itr, state) = Rest(itr, state)` (696) and `rest(itr::Rest, state) =
Rest(itr.itr, state)` (697): a `Rest` argument is rebased. -/
def mkRest : Sum It RestObj → V → RestObj
  | .inl itr, s => ⟨itr, s⟩
  | .inr r, s => ⟨r.itr, s⟩

/-- `rest(itr) = itr`, base/iterators.jl:698. -/
def rest1 (itr : It) : It := itr

/-- `rest_iteratorsize`, base/iterators.jl:737-738. -/
def restIsz : Isz → Isz
  | .isInfinite => .isInfinite
  | _ => .sizeUnknown

/-- The iterator of a `Rest`: `iterate(i::Rest, st=i.st) = iterate(i.itr, st)`
(732), `eltype`/`IteratorEltype` of `I` (735-736), `IteratorSize` (739). -/
def RestObj.it (r : RestObj) : It where
  first := r.itr.next r.st
  next := r.itr.next
  isz := restIsz r.itr.isz
  iel := r.itr.iel
  elt := r.itr.elt

theorem RF.pre_append {nx : V → Step} {y : Step} {s : V} (h : RF nx y s) :
    ∀ ys, PF nx (nx s) ys → ∃ pre, PF nx y (pre ++ ys) := by
  induction h with
  | @here x s =>
    intro ys hp
    exact ⟨[x], .cons hp⟩
  | @step y s x s' _ hn ih =>
    intro ys hp
    obtain ⟨pre, hpre⟩ := ih (x :: ys) (by rw [hn]; exact .cons hp)
    exact ⟨pre ++ [x], by simpa using hpre⟩

theorem RF.endless {nx : V → Step} {y : Step} {s : V} (h : RF nx y s)
    (hE : ∀ n, ∃ xs : List V, xs.length = n ∧ PF nx y xs) :
    ∀ n, ∃ xs : List V, xs.length = n ∧ PF nx (nx s) xs := by
  induction h with
  | @here x s =>
    intro n
    obtain ⟨xs, hl, hp⟩ := hE (n + 1)
    cases hp with
    | nil => simp at hl
    | cons hp' => exact ⟨_, by simpa using hl, hp'⟩
  | @step y s x s' _ hn ih =>
    intro n
    obtain ⟨xs, hl, hp⟩ := ih hE (n + 1)
    rw [hn] at hp
    cases hp with
    | nil => simp at hl
    | cons hp' => exact ⟨_, by simpa using hl, hp'⟩

/-- `Iterators.rest(itr, state)` yields what `itr` yields after `state`, for
every state reached by iterating `itr` (base/iterators.jl:677-695);
`rest(rest(itr, s₀), s)` is `rest(itr, s)` and `rest(itr)` is `itr`; its
`IteratorSize` (`SizeUnknown`, or `IsInfinite` for an infinite `itr`) and
`eltype` are truthful whenever `itr`'s are. -/
def RestSound : Prop :=
  ∀ (it : It) (s : V), RF it.next it.first s →
    (∀ ys, YF it.next (it.next s) ys → (mkRest (.inl it) s).it.Yields ys) ∧
    (∀ s0, mkRest (.inr ⟨it, s0⟩) s = mkRest (.inl it) s) ∧
    rest1 it = it ∧
    (it.SizeSound → (mkRest (.inl it) s).it.SizeSound) ∧
    (it.EltSound → (mkRest (.inl it) s).it.EltSound)

theorem restSound : RestSound := by
  intro it s hr
  refine ⟨fun ys h => h, fun _ => rfl, rfl, ?_, ?_⟩
  · intro hS
    refine ⟨?_, ?_, ?_⟩
    · intro hf
      cases hiz : it.isz <;> simp [RestObj.it, mkRest, restIsz, hiz, Isz.finite] at hf
    · intro m hm
      cases hiz : it.isz <;> simp [RestObj.it, mkRest, restIsz, hiz] at hm
    · intro hi
      have : it.isz = .isInfinite := by
        cases hiz : it.isz <;> simp [RestObj.it, mkRest, restIsz, hiz] at hi ⊢
      exact RF.endless hr (hS.2.2 this)
  · intro hE hiel ys hp y hy
    obtain ⟨pre, hpre⟩ := RF.pre_append hr ys hp
    exact hE hiel _ hpre y (List.mem_append_right _ hy)

/-! ## `TakeWhile`, `DropWhile` -/

/-- `iterate(ibl::TakeWhile, itr...)`, base/iterators.jl:930-935. -/
def twCont (p : V → Bool) : Step → Step
  | .ok none => .ok none
  | .ok (some (v, s)) => if p v then .ok (some (v, s)) else .ok none
  | .error e => .error e

/-- `takewhile(pred, xs) = TakeWhile(pred, xs)` (928) with `iterate`
(930-935), `IteratorSize` `SizeUnknown()` (937), `eltype` and
`IteratorEltype` of `I` (938-939). -/
def takeWhileIt (p : V → Bool) (it : It) : It where
  first := twCont p it.first
  next := fun s => twCont p (it.next s)
  isz := .sizeUnknown
  iel := it.iel
  elt := it.elt

/-- The loop of `iterate(ibl::DropWhile)`, base/iterators.jl:979-986. -/
def dwLoop (p : V → Bool) (nx : V → Step) : Nat → Step → Step
  | _, .ok none => .ok none
  | _, .error e => .error e
  | 0, .ok (some _) => .error .fuel
  | k + 1, .ok (some (v, s)) => if p v then dwLoop p nx k (nx s) else .ok (some (v, s))

/-- `dropwhile(pred, itr) = DropWhile(pred, itr)` (976) with
`iterate(ibl, itr) = iterate(ibl.xs, itr)` (978), `iterate(ibl)` (979-986),
`IteratorSize` `SizeUnknown()` (988), `eltype` and `IteratorEltype` (989-990). -/
def dropWhileIt (fuel : Nat) (p : V → Bool) (it : It) : It where
  first := dwLoop p it.next fuel it.first
  next := it.next
  isz := .sizeUnknown
  iel := it.iel
  elt := it.elt

theorem tw_YF (p : V → Bool) (nx : V → Step) {y : Step} {xs : List V} (h : YF nx y xs) :
    YF (fun s => twCont p (nx s)) (twCont p y) (xs.takeWhile p) := by
  induction h with
  | nil => exact .nil
  | @cons x s xs _ ih =>
    show YF _ (if p x then .ok (some (x, s)) else .ok none) _
    by_cases hp : p x
    · rw [if_pos hp, List.takeWhile_cons_of_pos hp]; exact .cons ih
    · rw [if_neg hp, List.takeWhile_cons_of_neg hp]; exact .nil

theorem tw_PF_inner (p : V → Bool) (nx : V → Step) : ∀ (zs : List V) (y : Step),
    PF (fun s => twCont p (nx s)) (twCont p y) zs → PF nx y zs := by
  intro zs
  induction zs with
  | nil => intro _ _; exact .nil
  | cons z zs ih =>
    intro y h
    match y, h with
    | .ok none, h => cases h
    | .error _, h => cases h
    | .ok (some (v, s)), h =>
      by_cases hp : p v
      · have : twCont p (.ok (some (v, s))) = .ok (some (v, s)) := by simp [twCont, hp]
        rw [this] at h
        cases h with
        | cons h' => exact .cons (ih _ h')
      · have : twCont p (.ok (some (v, s))) = .ok none := by simp [twCont, hp]
        rw [this] at h
        cases h

theorem dw_YF (p : V → Bool) (nx : V → Step) : ∀ (k : Nat) {y : Step} {xs : List V},
    YF nx y xs → xs.length < k → YF nx (dwLoop p nx k y) (xs.dropWhile p) := by
  intro k
  induction k with
  | zero => intro y xs _ hl; simp at hl
  | succ k ih =>
    intro y xs h hl
    cases h with
    | nil => exact .nil
    | @cons x s xs h' =>
      show YF nx (if p x then dwLoop p nx k (nx s) else .ok (some (x, s))) _
      by_cases hp : p x
      · rw [if_pos hp, List.dropWhile_cons_of_pos hp]
        exact ih h' (by simp at hl; omega)
      · rw [if_neg hp, List.dropWhile_cons_of_neg hp]
        exact .cons h'

theorem dw_PF_inner (p : V → Bool) (nx : V → Step) : ∀ (k : Nat) (y : Step) (zs : List V),
    PF nx (dwLoop p nx k y) zs → ∃ pre, PF nx y (pre ++ zs) := by
  intro k
  induction k with
  | zero =>
    intro y zs h
    match y, h with
    | .ok none, h => exact ⟨[], h⟩
    | .error _, h => exact ⟨[], h⟩
    | .ok (some _), h =>
      cases zs with
      | nil => exact ⟨[], .nil⟩
      | cons _ _ => cases h
  | succ k ih =>
    intro y zs h
    match y, h with
    | .ok none, h => exact ⟨[], h⟩
    | .error _, h => exact ⟨[], h⟩
    | .ok (some (v, s)), h =>
      by_cases hp : p v
      · have : dwLoop p nx (k + 1) (.ok (some (v, s))) = dwLoop p nx k (nx s) := by
          simp [dwLoop, hp]
        rw [this] at h
        obtain ⟨pre, hpre⟩ := ih _ _ h
        exact ⟨v :: pre, .cons hpre⟩
      · have : dwLoop p nx (k + 1) (.ok (some (v, s))) = .ok (some (v, s)) := by
          simp [dwLoop, hp]
        rw [this] at h
        exact ⟨[], h⟩

/-- `Iterators.takewhile(pred, itr)` yields the longest prefix of `itr` whose
elements satisfy `pred`, and `Iterators.dropwhile(pred, itr)` the rest
(base/iterators.jl:905-927, 952-975); both keep a truthful `eltype`. -/
def WhileSound : Prop :=
  ∀ (p : V → Bool) (it : It) (fuel : Nat),
    (∀ xs, it.Yields xs → (takeWhileIt p it).Yields (xs.takeWhile p)) ∧
    (∀ xs, it.Yields xs → xs.length < fuel → (dropWhileIt fuel p it).Yields (xs.dropWhile p)) ∧
    (it.EltSound → (takeWhileIt p it).EltSound ∧ (dropWhileIt fuel p it).EltSound)

theorem whileSound : WhileSound := by
  intro p it fuel
  refine ⟨fun xs h => tw_YF p it.next h, fun xs h hl => dw_YF p it.next fuel h hl, ?_⟩
  intro hE
  constructor
  · intro hiel zs hp z hz
    exact hE hiel zs (tw_PF_inner p it.next zs it.first hp) z hz
  · intro hiel zs hp z hz
    obtain ⟨pre, hpre⟩ := dw_PF_inner p it.next fuel it.first zs hp
    exact hE hiel _ hpre z (List.mem_append_right _ hz)

end JuliaLean.IteratorsCov
