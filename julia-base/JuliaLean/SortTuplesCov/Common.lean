import JuliaLean.Tuples.ProofsBasic

/-! Shared lemmas of the `SortTuplesCov` area about the tuple model's primitives. -/

namespace JuliaLean.SortTuplesCov

open JuliaLean
open JuliaLean.Tuples (R Err getfield bounds Ops Lawful)

variable {V : Type}

theorem i64_min_eq : IntTy.i64.min = -9223372036854775808 := by decide
theorem i64_max_eq : IntTy.i64.max = 9223372036854775807 := by decide

theorem wrap_i64_val (x : Int) (h1 : -9223372036854775808 ≤ x) (h2 : x ≤ 9223372036854775807) :
    (JInt.wrap .i64 x).val = x :=
  wrapInt_of_inRange .i64 x ⟨by rw [i64_min_eq]; exact h1, by rw [i64_max_eq]; exact h2⟩

theorem lit_i64_val (x : Int) (h1 : -9223372036854775808 ≤ x) (h2 : x ≤ 9223372036854775807) :
    (JInt.lit .i64 x).val = x := wrap_i64_val x h1 h2

theorem add_i64_val (a b : JInt .i64) (h1 : -9223372036854775808 ≤ a.val + b.val)
    (h2 : a.val + b.val ≤ 9223372036854775807) : (a + b).val = a.val + b.val :=
  wrap_i64_val _ h1 h2

theorem sub_i64_val (a b : JInt .i64) (h1 : -9223372036854775808 ≤ a.val - b.val)
    (h2 : a.val - b.val ≤ 9223372036854775807) : (a - b).val = a.val - b.val :=
  wrap_i64_val _ h1 h2

theorem convert_i64_ok (x : Int) (h1 : -9223372036854775808 ≤ x) (h2 : x ≤ 9223372036854775807) :
    JInt.convert .i64 x = .ok ⟨x, by rw [i64_min_eq, i64_max_eq]; exact ⟨h1, h2⟩⟩ := by
  unfold JInt.convert
  rw [dif_pos (by rw [i64_min_eq, i64_max_eq]; exact ⟨h1, h2⟩)]

theorem getfield_some {d : List V} {i : Int} (h1 : 1 ≤ i) (h2 : i ≤ d.length) :
    ∃ x, d[(i - 1).toNat]? = some x ∧ getfield d i = .ok x := by
  have hlt : (i - 1).toNat < d.length := by omega
  refine ⟨d[(i - 1).toNat], List.getElem?_eq_getElem hlt, ?_⟩
  unfold getfield
  rw [if_pos h1, List.getElem?_eq_getElem hlt]

theorem getfield_none {d : List V} {i : Int} (h : ¬ (1 ≤ i ∧ i ≤ d.length)) :
    getfield d i = bounds := by
  unfold getfield
  split
  · rw [List.getElem?_eq_none (by omega)]
  · rfl

/-- `t[a:b]` for `Int` endpoints inside `1:length(t)`. -/
theorem colon_ok (t : List V) (a b : JInt .i64) (h : b.val - a.val < 2 ^ 62) (hab : a.val ≤ b.val)
    (ha : 1 ≤ a.val) (hb : b.val ≤ t.length) :
    JuliaLean.Tuples.getindexColon t a b =
      .ok ((t.drop (a.val - 1).toNat).take (b.val - a.val + 1).toNat) := by
  classical
  have := JuliaLean.Tuples.unitRangeIndexCorrect V t a b h
  rw [if_neg (by omega), if_pos ⟨ha, hb⟩] at this
  revert this
  cases JuliaLean.Tuples.getindexColon t a b <;> simp [JuliaLean.Tuples.SameOutcome]

/-- `t[a:b]` for an empty `Int` range. -/
theorem colon_empty (t : List V) (a b : JInt .i64) (h : b.val - a.val < 2 ^ 62) (hab : b.val < a.val) :
    JuliaLean.Tuples.getindexColon t a b = .ok [] := by
  classical
  have := JuliaLean.Tuples.unitRangeIndexCorrect V t a b h
  rw [if_pos hab] at this
  revert this
  cases JuliaLean.Tuples.getindexColon t a b <;> simp [JuliaLean.Tuples.SameOutcome]

/-- `t[a:b]` for a nonempty `Int` range leaving `1:length(t)`. -/
theorem colon_bounds (t : List V) (a b : JInt .i64) (h : b.val - a.val < 2 ^ 62) (hab : a.val ≤ b.val)
    (hout : ¬ (1 ≤ a.val ∧ b.val ≤ t.length)) :
    JuliaLean.Tuples.getindexColon t a b = bounds := by
  classical
  have := JuliaLean.Tuples.unitRangeIndexCorrect V t a b h
  rw [if_neg (by omega), if_neg hout] at this
  revert this
  cases JuliaLean.Tuples.getindexColon t a b with
  | ok x => simp [JuliaLean.Tuples.SameOutcome, bounds]
  | error e =>
    intro he
    simp only [JuliaLean.Tuples.SameOutcome, bounds] at he
    cases e with
    | jl e => cases e <;> simp_all [Err.kind, bounds]
    | _ => simp [Err.kind] at he

/-! ### Lawful element orders -/

section Lawful

variable {o : Ops V}

theorem isequal_symm (hl : Lawful o) (a b : V) : o.isequal a b = o.isequal b a := by
  rw [hl.equiv, hl.equiv]
  cases o.isless a b <;> cases o.isless b a <;> rfl

theorem isless_of_isequal (hl : Lawful o) {a b : V} (h : o.isequal a b = true) :
    o.isless a b = false ∧ o.isless b a = false := by
  rw [hl.equiv] at h
  cases h1 : o.isless a b <;> cases h2 : o.isless b a <;> simp_all

theorem isequal_of_isless (hl : Lawful o) {a b : V} (h : o.isless a b = true) :
    o.isequal a b = false := by
  rw [hl.equiv, h]; rfl

theorem isequal_of_not (hl : Lawful o) {a b : V} (h1 : o.isless a b = false)
    (h2 : o.isless b a = false) : o.isequal a b = true := by
  rw [hl.equiv, h1, h2]; rfl

theorem isless_of_eq_lt (hl : Lawful o) {a b c : V} (hab : o.isequal a b = true)
    (hbc : o.isless b c = true) : o.isless a c = true := by
  cases h : o.isless a c
  · have hca : o.isless c a = false := by
      cases h' : o.isless c a
      · rfl
      · have := hl.trans _ _ _ hbc h'
        rw [(isless_of_isequal hl hab).2] at this
        cases this
    have hac : o.isequal a c = true := isequal_of_not hl h hca
    have hbc' : o.isequal b c = true :=
      hl.incompTrans _ _ _ (by rw [isequal_symm hl]; exact hab) hac
    rw [isequal_of_isless hl hbc] at hbc'
    cases hbc'
  · rfl

theorem isless_of_lt_eq (hl : Lawful o) {a b c : V} (hab : o.isless a b = true)
    (hbc : o.isequal b c = true) : o.isless a c = true := by
  cases h : o.isless a c
  · have hca : o.isless c a = false := by
      cases h' : o.isless c a
      · rfl
      · have := hl.trans _ _ _ h' hab
        rw [(isless_of_isequal hl hbc).2] at this
        cases this
    have hac : o.isequal a c = true := isequal_of_not hl h hca
    have hab' : o.isequal a b = true :=
      hl.incompTrans _ _ _ hac (by rw [isequal_symm hl]; exact hbc)
    rw [isequal_of_isless hl hab] at hab'
    cases hab'
  · rfl

end Lawful

end JuliaLean.SortTuplesCov
