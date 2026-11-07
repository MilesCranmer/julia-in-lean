import JuliaLean.Proofs.base.array.cartesian_contracts
import JuliaLean.Proofs.base.array.cartesian_refutations
import JuliaLean.Proofs.base.multidimensional.cartesian_iteration
import JuliaLean.Registry.Types

namespace JuliaLean.Multidim

/-! ## `findfirst` -/

local notation "U" => fun (n : Nat) => Rng.mk (i64 1) (i64 1) n

private theorem i64_val {x : Int} (h0 : 0 ≤ x) (h1 : x < 2 ^ 20) : (i64 x).val = x :=
  wrapInt_of_inRange .i64 x (by
    revert h1; simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)

private theorem i64_one : (i64 1).val = 1 := i64_val (by omega) (by decide)

private theorem unit_wf {n : Nat} (hn : n < 2 ^ 20) : (U n).WF := by
  refine ⟨show (i64 1).val ≠ 0 by rw [i64_one]; decide, fun j hj => ?_⟩
  have hj' : j < n := hj
  simp only [Rng.elem, i64_one]
  revert hn; simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega

private theorem unit_last (n : Nat) : (U n).last = i64 n := by
  show JInt.wrap .i64 ((i64 1).val + ((n : Int) - 1) * (i64 1).val) = JInt.wrap .i64 n
  rw [i64_one, Int.mul_one]
  congr 1
  omega

private theorem inAxes_cons (lo hi j : Int) (ax : List (Int × Int)) (J : List Int) :
    inAxes ((lo, hi) :: ax) (j :: J) = (decide (lo ≤ j ∧ j ≤ hi) && inAxes ax J) := by
  simp only [inAxes, List.length_cons, List.zip_cons_cons, List.all_cons]
  rw [show (J.length + 1 == ax.length + 1) = (J.length == ax.length) by
    cases h : J.length == ax.length <;> simp_all]
  exact Bool.and_left_comm _ _ _

private theorem elems_inAxes : ∀ (sz : List Nat) (t : List I64), (∀ n ∈ sz, n < 2 ^ 20) →
    t ∈ elems (sz.map U) → inAxes (oneAxes sz) (t.map (·.val)) = true
  | [], t, _, h => by simp [elems] at h; subst h; simp [inAxes, oneAxes]
  | n :: sz, t, hs, h => by
    simp only [List.map_cons, elems, List.mem_flatMap, List.mem_map] at h
    obtain ⟨u, hu, x, hx, rfl⟩ := h
    simp only [Rng.elems, List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hn : n < 2 ^ 20 := hs n (by simp)
    have hv := ge_val (unit_wf hn) hj
    simp only [Rng.elem, i64_one] at hv
    rw [List.map_cons, show oneAxes (n :: sz) = (1, (n : Int)) :: oneAxes sz from rfl,
      inAxes_cons, elems_inAxes sz u (fun m hm => hs m (by simp [hm])) hu]
    show (decide (1 ≤ (ge (U n) j).val ∧ (ge (U n) j).val ≤ n) && true) = true
    rw [hv]
    simp only [Bool.and_true, decide_eq_true_eq]
    omega

private theorem foldl_len : ∀ (sz : List Nat) (a : Nat),
    sz.foldl (· * ·) a = a * (elems (sz.map U)).length
  | [], a => by simp [elems]
  | n :: sz, a => by
    rw [List.foldl_cons, foldl_len sz, List.map_cons, elems_cons_length]
    show a * n * _ = a * (_ * n)
    rw [Nat.mul_assoc, Nat.mul_comm n]

private theorem tupleLess_ge : ∀ (L : List Nat), (∀ n ∈ L, 0 < n ∧ n < 2 ^ 20) →
    tupleLess (L.map fun (n : Nat) => i64 n) (L.map fun _ => i64 1) = false
  | [], _ => rfl
  | n :: L, h => by
    have hn := h n (by simp)
    simp only [List.map_cons, tupleLess]
    rw [tupleLess_ge L (fun m hm => h m (by simp [hm])),
      i64_val (x := (n : Int)) (by omega) (by exact_mod_cast hn.2), i64_one]
    simp
    omega

private theorem loop (sz : List Nat) (A : List Int → Bool) (hs : ∀ n ∈ sz, 0 < n ∧ n < 2 ^ 20) :
    ∀ (fuel k : Nat) (hk : k < (elems (sz.map U)).length), (elems (sz.map U)).length ≤ fuel + k →
    findLoop inc sz A fuel (elems (sz.map U))[k] =
      .ok (((elems (sz.map U)).drop k).find? fun I => A (I.map (·.val))) := by
  have hwf : ∀ r ∈ sz.map U, r.WF ∧ 0 < r.len := by
    intro r hr
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hr
    exact ⟨unit_wf (hs n hn).2, (hs n hn).1⟩
  have hlast := last_elem _ hwf
  rw [List.map_map] at hlast
  have hlast' : (sz.map U).map (·.last) = sz.map fun (n : Nat) => i64 n := by
    rw [List.map_map]; exact List.map_congr_left fun n _ => unit_last n
  rw [List.map_map] at hlast'
  intro fuel
  induction fuel with
  | zero => intro k hk h; omega
  | succ fuel ih =>
    intro k hk hf
    have hin := elems_inAxes sz _ (fun n hn => (hs n hn).2) (List.getElem_mem hk)
    rw [findLoop, List.drop_eq_getElem_cons hk, List.find?_cons]
    simp only [hin, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hA : A ((elems (sz.map U))[k].map (·.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hfk := fw _ (fun r hr => (hwf r hr).1) k _ (List.getElem?_eq_getElem hk)
      by_cases hl : (elems (sz.map U))[k] = sz.map fun (n : Nat) => i64 n
      · rw [ite_eq_left hl]
        have hfl := fw _ (fun r hr => (hwf r hr).1) _ _ hlast
        rw [hlast', ← hl, hfk,
          show (elems (sz.map U)).length - 1 + 1 = (elems (sz.map U)).length by omega,
          List.getElem?_eq_none (Nat.le_refl _)] at hfl
        have : (elems (sz.map U)).length ≤ k + 1 := by
          rcases Nat.lt_or_ge (k + 1) (elems (sz.map U)).length with h1 | h1
          · rw [List.getElem?_eq_getElem h1] at hfl; cases hfl
          · exact h1
        rw [List.drop_eq_nil_of_le this]
        rfl
      · rw [ite_eq_right hl]
        have hk1 : k + 1 < (elems (sz.map U)).length := by
          rcases Nat.lt_or_ge (k + 1) (elems (sz.map U)).length with h1 | h1
          · exact h1
          · exfalso; apply hl
            have h2 := hlast
            rw [hlast', show (elems (sz.map U)).length - 1 = k by omega,
              List.getElem?_eq_getElem hk] at h2
            exact Option.some.inj h2
        rw [List.getElem?_eq_getElem hk1] at hfk
        have hp : inc (elems (sz.map U))[k] (sz.map U) = (true, (elems (sz.map U))[k + 1]) := by
          unfold opt at hfk
          split at hfk
          · rename_i hc
            exact Prod.ext hc (Option.some.inj hfk)
          · cases hfk
        rw [hp]
        exact ih (k + 1) hk1 (by omega)
    · rfl

theorem findfirstNonempty : FindfirstNonempty := by
  intro sz A hs
  have hwf : ∀ r ∈ sz.map U, r.WF ∧ 0 < r.len := by
    intro r hr
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hr
    exact ⟨unit_wf (hs n hn).2, (hs n hn).1⟩
  have hpos := elems_pos' _ fun r hr => (hwf r hr).2
  have hfirst := first_elem _ hwf
  rw [List.map_map, List.getElem?_eq_getElem hpos] at hfirst
  have hstart : sz.map (fun _ => i64 1) = (elems (sz.map U))[0] :=
    (Option.some.inj hfirst).symm
  have hci : ciLess (sz.map fun (n : Nat) => i64 n) (sz.map fun _ => i64 1) = false := by
    unfold ciLess
    rw [show (sz.map fun (n : Nat) => i64 n).reverse = sz.reverse.map fun (n : Nat) => i64 n by simp,
      show (sz.map fun _ => i64 1).reverse = sz.reverse.map fun _ => i64 1 by simp]
    exact tupleLess_ge _ fun n hn => hs n (List.mem_reverse.mp hn)
  unfold findfirst findnext
  simp only [hci, Bool.false_eq_true, ↓reduceIte]
  rw [hstart, loop sz A hs (sz.foldl (· * ·) 1 + 1) 0 hpos (by rw [foldl_len, Nat.one_mul]; omega)]
  rfl

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "multidim-findfirst-nonempty", juliaFile := "base/array.jl"
    juliaFns := ["findfirst(testf::Function, A::AbstractArray)", "findnext(testf::Function, A, start)", "nextind(::AbstractArray, ::CartesianIndex)"]
    statement := "For an array with no empty dimension, findfirst(f, A) returns the first CartesianIndex in column-major order where f holds, or nothing."
    source := "base/array.jl:2488-2492 (findfirst docstring)"
    status := .proven, prop := ``FindfirstNonempty, thm := some ``findfirstNonempty }
]

end JuliaLean.Multidim
