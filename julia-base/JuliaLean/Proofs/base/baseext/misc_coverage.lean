import JuliaLean.base.baseext

namespace JuliaLean.MiscCov.BaseExt

variable {V : Type}

/-- Contract of `base/baseext.jl`: the `VecElement` constructor and conversions store
`convert(T, x)` (and are the identity on a `VecElement{T}`); every `undef` constructor
builds the array of `Int(d)` dimensions with `prod(d)` undefined elements, throwing
`InexactError` exactly when a dimension does not fit in `Int`, and the
`Vector`/`Matrix`/`Vector()` forms have element type `Any`; the `nothing`/`missing`
constructors fill every element with the converted singleton. -/
def Contract : Prop :=
  (∀ (convT : V → M V) (x : V), vecElement convT x = convT x ∧ convertOther convT x = convT x ∧
    convertSame x = .ok x) ∧
  (∀ (T : String) (d : Dims) (A : Arr V), undefN T d = .ok A →
    A.eltype = T ∧ A.dims = d ∧ A.elems.length = (d.foldl (· * ·) 1).toNat ∧ ∀ e ∈ A.elems, e = none) ∧
  (∀ (T : String) (d : Dims), d.any (fun m => !(decide (-(2 ^ 63) ≤ m ∧ m < 2 ^ 63))) →
    (undefN T d : M (Arr V)) = .error .inexactError) ∧
  (∀ (T : String) (m : Int), (undef1 T m : M (Arr V)) = undefN T [m]) ∧
  (∀ (T : String) (m n : Int), (undef2 T m n : M (Arr V)) = undefN T [m, n]) ∧
  (∀ (T : String) (m n o : Int), (undef3 T m n o : M (Arr V)) = undefN T [m, n, o]) ∧
  (∀ m : Int, (vectorAny m : M (Arr V)) = undefN "Any" [m]) ∧
  (∀ m n : Int, (matrixAny m n : M (Arr V)) = undefN "Any" [m, n]) ∧
  ((vector0 : M (Arr V)).map (fun A => (A.eltype, A.dims, A.elems.length)) = .ok ("Any", [0], 0)) ∧
  (∀ (T : String) (convT : V → M V) (x : V) (d : Dims) (A : Arr V),
    filled T convT x d = .ok A → ∃ y, convT x = .ok y ∧ A.dims = d ∧ ∀ e ∈ A.elems, e = some y)

theorem toInts_ok : ∀ (d : Dims) (l : List Int), toInts d = .ok l → l = d := by
  intro d
  induction d with
  | nil => intro l h; simp only [toInts, Except.ok.injEq] at h; exact h.symm
  | cons m ms ih =>
    intro l h
    simp only [toInts] at h
    cases hm : toInt m with
    | error e => rw [hm] at h; cases h
    | ok a =>
      rw [hm] at h
      cases hr : toInts ms with
      | error e => rw [hr] at h; cases h
      | ok rest =>
        rw [hr] at h
        cases h
        have ha : a = m := by
          simp only [toInt] at hm
          split at hm
          · cases hm; rfl
          · cases hm
        rw [ha, ih rest hr]

theorem toInts_err : ∀ (d : Dims), d.any (fun m => !(decide (-(2 ^ 63) ≤ m ∧ m < 2 ^ 63))) →
    toInts d = .error .inexactError := by
  intro d
  induction d with
  | nil => intro h; simp at h
  | cons m ms ih =>
    intro h
    simp only [toInts]
    by_cases hm : -(2 ^ 63) ≤ m ∧ m < 2 ^ 63
    · have ht : toInt m = .ok m := by simp only [toInt]; rw [if_pos hm]
      rw [ht]
      have h' : ms.any (fun m => !(decide (-(2 ^ 63) ≤ m ∧ m < 2 ^ 63))) := by
        simp only [List.any_cons, hm, decide_true, Bool.not_true, Bool.false_or] at h
        exact h
      rw [ih h']
    · have ht : toInt m = .error .inexactError := by simp only [toInt]; rw [if_neg hm]
      rw [ht]

theorem undef1_eq (T : String) (m : Int) : (undef1 T m : M (Arr V)) = undefN T [m] := by
  simp only [undef1, undefN, toInts, bind, Except.bind, pure, Except.pure]
  cases toInt m <;> rfl

theorem undef2_eq (T : String) (m n : Int) : (undef2 T m n : M (Arr V)) = undefN T [m, n] := by
  simp only [undef2, undefN, toInts, bind, Except.bind, pure, Except.pure]
  cases toInt m <;> cases toInt n <;> rfl

theorem undef3_eq (T : String) (m n o : Int) : (undef3 T m n o : M (Arr V)) = undefN T [m, n, o] := by
  simp only [undef3, undefN, toInts, bind, Except.bind, pure, Except.pure]
  cases toInt m <;> cases toInt n <;> cases toInt o <;> rfl

theorem contract_proven : @Contract V := by
  refine ⟨fun _ _ => ⟨rfl, rfl, rfl⟩, ?_, ?_, undef1_eq, undef2_eq, undef3_eq,
    fun m => undef1_eq "Any" m, fun m n => undef2_eq "Any" m n, rfl, ?_⟩
  · intro T d A h
    simp only [undefN, bind, Except.bind] at h
    cases hd : toInts d with
    | error e => rw [hd] at h; cases h
    | ok l =>
      rw [hd] at h
      have := toInts_ok d l hd
      subst this
      simp only [core] at h
      split at h
      · cases h
      · cases h
        refine ⟨rfl, rfl, by simp, ?_⟩
        intro e he
        exact (List.eq_of_mem_replicate he)
  · intro T d h
    simp only [undefN, bind, Except.bind, toInts_err d h]
  · intro T convT x d A h
    simp only [filled, fill, bind, Except.bind, pure, Except.pure] at h
    cases hu : (undefN T d : M (Arr V)) with
    | error e => rw [hu] at h; cases h
    | ok B =>
      rw [hu] at h
      cases hc : convT x with
      | error e => rw [hc] at h; cases h
      | ok y =>
        rw [hc] at h
        cases h
        refine ⟨y, rfl, ?_, ?_⟩
        · simp only [undefN, bind, Except.bind] at hu
          cases hd : toInts d with
          | error e => rw [hd] at hu; cases hu
          | ok l =>
            rw [hd] at hu
            have := toInts_ok d l hd
            subst this
            simp only [core] at hu
            split at hu
            · cases hu
            · cases hu; rfl
        · intro e he
          simp only [List.mem_map] at he
          obtain ⟨_, _, h⟩ := he
          exact h.symm

end JuliaLean.MiscCov.BaseExt

namespace JuliaLean.MiscCov

def BaseExtContractClosed : Prop := @BaseExt.Contract Unit
theorem baseExtContractClosed_proven : BaseExtContractClosed := BaseExt.contract_proven

end JuliaLean.MiscCov
