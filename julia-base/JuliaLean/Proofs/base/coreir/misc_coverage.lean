import JuliaLean.base.coreir

namespace JuliaLean.MiscCov.CoreIR

/-- The two-argument constructor builds a `PartialStruct` satisfying every assertion of
the three-argument one (`base/coreir.jl:22-48` docstring): for a struct with `n` fields
and `n` lattice elements, and for a variable-length tuple whose last element is the
`Vararg` and whose `min_ninitialized` is `n - 1`, it errors exactly when one of the first
`min_ninitialized` fields is `Union{}`, and otherwise marks those fields `false`, a
later `Union{}` field `true`, the rest `nothing`; `==` compares the three fields and
`getproperty` returns them. -/
def Contract : Prop :=
  (phiNode = ([], [])) ∧
  (∀ (typ : TypInfo) (fields : List Lat),
    ((∃ n, typ.fldcnt = some n ∧ n = fields.length ∧ typ.minInit ≤ n) ∨
     (typ.fldcnt = none ∧ typ.isTuple ∧ (fields.getLast?.map (·.isVararg)) = some true ∧
       (fields.getLast?.map (·.isBottom)) = some false ∧ typ.minInit + 1 = fields.length)) →
    ((fields.take typ.minInit).any (·.isBottom) → mk2 typ fields =
        .error (.errorException "This object never exists at runtime")) ∧
    (¬ (fields.take typ.minInit).any (·.isBottom) → ∃ p, mk2 typ fields = .ok p ∧
      p.typ = typ ∧ p.fields = fields ∧ p.undefs.length = fields.length ∧
      ∀ i, i < fields.length →
        p.undefs.getD i none = (if i < typ.minInit then some false
          else if (fields.getD i ⟨0, false, false⟩).isBottom then some true else none))) ∧
  (∀ a b : PartialStruct, eq a b = true ↔ a = b) ∧
  (∀ p : PartialStruct, getproperty p .undefs = .inr (.inl p.undefs) ∧
    getproperty p .typ = .inl p.typ ∧ getproperty p .fields = .inr (.inr p.fields))

theorem initUndefs_getD (typ : TypInfo) (fields : List Lat) (i : Nat) (hi : i < fields.length) :
    ((List.range fields.length).map fun i =>
      if i < typ.minInit then some false
      else if (fields.getD i ⟨0, false, false⟩).isBottom then some true else (none : Undef)).getD i none =
    (if i < typ.minInit then some false
      else if (fields.getD i ⟨0, false, false⟩).isBottom then some true else none) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem contract_proven : Contract := by
  refine ⟨rfl, ?_, ?_, fun p => ⟨rfl, rfl, rfl⟩⟩
  · intro typ fields hpre
    refine ⟨?_, ?_⟩
    · intro hb
      simp [mk2, initUndefs, hb]
    · intro hb
      have hU : initUndefs typ fields = some ((List.range fields.length).map fun i =>
          if i < typ.minInit then some false
          else if (fields.getD i ⟨0, false, false⟩).isBottom then some true else none) := by
        simp [initUndefs, hb]
      obtain ⟨U, hUdef⟩ : ∃ U : List Undef, U = (List.range fields.length).map fun i =>
          if i < typ.minInit then some false
          else if (fields.getD i ⟨0, false, false⟩).isBottom then some true else (none : Undef) :=
        ⟨_, rfl⟩
      rw [← hUdef] at hU
      have hlen : U.length = fields.length := by simp [hUdef]
      -- no field before `minInit` is `Union{}`
      have hnb : ∀ i, i < typ.minInit → i < fields.length →
          (fields.getD i ⟨0, false, false⟩).isBottom = false := by
        intro i h1 h2
        have : ¬ (fields.take typ.minInit).any (·.isBottom) = true := hb
        simp only [List.any_eq_true, not_exists, not_and] at this
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
        have hm : fields[i] ∈ fields.take typ.minInit :=
          List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
        simpa using this _ hm
      have hloop : ((List.range fields.length).all fun i =>
          !(fields.getD i ⟨0, false, false⟩).isBottom || U.getD i none == some true) = true := by
        rw [List.all_eq_true]
        intro i hi
        have hi' := List.mem_range.mp hi
        rw [hUdef, initUndefs_getD typ fields i hi']
        by_cases h1 : i < typ.minInit
        · rw [if_pos h1, hnb i h1 hi']; rfl
        · by_cases h2 : (fields.getD i ⟨0, false, false⟩).isBottom <;> simp [h1, h2]
      refine ⟨⟨typ, U, fields⟩, ?_, rfl, rfl, hlen, ?_⟩
      · simp only [mk2, hU, mk3]
        rcases hpre with ⟨n, hn, hnl, _⟩ | ⟨hn, ht, hv, hbot, hmin⟩
        · have hc : mk3Checks typ U fields = some true := by
            simp only [mk3Checks, mk3Checks.loopOk, hn, hloop, hnl, hlen, beq_self_eq_true, Bool.and_true]
          rw [hc]
        · have hidx : fields.length - 1 < fields.length := by omega
          have hnot : ¬ (fields.length - 1 < typ.minInit) := by omega
          obtain ⟨f, hf⟩ : ∃ f, fields.getLast? = some f := by
            cases h : fields.getLast? with
            | none => simp [h] at hv
            | some f => exact ⟨f, rfl⟩
          have hfv : f.isVararg = true := by simpa [hf] using hv
          have hfb : f.isBottom = false := by simpa [hf] using hbot
          have hget : fields.getD (fields.length - 1) ⟨0, false, false⟩ = f := by
            rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, hf]; rfl
          have hlast : U.getLast? = some none := by
            rw [List.getLast?_eq_getElem?, hlen, hUdef, List.getElem?_map, List.getElem?_range hidx]
            simp only [Option.map]
            rw [if_neg hnot, hget, hfb]; rfl
          have hm' : typ.minInit = fields.length - 1 := by omega
          have hc : mk3Checks typ U fields = some true := by
            simp only [mk3Checks, mk3Checks.loopOk, hn, hf, ht, hfv, hlast, hloop, hlen, hm', Bool.true_and,
              beq_self_eq_true, Bool.and_true]
          rw [hc]
      · intro i hi
        rw [hUdef, initUndefs_getD typ fields i hi]
  · intro a b
    constructor
    · intro h
      simp only [eq, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      cases a; cases b; simp_all
    · intro h; subst h; simp [eq]

end JuliaLean.MiscCov.CoreIR
