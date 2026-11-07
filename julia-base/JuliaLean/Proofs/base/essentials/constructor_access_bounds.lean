import JuliaLean.Proofs.base.array.common.index_bounds

namespace JuliaLean.MemSafety.G5

/-! ## generated default constructors in `base/essentials.jl` -/

/-- Inputs that affect control flow in `_fieldtypes_constrain_typevars` and
`_defaultctors`. `isAny` also represents the DataType invariant that `names`
and `fts` have the same field count. -/
structure DefaultCtorInput where
  typevars : List Nat
  isAny : List Bool
  hasFieldTypevar : Nat → Nat → Bool
  hasUpperTypevar : Nat → Nat → Bool
  sameTypevar : Nat → Nat → Bool

/-- A checked while scan with a break. `step j = some result` stops at `j`;
`none` advances exactly as the source loops do. -/
def scanUntilResult (start : Nat) : Nat → (Nat → Option Bool) → List Nat × Bool
  | 0, _ => ([], false)
  | count + 1, step =>
    match step start with
    | some result => ([start], result)
    | none =>
      let rest := scanUntilResult (start + 1) count step
      (start :: rest.1, rest.2)

inductive CtorSourceAccess where
  | typevar (index : Nat)
  | fieldtype (index : Nat)

/-- The outer reverse loop and its two inner scans at essentials.jl:1292-1327.
The returned Boolean is the source function's return value. -/
def fieldtypesConstrainLoop (input : DefaultCtorInput) : Nat → Nat →
    List CtorSourceAccess × Bool
  | 0, _ => ([], true)
  | _ + 1, 0 => ([], true)
  | fuel + 1, i + 1 =>
    let fieldScan := scanUntilResult 1 input.isAny.length fun j =>
      if input.hasFieldTypevar (i + 1) j then some true else none
    let current := .typevar (i + 1) :: fieldScan.1.map .fieldtype
    if fieldScan.2 then
      let rest := fieldtypesConstrainLoop input fuel i
      (current ++ rest.1, rest.2)
    else
      let upperScan := scanUntilResult (i + 2) (input.typevars.length - (i + 1)) fun j =>
        if input.hasUpperTypevar (i + 1) j then some true
        else if input.sameTypevar (i + 1) j then some false
        else none
      if upperScan.2 then
        let rest := fieldtypesConstrainLoop input fuel i
        (current ++ upperScan.1.map .typevar ++ rest.1, rest.2)
      else (current ++ upperScan.1.map .typevar, false)

def fieldtypesConstrain (input : DefaultCtorInput) : List CtorSourceAccess × Bool :=
  fieldtypesConstrainLoop input input.typevars.length input.typevars.length

private theorem scanUntilResult_safe : ∀ start count step index,
    index ∈ (scanUntilResult start count step).1 → start ≤ index ∧ index < start + count := by
  intro start count
  induction count generalizing start with
  | zero => intro; simp [scanUntilResult]
  | succ count ih =>
    intro step index h
    simp only [scanUntilResult] at h
    split at h
    · simp at h
      omega
    · simp only [List.mem_cons] at h
      rcases h with rfl | h
      · omega
      · have hs := ih (start + 1) step index h
        omega

private theorem fieldtypesConstrainLoop_safe (input : DefaultCtorInput) :
    ∀ fuel i access, i ≤ input.typevars.length →
      access ∈ (fieldtypesConstrainLoop input fuel i).1 →
      match access with
      | .typevar j => OneBasedInBounds input.typevars.length j
      | .fieldtype j => OneBasedInBounds input.isAny.length j := by
  intro fuel
  induction fuel with
  | zero => intro; simp [fieldtypesConstrainLoop]
  | succ fuel ih =>
    intro i access hi hmem
    cases i with
    | zero => simp [fieldtypesConstrainLoop] at hmem
    | succ i =>
      simp only [fieldtypesConstrainLoop] at hmem
      split at hmem
      · simp only [List.mem_append, List.mem_cons, List.mem_map] at hmem
        rcases hmem with (rfl | ⟨j, hj, rfl⟩) | hmem
        · exact ⟨by omega, hi⟩
        · have hs := scanUntilResult_safe 1 input.isAny.length _ j hj
          exact ⟨by omega, by omega⟩
        · exact ih i access (by omega) hmem
      · split at hmem
        · simp only [List.mem_append, List.mem_cons, List.mem_map] at hmem
          rcases hmem with ((rfl | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | hmem
          · exact ⟨by omega, hi⟩
          · have hs := scanUntilResult_safe 1 input.isAny.length _ j hj
            exact ⟨by omega, by omega⟩
          · have hs := scanUntilResult_safe (i + 2)
                (input.typevars.length - (i + 1)) _ j hj
            exact ⟨by omega, by omega⟩
          · exact ih i access (by omega) hmem
        · simp only [List.mem_append, List.mem_cons, List.mem_map] at hmem
          rcases hmem with (rfl | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩
          · exact ⟨by omega, hi⟩
          · have hs := scanUntilResult_safe 1 input.isAny.length _ j hj
            exact ⟨by omega, by omega⟩
          · have hs := scanUntilResult_safe (i + 2)
                (input.typevars.length - (i + 1)) _ j hj
            exact ⟨by omega, by omega⟩

/-- Accesses emitted by one pass over the fields for the inner constructor.
`bodyIndex` is the source's `bidx`; it advances by two only for non-`Any` fields. -/
def innerBodyIndices : List Bool → Nat → List Nat
  | [], _ => []
  | isAny :: rest, bodyIndex =>
    if isAny then innerBodyIndices rest bodyIndex
    else bodyIndex :: (bodyIndex + 1) :: innerBodyIndices rest (bodyIndex + 2)

private theorem innerBodyIndices_safe : ∀ fields bodyIndex index,
    index ∈ innerBodyIndices fields bodyIndex →
      bodyIndex ≤ index ∧ index < bodyIndex + 2 * fields.count false := by
  intro fields
  induction fields with
  | nil => intro; simp [innerBodyIndices]
  | cons isAny rest ih =>
    intro bodyIndex index h
    cases isAny
    · simp only [innerBodyIndices, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | rfl | h
      · simp <;> omega
      · simp <;> omega
      · have hs := ih (bodyIndex + 2) index h
        simp only [List.count_cons, beq_self_eq_true, ↓reduceIte]
        omega
    · simp only [innerBodyIndices, ↓reduceIte] at h
      have hs := ih bodyIndex index h
      simpa using hs

inductive CtorBuffer where
  | tvars | names | fields | argnames | curlyArgs | outerNewArgs | innerNewArgs
  | atypes | bodyArgs | innerAtypes
  deriving DecidableEq

structure CtorAccess where
  buffer : CtorBuffer
  index : Nat

def ctorBufferLength (input : DefaultCtorInput) : CtorBuffer → Nat
  | .tvars => input.typevars.length
  | .names | .fields | .innerNewArgs => input.isAny.length
  | .argnames | .outerNewArgs | .atypes | .innerAtypes => input.isAny.length + 1
  | .curlyArgs => input.typevars.length + 1
  | .bodyArgs => 2 * input.isAny.count false + 1

private def tagged (buffer : CtorBuffer) (indices : List Nat) : List CtorAccess :=
  indices.map (⟨buffer, ·⟩)

/-- All unchecked accesses in `_defaultctor_typeinfo` and `_defaultctors`,
including the constraint-result branch, parametric branch, all-Any early return,
field loop, `bidx` updates, reverse typevar loop, and exact allocation sizes. -/
def defaultCtorAccesses (input : DefaultCtorInput) : List CtorAccess :=
  let nparams := input.typevars.length
  let n := input.isAny.length
  let constrain := fieldtypesConstrain input
  let sourceReads := constrain.1.map fun access => match access with
    | .typevar i => ⟨.tvars, i⟩
    | .fieldtype i => ⟨.fields, i⟩
  let typeInfo := tagged .tvars (oneBasedLoop nparams)
  let fieldLoop := tagged .names (oneBasedLoop n) ++ tagged .fields (oneBasedLoop n) ++
    tagged .argnames (1 :: (oneBasedLoop n).map (· + 1))
  let outer := if constrain.2 then
      (if nparams = 0 then [] else tagged .curlyArgs (1 :: (oneBasedLoop nparams).map (· + 1))) ++
      tagged .outerNewArgs (1 :: (oneBasedLoop n).map (· + 1)) ++
      tagged .atypes (1 :: (oneBasedLoop n).map (· + 1))
    else []
  let earlyReturn := constrain.2 && nparams = 0 && input.isAny.all id
  let inner := if earlyReturn then [] else
    tagged .innerNewArgs (oneBasedLoop n) ++
    tagged .bodyArgs (innerBodyIndices input.isAny 1) ++
    tagged .tvars (oneBasedLoop nparams).reverse ++
    tagged .innerAtypes (1 :: (oneBasedLoop n).map (· + 1))
  sourceReads ++ typeInfo ++ fieldLoop ++ outer ++ inner

def DefaultCtorAccessesInBounds : Prop :=
  ∀ input access, access ∈ defaultCtorAccesses input →
    OneBasedInBounds (ctorBufferLength input access.buffer) access.index


private theorem shiftedLoop_safe (n index : Nat) :
    index ∈ 1 :: (oneBasedLoop n).map (· + 1) → OneBasedInBounds (n + 1) index := by
  intro h
  simp only [List.mem_cons, List.mem_map] at h
  rcases h with rfl | ⟨i, hi, rfl⟩
  · simp [OneBasedInBounds]
  · have hs := oneBasedLoop_safe n i hi
    simp only [OneBasedInBounds] at hs ⊢
    omega

/-- A branch-free superset of `defaultCtorAccesses`; it keeps every possible
constructor-generation branch while preserving each source-computed index. -/
private def defaultCtorAllAccesses (input : DefaultCtorInput) : List CtorAccess :=
  let nparams := input.typevars.length
  let n := input.isAny.length
  let sourceReads := (fieldtypesConstrain input).1.map fun access => match access with
    | .typevar i => ⟨.tvars, i⟩
    | .fieldtype i => ⟨.fields, i⟩
  sourceReads ++
    (tagged .tvars (oneBasedLoop nparams) ++
    (tagged .names (oneBasedLoop n) ++
    (tagged .fields (oneBasedLoop n) ++
    (tagged .argnames (1 :: (oneBasedLoop n).map (· + 1)) ++
    (tagged .curlyArgs (1 :: (oneBasedLoop nparams).map (· + 1)) ++
    (tagged .outerNewArgs (1 :: (oneBasedLoop n).map (· + 1)) ++
    (tagged .atypes (1 :: (oneBasedLoop n).map (· + 1)) ++
    (tagged .innerNewArgs (oneBasedLoop n) ++
    (tagged .bodyArgs (innerBodyIndices input.isAny 1) ++
    (tagged .tvars (oneBasedLoop nparams).reverse ++
      tagged .innerAtypes (1 :: (oneBasedLoop n).map (· + 1))))))))))))

private theorem defaultCtorAccesses_subset (input : DefaultCtorInput) (access : CtorAccess) :
    access ∈ defaultCtorAccesses input → access ∈ defaultCtorAllAccesses input := by
  intro h
  by_cases hc : (fieldtypesConstrain input).2
  · by_cases hp : input.typevars.length = 0
    · by_cases ha : input.isAny.all id
      · simp [defaultCtorAccesses, defaultCtorAllAccesses, hc, hp, ha,
          List.mem_append] at h ⊢
        grind
      · simp [defaultCtorAccesses, defaultCtorAllAccesses, hc, hp, ha,
          List.mem_append] at h ⊢
        grind
    · simp [defaultCtorAccesses, defaultCtorAllAccesses, hc, hp,
        List.mem_append] at h ⊢
      grind
  · simp [defaultCtorAccesses, defaultCtorAllAccesses, hc,
      List.mem_append] at h ⊢
    grind

theorem defaultCtorAccessesInBounds : DefaultCtorAccessesInBounds := by
  intro input access h0
  have hall := defaultCtorAccesses_subset input access h0
  clear h0
  unfold defaultCtorAllAccesses at hall
  simp only [List.mem_append] at hall
  rcases hall with h | hall
  · simp only [List.mem_map] at h
    obtain ⟨source, hs, rfl⟩ := h
    have hb := fieldtypesConstrainLoop_safe input input.typevars.length
      input.typevars.length source (by omega) hs
    cases source <;> exact hb
  · rcases hall with h | hall
    · simp only [tagged, List.mem_map] at h
      obtain ⟨i, hi, rfl⟩ := h
      exact oneBasedLoop_safe _ _ hi
    · rcases hall with h | hall
      · simp only [tagged, List.mem_map] at h
        obtain ⟨i, hi, rfl⟩ := h
        exact oneBasedLoop_safe _ _ hi
      · rcases hall with h | hall
        · simp only [tagged, List.mem_map] at h
          obtain ⟨i, hi, rfl⟩ := h
          exact oneBasedLoop_safe _ _ hi
        · rcases hall with h | hall
          · simp only [tagged, List.mem_map] at h
            obtain ⟨i, hi, rfl⟩ := h
            exact shiftedLoop_safe _ _ hi
          · rcases hall with h | hall
            · simp only [tagged, List.mem_map] at h
              obtain ⟨i, hi, rfl⟩ := h
              exact shiftedLoop_safe _ _ hi
            · rcases hall with h | hall
              · simp only [tagged, List.mem_map] at h
                obtain ⟨i, hi, rfl⟩ := h
                exact shiftedLoop_safe _ _ hi
              · rcases hall with h | hall
                · simp only [tagged, List.mem_map] at h
                  obtain ⟨i, hi, rfl⟩ := h
                  exact shiftedLoop_safe _ _ hi
                · rcases hall with h | hall
                  · simp only [tagged, List.mem_map] at h
                    obtain ⟨i, hi, rfl⟩ := h
                    exact oneBasedLoop_safe _ _ hi
                  · rcases hall with h | hall
                    · simp only [tagged, List.mem_map] at h
                      obtain ⟨i, hi, rfl⟩ := h
                      have hs := innerBodyIndices_safe input.isAny 1 i hi
                      simp only [ctorBufferLength, OneBasedInBounds] at hs ⊢
                      omega
                    · rcases hall with h | h
                      · simp only [tagged, List.mem_map, List.mem_reverse] at h
                        obtain ⟨i, hi, rfl⟩ := h
                        exact oneBasedLoop_safe _ _ hi
                      · simp only [tagged, List.mem_map] at h
                        obtain ⟨i, hi, rfl⟩ := h
                        exact shiftedLoop_safe _ _ hi


end JuliaLean.MemSafety.G5
