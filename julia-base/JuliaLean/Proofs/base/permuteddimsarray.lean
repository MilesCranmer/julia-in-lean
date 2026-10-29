import JuliaLean.base.permuteddimsarray
import JuliaLean.base.array
import JuliaLean.base.multidimensional
import JuliaLean.Registry.Types

/-!
# Properties of `base/permuteddimsarray.jl`

The properties describe valid dimension mappings, shared indexed access, shape and stride order,
copy-loop coverage, and the documented pointer rejection.
-/

namespace JuliaLean.Proofs.base.permuteddimsarray

open JuliaLean JuliaLean.base.permuteddimsarray JuliaLean.Registry

/-! ## Independent index and shape specifications -/

def IsIntegerPermutation {N : Nat} {t : IntTy} (perm : TupleN (JInt t) N) : Prop :=
  perm.values.Nodup ∧
    ∀ x, x ∈ perm.values → 1 ≤ x.val ∧ x.val ≤ Int.ofNat N

def InversePermutation {N : Nat} {t : IntTy}
    (perm inverse : TupleN (JInt t) N) : Prop :=
  ∀ d, d < N → ∃ p,
    perm.values[d]? = some p ∧
    inverse.values[(p.val - 1).toNat]? = some (JInt.wrap t (Int.ofNat d + 1))

def ParentCoordinates {T A : Type} {N : Nat}
    (view : PermutedDimsArray T A N)
    (viewIndices parentIndices : TupleN Index N) : Prop :=
  ∀ k, k < N → ∃ p x,
    view.iperm.values[k]? = some p ∧
    viewIndices.values[(p.val - 1).toNat]? = some x ∧
    parentIndices.values[k]? = some x

def PermutedValues {α : Type} {N : Nat}
    (result source : TupleN α N) (perm : TupleN Index N) : Prop :=
  ∀ d, d < N → ∃ p value,
    perm.values[d]? = some p ∧
    source.values[(p.val - 1).toNat]? = some value ∧
    result.values[d]? = some value

def TupleGetSound {N : Nat} (get : TupleN Index N → Index → Result Index) : Prop :=
  ∀ xs i x, get xs i = .ok x →
    ∃ k, i.val = Int.ofNat k + 1 ∧ xs.values[k]? = some x

def AllSound (all : List Index → (Index → Result Bool) → Result Bool) : Prop :=
  ∀ xs predicate, all xs predicate = .ok true →
    ∀ x, x ∈ xs → predicate x = .ok true

def TupleBuilderSound {α : Type}
    (ntuple : (n : Nat) → (Index → Result α) → Result (TupleN α n)) : Prop :=
  ∀ n f result, ntuple n f = .ok result →
    ∀ d, d < n → ∃ value,
      f (int (Int.ofNat d + 1)) = .ok value ∧ result.values[d]? = some value

def TupleReadSound {α : Type} {N : Nat}
    (get : TupleN α N → Index → Result α) : Prop :=
  ∀ xs i value, get xs i = .ok value →
    xs.values[(i.val - 1).toNat]? = some value

def PermutedConstructorInvariant : Prop :=
  ∀ {T A : Type} {N : Nat} {t u : IntTy}
    (data : A) (perm : TupleN (JInt t) N) (iperm : TupleN (JInt u) N)
    (isperm : TupleN Index N → Result Bool)
    (all : List Index → (Index → Result Bool) → Result Bool)
    (tupleGet : TupleN Index N → Index → Result Index)
    (renderPerm : TupleN (JInt t) N → String)
    (renderIperm : TupleN (JInt u) N → String)
    (result : PermutedDimsArray T A N),
    N ≤ 9223372036854775807 →
    (∀ p, isperm p = .ok true → IsIntegerPermutation p) →
    AllSound all → TupleGetSound tupleGet →
    innerConstructor isperm all tupleGet renderPerm renderIperm data perm iperm = .ok result →
      result.parent = data ∧ result.perm = toIntTuple perm ∧
      result.iperm = toIntTuple iperm ∧ IsIntegerPermutation result.perm ∧
      InversePermutation result.perm result.iperm

def PermutedReadInvariant : Prop :=
  ∀ {T A V : Type} {N : Nat}
    (view : PermutedDimsArray T A N) (indices parentIndices : TupleN Index N)
    (checkbounds : PermutedDimsArray T A N → TupleN Index N → Result Unit)
    (readParent : A → TupleN Index N → Result V)
    (ntuple : (n : Nat) → (Index → Result Index) → Result (TupleN Index n))
    (tupleGet : TupleN Index N → Index → Result Index) (value : V),
    checkbounds view indices = .ok () →
    ParentCoordinates view indices parentIndices →
    genpermTuple ntuple tupleGet tupleGet indices view.iperm = .ok parentIndices →
    readParent view.parent parentIndices = .ok value →
      getindex checkbounds readParent ntuple tupleGet view indices = .ok value
def mutationOutcome {T β : Type} (operation : MutationResult T β)
    (initial : JuliaLean.base.array.MutableMemory T) :
    Except JuliaLean.base.array.Error (Except Error β) × JuliaLean.base.array.MutableMemory T :=
  (operation.run).run initial

def mutableCellAt {T : Type} (state : JuliaLean.base.array.MutableMemory T)
    (handle : Nat) (index : Index) : Option T :=
  ((JuliaLean.base.array.MutableMemory.contents state handle)[(index.val - 1).toNat]?).join

def PermutedSetEffect : Prop :=
  ∀ {T : Type} {N : Nat}
    (view : PermutedDimsArray T Nat N) (indices parentIndices : TupleN Index N)
    (value : T) (linearIndex : TupleN Index N → Index)
    (checkbounds : PermutedDimsArray T Nat N → TupleN Index N → MutationResult T Unit)
    (setParent : Nat → T → TupleN Index N → MutationResult T Unit)
    (ntuple : (n : Nat) → (Index → MutationResult T Index) → MutationResult T (TupleN Index n))
    (tupleGet : TupleN Index N → Index → MutationResult T Index)
    (initial final : JuliaLean.base.array.MutableMemory T),
    mutationOutcome (checkbounds view indices) initial = (.ok (.ok ()), initial) →
    mutationOutcome (genpermTuple ntuple tupleGet tupleGet indices view.iperm) initial =
      (.ok (.ok parentIndices), initial) →
    mutationOutcome (setParent view.parent value parentIndices) initial = (.ok (.ok ()), final) →
    mutableCellAt final view.parent (linearIndex parentIndices) = some value →
    (∀ handle index, handle ≠ view.parent ∨ index ≠ linearIndex parentIndices →
      mutableCellAt final handle index = mutableCellAt initial handle index) →
    mutationOutcome (setindex checkbounds setParent ntuple tupleGet view value indices) initial =
      (.ok (.ok value), final)

def PermutedAssignmentEffect : Prop :=
  (∀ {T : Type} {N : Nat}
    (view : PermutedDimsArray T Nat N) (indices : TupleN Index N)
    (checkbounds : PermutedDimsArray T Nat N → TupleN Index N → MutationResult T Bool)
    (isassignedParent : Nat → TupleN Index N → MutationResult T Bool)
    (ntuple : (n : Nat) → (Index → MutationResult T Index) → MutationResult T (TupleN Index n))
    (tupleGet : TupleN Index N → Index → MutationResult T Index)
    (initial : JuliaLean.base.array.MutableMemory T),
    mutationOutcome (checkbounds view indices) initial = (.ok (.ok false), initial) →
    mutationOutcome (isassigned checkbounds isassignedParent ntuple tupleGet view indices) initial =
      (.ok (.ok false), initial)) ∧
  (∀ {T : Type} {N : Nat}
    (view : PermutedDimsArray T Nat N) (indices parentIndices : TupleN Index N)
    (checkbounds : PermutedDimsArray T Nat N → TupleN Index N → MutationResult T Bool)
    (isassignedParent : Nat → TupleN Index N → MutationResult T Bool)
    (ntuple : (n : Nat) → (Index → MutationResult T Index) → MutationResult T (TupleN Index n))
    (tupleGet : TupleN Index N → Index → MutationResult T Index)
    (initial : JuliaLean.base.array.MutableMemory T) (assigned : Bool),
    mutationOutcome (checkbounds view indices) initial = (.ok (.ok true), initial) →
    mutationOutcome (genpermTuple ntuple tupleGet tupleGet indices view.iperm) initial =
      (.ok (.ok parentIndices), initial) →
    mutationOutcome (isassignedParent view.parent parentIndices) initial =
      (.ok (.ok assigned), initial) →
    mutationOutcome (isassigned checkbounds isassignedParent ntuple tupleGet view indices) initial =
      (.ok (.ok assigned), initial))

def PermutedIndexedStorage : Prop := PermutedSetEffect ∧ PermutedAssignmentEffect


def PermutedCorrect : Prop :=
  PermutedConstructorInvariant ∧ PermutedReadInvariant

/-! ## The prior integer-width expectation -/

def PermutedAnyIntType : Prop :=
  ∀ {T A : Type} {N : Nat} {t : IntTy}
    (data : A) (perm inverse : TupleN (JInt t) N)
    (length : TupleN (JInt t) N → Result Index)
    (invperm : TupleN (JInt t) N → Result (TupleN (JInt t) N))
    (splatPerm : TupleN (JInt t) N → Result (TupleN (JInt t) N))
    (splatIperm : TupleN (JInt t) N → Result (TupleN (JInt t) N))
    (isperm : TupleN Index N → Result Bool)
    (all : List Index → (Index → Result Bool) → Result Bool)
    (tupleGet : TupleN Index N → Index → Result Index)
    (showInput : TupleN (JInt t) N → String)
    (render : TupleN (JInt t) N → String),
    length perm = .ok (int (Int.ofNat N)) →
    invperm perm = .ok inverse → splatPerm perm = .ok perm → splatIperm inverse = .ok inverse →
    IsIntegerPermutation perm → InversePermutation perm inverse →
    isperm (toIntTuple perm) = .ok true →
    all ((List.range N).map fun d => int (Int.ofNat d + 1)) (fun d => do
      let p ← tupleGet (toIntTuple perm) d
      let q ← tupleGet (toIntTuple inverse) p
      pure (q == d)) = .ok true →
    ∃ result : PermutedDimsArray T A N,
      constructPermutedDimsArray length invperm splatPerm splatIperm isperm all tupleGet
        showInput render render data perm = .ok result

/-! ## Shape, strides, access and copy contracts -/

def PermutedShape : Prop :=
  ∀ {T A Ax : Type} {N : Nat}
    (view : PermutedDimsArray T A N)
    (sizeParent : A → Result (TupleN Index N))
    (axesParent : A → Result (TupleN Ax N))
    (ntupleIndex : (n : Nat) → (Index → Result Index) → Result (TupleN Index n))
    (tupleGetIndex : TupleN Index N → Index → Result Index)
    (ntupleAxes : (n : Nat) → (Index → Result Ax) → Result (TupleN Ax n))
    (tupleGetAxes : TupleN Ax N → Index → Result Ax)
    (parentSize resultSize : TupleN Index N) (parentAxes resultAxes : TupleN Ax N),
    N ≤ 9223372036854775807 →
    TupleBuilderSound ntupleIndex → TupleReadSound tupleGetIndex →
    TupleBuilderSound ntupleAxes → TupleReadSound tupleGetAxes →
    sizeParent view.parent = .ok parentSize →
    JuliaLean.base.permuteddimsarray.size sizeParent ntupleIndex tupleGetIndex view = .ok resultSize →
    axesParent view.parent = .ok parentAxes →
    JuliaLean.base.permuteddimsarray.axes axesParent ntupleAxes tupleGetAxes tupleGetIndex view = .ok resultAxes →
    PermutedValues resultSize parentSize view.perm ∧
      PermutedValues resultAxes parentAxes view.perm

def PermutedStrides : Prop :=
  ∀ {T A : Type} {N : Nat}
    (view : PermutedDimsArray T A N) (stridesParent : A → Result (TupleN Index N))
    (ntuple : (n : Nat) → (Index → Result Index) → Result (TupleN Index n))
    (tupleGet : TupleN Index N → Index → Result Index)
    (parentStrides result : TupleN Index N),
    N ≤ 9223372036854775807 →
    TupleBuilderSound ntuple → TupleReadSound tupleGet →
    stridesParent view.parent = .ok parentStrides →
    strides stridesParent ntuple tupleGet view = .ok result →
    PermutedValues result parentStrides view.perm


def PointerOffsetUnsupported : Prop :=
  ∀ {T A X : Type} {N : Nat} (view : PermutedDimsArray T A N) (offset : X),
    pointer (m := Result) (R := Unit) view offset =
      .error (.argumentError "pointer(A, i) is deliberately unsupported for PermutedDimsArray")

def TiledAxisPartition : Prop :=
  ∀ axis : Axis,
    (∀ i, axis.contains i = true →
      ∃ start, start ∈ tileStartsAxis axis ∧ i ∈ tileValues start axis) ∧
    (∀ i start₁ start₂, start₁ ∈ tileStartsAxis axis → start₂ ∈ tileStartsAxis axis →
      i ∈ tileValues start₁ axis → i ∈ tileValues start₂ axis → start₁ = start₂) ∧
    (∀ start i, start ∈ tileStartsAxis axis → i ∈ tileValues start axis → axis.contains i = true)

def PermutedBangReturnsDestination : Prop :=
  ∀ {D S P IP T Ax : Type} {N : Nat}
    (axesDest : D → Result (TupleN Ax N)) (axesSrc : S → Result (TupleN Ax N))
    (checkdims : TupleN Ax N → TupleN Ax N → P → Result Unit)
    (invperm : P → Result IP) (construct : D → IP → Result (PermutedDimsArray T D N))
    (copy : PermutedDimsArray T D N → S → Result (PermutedDimsArray T D N))
    (dest : D) (src : S) (perm : P) (result : D),
    permutedimsBang axesDest axesSrc checkdims invperm construct copy dest src perm = .ok result →
    result = dest

def PermutedCopyContract : Prop := PermutedBangReturnsDestination ∧ TiledAxisPartition ∧ PermutedIndexedStorage

def PermutedVectorRow : Prop :=
  ∀ {A B Ids : Type}
    (length : A → Result Index) (reshape : A → TupleN Index 2 → Result B)
    (size : B → Result (TupleN Index 2))
    (dataidsParent : A → Result Ids) (dataidsRow : B → Result Ids)
    (vector : A) (n : Index) (row : B),
    (∀ data dims reshaped, reshape data dims = .ok reshaped →
      size reshaped = .ok dims ∧ dataidsRow reshaped = dataidsParent data) →
    length vector = .ok n → permutedimsVector length reshape vector = .ok row →
    ∃ dimensions, size row = .ok dimensions ∧ dimensions.values = [int 1, n] ∧
      dataidsRow row = dataidsParent vector

theorem permutedAnyIntType_refuted : ¬ PermutedAnyIntType := by
  intro property
  let p : TupleN (JInt .i32) 1 := ⟨[JInt.lit .i32 1], rfl⟩
  have permutation : IsIntegerPermutation p := by
    constructor
    · decide
    · intro x hx
      have equal : x = JInt.lit .i32 1 := List.mem_singleton.mp hx
      subst x
      decide
  have inverse : InversePermutation p p := by
    intro d hd
    have equal : d = 0 := by omega
    subst d
    exact ⟨JInt.lit .i32 1, rfl, rfl⟩
  have h := property (T := Unit) () p p
    (fun _ => .ok (int 1)) (fun x => .ok x) (fun x => .ok x) (fun x => .ok x)
    (fun _ => .ok true) (fun _ _ => .ok true) (fun _ _ => .ok (int 1))
    (fun _ => "") (fun _ => "") rfl rfl rfl rfl permutation inverse rfl rfl
  obtain ⟨result, h⟩ := h
  change (Except.error (.errorException "perm and iperm must both be NTuple{1,Int}") :
    Result (PermutedDimsArray Unit Unit 1)) = .ok result at h
  cases h

private def highAxis : Axis := ⟨int 9223372036854775807, int 1, 1⟩

theorem tiledAxisPartition_refuted : ¬ TiledAxisPartition := by
  intro property
  have contains : highAxis.contains (int 9223372036854775807) = true := by decide
  obtain ⟨start, hstart, hvalue⟩ := (property highAxis).1 _ contains
  have starts : tileStartsAxis highAxis = [int 9223372036854775807] := by decide
  rw [starts] at hstart
  have equal := List.mem_singleton.mp hstart
  subst start
  have empty : tileValues (int 9223372036854775807) highAxis = [] := by decide
  rw [empty] at hvalue
  exact List.not_mem_nil hvalue

theorem permutedCopyContract_refuted : ¬ PermutedCopyContract := by
  intro property
  exact tiledAxisPartition_refuted property.2.1

theorem pointerOffsetUnsupported_proven : PointerOffsetUnsupported := by
  intro T A X N view offset
  rfl

theorem permutedReadInvariant_proven : PermutedReadInvariant := by
  intro T A V N view indices parentIndices bounds read ntuple get value hb _ hp hv
  simp [getindex, hb, hp, hv, Bind.bind, Except.bind]

theorem permutedVectorRow_proven : PermutedVectorRow := by
  intro A B Ids length reshape size dataidsParent dataidsRow vector n row law hl hr
  have reshaped : reshape vector ⟨[int 1, n], by simp⟩ = .ok row := by
    simpa [permutedimsVector, hl, Bind.bind, Except.bind] using hr
  obtain ⟨hs, hi⟩ := law vector _ row reshaped
  exact ⟨_, hs, rfl, hi⟩

private theorem mutationOutcome_bind {T β γ : Type}
    (action : MutationResult T β) (next : β → MutationResult T γ)
    (initial final : JuliaLean.base.array.MutableMemory T) (value : β)
    (h : mutationOutcome action initial = (.ok (.ok value), final)) :
    mutationOutcome (action >>= next) initial = mutationOutcome (next value) final := by
  simp only [mutationOutcome, ExceptT.run, ExceptT.bind, ExceptT.mk,
    StateT.bind, Bind.bind] at *
  rw [h]
  rfl

theorem permutedSetEffect_proven : PermutedSetEffect := by
  intro T N view indices parentIndices value linear bounds set ntuple get initial final hb hp hs _ _
  unfold setindex
  rw [mutationOutcome_bind _ _ _ _ _ hb, mutationOutcome_bind _ _ _ _ _ hp,
    mutationOutcome_bind _ _ _ _ _ hs]
  rfl

theorem permutedAssignmentEffect_proven : PermutedAssignmentEffect := by
  constructor
  · intro T N view indices bounds assigned ntuple get initial hb
    unfold isassigned
    rw [mutationOutcome_bind _ _ _ _ _ hb]
    rfl
  · intro T N view indices parentIndices bounds assigned ntuple get initial value hb hp ha
    unfold isassigned
    rw [mutationOutcome_bind _ _ _ _ _ hb]
    change mutationOutcome (do
      let parentIndices ← genpermTuple ntuple get get indices view.iperm
      let x ← assigned view.parent parentIndices
      pure x) initial = _
    rw [mutationOutcome_bind _ _ _ _ _ hp]
    exact ha

theorem permutedIndexedStorage_proven : PermutedIndexedStorage :=
  ⟨permutedSetEffect_proven, permutedAssignmentEffect_proven⟩

private theorem dimensionIndexValue {N d : Nat}
    (bound : N ≤ 9223372036854775807) (hd : d < N) :
    (int (Int.ofNat d + 1)).val = Int.ofNat d + 1 := by
  change wrapInt .i64 (Int.ofNat d + 1) = Int.ofNat d + 1
  apply wrapInt_of_inRange .i64
  change -9223372036854775808 ≤ (d : Int) + 1 ∧
    (d : Int) + 1 ≤ 9223372036854775807
  omega

theorem genpermTuple_sound {α : Type} {N : Nat}
    (ntuple : (n : Nat) → (Index → Result α) → Result (TupleN α n))
    (getInput : TupleN α N → Index → Result α)
    (getPerm : TupleN Index N → Index → Result Index)
    (input result : TupleN α N) (perm : TupleN Index N)
    (bound : N ≤ 9223372036854775807) (builder : TupleBuilderSound ntuple)
    (inputLaw : TupleReadSound getInput) (permLaw : TupleReadSound getPerm)
    (h : genpermTuple ntuple getInput getPerm input perm = .ok result) :
    PermutedValues result input perm := by
  intro d hd
  obtain ⟨value, hvalue, hresult⟩ := builder N _ result h d hd
  change (do
    let p ← getPerm perm (int (Int.ofNat d + 1))
    getInput input p) = .ok value at hvalue
  cases hg : getPerm perm (int (Int.ofNat d + 1)) with
  | error error =>
    rw [hg] at hvalue
    cases hvalue
  | ok p =>
    have hv : getInput input p = .ok value := by
      rw [hg] at hvalue
      exact hvalue
    have hp := permLaw perm _ p hg
    have offset : ((int (Int.ofNat d + 1)).val - 1).toNat = d := by
      rw [dimensionIndexValue bound hd]
      simp
    rw [offset] at hp
    exact ⟨p, value, hp, inputLaw input p value hv, hresult⟩

theorem permutedShape_proven : PermutedShape := by
  intro T A Ax N view sizeParent axesParent ntupleIndex getIndex ntupleAxes getAxes
    parentSize resultSize parentAxes resultAxes bound builderIndex readIndex builderAxes readAxes
    hs hr ha har
  constructor
  · apply genpermTuple_sound ntupleIndex getIndex getIndex parentSize resultSize view.perm
      bound builderIndex readIndex readIndex
    simpa [JuliaLean.base.permuteddimsarray.size, hs, Bind.bind, Except.bind] using hr
  · apply genpermTuple_sound ntupleAxes getAxes getIndex parentAxes resultAxes view.perm
      bound builderAxes readAxes readIndex
    simpa [JuliaLean.base.permuteddimsarray.axes, ha, Bind.bind, Except.bind] using har

theorem permutedStrides_proven : PermutedStrides := by
  intro T A N view stridesParent ntuple get parentStrides result bound builder read hs hr
  apply genpermTuple_sound ntuple get get parentStrides result view.perm bound builder read read
  simpa [strides, genpermTuple, hs, Bind.bind, Except.bind] using hr

theorem permutedConstructorInvariant_proven : PermutedConstructorInvariant := by
  intro T A N t u data perm iperm isperm all get renderPerm renderIperm result
    bound permLaw allLaw getLaw h
  let predicate := fun d => do
    let p ← get (toIntTuple perm) d
    let inverse ← get (toIntTuple iperm) p
    pure (inverse == d)
  let dimensions := (List.range N).map fun d => int (Int.ofNat d + 1)
  have checked : isperm (toIntTuple perm) = .ok true ∧
      all dimensions predicate = .ok true ∧
      result = ⟨data, toIntTuple perm, toIntTuple iperm⟩ := by
    unfold innerConstructor at h
    split at h
    next =>
      dsimp only at h
      cases hp : isperm (toIntTuple perm) with
      | error e => simp [hp, Bind.bind, Except.bind] at h
      | ok valid =>
        cases valid with
        | false => simp [hp, Bind.bind, Except.bind] at h
        | true =>
          rw [hp] at h
          change (do
            let inverses ← all dimensions predicate
            if !inverses then
              throw (Error.argumentError (renderPerm perm ++ " and " ++ renderIperm iperm ++ " must be inverses"))
            pure (⟨data, toIntTuple perm, toIntTuple iperm⟩ : PermutedDimsArray T A N)) =
              .ok result at h
          cases ha : all dimensions predicate with
          | error e => rw [ha] at h; cases h
          | ok inverse =>
            cases inverse with
            | false => rw [ha] at h; cases h
            | true =>
              refine ⟨rfl, rfl, ?_⟩
              rw [ha] at h
              exact (Except.ok.inj h).symm
    next => cases h
  obtain ⟨hp, ha, rfl⟩ := checked
  refine ⟨rfl, rfl, rfl, permLaw _ hp, ?_⟩
  intro d hd
  have membership : int (Int.ofNat d + 1) ∈ dimensions := by
    exact List.mem_map.mpr ⟨d, List.mem_range.mpr hd, rfl⟩
  have test := allLaw dimensions predicate ha _ membership
  change (do
    let p ← get (toIntTuple perm) (int (Int.ofNat d + 1))
    let inverse ← get (toIntTuple iperm) p
    pure (inverse == int (Int.ofNat d + 1))) = .ok true at test
  cases hg : get (toIntTuple perm) (int (Int.ofNat d + 1)) with
  | error e => rw [hg] at test; cases test
  | ok p =>
    rw [hg] at test
    change (do
      let inverse ← get (toIntTuple iperm) p
      pure (inverse == int (Int.ofNat d + 1))) = .ok true at test
    cases hi : get (toIntTuple iperm) p with
    | error e => rw [hi] at test; cases test
    | ok inverse =>
      rw [hi] at test
      change Except.ok (inverse.val == (int (Int.ofNat d + 1)).val) = .ok true at test
      have equal : inverse = int (Int.ofNat d + 1) := by
        apply Subtype.ext
        exact of_decide_eq_true (Except.ok.inj test)
      obtain ⟨k, hk, hvalue⟩ := getLaw _ _ _ hg
      have kd : k = d := by
        rw [dimensionIndexValue bound hd] at hk
        change (d : Int) + 1 = (k : Int) + 1 at hk
        omega
      subst k
      obtain ⟨j, hj, hinverse⟩ := getLaw _ _ _ hi
      have jvalue : (p.val - 1).toNat = j := by rw [hj]; simp
      refine ⟨p, hvalue, ?_⟩
      rw [jvalue, hinverse, equal]
      rfl

theorem permutedCorrect_proven : PermutedCorrect :=
  ⟨permutedConstructorInvariant_proven, permutedReadInvariant_proven⟩

/-! Nothing to promise: parent@48: returns the stored parent field, a structural projection.
Nothing to promise: has_offset_axes@51: forwards offset-axis detection to the parent.
Nothing to promise: similar@52: forwards allocation to the parent interface.
Nothing to promise: dataids@53: forwards alias identity to the parent.
Nothing to promise: unaliascopy@54: reconstructs the same wrapper around the parent's unaliascopy result.
Nothing to promise: cconvert@55: forwards pointer conversion to the parent.
Nothing to promise: elsize@68: forwards element size to the parent array type.
Nothing to promise: _mapreduce_dim@351: dispatches the reduction to the parent.
Nothing to promise: _mapreduce_dim@354: dispatches the product reduction to the parent.
Nothing to promise: mapreducedim!@358: wraps the destination and forwards reduction.
Nothing to promise: mapreducedim!@363: wraps the product destination and forwards reduction.
Nothing to promise: showarg@369: writes the wrapper's display components through Julia's IO interface.
-/

/-! Method -> property table:
PermutedDimsArray{T,N,perm,iperm,AA}@12 -> reinterpretarrays-permuted-index
PermutedDimsArray(data::AbstractArray,perm)@42 -> reinterpretarrays-permuted-index, reinterpretarrays-permuted-int-type
parent(::PermutedDimsArray)@48 -> nothing-to-promise
size(::PermutedDimsArray)@49 -> permuteddims-shape-axes
axes(::PermutedDimsArray)@50 -> permuteddims-shape-axes
has_offset_axes(::PermutedDimsArray)@51 -> nothing-to-promise
similar(::PermutedDimsArray,T,dims)@52 -> nothing-to-promise
dataids(::PermutedDimsArray)@53 -> nothing-to-promise
unaliascopy(::PermutedDimsArray)@54 -> nothing-to-promise
cconvert(::Ptr,::PermutedDimsArray)@55 -> nothing-to-promise
pointer(::PermutedDimsArray,Integer)@62 -> permuteddims-pointer-offset
strides(::PermutedDimsArray)@64 -> permuteddims-strides
elsize(::Type{<:PermutedDimsArray})@68 -> nothing-to-promise
getindex(::PermutedDimsArray,I...)@70 -> reinterpretarrays-permuted-index, permuteddims-indexed-storage
setindex!(::PermutedDimsArray,val,I...)@75 -> permuteddims-indexed-storage
isassigned(::PermutedDimsArray,I...)@81 -> permuteddims-indexed-storage
genperm(::NTuple,::Dims)@87 -> reinterpretarrays-permuted-index
genperm(I,::AbstractVector{Int})@88 -> reinterpretarrays-permuted-index
permutedims(::AbstractArray,perm)@198 -> permuteddims-copy-contract
permutedims(::AbstractMatrix)@203 -> permuteddims-shape-axes, permuteddims-copy-contract
permutedims(::AbstractVector)@273 -> permuteddims-vector-row
permutedims!(dest,src,perm)@286 -> permuteddims-copy-contract
copyto!(::PermutedDimsArray,::AbstractArray)@293 -> permuteddims-copy-contract
_copy!(::PermutedDimsArray,src)@300 -> permuteddims-copy-contract
_permutedims!(...,::CartesianIndices{0},...)@319 -> permuteddims-copy-contract, permuteddims-tile-ranges
_permutedims!(...,R1,...)@333 -> permuteddims-copy-contract, permuteddims-tile-ranges
_mapreduce_dim(::CommutativeOps)@351 -> nothing-to-promise
_mapreduce_dim(identity,product)@354 -> nothing-to-promise
mapreducedim!(::CommutativeOps)@358 -> nothing-to-promise
mapreducedim!(identity,product)@363 -> nothing-to-promise
showarg(::PermutedDimsArray)@369 -> nothing-to-promise
-/

def entry (id : String) (juliaFns : List String) (statement source : String)
    (prop : Lean.Name) (status : Status) (thm : Lean.Name) (issue : String := "") : Entry :=
  { id := id, juliaFile := "base/permuteddimsarray.jl", juliaFns := juliaFns,
    statement := statement, source := source, status := status, prop := prop, thm := some thm,
    issue := issue }

def entries : List Entry := [
  entry "reinterpretarrays-permuted-index"
    ["PermutedDimsArray{T,N,perm,iperm,AA}@12", "PermutedDimsArray(data::AbstractArray,perm)@42",
      "getindex(::PermutedDimsArray,I...)@70", "genperm(::NTuple,::Dims)@87", "genperm(I,::AbstractVector{Int})@88"]
    "For a permutation with Int entries, construction enforces both inverse mappings and in-bounds B[I...] reads A[J...] with J[perm[d]] = I[d]."
    "base/permuteddimsarray.jl:12-46,70-88; PermutedDimsArray docstring:20-40"
    ``PermutedCorrect .proven ``permutedCorrect_proven,
  entry "reinterpretarrays-permuted-int-type"
    ["PermutedDimsArray(data::AbstractArray,perm)@42"]
    "PermutedDimsArray accepts every permutation of 1:ndims(A), whatever integer type its entries have."
    "base/permuteddimsarray.jl:20-27,42-46; permutedims contract:94-95"
    ``PermutedAnyIntType .refuted ``permutedAnyIntType_refuted
    "none found (queries: perm and iperm must both be NTuple, PermutedDimsArray Int32, PermutedDimsArray perm type, PermutedDimsArray non-Int, PermutedDimsArray integer permutation)",
  entry "permuteddims-shape-axes"
    ["size(::PermutedDimsArray)@49", "axes(::PermutedDimsArray)@50", "permutedims(::AbstractMatrix)@203"]
    "Each result dimension and axis is the parent dimension or axis selected by the corresponding permutation entry; the matrix convenience method swaps dimensions 1 and 2."
    "base/permuteddimsarray.jl:49-50,181-182,203"
    ``PermutedShape .proven ``permutedShape_proven,
  entry "permuteddims-indexed-storage"
    ["setindex!(::PermutedDimsArray,val,I...)@75", "isassigned(::PermutedDimsArray,I...)@81"]
    "A checked write changes the parent cell at the inverse-permuted index and returns the assigned value; isassigned queries that same parent cell and returns false outside the view bounds."
    "base/permuteddimsarray.jl:23-25,75-85; shared-storage docstring:20-25"
    ``PermutedIndexedStorage .proven ``permutedIndexedStorage_proven,
  entry "permuteddims-pointer-offset"
    ["pointer(::PermutedDimsArray,Integer)@62"]
    "pointer(A, i) always throws ArgumentError because a linear offset is ambiguous for a permuted view."
    "base/permuteddimsarray.jl:57-62" ``PointerOffsetUnsupported .proven ``pointerOffsetUnsupported_proven,
  entry "permuteddims-strides"
    ["strides(::PermutedDimsArray)@64"]
    "Each view stride is the parent stride selected by the corresponding permutation entry."
    "base/permuteddimsarray.jl:64-67" ``PermutedStrides .proven ``permutedStrides_proven,
  entry "permuteddims-copy-contract"
    ["permutedims(::AbstractArray,perm)@198", "permutedims(::AbstractMatrix)@203", "permutedims!(dest,src,perm)@286",
      "copyto!(::PermutedDimsArray,::AbstractArray)@293", "_copy!(::PermutedDimsArray,src)@300",
      "_permutedims!(...,::CartesianIndices{0},...)@319", "_permutedims!(...,R1,...)@333"]
    "For a valid, shape-compatible permutation, copying preserves source element values at their permuted coordinates, overwrites the destination, and returns the supplied destination; tiled loops cover each axis exactly once."
    "permutedims docstring base/permuteddimsarray.jl:90-106,181-182; permutedims! docstring:275-284; bodies:198-201,286-347"
    ``PermutedCopyContract .refuted ``permutedCopyContract_refuted
    "none found (queries: permuteddims overflow; permutedims offset axes; permutedims tile; permutedims typemax)",
  entry "permuteddims-vector-row"
    ["permutedims(::AbstractVector)@273"]
    "permutedims(v) has shape 1 × length(v) and shares the vector's data."
    "permutedims vector docstring base/permuteddimsarray.jl:205-224,247-254,273"
    ``PermutedVectorRow .proven ``permutedVectorRow_proven,
  entry "permuteddims-tile-ranges"
    ["_permutedims!(...,::CartesianIndices{0},...)@319", "_permutedims!(...,R1,...)@333"]
    "Every coordinate visited by an eight-wide tile belongs to its source axis, and the tiles partition each axis without gaps or overlaps."
    "computed tile bounds and @inbounds assignments, base/permuteddimsarray.jl:319-347"
    ``TiledAxisPartition .refuted ``tiledAxisPartition_refuted
    "none found (queries: permuteddims overflow; permutedims offset axes; permutedims tile; permutedims typemax)"
]

end JuliaLean.Proofs.base.permuteddimsarray
