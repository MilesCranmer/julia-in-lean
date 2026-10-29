import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.MultidimensionalRepairE

open JuliaLean.Registry

inductive Error where | argument | dimensionMismatch | bounds | source (id : Nat) deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

def isPermutation (perm : List Nat) (rank : Nat) : Bool :=
  decide (perm.length = rank) &&
    decide (perm.mergeSort (· < ·) = (List.range rank).map (· + 1))

def permuteDimensions (dimensions perm : List Nat) : List Nat :=
  perm.map fun dimension => dimensions[dimension - 1]?.getD 0

def permutedims (size : A → Result (List Nat)) (similar : A → List Nat → Result B)
    (permutedimsBang : B → A → List Nat → Result B)
    (array : A) (perm : List Nat) : Result B :=
  match size array with
  | .error error => .error error
  | .ok dimensions =>
      if !isPermutation perm dimensions.length then .error .argument else
      let target := permuteDimensions dimensions perm
      match similar array target with
      | .error error => .error error
      | .ok destination => permutedimsBang destination array perm

def sizeToStrides : List Nat → List Nat
  | [] => []
  | first :: rest => 1 :: strides first rest
where
  strides : Nat → List Nat → List Nat
    | _, [] => []
    | stride, dimension :: rest => stride :: strides (stride * dimension) rest

def permutedimsLoop (source : List V) (dimensions perm : List Nat)
    (destinationCoordinates : List (List Nat)) : Result (List V) :=
  if !isPermutation perm dimensions.length then .error .argument else
  let native := sizeToStrides dimensions
  let strides := perm.map fun dimension => native[dimension - 1]!
  let offset : Int := 1 - Int.ofNat (strides.foldl (· + ·) 0)
  destinationCoordinates.mapM fun coordinate =>
    let linear : Int := offset + Int.ofNat ((List.zip coordinate strides).foldl
      (fun total pair => total + pair.1 * pair.2) 0)
    match source[(linear - 1).toNat]? with
    | none => .error .bounds
    | some value => .ok value

def permutedimsBang (checkDims : List Nat → Result Unit) (source : List V)
    (dimensions perm : List Nat) (destinationCoordinates : List (List Nat)) : Result (List V) :=
  match checkDims perm with
  | .error error => .error error
  | .ok _ => permutedimsLoop source dimensions perm destinationCoordinates

def findEquivalent (equal : R → R → Bool) (rows : List R) (candidates : List Nat)
    (row : R) : Option Nat := candidates.find? fun index =>
      match rows[index]? with | some candidate => equal candidate row | none => false

def uniqueRows (hash : R → UInt64) (equal : R → R → Bool) (rows : List R) : List Nat :=
  loop rows [] [] 0
where
  loop : List R → List (UInt64 × List Nat) → List Nat → Nat → List Nat
    | [], _, unique, _ => unique
    | row :: rest, buckets, unique, index =>
        let rowHash := hash row
        let candidates := (buckets.find? fun bucket => bucket.1 = rowHash).map (·.2) |>.getD []
        match findEquivalent equal rows candidates row with
        | some _ => loop rest buckets unique (index + 1)
        | none =>
            let updated := if candidates = [] then (rowHash, [index]) :: buckets else
              buckets.map fun bucket => if bucket.1 = rowHash then (rowHash, bucket.2 ++ [index]) else bucket
            loop rest updated (unique ++ [index]) (index + 1)

theorem uniqueLoop_bound (hash : R → UInt64) (equal : R → R → Bool) (rows : List R) :
    ∀ remaining buckets unique index,
      (∀ value ∈ unique, value < rows.length) → index + remaining.length = rows.length →
      ∀ value ∈ uniqueRows.loop hash equal rows remaining buckets unique index,
        value < rows.length := by
  intro remaining
  induction remaining with
  | nil => intro buckets unique index hu hlen value hv; exact hu value hv
  | cons row rest ih =>
      intro buckets unique index hu hlen value hv
      simp at hlen
      simp only [uniqueRows.loop] at hv
      split at hv
      · apply ih _ unique (index + 1) hu (by omega) value hv
      · apply ih _ (unique ++ [index]) (index + 1)
          (by
            intro candidate hc
            simp at hc
            rcases hc with hc | rfl
            · exact hu candidate hc
            · omega)
          (by omega) value hv

theorem uniqueRows_bound (hash : R → UInt64) (equal : R → R → Bool) (rows : List R) :
    ∀ value ∈ uniqueRows hash equal rows, value < rows.length := by
  exact uniqueLoop_bound hash equal rows rows [] [] 0 (by simp) (by simp)

def selectUniqueDimension (copy : A → Result A) (rows : A → D → Result (List R))
    (hash : R → UInt64) (equal : R → R → Bool) (select : A → D → List Nat → Result A)
    (array : A) (dimension : Int) (rank : Nat) (dim : D) : Result A :=
  if dimension < 1 ∨ dimension > rank then copy array else
  match rows array dim with
  | .error error => .error error
  | .ok rowValues => select array dim (uniqueRows hash equal rowValues)

def sortslices (matrixFastPath : Bool) (fast : A → Result A) (similar : A → Result A)
    (sortBang : A → A → Result Unit) (array : A) : Result A :=
  if matrixFastPath then fast array else match similar array with
  | .error error => .error error
  | .ok destination => match sortBang destination array with
    | .error error => .error error
    | .ok _ => .ok destination

def sortslicesBang (eachslice : A → Result (List S)) (sortperm : List S → Result (List Nat))
    (destinationSlices : B → Result (List D)) (assign : D → S → Result Unit)
    (destination : B) (source : A) : Result Unit :=
  match eachslice source with
  | .error error => .error error
  | .ok slices => match sortperm slices with
    | .error error => .error error
    | .ok permutation => match destinationSlices destination with
      | .error error => .error error
      | .ok outputs => assignLoop outputs permutation slices
where
  assignLoop : List D → List Nat → List S → Result Unit
    | [], _, _ | _, [], _ => .ok ()
    | output :: outputs, index :: indices, slices => match slices[index - 1]? with
      | none => .error .bounds
      | some slice => match assign output slice with
        | .error error => .error error
        | .ok _ => assignLoop outputs indices slices

def refGetindex (getindex : R → Result V) (reference : R) := getindex reference
def refSetindex (setindex : R → V → Result O) (reference : R) (value : V) := setindex reference value

def fibonacciHashIndices (length firstIndex : Nat) : List Nat :=
  loop length (firstIndex + length - 1) 1 1 1 []
where
  loop : Nat → Nat → Nat → Nat → Nat → List Nat → List Nat
    | 0, _, _, _, _, output => output
    | fuel + 1, index, skip, previous, iteration, output =>
        if index < skip + firstIndex then output ++ [index] else
        let nextIndex := index - skip
        let nextSkip := if iteration % 4096 = 0 then skip + previous else skip
        let nextPrevious := if iteration % 4096 = 0 then skip else previous
        loop fuel nextIndex nextSkip nextPrevious (iteration + 1) (output ++ [index])

def hashSequential (hash : V → UInt64 → UInt64) (values : List V) (seed : UInt64) : UInt64 :=
  values.foldl (fun state value => hash value state) seed

def hashEightStreams (hash mix : UInt64 → UInt64 → UInt64)
    (values : List UInt64) (seed : UInt64) : UInt64 :=
  let streams := values.zipIdx.foldl (fun state pair =>
    state.set (pair.2 % 8) (hash pair.1 state[pair.2 % 8]!)) (List.replicate 8 seed)
  streams.foldl (fun state stream => mix stream state) seed

def hashShaped (hashEndpoints : List Int → UInt64 → UInt64)
    (hashValue : V → UInt64 → UInt64) (mix : UInt64 → UInt64 → UInt64)
    (hashUInt : UInt64 → UInt64) (hashFib : List V → UInt64 → UInt64)
    (firsts lasts : List Int) (values : List V) (seed : UInt64) : UInt64 :=
  let shaped := hashEndpoints lasts (hashEndpoints firsts seed)
  if values.length < 8 then hashSequential hashValue values shaped
  else if values.length < 32768 then
    let streams := values.zipIdx.foldl (fun state pair =>
      state.set (pair.2 % 8) (hashValue pair.1 state[pair.2 % 8]!)) (List.replicate 8 shaped)
    hashUInt (streams.foldl (fun state stream => mix stream state) shaped)
  else hashFib values shaped

def Contract : Prop :=
  (∀ {A B : Type} size similar copy array perm output,
    permutedims (A := A) (B := B) size similar copy array perm = .ok output →
      ∃ dimensions destination, size array = .ok dimensions ∧ isPermutation perm dimensions.length = true ∧
        similar array (permuteDimensions dimensions perm) = .ok destination ∧
        copy destination array perm = .ok output) ∧
  (∀ {V : Type} check source dimensions perm coordinates output,
    permutedimsBang (V := V) check source dimensions perm coordinates = .ok output →
      check perm = .ok () ∧ output.length = coordinates.length) ∧
  (∀ {R : Type} hash equal rows value,
    value ∈ uniqueRows (R := R) hash equal rows → value < rows.length) ∧
  (∀ {A : Type} fastPath fast similar sortBang array output,
    sortslices (A := A) fastPath fast similar sortBang array = .ok output →
      (fastPath = true ∧ fast array = .ok output) ∨
      ∃ destination, fastPath = false ∧ similar array = .ok destination ∧
        sortBang destination array = .ok () ∧ output = destination) ∧
  (∀ {R V : Type} getindex reference, refGetindex (R := R) (V := V) getindex reference = getindex reference) ∧
  (∀ {R V O : Type} setindex reference value,
    refSetindex (R := R) (V := V) (O := O) setindex reference value = setindex reference value) ∧
  (∀ {V : Type} hashEndpoints hashValue mix hashUInt hashFib firsts lasts values seed,
    hashShaped (V := V) hashEndpoints hashValue mix hashUInt hashFib firsts lasts values seed =
      if values.length < 8 then
        hashSequential hashValue values (hashEndpoints lasts (hashEndpoints firsts seed))
      else if values.length < 32768 then
        let shaped := hashEndpoints lasts (hashEndpoints firsts seed)
        let streams := values.zipIdx.foldl (fun state pair =>
          state.set (pair.2 % 8) (hashValue pair.1 state[pair.2 % 8]!)) (List.replicate 8 shaped)
        hashUInt (streams.foldl (fun state stream => mix stream state) shaped)
      else hashFib values (hashEndpoints lasts (hashEndpoints firsts seed)))

theorem mapM_length {E A B : Type} (f : A → Except E B) : ∀ (xs : List A) (ys : List B),
    List.mapM f xs = Except.ok ys → ys.length = xs.length := by
  intro xs
  induction xs with
  | nil => intro ys h; simpa using congrArg List.length (Except.ok.inj h).symm
  | cons x xs ih =>
      intro ys h
      cases hx : f x with
      | error e => simp [List.mapM_cons, hx, bind, Except.bind] at h
      | ok y =>
          cases ht : xs.mapM f with
          | error e => simp [List.mapM_cons, hx, ht, bind, Except.bind] at h
          | ok tail => simp [List.mapM_cons, hx, ht, bind, Except.bind, pure, Except.pure] at h
                       subst ys; simp [ih tail ht]

theorem contract : Contract := by
  unfold Contract
  refine ⟨?_, ?_, ?_, ?_, fun _ _ => rfl, fun _ _ _ => rfl, ?_⟩
  · intro A B size similar copy array perm output h
    cases hs : size array with
    | error error => simp [permutedims, hs] at h
    | ok dimensions =>
        by_cases hp : isPermutation perm dimensions.length
        · cases hm : similar array (permuteDimensions dimensions perm) with
          | error error => simp [permutedims, hs, hp, hm] at h
          | ok destination => exact ⟨dimensions, destination, rfl, hp, hm,
              by simpa [permutedims, hs, hp, hm] using h⟩
        · simp [permutedims, hs, hp] at h
  · intro V check source dimensions perm coordinates output h
    cases hc : check perm with
    | error error => simp [permutedimsBang, hc] at h
    | ok checked =>
        by_cases hp : isPermutation perm dimensions.length
        · exact ⟨rfl, mapM_length _ _ _ (by
            simpa [permutedimsBang, hc, permutedimsLoop, hp] using h)⟩
        · simp [permutedimsBang, hc, permutedimsLoop, hp] at h
  · intro R hash equal rows value member
    exact uniqueRows_bound hash equal rows value member
  · intro A fastPath fast similar sortBang array output h
    cases fastPath
    · cases hs : similar array with
      | error error => simp [sortslices, hs] at h
      | ok destination =>
          cases hb : sortBang destination array with
          | error error => simp [sortslices, hs, hb] at h
          | ok checked => simp [sortslices, hs, hb] at h; exact Or.inr ⟨destination, rfl, rfl, hb, h.symm⟩
    · exact Or.inl ⟨rfl, by simpa [sortslices] using h⟩
  · intros
    rfl

def entries : List Entry := []

end JuliaLean.MultidimCov.MultidimensionalRepairE
