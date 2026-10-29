import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.MultidimensionalRepairC2

open JuliaLean.Registry

inductive Error where | source (id : Nat) | bounds deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

structure LogicalState (K S : Type) where
  count : Nat
  iterator : List K
  state : S
  deriving Repr, DecidableEq

def collectLogical (sum : Nat) (iterate : S → Result (Option (K × S))) :
    Nat → S → Result (List K)
  | 0, _ => .ok []
  | fuel + 1, state =>
      match iterate state with
      | .error error => .error error
      | .ok none => .ok []
      | .ok (some (value, next)) =>
          match collectLogical sum iterate fuel next with
          | .error error => .error error
          | .ok tail => .ok (value :: tail)

def iterateLinearInitial (linearIndices : M → Result R)
    (iterate : Nat → R → Result O) (mask : M) : Result O :=
  match linearIndices mask with
  | .error error => .error error
  | .ok indices => iterate 1 indices

def iterateCartesianInitial (axes : M → Result AX) (cartesianIndices : AX → Result R)
    (iterate : Nat → R → Result O) (mask : M) : Result O :=
  match axes mask with
  | .error error => .error error
  | .ok maskAxes => match cartesianIndices maskAxes with
    | .error error => .error error
    | .ok indices => iterate 1 indices

def iterateLogical (sum count : Nat) (mask : K → Result Bool) :
    List K → Result (Option (K × Nat × List K))
  | indices =>
      if count > sum then .ok none else scan indices
where
  scan : List K → Result (Option (K × Nat × List K))
    | [] => .ok none
    | index :: rest => match mask index with
      | .error error => .error error
      | .ok true => .ok (some (index, count + 1, rest))
      | .ok false => scan rest

structure BitState (Tail : Type) where
  firstIndex : Nat
  chunkIndex : Nat
  tail : Tail
  chunk : UInt64
  deriving Repr, DecidableEq

def bitLinearInitial (sum : Nat) (chunks : List UInt64) : Result (Option (BitState Unit)) :=
  if sum = 0 then .ok none else match chunks with
  | [] => .error .bounds
  | chunk :: _ => .ok (some ⟨1, 1, (), chunk⟩)

def bitCartesianInitial (sum rank : Nat) (chunks : List UInt64) :
    Result (Option (BitState (List Nat))) :=
  if sum = 0 then .ok none else match chunks with
  | [] => .error .bounds
  | chunk :: _ => .ok (some ⟨1, 1, List.replicate (rank - 1) 1, chunk⟩)

def scanNonzeroChunkFuel (chunks : List UInt64) : Nat → Nat → Nat → UInt64 → Option (Nat × Nat × UInt64)
  | 0, _, _, _ => none
  | fuel + 1, firstIndex, chunkIndex, chunk =>
      if chunk ≠ 0 then some (firstIndex, chunkIndex, chunk)
      else if chunkIndex ≥ chunks.length then none
      else match chunks[chunkIndex]? with
        | none => none
        | some next => scanNonzeroChunkFuel chunks fuel (firstIndex + 64) (chunkIndex + 1) next

def scanNonzeroChunk (chunks : List UInt64) (firstIndex chunkIndex : Nat) (chunk : UInt64) :=
  scanNonzeroChunkFuel chunks (chunks.length + 1) firstIndex chunkIndex chunk

structure BitOutput (K Tail : Type) where
  value : K
  state : BitState Tail
  deriving Repr, DecidableEq

def bitIterate (trailingZeros : UInt64 → Nat) (clearLowBit : UInt64 → UInt64)
    (overflowIndex : Nat → Tail → Result (Nat × Tail))
    (construct : Nat → Tail → Result K) (chunks : List UInt64)
    (state : BitState Tail) : Result (Option (BitOutput K Tail)) :=
  match scanNonzeroChunk chunks state.firstIndex state.chunkIndex state.chunk with
  | none => .ok none
  | some (firstIndex, chunkIndex, chunk) =>
      let zeros := trailingZeros chunk
      match overflowIndex (firstIndex + zeros) state.tail with
      | .error error => .error error
      | .ok (nextFirst, nextTail) => match construct nextFirst nextTail with
        | .error error => .error error
        | .ok value => .ok (some ⟨value,
            ⟨nextFirst - zeros, chunkIndex, nextTail, clearLowBit chunk⟩⟩)

def ensureIndexable (collect : L → Result C) (ensureTail : List I → Result (List O))
    (head : L) (tail : List I) : Result (C × List O) :=
  match collect head with
  | .error error => .error error
  | .ok collected => match ensureTail tail with
    | .error error => .error error
    | .ok ensured => .ok (collected, ensured)

def Contract : Prop :=
  (∀ {K S : Type} sum iterate state output,
    collectLogical (K := K) (S := S) sum iterate sum state = .ok output → output.length ≤ sum) ∧
  (∀ {M R O : Type} linearIndices iterate mask output,
    iterateLinearInitial (M := M) (R := R) (O := O) linearIndices iterate mask = .ok output →
      ∃ indices, linearIndices mask = .ok indices ∧ iterate 1 indices = .ok output) ∧
  (∀ {M AX R O : Type} axes construct iterate mask output,
    iterateCartesianInitial (M := M) (AX := AX) (R := R) (O := O)
      axes construct iterate mask = .ok output →
      ∃ maskAxes indices, axes mask = .ok maskAxes ∧ construct maskAxes = .ok indices ∧
        iterate 1 indices = .ok output) ∧
  (∀ {K : Type} sum count mask indices output,
    iterateLogical (K := K) sum count mask indices = .ok (some output) →
      count ≤ sum ∧ output.2.1 = count + 1) ∧
  (∀ sum chunks state, bitLinearInitial sum chunks = .ok (some state) →
      sum ≠ 0 ∧ state.firstIndex = 1 ∧ state.chunkIndex = 1) ∧
  (∀ sum rank chunks state, bitCartesianInitial sum rank chunks = .ok (some state) →
      sum ≠ 0 ∧ state.tail = List.replicate (rank - 1) 1) ∧
  (∀ {K Tail : Type} trailingZeros clearLowBit overflowIndex construct chunks state output,
    bitIterate (K := K) (Tail := Tail) trailingZeros clearLowBit overflowIndex construct chunks state =
      .ok (some output) → ∃ firstIndex chunkIndex chunk,
        scanNonzeroChunk chunks state.firstIndex state.chunkIndex state.chunk =
          some (firstIndex, chunkIndex, chunk) ∧ output.state.chunkIndex = chunkIndex) ∧
  (∀ {L C I O : Type} collect ensureTail head tail output,
    ensureIndexable (L := L) (C := C) (I := I) (O := O)
      collect ensureTail head tail = .ok output →
      collect head = .ok output.1 ∧ ensureTail tail = .ok output.2)

theorem collectLogical_length {K S : Type} (sum : Nat) (iterate : S → Result (Option (K × S))) :
    ∀ fuel state output, collectLogical sum iterate fuel state = .ok output → output.length ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro state output h; simpa [collectLogical] using congrArg List.length (Except.ok.inj h).symm
  | succ fuel ih =>
      intro state output h
      cases hi : iterate state with
      | error error => simp [collectLogical, hi] at h
      | ok option =>
          cases option with
          | none => simp [collectLogical, hi] at h; subst output; simp
          | some pair =>
              cases pair with
              | mk value next =>
                  cases ht : collectLogical sum iterate fuel next with
                  | error error => simp [collectLogical, hi, ht] at h
                  | ok tail =>
                      simp [collectLogical, hi, ht] at h
                      subst output
                      have := ih next tail ht
                      simp_all

theorem scanLogical_count {K : Type} (count : Nat) (mask : K → Result Bool) :
    ∀ indices output, iterateLogical.scan count mask indices = .ok (some output) →
      output.2.1 = count + 1 := by
  intro indices
  induction indices with
  | nil => simp [iterateLogical.scan]
  | cons index rest ih =>
      intro output h
      cases hm : mask index with
      | error error => simp [iterateLogical.scan, hm] at h
      | ok matched =>
          cases matched
          · exact ih output (by simpa [iterateLogical.scan, hm] using h)
          · simp [iterateLogical.scan, hm] at h
            subst output
            rfl

theorem contract : Contract := by
  unfold Contract
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros
    exact collectLogical_length _ _ _ _ _ ‹_›
  · intro M R O linearIndices iterate mask output h
    cases hi : linearIndices mask with
    | error error => simp [iterateLinearInitial, hi] at h
    | ok indices => exact ⟨indices, rfl, by simpa [iterateLinearInitial, hi] using h⟩
  · intro M AX R O axes construct iterate mask output h
    cases ha : axes mask with
    | error error => simp [iterateCartesianInitial, ha] at h
    | ok maskAxes =>
        cases hc : construct maskAxes with
        | error error => simp [iterateCartesianInitial, ha, hc] at h
        | ok indices => exact ⟨maskAxes, indices, rfl, hc,
            by simpa [iterateCartesianInitial, ha, hc] using h⟩
  · intro K sum count mask indices output h
    by_cases hd : count > sum
    · simp [iterateLogical, hd] at h
    · have hc : count ≤ sum := by omega
      simp [iterateLogical, hd] at h
      exact ⟨hc, scanLogical_count count mask indices output h⟩
  · intro sum chunks state h
    by_cases hz : sum = 0
    · simp [bitLinearInitial, hz] at h
    · cases chunks <;> simp [bitLinearInitial, hz] at h ⊢
      subst state
      simp
  · intro sum rank chunks state h
    by_cases hz : sum = 0
    · simp [bitCartesianInitial, hz] at h
    · cases chunks <;> simp [bitCartesianInitial, hz] at h ⊢
      subst state
      simp
  · intro K Tail trailingZeros clearLowBit overflowIndex construct chunks state output h
    unfold bitIterate at h
    cases hs : scanNonzeroChunk chunks state.firstIndex state.chunkIndex state.chunk with
    | none => simp [hs] at h
    | some scanned =>
        rcases scanned with ⟨firstIndex, chunkIndex, chunk⟩
        cases ho : overflowIndex (firstIndex + trailingZeros chunk) state.tail with
        | error error => simp [hs, ho] at h
        | ok overflowed =>
            rcases overflowed with ⟨nextFirst, nextTail⟩
            cases hc : construct nextFirst nextTail with
            | error error => simp [hs, ho, hc] at h
            | ok value =>
                simp [hs, ho, hc] at h
                subst output
                exact ⟨firstIndex, chunkIndex, chunk, rfl, rfl⟩
  · intro L C I O collect ensureTail head tail output h
    cases hc : collect head with
    | error error => simp [ensureIndexable, hc] at h
    | ok collected =>
        cases ht : ensureTail tail with
        | error error => simp [ensureIndexable, hc, ht] at h
        | ok ensured =>
            simp [ensureIndexable, hc, ht] at h
            subst output
            exact ⟨rfl, rfl⟩

def entries : List Entry := []

end JuliaLean.MultidimCov.MultidimensionalRepairC2
