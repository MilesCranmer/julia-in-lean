import JuliaLean.MultidimCov.ArrayV2Grow

namespace JuliaLean.MemSafety.G1.GrowthBounds

open JuliaLean.MultidimCov.ArrayV2

/-- The no-copy branch of `_growbeg!`. The positive delta comes from its
zero-count return, and the position is relative to the existing reference. -/
theorem growbeg_direct {α : Type} (a : Arr α) (n delta : Int)
    (ha : VecOK a n) (hd : 0 < delta) (hfit : delta ≤ a.off - 1) :
    1 ≤ a.off - delta ∧ a.off - delta ≤ a.mem.len ∧
      a.off - delta - 1 + (n + delta) ≤ a.mem.len := by
  obtain ⟨_, ho, hn, hw, _, _⟩ := vecOK_unpack ha
  omega

/-- The reuse branch of `_growbeg_internal!`: both copy spans, the new
reference, and each iteration of the clearing loop lie in the old memory. -/
theorem growbeg_reuse {α : Type} (a : Arr α) (n delta : Int)
    (ha : VecOK a n) (hd : 0 < delta) (hroom : n + delta < a.mem.len) :
    let off := Int.tdiv (a.mem.len - (n + delta)) 2 + 1
    1 ≤ off ∧ off ≤ a.mem.len ∧
    1 ≤ a.off ∧ a.off - 1 + n ≤ a.mem.len ∧
    1 ≤ off + delta ∧ off + delta - 1 + n ≤ a.mem.len ∧
    ∀ j, a.off ≤ j → j < min (off + delta) (a.off + n) →
      1 ≤ j ∧ j ≤ a.mem.len := by
  obtain ⟨_, ho, hn, hw, _, _⟩ := vecOK_unpack ha
  have hq := Int.tdiv_eq_ediv_of_nonneg (a := a.mem.len - (n + delta)) (b := 2) (by omega)
  dsimp
  rw [hq]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  intro j hj hjend
  simp only [Int.min_def] at hjend
  split at hjend <;> omega
/-- The newly allocated branch of `_growbeg_internal!`. The checked minimum
capacity is computed from the original length and delta, not assumed as a
copy-span bound. -/
theorem growbeg_alloc {α : Type} (a : Arr α) (n delta : Int)
    (ha : VecOK a n) (hd : 0 < delta) :
    let cap := max (m1102 n) (n + 2 * delta + 1)
    let off := Int.tdiv (cap - (n + delta)) 2 + 1
    1 ≤ off ∧ off ≤ cap ∧
    1 ≤ a.off ∧ a.off - 1 + n ≤ a.mem.len ∧
    1 ≤ off + delta ∧ off + delta - 1 + n ≤ cap := by
  obtain ⟨_, ho, hn, hw, _, _⟩ := vecOK_unpack ha
  have hc : n + 2 * delta + 1 ≤ max (m1102 n) (n + 2 * delta + 1) := by
    simp only [Int.max_def]
    split <;> omega
  have hq := Int.tdiv_eq_ediv_of_nonneg
    (a := max (m1102 n) (n + 2 * delta + 1) - (n + delta)) (b := 2) (by omega)
  dsimp
  rw [hq]
  omega

/-- Queue compaction in `_growend_internal!` bounds the new reference,
copy, and every clearing-loop iteration from the input vector invariant. -/
theorem growend_reuse {α : Type} (a : Arr α) (n delta : Int)
    (ha : VecOK a n) (hd : 0 < delta)
    (hqueue : a.off - 1 > n + delta) :
    let off := Int.tdiv (n + delta) 8 + 1
    1 ≤ off ∧ off ≤ a.mem.len ∧
    1 ≤ a.off ∧ a.off - 1 + n ≤ a.mem.len ∧
    off - 1 + n ≤ a.mem.len ∧
    ∀ j, max a.off (off + n) ≤ j → j < a.off + n →
      1 ≤ j ∧ j ≤ a.mem.len := by
  obtain ⟨_, ho, hn, hw, _, _⟩ := vecOK_unpack ha
  have hq := Int.tdiv_eq_ediv_of_nonneg (a := n + delta) (b := 8) (by omega)
  dsimp
  rw [hq]
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
  intro j hj hjend
  simp only [Int.max_def] at hj
  split at hj <;> omega

/-- The allocated `_growend_internal!` branch uses the checked requested
capacity as one argument to `max`. -/
theorem growend_alloc {α : Type} (a : Arr α) (n delta : Int)
    (ha : VecOK a n) (hd : 0 < delta) :
    let cap := max (m1102 a.mem.len) (a.off - 1 + (n + delta))
    1 ≤ a.off ∧ a.off ≤ cap ∧
    a.off - 1 + n ≤ a.mem.len ∧ a.off - 1 + n ≤ cap := by
  obtain ⟨_, ho, hn, hw, _, _⟩ := vecOK_unpack ha
  have hc : a.off - 1 + (n + delta) ≤
      max (m1102 a.mem.len) (a.off - 1 + (n + delta)) := by
    simp only [Int.max_def]
    split <;> omega
  dsimp
  omega

/-- Successful checked arithmetic bounds the capacity calculation and all
un-checked additions in the allocated grow-begin branch. -/
theorem growbeg_alloc_machine_bounds {α : Type} (a : Arr α) (n delta : Int)
    (ha : VecOK a n) (hd : 0 < delta)
    (hchecked : n + 2 * delta + 1 ≤ 9223372036854775807) :
    let cap := max (m1102 n) (n + 2 * delta + 1)
    let off := Int.tdiv (cap - (n + delta)) 2 + 1
    0 ≤ cap ∧ cap ≤ 9223372036854775807 ∧
    0 ≤ cap - (n + delta) ∧ off + delta ≤ 9223372036854775807 ∧
    a.off + n ≤ 9223372036854775807 := by
  obtain ⟨_, ho, hn, hw, hs, _⟩ := vecOK_unpack ha
  have hbase := m1102_bounds (n := n) hn (by omega)
  have hc : n + 2 * delta + 1 ≤ max (m1102 n) (n + 2 * delta + 1) := by
    simp only [Int.max_def]; split <;> omega
  have hcap : max (m1102 n) (n + 2 * delta + 1) ≤ 9223372036854775807 := by
    simp only [Int.max_def]; split <;> omega
  have hq := Int.tdiv_eq_ediv_of_nonneg
    (a := max (m1102 n) (n + 2 * delta + 1) - (n + delta)) (b := 2) (by omega)
  dsimp
  rw [hq]
  omega

/-- The checked grow-end allocation size and `overallocation` both fit
machine `Int`; the old-window end also fits from `VecOK`. -/
theorem growend_alloc_machine_bounds {α : Type} (a : Arr α) (n delta : Int)
    (ha : VecOK a n) (hd : 0 < delta)
    (hchecked : a.off - 1 + (n + delta) ≤ 9223372036854775807) :
    0 ≤ max (m1102 a.mem.len) (a.off - 1 + (n + delta)) ∧
    max (m1102 a.mem.len) (a.off - 1 + (n + delta)) ≤ 9223372036854775807 ∧
    a.off + n ≤ 9223372036854775807 := by
  obtain ⟨_, ho, hn, hw, hs, _⟩ := vecOK_unpack ha
  have hbase := m1102_bounds (n := a.mem.len) (by omega) (by omega)
  simp only [Int.max_def]
  split <;> omega

def GrowbegAccessBounds : Prop :=
  ∀ {α : Type} (a : Arr α) (n delta : Int), VecOK a n → 0 < delta →
    (delta ≤ a.off - 1 →
      1 ≤ a.off - delta ∧ a.off - delta ≤ a.mem.len ∧
      a.off - delta - 1 + (n + delta) ≤ a.mem.len) ∧
    (n + delta < a.mem.len →
      let off := Int.tdiv (a.mem.len - (n + delta)) 2 + 1
      1 ≤ off ∧ off ≤ a.mem.len ∧ 1 ≤ a.off ∧
      a.off - 1 + n ≤ a.mem.len ∧ 1 ≤ off + delta ∧
      off + delta - 1 + n ≤ a.mem.len ∧
      ∀ j, a.off ≤ j → j < min (off + delta) (a.off + n) →
        1 ≤ j ∧ j ≤ a.mem.len) ∧
    (let cap := max (m1102 n) (n + 2 * delta + 1)
     let off := Int.tdiv (cap - (n + delta)) 2 + 1
     1 ≤ off ∧ off ≤ cap ∧ 1 ≤ a.off ∧
     a.off - 1 + n ≤ a.mem.len ∧ 1 ≤ off + delta ∧
     off + delta - 1 + n ≤ cap) ∧
    (n + 2 * delta + 1 ≤ 9223372036854775807 →
      let cap := max (m1102 n) (n + 2 * delta + 1)
      let off := Int.tdiv (cap - (n + delta)) 2 + 1
      0 ≤ cap ∧ cap ≤ 9223372036854775807 ∧
      0 ≤ cap - (n + delta) ∧ off + delta ≤ 9223372036854775807 ∧
      a.off + n ≤ 9223372036854775807)

theorem growbegAccessBounds_proven : GrowbegAccessBounds := by
  intro α a n delta ha hd
  exact ⟨growbeg_direct a n delta ha hd, growbeg_reuse a n delta ha hd,
    growbeg_alloc a n delta ha hd, growbeg_alloc_machine_bounds a n delta ha hd⟩

def GrowendAccessBounds : Prop :=
  ∀ {α : Type} (a : Arr α) (n delta : Int), VecOK a n → 0 < delta →
    (a.off - 1 > n + delta →
      let off := Int.tdiv (n + delta) 8 + 1
      1 ≤ off ∧ off ≤ a.mem.len ∧ 1 ≤ a.off ∧
      a.off - 1 + n ≤ a.mem.len ∧ off - 1 + n ≤ a.mem.len ∧
      ∀ j, max a.off (off + n) ≤ j → j < a.off + n →
        1 ≤ j ∧ j ≤ a.mem.len) ∧
    (let cap := max (m1102 a.mem.len) (a.off - 1 + (n + delta))
     1 ≤ a.off ∧ a.off ≤ cap ∧ a.off - 1 + n ≤ a.mem.len ∧
     a.off - 1 + n ≤ cap) ∧
    (a.off - 1 + (n + delta) ≤ 9223372036854775807 →
      0 ≤ max (m1102 a.mem.len) (a.off - 1 + (n + delta)) ∧
      max (m1102 a.mem.len) (a.off - 1 + (n + delta)) ≤ 9223372036854775807 ∧
      a.off + n ≤ 9223372036854775807)

theorem growendAccessBounds_proven : GrowendAccessBounds := by
  intro α a n delta ha hd
  exact ⟨growend_reuse a n delta ha hd, growend_alloc a n delta ha hd,
    growend_alloc_machine_bounds a n delta ha hd⟩

/-- A vector's window and the fixed-width memory length bound. The runtime
allocator checks this length against `MAXINTVAL` in `src/genericmemory.c`;
the window relation also permits an empty vector at the end of memory. -/
def MachineVector (a : Arr α) (n : Int) : Prop :=
  a.dims = [n] ∧ 0 ≤ n ∧ 1 ≤ a.off ∧
    a.off - 1 + n ≤ a.mem.len ∧ a.mem.len < typemaxInt

/-- `_growbeg!` returns for zero and rejects negative deltas before it can
call `_growbeg_internal!` (base/array.jl:1151-1166). -/
theorem growbeg_internal_delta_positive {delta : Int}
    (hnonnegative : 0 ≤ delta) (hnonzero : delta ≠ 0) : 0 < delta := by
  omega

/-- `_growend!` calls the internal helper only when the existing tail
capacity is smaller than delta (base/array.jl:1212-1221). -/
theorem growend_internal_delta_positive {α : Type} {a : Arr α} {n delta : Int}
    (ha : MachineVector a n) (hdelta : 0 ≤ delta)
    (hcall : a.mem.len - (a.off - 1) - n < delta) : 0 < delta := by
  obtain ⟨_, hn, ho, hw, hm⟩ := ha
  omega

/-- The grow-begin direct branch moves the reference within the existing
window without requiring any bound smaller than the machine limit. -/
theorem growbeg_direct_machine {α : Type} (a : Arr α) (n delta : Int)
    (ha : MachineVector a n) (hd : 0 < delta) (hfit : delta ≤ a.off - 1) :
    1 ≤ a.off - delta ∧ a.off - delta ≤ a.mem.len ∧
      a.off - delta - 1 + (n + delta) ≤ a.mem.len := by
  obtain ⟨_, hn, ho, hw, hm⟩ := ha
  omega

/-- In the grow-begin reuse branch the recentered copy and clearing range
fit in the original memory. -/
theorem growbeg_reuse_machine {α : Type} (a : Arr α) (n delta : Int)
    (ha : MachineVector a n) (hd : 0 < delta) (hroom : n + delta < a.mem.len) :
    let off := Int.tdiv (a.mem.len - (n + delta)) 2 + 1
    1 ≤ off ∧ off ≤ a.mem.len ∧
    1 ≤ off + delta ∧ off + delta - 1 + n ≤ a.mem.len ∧
    ∀ j, a.off ≤ j → j < min (off + delta) (a.off + n) →
      1 ≤ j ∧ j ≤ a.mem.len := by
  obtain ⟨_, hn, ho, hw, hm⟩ := ha
  have hq := Int.tdiv_eq_ediv_of_nonneg (a := a.mem.len - (n + delta)) (b := 2) (by omega)
  dsimp
  rw [hq]
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  intro j hj hjend
  simp only [Int.min_def] at hjend
  split at hjend <;> omega

/-- In the grow-end queue branch the copy and clearing range fit in the
original memory. -/
theorem growend_reuse_machine {α : Type} (a : Arr α) (n delta : Int)
    (ha : MachineVector a n) (hd : 0 < delta)
    (hqueue : a.off - 1 > n + delta) :
    let off := Int.tdiv (n + delta) 8 + 1
    1 ≤ off ∧ off ≤ a.mem.len ∧ off - 1 + n ≤ a.mem.len ∧
    ∀ j, max a.off (off + n) ≤ j → j < a.off + n →
      1 ≤ j ∧ j ≤ a.mem.len := by
  obtain ⟨_, hn, ho, hw, hm⟩ := ha
  have hq := Int.tdiv_eq_ediv_of_nonneg (a := n + delta) (b := 8) (by omega)
  dsimp
  rw [hq]
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro j hj hjend
  simp only [Int.max_def] at hj
  split at hj <;> omega

/-- Successful checked capacity arithmetic is sufficient to bound the
grow-begin allocation and copy without a small-allocation hypothesis. -/
theorem growbeg_alloc_machine {α : Type} (a : Arr α) (n delta : Int)
    (ha : MachineVector a n) (hd : 0 < delta)
    (hchecked : n + 2 * delta + 1 ≤ typemaxInt) :
    let cap := max (m1102 n) (n + 2 * delta + 1)
    let off := Int.tdiv (cap - (n + delta)) 2 + 1
    0 ≤ cap ∧ cap ≤ typemaxInt ∧ 1 ≤ off ∧ off ≤ cap ∧
    1 ≤ off + delta ∧ off + delta - 1 + n ≤ cap := by
  obtain ⟨_, hn, ho, hw, hm⟩ := ha
  have hbase := m1102_bounds (n := n) hn (by unfold typemaxInt at *; omega)
  have hc : n + 2 * delta + 1 ≤ max (m1102 n) (n + 2 * delta + 1) := by
    simp only [Int.max_def]; split <;> omega
  have hcap : max (m1102 n) (n + 2 * delta + 1) ≤ typemaxInt := by
    simp only [Int.max_def]; split <;> unfold typemaxInt at * <;> omega
  have hq := Int.tdiv_eq_ediv_of_nonneg
    (a := max (m1102 n) (n + 2 * delta + 1) - (n + delta)) (b := 2) (by omega)
  dsimp
  rw [hq]
  omega

/-- Successful checked capacity arithmetic is sufficient to bound the
grow-end allocation and copy. -/
theorem growend_alloc_machine {α : Type} (a : Arr α) (n delta : Int)
    (ha : MachineVector a n) (hd : 0 < delta)
    (hchecked : a.off - 1 + (n + delta) ≤ typemaxInt) :
    let cap := max (m1102 a.mem.len) (a.off - 1 + (n + delta))
    0 ≤ cap ∧ cap ≤ typemaxInt ∧ 1 ≤ a.off ∧ a.off ≤ cap ∧
      a.off - 1 + n ≤ cap := by
  obtain ⟨_, hn, ho, hw, hm⟩ := ha
  have hbase := m1102_bounds (n := a.mem.len) (by omega) (by unfold typemaxInt at *; omega)
  dsimp
  simp only [Int.max_def]
  split <;> unfold typemaxInt at * <;> omega

/-- Unchecked operations observed during vector growth. A zero-count copy
does not dereference either endpoint; reference construction is separate. -/
inductive GrowthAccess where
  | reference (capacity offset : Int)
  | copy (destCapacity destOffset sourceCapacity sourceOffset count : Int)
  | clear (capacity first last : Int)

/-- The unchecked operations reached by `_growbeg_internal!`
(`base/array.jl:1116-1148`), in execution order. -/
def growbegInternalAccesses (capacity offset delta len : Int) : R (List GrowthAccess) := do
  let newlen ← checkedAdd len delta
  if offset < 1 ∨ wrap64 (offset - 1) > capacity ∨ len > wrap64 (capacity - wrap64 (offset - 1)) then
    .error .concurrency
  else do
    let twice ← checkedMul 2 delta
    let required ← checkedAdd len twice
    let required ← checkedAdd required 1
    let newcapacity := max (m1102 len) required
    let proposed := wrap64 (Int.tdiv (wrap64 (newcapacity - newlen)) 2 + 1)
    if newlen < capacity ∧ proposed < wrap64 (capacity - newlen) then
      let off := wrap64 (Int.tdiv (wrap64 (capacity - newlen)) 2 + 1)
      let dest := wrap64 (off + delta)
      pure [.copy capacity dest capacity offset len,
        .clear capacity offset (wrap64 (min dest (wrap64 (offset + len)) - 1)),
        .reference capacity off]
    else if newcapacity < 0 ∨ typemaxInt - 1 ≤ newcapacity then
      .error .argument
    else
      pure [.copy newcapacity (wrap64 (proposed + delta)) capacity offset len,
        .reference newcapacity proposed]

/-- The unchecked operations reached by `_growend_internal!`
(`base/array.jl:1171-1208`), in execution order. -/
def growendInternalAccesses (capacity offset delta len : Int) : R (List GrowthAccess) := do
  let newlen ← checkedAdd len delta
  if offset < 1 ∨ wrap64 (offset - 1) > capacity ∨ len > wrap64 (capacity - wrap64 (offset - 1)) then
    .error .concurrency
  else do
    let requested ← checkedAdd (wrap64 (offset - 1)) newlen
    if wrap64 (offset - 1) > newlen ∧ wrap64 (wrap64 (offset - 1) - newlen) > Int.tdiv newlen 4 then
      let off := wrap64 (Int.tdiv newlen 8 + 1)
      pure [.reference capacity off, .copy capacity off capacity offset len,
        .clear capacity (max offset (wrap64 (off + len))) (wrap64 (offset + len - 1))]
    else
      let newcapacity := max (m1102 capacity) requested
      if newcapacity < 0 ∨ typemaxInt - 1 ≤ newcapacity then
        .error .argument
      else
        pure [.reference newcapacity offset, .copy newcapacity offset capacity offset len]

/-- Public `_growbeg!` converts the delta, rejects negative values, and
handles zero before computing a checked new length. -/
def growbegAccesses (capacity offset len delta0 : Int) : R (List GrowthAccess) := do
  let delta ← toInt delta0
  if delta = 0 then pure [] else
  if delta < 0 then .error .argument else do
    let _ ← checkedAdd len delta
    if delta ≤ wrap64 (offset - 1) then
      pure [.reference capacity (wrap64 (offset - delta))]
    else
      growbegInternalAccesses capacity offset delta len

/-- Public `_growend!` tests tail capacity before entering its helper. -/
def growendAccesses (capacity offset len delta0 : Int) : R (List GrowthAccess) := do
  let delta ← toInt delta0
  if delta < 0 then .error .argument else
  if wrap64 (wrap64 (capacity - wrap64 (offset - 1)) - len) < delta then
    growendInternalAccesses capacity offset delta len
  else
    pure []

theorem growbeg_zero_accesses (capacity offset len : Int) :
    growbegAccesses capacity offset len 0 = .ok [] := by
  rfl

theorem growend_zero_accesses {α : Type} (a : Arr α) (n : Int)
    (ha : MachineVector a n) :
    growendAccesses a.mem.len a.off n 0 = .ok [] := by
  obtain ⟨_, hn, ho, hw, hm⟩ := ha
  have hoff : wrap64 (a.off - 1) = a.off - 1 := by
    apply wrap64_id <;> unfold typemaxInt at * <;> omega
  have hcapacity : wrap64 (a.mem.len - (a.off - 1)) = a.mem.len - (a.off - 1) := by
    apply wrap64_id <;> unfold typemaxInt at * <;> omega
  have havailable : wrap64 (a.mem.len - (a.off - 1) - n) = a.mem.len - (a.off - 1) - n := by
    apply wrap64_id <;> unfold typemaxInt at * <;> omega
  simp [growendAccesses, toInt, typeminInt, typemaxInt, hoff, hcapacity, havailable]
  omega

/-- Bounds obligations for the operations recorded in a growth trace. -/
def GrowthAccess.safe : GrowthAccess → Prop
  | .reference cap off => 1 ≤ off ∧ off ≤ cap
  | .copy dc d sc s n =>
      0 ≤ n ∧ (n = 0 ∨ (1 ≤ d ∧ d + n - 1 ≤ dc ∧ 1 ≤ s ∧ s + n - 1 ≤ sc))
  | .clear cap first last => ∀ j, first ≤ j → j ≤ last → 1 ≤ j ∧ j ≤ cap

def GrowbegPublicSafety : Prop :=
  ∀ {α : Type} (a : Arr α) (n delta : Int), MachineVector a n →
    ∀ accesses, growbegAccesses a.mem.len a.off n delta = .ok accesses →
      ∀ access, access ∈ accesses → access.safe

def GrowendPublicSafety : Prop :=
  ∀ {α : Type} (a : Arr α) (n delta : Int), MachineVector a n →
    ∀ accesses, growendAccesses a.mem.len a.off n delta = .ok accesses →
      ∀ access, access ∈ accesses → access.safe

end JuliaLean.MemSafety.G1.GrowthBounds
