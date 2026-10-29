import JuliaLean.MultidimCov.ArrayV2Filter

/-!
Properties of `filter`, `filter!` and `filter(f)` (`ArrayV2Filter.lean`).
-/

namespace JuliaLean.MultidimCov.ArrayV2

/-- The filtering contract (docstrings `base/array.jl:2995` and `3048`): the slots are visited
in order; reading an `#undef` slot is an `UndefRefError`, `f(x)` must return a `Bool`
(`TypeError` otherwise) and its exceptions propagate; the result keeps, in order, exactly
the elements for which `f` is `true`. -/
def keptSpec (f : α → R (Option Bool)) : List (Option α) → R (List α)
  | [] => pure []
  | none :: _ => .error .undefRef
  | some x :: rest => do
    let b ← predBool f x
    let r ← keptSpec f rest
    pure (if b then x :: r else r)

/-- Selecting indices and then reading their values gives the same ordered
selection as applying the predicate to the values directly. -/
theorem keptSpec_map (f : α → R (Option Bool)) (decode : β → α) :
    ∀ xs : List β,
      keptSpec f ((xs.map decode).map some) =
        (keptSpec (fun x => f (decode x)) (xs.map some)).map (List.map decode)
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, keptSpec]
    change (predBool f (decode x) >>= fun b => do
      let r ← keptSpec f ((xs.map decode).map some)
      pure (if b then decode x :: r else r)) =
      ((predBool f (decode x) >>= fun b => do
        let r ← keptSpec (fun y => f (decode y)) (xs.map some)
        pure (if b then x :: r else r)).map (List.map decode))
    rw [keptSpec_map f decode xs]
    cases hp : predBool f (decode x) with
    | error e => simp [hp, bind_error, Except.map]
    | ok b =>
      cases hr : keptSpec (fun y => f (decode y)) (xs.map some) <;>
        cases b <;> simp [hp, hr, bind_ok, bind_error, pure_ok, Except.map]

/-- Select the elements at true positions in a mask, in input order. -/
def selectMask : List α → List Bool → List α
  | x :: xs, b :: bs => if b then x :: selectMask xs bs else selectMask xs bs
  | _, _ => []

theorem mapBoolMaskTarget_spec (f : α → R (Option Bool)) :
    ∀ xs mask, mapBoolMaskTarget f xs = .ok mask →
      mask.length = xs.length ∧ keptSpec f (xs.map some) = .ok (selectMask xs mask)
  | [], mask, h => by
    simp [mapBoolMaskTarget] at h
    subst mask
    simp [keptSpec, selectMask]
  | x :: xs, mask, h => by
    simp only [mapBoolMaskTarget, List.mapM_cons] at h
    cases hp : predBool f x with
    | error e => simp [hp, bind_error] at h
    | ok b =>
      simp only [hp, bind_ok] at h
      cases ht : xs.mapM (predBool f) with
      | error e => simp [ht, bind_error] at h
      | ok bs =>
        simp only [ht, bind_ok, pure_ok] at h
        cases h
        have ih := mapBoolMaskTarget_spec f xs bs ht
        cases b <;> simp [keptSpec, selectMask, hp, ih.1, ih.2, bind_ok, pure_ok]

/-- A mask-building error is the first predicate error in the ordered selection. -/
theorem mapBoolMaskTarget_error (f : α → R (Option Bool)) :
    ∀ xs e, mapBoolMaskTarget f xs = .error e →
      keptSpec f (xs.map some) = .error e
  | [], _, h => by simp [mapBoolMaskTarget] at h
  | x :: xs, e, h => by
    simp only [mapBoolMaskTarget, List.mapM_cons] at h
    cases hp : predBool f x with
    | error err =>
      simp only [hp, bind_error, Except.error.injEq] at h
      subst e
      simp [keptSpec, hp, bind_error]
    | ok b =>
      simp only [hp, bind_ok] at h
      cases hr : xs.mapM (predBool f) with
      | ok mask => simp [hr, bind_ok, pure_ok] at h
      | error err =>
        simp only [hr, bind_error, Except.error.injEq] at h
        subst e
        have ih := mapBoolMaskTarget_error f xs err hr
        simp [keptSpec, hp, ih, bind_ok, bind_error]

/-- The trace records exactly the inputs visited before success or the first failure. -/
theorem mapBoolMaskTrace_spec (f : α → R (Option Bool)) :
    ∀ xs, (mapBoolMaskTrace f xs).2 = mapBoolMaskTarget f xs ∧
      (∃ rest, xs = (mapBoolMaskTrace f xs).1 ++ rest) ∧
      (∀ e, (mapBoolMaskTrace f xs).2 = .error e →
        ∃ pre x rest, xs = pre ++ x :: rest ∧
          (mapBoolMaskTrace f xs).1 = pre ++ [x] ∧ predBool f x = .error e ∧
          ∀ y ∈ pre, ∃ b, predBool f y = .ok b)
  | [] => by simp [mapBoolMaskTrace, mapBoolMaskTarget]
  | x :: xs => by
    have ih := mapBoolMaskTrace_spec f xs
    cases hp : predBool f x with
    | error e =>
      simp only [mapBoolMaskTrace, hp, mapBoolMaskTarget, List.mapM_cons, bind_error]
      refine ⟨trivial, ⟨xs, rfl⟩, ?_⟩
      intro e' h
      cases h
      exact ⟨[], x, xs, rfl, rfl, hp, by simp⟩
    | ok b =>
      cases ht : mapBoolMaskTrace f xs with
      | mk calls result =>
        simp only [ht] at ih
        simp only [mapBoolMaskTrace, hp, ht, mapBoolMaskTarget, List.mapM_cons, bind_ok]
        rcases ih with ⟨heq, ⟨rest, hrest⟩, herr⟩
        refine ⟨?_, ⟨rest, by simp [hrest]⟩, ?_⟩
        · change result.map (b :: ·) = (xs.mapM (predBool f) >>= fun bs => pure (b :: bs))
          change result = xs.mapM (predBool f) at heq
          rw [← heq]
          cases result <;> rfl
        · intro e h
          cases hr : result with
          | ok bs => simp [hr, Except.map] at h
          | error e' =>
            simp only [hr, Except.map] at h
            cases h
            obtain ⟨pre, y, rest, hxs, hcalls, hy, hprefix⟩ := herr _ hr
            refine ⟨x :: pre, y, rest, by simp [hxs], by simp [hcalls], hy, ?_⟩
            intro z hz
            simp only [List.mem_cons] at hz
            rcases hz with rfl | hz
            · exact ⟨b, hp⟩
            · exact hprefix z hz

/-- If allocation succeeds and logical indexing selects the true mask positions,
the Cartesian target returns the independently specified kept elements. -/
theorem filterCartesianTarget_spec (ops : CartesianOps α) (f : α → R (Option Bool))
    (a : AbsArr α) (halloc : ops.allocate a = .ok ())
    (hindex : ∀ mask, mask.length = a.elems.length →
      ops.index a mask = .ok (selectMask a.elems mask))
    (mask : List Bool) (hmask : mapBoolMaskTarget f a.elems = .ok mask) :
    filterCartesianTarget ops f a = keptSpec f (a.elems.map some) := by
  have h := mapBoolMaskTarget_spec f a.elems mask hmask
  simp [filterCartesianTarget, halloc, hmask, hindex mask h.1, h.2, bind_ok, pure_ok]

theorem target_cartesian_empty :
    m3032 (fun _ : Unit => .ok (some true)) false ⟨[], false⟩ = .ok [] := rfl

theorem target_nonBool_stops :
    mapBoolMaskTrace (fun x : Nat => if x = 4 then .ok none else .ok (some true))
      [1, 4, 2, 5] = ([1, 4], .error .typeError) := rfl

/-- When indexed reads and mask writes obey their ordinary interfaces, the
paired `map!` loop computes the same mask as the pure predicate kernel. -/
theorem indexedMaskLoop_kernel (f : α → R (Option Bool)) (a : IndexedAbsArr α)
    (dest : MaskDestination (List Bool)) (decode : List Int → α)
    (hget : ∀ j, a.get j = .ok (decode j))
    (hset : ∀ state i b, dest.set state i b = .ok (state ++ [b])) :
    ∀ js is state, js.length = is.length →
      indexedMaskLoop f a dest is js state =
        (mapBoolMaskTarget (fun j => f (decode j)) js).map (state ++ ·)
  | [], [], state, _ => by simp [indexedMaskLoop, mapBoolMaskTarget, Except.map]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | j :: js, i :: is, state, h => by
    simp only [List.length_cons, Nat.succ.injEq] at h
    simp only [indexedMaskLoop, hget, bind_ok, hset]
    have hpred : predBool (fun j => f (decode j)) j = predBool f (decode j) := rfl
    simp only [mapBoolMaskTarget, List.mapM_cons, hpred]
    cases hp : predBool f (decode j) with
    | error e => simp [hp, bind_error, Except.map]
    | ok b =>
      simp only [hp, bind_ok, hset]
      rw [indexedMaskLoop_kernel f a dest decode hget hset js is (state ++ [b]) h]
      simp only [mapBoolMaskTarget]
      cases js.mapM (predBool (fun j => f (decode j))) <;>
        simp [Except.map, bind_ok, bind_error, pure_ok, List.append_assoc]

/-- The same simulation requires successful reads only at visited indices. -/
theorem indexedMaskLoop_kernel_on_indices (f : α → R (Option Bool))
    (a : IndexedAbsArr α) (dest : MaskDestination (List Bool))
    (decode : List Int → α)
    (hset : ∀ state i b, dest.set state i b = .ok (state ++ [b])) :
    ∀ js is state, js.length = is.length →
      (∀ j ∈ js, a.get j = .ok (decode j)) →
      indexedMaskLoop f a dest is js state =
        (mapBoolMaskTarget (fun j => f (decode j)) js).map (state ++ ·)
  | [], [], state, _, _ => by simp [indexedMaskLoop, mapBoolMaskTarget, Except.map]
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | j :: js, i :: is, state, h, hg => by
    simp only [List.length_cons, Nat.succ.injEq] at h
    have hj := hg j (by simp)
    have hrest : ∀ k ∈ js, a.get k = .ok (decode k) := by
      intro k hk
      exact hg k (by simp [hk])
    simp only [indexedMaskLoop, hj, bind_ok, hset]
    have hpred : predBool (fun k => f (decode k)) j = predBool f (decode j) := rfl
    simp only [mapBoolMaskTarget, List.mapM_cons, hpred]
    cases hp : predBool f (decode j) with
    | error e => simp [hp, bind_error, Except.map]
    | ok b =>
      simp only [hp, bind_ok, hset]
      rw [indexedMaskLoop_kernel_on_indices f a dest decode hset js is
        (state ++ [b]) h hrest]
      simp only [mapBoolMaskTarget]
      cases js.mapM (predBool (fun k => f (decode k))) <;>
        simp [Except.map, bind_ok, bind_error, pure_ok, List.append_assoc]

/-- For a nonmutating source and deterministic predicate, under successful
reads at visited indices, append-only mask writes, and lawful logical
indexing, the Cartesian branch returns the documented ordered selection. -/
theorem indexedFilterCartesian_success (ops : IndexedCartesianOps α (List Bool))
    (f : α → R (Option Bool)) (a : IndexedAbsArr α)
    (dest : MaskDestination (List Bool)) (decode : List Int → α)
    (halloc : ops.similar a = .ok dest)
    (hcount : dest.eachindex.length = a.eachindex.length)
    (hinit : dest.initial = [])
    (hget : ∀ j ∈ a.eachindex, a.get j = .ok (decode j))
    (hset : ∀ state i b, dest.set state i b = .ok (state ++ [b]))
    (hindex : ∀ mask, mask.length = a.eachindex.length →
      ops.logicalIndex a dest mask =
        .ok (selectMask (a.eachindex.map decode) mask))
    (mask : List Bool)
    (hmask : mapBoolMaskTarget (fun j => f (decode j)) a.eachindex = .ok mask) :
    indexedFilterCartesian ops f a = keptSpec f ((a.eachindex.map decode).map some) := by
  have hloop := indexedMaskLoop_kernel_on_indices f a dest decode hset
    a.eachindex dest.eachindex [] hcount.symm hget
  rw [← hinit] at hloop
  have hmap : mapBoolMaskTarget f (a.eachindex.map decode) = .ok mask := by
    unfold mapBoolMaskTarget at *
    rw [List.mapM_map]
    exact hmask
  have hs := mapBoolMaskTarget_spec f (a.eachindex.map decode) mask hmap
  simp only [List.length_map] at hs
  rw [hinit] at hloop
  unfold indexedFilterCartesian
  rw [halloc, bind_ok, hinit, hloop, hmask]
  simpa [Except.map, hindex mask hs.1, bind_ok] using hs.2.symm

/-- With successful reads and writes, a predicate failure stops the Cartesian
branch before logical indexing and propagates the same error. -/
theorem indexedFilterCartesian_predicate_error (ops : IndexedCartesianOps α (List Bool))
    (f : α → R (Option Bool)) (a : IndexedAbsArr α)
    (dest : MaskDestination (List Bool)) (decode : List Int → α)
    (halloc : ops.similar a = .ok dest)
    (hcount : dest.eachindex.length = a.eachindex.length)
    (hget : ∀ j ∈ a.eachindex, a.get j = .ok (decode j))
    (hset : ∀ state i b, dest.set state i b = .ok (state ++ [b]))
    (e) (hmask : mapBoolMaskTarget (fun j => f (decode j)) a.eachindex = .error e) :
    indexedFilterCartesian ops f a = .error e := by
  have hloop := indexedMaskLoop_kernel_on_indices f a dest decode hset
    a.eachindex dest.eachindex dest.initial hcount.symm hget
  simp [indexedFilterCartesian, halloc, hloop, hmask, Except.map, bind_ok, bind_error]

/-- The Cartesian branch meets the ordered filtering contract under its
allocation, mask-write and logical-indexing interfaces. -/
theorem indexedFilterCartesian_spec (ops : IndexedCartesianOps α (List Bool))
    (f : α → R (Option Bool)) (a : IndexedAbsArr α)
    (dest : MaskDestination (List Bool)) (decode : List Int → α)
    (halloc : ops.similar a = .ok dest)
    (hcount : dest.eachindex.length = a.eachindex.length)
    (hinit : dest.initial = [])
    (hget : ∀ j ∈ a.eachindex, a.get j = .ok (decode j))
    (hset : ∀ state i b, dest.set state i b = .ok (state ++ [b]))
    (hindex : ∀ mask, mask.length = a.eachindex.length →
      ops.logicalIndex a dest mask = .ok (selectMask (a.eachindex.map decode) mask)) :
    indexedFilterCartesian ops f a = keptSpec f ((a.eachindex.map decode).map some) := by
  cases hm : mapBoolMaskTarget (fun j => f (decode j)) a.eachindex with
  | ok mask =>
    exact indexedFilterCartesian_success ops f a dest decode halloc hcount hinit hget hset hindex mask hm
  | error e =>
    have he := indexedFilterCartesian_predicate_error ops f a dest decode halloc hcount hget hset e hm
    have hv : mapBoolMaskTarget f (a.eachindex.map decode) = .error e := by
      unfold mapBoolMaskTarget at *
      rw [List.mapM_map]
      exact hm
    rw [he, mapBoolMaskTarget_error f (a.eachindex.map decode) e hv]

/-- Allocation errors occur before any source read or predicate call. -/
theorem indexedFilterCartesian_allocation_error (ops : IndexedCartesianOps α σ)
    (f : α → R (Option Bool)) (a : IndexedAbsArr α) (e)
    (h : ops.similar a = .error e) :
    indexedFilterCartesian ops f a = .error e := by
  simp [indexedFilterCartesian, h, bind_error]


/-- The linear branch reports allocation failure before reading the source. -/
theorem indexedFilterLinear_allocation_error (ops : IndexedLinearOps α σ)
    (f : α → R (Option Bool)) (a : IndexedLinearArr α) (e)
    (h : ops.allocate a.length = .error e) :
    indexedFilterLinear ops f a = .error e := by
  simp [indexedFilterLinear, h, bind_error]

/-- A failed index-vector write stops the linear loop before the source read. -/
theorem indexedLinearLoop_write_error (ops : IndexedLinearOps α σ)
    (f : α → R (Option Bool)) (a : IndexedLinearArr α)
    (idx : Int) (rest : List Int) (state : σ) (j : Int) (e)
    (h : ops.set state j idx = .error e) :
    indexedLinearLoop ops f a (idx :: rest) state j = .error e := by
  simp [indexedLinearLoop, h, bind_error]

/-- A source read failure follows the index-vector write and stops the loop. -/
theorem indexedLinearLoop_read_error (ops : IndexedLinearOps α σ)
    (f : α → R (Option Bool)) (a : IndexedLinearArr α)
    (idx : Int) (rest : List Int) (state state' : σ) (j : Int) (e)
    (hset : ops.set state j idx = .ok state') (hget : a.get idx = .error e) :
    indexedLinearLoop ops f a (idx :: rest) state j = .error e := by
  simp [indexedLinearLoop, hset, hget, bind_ok, bind_error]

/-- A failed predicate assertion stops the loop after the write and read. -/
theorem indexedLinearLoop_predicate_error (ops : IndexedLinearOps α σ)
    (f : α → R (Option Bool)) (a : IndexedLinearArr α)
    (idx : Int) (rest : List Int) (state state' : σ) (j : Int) (x : α) (e)
    (hset : ops.set state j idx = .ok state') (hget : a.get idx = .ok x)
    (hpred : predBool f x = .error e) :
    indexedLinearLoop ops f a (idx :: rest) state j = .error e := by
  simp [indexedLinearLoop, hset, hget, hpred, bind_ok, bind_error]

/-- A prefix relation abstracts the initialized part of the index vector.
Writing the next candidate preserves the old prefix and extends it if kept. -/
theorem indexedLinearLoop_selection (ops : IndexedLinearOps α σ)
    (f : α → R (Option Bool)) (a : IndexedLinearArr α) (decode : Int → α)
    (Inv : σ → Int → List Int → Prop)
    (hset : ∀ state j pre idx, Inv state j pre → pre.length < a.eachindex.length →
      ∃ state', ops.set state j idx = .ok state' ∧
        Inv state' j pre ∧ Inv state' (wrap64 (j + 1)) (pre ++ [idx])) :
    ∀ indices state j pre selected,
      (∀ idx ∈ indices, a.get idx = .ok (decode idx)) →
      pre.length + indices.length ≤ a.eachindex.length →
      Inv state j pre →
      keptSpec (fun idx => f (decode idx)) (indices.map some) = .ok selected →
      ∃ final j', indexedLinearLoop ops f a indices state j = .ok (final, j') ∧
        Inv final j' (pre ++ selected)
  | [], state, j, pre, selected, _, _, hinv, hs => by
      simp [keptSpec] at hs
      subst selected
      exact ⟨state, j, rfl, by simpa using hinv⟩
  | idx :: rest, state, j, pre, selected, hg, hbound, hinv, hs => by
      have hget := hg idx (by simp)
      have hrest : ∀ k ∈ rest, a.get k = .ok (decode k) := by
        intro k hk
        exact hg k (by simp [hk])
      obtain ⟨state', hw, hfalse, htrue⟩ := hset state j pre idx hinv (by simp at hbound; omega)
      simp only [List.map_cons, keptSpec] at hs
      change (predBool f (decode idx) >>= fun b => do
        let r ← keptSpec (fun k => f (decode k)) (rest.map some)
        pure (if b then idx :: r else r)) = .ok selected at hs
      cases hp : predBool f (decode idx) with
      | error e => simp [hp, bind_error] at hs
      | ok b =>
        simp only [hp, bind_ok] at hs
        cases hr : keptSpec (fun k => f (decode k)) (rest.map some) with
        | error e => simp [hr, bind_error] at hs
        | ok kept =>
          simp only [hr, bind_ok, pure_ok] at hs
          cases b
          · simp only [if_false, Except.ok.injEq] at hs
            subst selected
            obtain ⟨final, j', hloop, hfinal⟩ :=
              indexedLinearLoop_selection ops f a decode Inv hset rest state' j pre kept hrest
                (by simp at hbound; omega) hfalse hr
            exact ⟨final, j', by simpa [indexedLinearLoop, hw, hget, hp, bind_ok] using hloop, hfinal⟩
          · simp only [if_true, Except.ok.injEq] at hs
            subst selected
            obtain ⟨final, j', hloop, hfinal⟩ :=
              indexedLinearLoop_selection ops f a decode Inv hset rest state' (wrap64 (j + 1))
                (pre ++ [idx]) kept hrest (by simp at hbound ⊢; omega) htrue hr
            refine ⟨final, j', ?_, ?_⟩
            · simpa [indexedLinearLoop, hw, hget, hp, bind_ok] using hloop
            · simpa [List.append_assoc] using hfinal


/-- With successful reads and writes, the first predicate failure propagates. -/
theorem indexedLinearLoop_selection_error (ops : IndexedLinearOps α σ)
    (f : α → R (Option Bool)) (a : IndexedLinearArr α) (decode : Int → α)
    (Inv : σ → Int → List Int → Prop)
    (hset : ∀ state j pre idx, Inv state j pre → pre.length < a.eachindex.length →
      ∃ state', ops.set state j idx = .ok state' ∧
        Inv state' j pre ∧ Inv state' (wrap64 (j + 1)) (pre ++ [idx])) :
    ∀ indices state j pre e,
      (∀ idx ∈ indices, a.get idx = .ok (decode idx)) →
      pre.length + indices.length ≤ a.eachindex.length →
      Inv state j pre →
      keptSpec (fun idx => f (decode idx)) (indices.map some) = .error e →
      indexedLinearLoop ops f a indices state j = .error e
  | [], _, _, _, _, _, _, _, hs => by simp [keptSpec] at hs
  | idx :: rest, state, j, pre, e, hg, hbound, hinv, hs => by
      have hget := hg idx (by simp)
      have hrest : ∀ k ∈ rest, a.get k = .ok (decode k) := by
        intro k hk
        exact hg k (by simp [hk])
      obtain ⟨state', hw, hfalse, htrue⟩ := hset state j pre idx hinv (by simp at hbound; omega)
      simp only [List.map_cons, keptSpec] at hs
      change (predBool f (decode idx) >>= fun b => do
        let r ← keptSpec (fun k => f (decode k)) (rest.map some)
        pure (if b then idx :: r else r)) = .error e at hs
      cases hp : predBool f (decode idx) with
      | error err =>
        simp only [hp, bind_error, Except.error.injEq] at hs
        subst e
        simp [indexedLinearLoop, hw, hget, hp, bind_ok, bind_error]
      | ok b =>
        simp only [hp, bind_ok] at hs
        cases hr : keptSpec (fun k => f (decode k)) (rest.map some) with
        | ok kept => simp [hr, bind_ok, pure_ok] at hs
        | error err =>
          simp only [hr, bind_error, Except.error.injEq] at hs
          subst e
          cases b
          · have ih := indexedLinearLoop_selection_error ops f a decode Inv hset
              rest state' j pre err hrest (by simp at hbound; omega) hfalse hr
            simpa [indexedLinearLoop, hw, hget, hp, bind_ok] using ih
          · have ih := indexedLinearLoop_selection_error ops f a decode Inv hset
              rest state' (wrap64 (j + 1)) (pre ++ [idx]) err hrest
              (by simp at hbound ⊢; omega) htrue hr
            simpa [indexedLinearLoop, hw, hget, hp, bind_ok] using ih
/-- Under the index-vector and indexing interfaces, the linear branch returns
the values at precisely the selected indices, including offset indices. -/
theorem indexedFilterLinear_success (ops : IndexedLinearOps α σ)
    (f : α → R (Option Bool)) (a : IndexedLinearArr α) (decode : Int → α)
    (Inv : σ → Int → List Int → Prop) (initial : σ)
    (halloc : ops.allocate a.length = .ok initial)
    (hinit : Inv initial 1 [])
    (hget : ∀ idx ∈ a.eachindex, a.get idx = .ok (decode idx))
    (hset : ∀ state j pre idx, Inv state j pre → pre.length < a.eachindex.length →
      ∃ state', ops.set state j idx = .ok state' ∧
        Inv state' j pre ∧ Inv state' (wrap64 (j + 1)) (pre ++ [idx]))
    (hfinish : ∀ state j selected, Inv state j selected →
      ∃ resized emptied,
        ops.resize state (wrap64 (j - 1)) = .ok resized ∧
        ops.index a resized = .ok (selected.map decode) ∧
        ops.empty resized = .ok emptied ∧
        ∃ final, ops.sizehint emptied = .ok final)
    (selected : List Int)
    (hs : keptSpec (fun idx => f (decode idx)) (a.eachindex.map some) = .ok selected) :
    indexedFilterLinear ops f a = .ok (selected.map decode) := by
  obtain ⟨state, j, hloop, hinv⟩ :=
    indexedLinearLoop_selection ops f a decode Inv hset a.eachindex initial 1 [] selected hget
      (by simp) hinit hs
  simp only [List.nil_append] at hinv
  obtain ⟨resized, emptied, hr, hi, he, final, hh⟩ := hfinish state j selected hinv
  simp [indexedFilterLinear, halloc, hloop, hr, hi, he, hh, bind_ok]

/-- The linear branch stops before resizing or indexing on a predicate error. -/
theorem indexedFilterLinear_predicate_error (ops : IndexedLinearOps α σ)
    (f : α → R (Option Bool)) (a : IndexedLinearArr α) (decode : Int → α)
    (Inv : σ → Int → List Int → Prop) (initial : σ)
    (halloc : ops.allocate a.length = .ok initial)
    (hinit : Inv initial 1 [])
    (hget : ∀ idx ∈ a.eachindex, a.get idx = .ok (decode idx))
    (hset : ∀ state j pre idx, Inv state j pre → pre.length < a.eachindex.length →
      ∃ state', ops.set state j idx = .ok state' ∧
        Inv state' j pre ∧ Inv state' (wrap64 (j + 1)) (pre ++ [idx]))
    (e) (hs : keptSpec (fun idx => f (decode idx)) (a.eachindex.map some) = .error e) :
    indexedFilterLinear ops f a = .error e := by
  have hloop := indexedLinearLoop_selection_error ops f a decode Inv hset
    a.eachindex initial 1 [] e hget (by simp) hinit hs
  simp [indexedFilterLinear, halloc, hloop, bind_ok, bind_error]

/-- The linear branch meets the ordered filtering contract when the supplied
index-vector and source indexing operations obey their stated interfaces. -/
theorem indexedFilterLinear_spec (ops : IndexedLinearOps α σ)
    (f : α → R (Option Bool)) (a : IndexedLinearArr α) (decode : Int → α)
    (Inv : σ → Int → List Int → Prop) (initial : σ)
    (halloc : ops.allocate a.length = .ok initial)
    (hinit : Inv initial 1 [])
    (hget : ∀ idx ∈ a.eachindex, a.get idx = .ok (decode idx))
    (hset : ∀ state j pre idx, Inv state j pre → pre.length < a.eachindex.length →
      ∃ state', ops.set state j idx = .ok state' ∧
        Inv state' j pre ∧ Inv state' (wrap64 (j + 1)) (pre ++ [idx]))
    (hfinish : ∀ state j selected, Inv state j selected →
      ∃ resized emptied,
        ops.resize state (wrap64 (j - 1)) = .ok resized ∧
        ops.index a resized = .ok (selected.map decode) ∧
        ops.empty resized = .ok emptied ∧
        ∃ final, ops.sizehint emptied = .ok final) :
    indexedFilterLinear ops f a = keptSpec f ((a.eachindex.map decode).map some) := by
  rw [keptSpec_map]
  cases hs : keptSpec (fun idx => f (decode idx)) (a.eachindex.map some) with
  | error e =>
    simpa [Except.map] using indexedFilterLinear_predicate_error ops f a decode Inv initial
      halloc hinit hget hset e hs
  | ok selected =>
    simpa [Except.map] using indexedFilterLinear_success ops f a decode Inv initial
      halloc hinit hget hset hfinish selected hs

theorem keptSpec_length (f : α → R (Option Bool)) :
    ∀ (xs : List (Option α)) (ys : List α), keptSpec f xs = .ok ys → ys.length ≤ xs.length
  | [], ys, h => by simp [keptSpec] at h; subst h; simp
  | none :: _, _, h => by simp [keptSpec] at h
  | some x :: rest, ys, h => by
    simp only [keptSpec] at h
    cases hp : predBool f x with
    | error e => rw [hp, bind_error] at h; cases h
    | ok b =>
      rw [hp, bind_ok] at h
      cases hr : keptSpec f rest with
      | error e => rw [hr, bind_error] at h; cases h
      | ok r =>
        rw [hr, bind_ok, pure_ok] at h
        cases h
        have := keptSpec_length f rest r hr
        cases b <;> simp <;> omega

theorem newArray_vec1 {n : Int} (h0 : 0 ≤ n) (h1 : n ≤ 1152921504606846976) :
    (newArray [n] : R (Arr α)) = .ok ⟨Mem.undef n, 1, [n]⟩ := by
  unfold newArray typemaxInt
  rw [if_pos (by simp; omega)]
  simp

/-- `resize!(a, nl)` shrinking a valid vector keeps the first `nl` slots and a valid vector. -/
theorem resize_shrink {a : Arr α} {n nl : Int} (ha : VecOK a n) (h0 : 0 ≤ nl) (h1 : nl ≤ n) :
    ∃ a', m1564 a nl false = .ok a' ∧ VecOK a' nl ∧ ∀ k, 1 ≤ k → k ≤ nl → a'.at k = a.at k := by
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  unfold m1564; rw [toInt_ok (by omega) (by omega), bind_ok]; simp only [hn]
  rw [if_neg (by omega)]
  by_cases he : nl = n
  · subst he; rw [if_neg (by simp)]; exact ⟨a, rfl, ha, fun _ _ _ => rfl⟩
  · rw [if_pos he, if_neg (show ¬ nl < 0 by omega)]
    simp only [Bool.false_eq_true, if_false]
    obtain ⟨a', e, hv', hva, hl, hk⟩ := m1296_spec ha (delta := n - nl) (by omega) (by omega)
    refine ⟨a', e, ⟨by rw [show nl = n - (n - nl) by omega]; exact hv', hva, ?_⟩,
      fun k h1 h2 => hk k h1 (by omega)⟩
    unfold Small; rw [hl]; exact ha.2.2

/-- `sizehint!(a, length(a))` (shrinking allowed, `first = false`) keeps every slot. -/
theorem m1617_same {a : Arr α} {n : Int} (ha : VecOK a n) :
    ∃ a', m1617 a n false true = .ok a' ∧ VecOK a' n ∧ ∀ k, 1 ≤ k → k ≤ n → a'.at k = a.at k := by
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  unfold m1617
  simp only [hn]
  rw [toInt_ok (by omega) (by omega), bind_ok]
  simp only [Int.max_self]
  rw [if_pos (by omega)]
  by_cases hc : a.mem.len - n ≤ Int.tdiv a.mem.len 8
  · rw [if_pos (Or.inr hc)]; exact ⟨a, rfl, ha, fun _ _ _ => rfl⟩
  · rw [if_neg (by simp [hc])]
    simp only [Bool.false_eq_true, if_false, bind_ok]
    rw [refCopy_ok hn0 (by right; simp only [m1114, Mem.undef_len]; omega) (by right; omega), bind_ok, pure_ok]
    refine ⟨_, rfl, ⟨hv, ⟨Int.le_refl 1, by simp [length, hv]; omega, by simp [length, hv, m1114]⟩, ?_⟩,
      fun k h1 h2 => ?_⟩
    · unfold Small; simp only [Mem.copy_len, m1114, Mem.undef_len]; exact Int.le_trans (by omega) ha.2.2
    · simp only [Arr.at, Mem.copy_get, m1114, Mem.undef_get]
      rw [if_pos (by omega)]; congr 1; omega

theorem getElem?_acc_lt {acc ys : List α} {t : Int} (h1 : 1 ≤ t) (h : t - 1 < acc.length) :
    (acc ++ ys)[(t - 1).toNat]? = acc[(t - 1).toNat]? :=
  List.getElem?_append_left (by omega)

theorem getElem?_acc_eq {acc : List α} {x : α} {t : Int} (h : t - 1 = acc.length) :
    (acc ++ [x])[(t - 1).toNat]? = some x := by
  rw [List.getElem?_append_right (by omega), show (t - 1).toNat - acc.length = 0 by omega]
  rfl

/-- Initialized prefix of the actual index vector. -/
def linearVectorPrefix (n : Int) (state : Arr Int) (j : Int) (pre : List Int) : Prop :=
  VecOK state n ∧ (pre.length : Int) ≤ n ∧ j = (pre.length : Int) + 1 ∧
  ∀ t, 1 ≤ t → t < j → state.at t = pre[(t - 1).toNat]?

/-- The concrete unchecked write preserves the selected prefix and extends it
when the predicate keeps the candidate. -/
theorem linearVectorPrefix_write (n : Int) (hmax : n < typemaxInt)
    (state : Arr Int) (j : Int) (pre : List Int) (idx : Int)
    (hinv : linearVectorPrefix n state j pre) (hroom : (pre.length : Int) < n) :
    linearVectorPrefix n (setU state j (some idx)) j pre ∧
    linearVectorPrefix n (setU state j (some idx)) (wrap64 (j + 1)) (pre ++ [idx]) := by
  obtain ⟨hvec, hlen, hj, hslots⟩ := hinv
  have hvec' : VecOK (setU state j (some idx)) n := by
    simpa [VecOK, IsVec, Valid, Small] using hvec
  have hw : wrap64 (j + 1) = j + 1 := by
    apply wrap64_id <;> unfold typemaxInt at hmax <;> omega
  constructor
  · refine ⟨hvec', hlen, hj, ?_⟩
    intro t ht1 htj
    rw [setU_at, if_neg (show t ≠ j by omega)]
    exact hslots t ht1 htj
  · refine ⟨hvec', ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton]
      omega
    · simp only [hw, List.length_append, List.length_singleton]
      omega
    · rw [hw]
      intro t ht1 htj
      by_cases ht : t = j
      · subst t
        simp only [setU_at, if_true]
        symm
        exact getElem?_acc_eq (by omega)
      · simp only [setU_at, if_neg ht]
        rw [getElem?_acc_lt ht1 (by omega)]
        exact hslots t ht1 (by omega)

/-- A newly allocated index vector has an empty initialized prefix. -/
theorem linearVectorPrefix_initial (n : Int) (hn : 0 ≤ n) (hsmall : n ≤ 2 ^ 60) :
    linearVectorPrefix n ⟨Mem.undef n, 1, [n]⟩ 1 [] := by
  refine ⟨?_, by simpa using hn, by simp, ?_⟩
  · refine ⟨rfl, ?_, ?_⟩
    · simp [Valid, length, Mem.undef_len, hn]
    · simpa [Small, Mem.undef_len] using hsmall
  · intro t ht1 htj
    omega

/-- The actual vector write implements the prefix interface while there is a
free slot, provided the counter increment remains representable. -/
theorem linearVectorOps_write (index : IndexedLinearArr α → Arr Int → R (List α))
    (a : IndexedLinearArr α) (hcount : a.length = a.eachindex.length)
    (hmax : a.length < typemaxInt) :
    ∀ state j pre idx, linearVectorPrefix a.length state j pre →
      pre.length < a.eachindex.length →
      ∃ state', (linearVectorOps index).set state j idx = .ok state' ∧
        linearVectorPrefix a.length state' j pre ∧
        linearVectorPrefix a.length state' (wrap64 (j + 1)) (pre ++ [idx]) := by
  intro state j pre idx hinv hroom
  refine ⟨setU state j (some idx), rfl, ?_⟩
  apply linearVectorPrefix_write a.length hmax state j pre idx hinv
  rw [hcount]
  exact_mod_cast hroom

/-- The `filter(f, a::Array)` loop writes the kept elements, in order, to slots `j, j+1, …`. -/
theorem filterLoop_spec (f : α → R (Option Bool)) (a : Arr α) :
    ∀ (xs : List (Option α)) (b : Arr α) (i j : Int) (acc : List α),
    (∀ m (h : m < xs.length), a.at (i + m) = xs[m]) →
    (∀ t, 1 ≤ t → t < j → b.at t = acc[(t - 1).toNat]?) → (acc.length : Int) = j - 1 →
    (∀ e, keptSpec f xs = .error e → filterLoop f a b xs.length i j = .error e) ∧
    (∀ ys, keptSpec f xs = .ok ys → ∃ b', filterLoop f a b xs.length i j = .ok (b', j + ys.length) ∧
      b'.mem.len = b.mem.len ∧ b'.off = b.off ∧ b'.dims = b.dims ∧
      ∀ t, 1 ≤ t → t < j + ys.length → b'.at t = (acc ++ ys)[(t - 1).toNat]?)
  | [], b, i, j, acc, _, hb, _ => by
    refine ⟨fun e h => by simp [keptSpec] at h, fun ys h => ?_⟩
    simp [keptSpec] at h; subst h
    refine ⟨b, by simp [filterLoop], rfl, rfl, rfl, fun t h1 h2 => ?_⟩
    simpa using hb t h1 (by simpa using h2)
  | none :: rest, b, i, j, acc, hx, _, _ => by
    have h0 : a.at i = none := by
      have := hx 0 (by simp); rw [show i + ((0 : Nat) : Int) = i by simp] at this; exact this
    have hl : (none :: rest).length = rest.length + 1 := rfl
    rw [hl]
    refine ⟨fun e h => ?_, fun ys h => by simp [keptSpec] at h⟩
    simp [keptSpec] at h; subst h
    simp [filterLoop, getU, h0]
  | some x :: rest, b, i, j, acc, hx, hb, hacc => by
    have h0 : a.at i = some x := by
      have := hx 0 (by simp); rw [show i + ((0 : Nat) : Int) = i by simp] at this; exact this
    have hr : ∀ m (h : m < rest.length), a.at (i + 1 + m) = rest[m] := by
      intro m h
      have := hx (m + 1) (by simp; omega)
      rw [show i + ((m + 1 : Nat) : Int) = i + 1 + m by push_cast; omega] at this
      simpa using this
    have hl : (some x :: rest).length = rest.length + 1 := rfl
    rw [hl]
    simp only [filterLoop, getU, h0, bind_ok, keptSpec]
    cases hp : predBool f x with
    | error e =>
      refine ⟨fun e' h => ?_, fun ys h => by simp at h⟩
      simp at h; subst h; rfl
    | ok keep =>
      simp only [bind_ok]
      cases keep
      · have hb' : ∀ t, 1 ≤ t → t < j → (setU b j (some x)).at t = acc[(t - 1).toNat]? := by
          intro t h1 h2; rw [setU_at, if_neg (by omega)]; exact hb t h1 h2
        obtain ⟨ihe, iho⟩ := filterLoop_spec f a rest (setU b j (some x)) (i + 1) j acc hr hb' hacc
        simp only [Bool.false_eq_true, if_false]
        refine ⟨fun e h => ?_, fun ys h => ?_⟩
        · cases hk : keptSpec f rest with
          | error e' => rw [hk, bind_error] at h; cases h; exact ihe _ hk
          | ok r => rw [hk, bind_ok] at h; cases h
        · cases hk : keptSpec f rest with
          | error e' => rw [hk, bind_error] at h; cases h
          | ok r =>
            rw [hk, bind_ok, pure_ok] at h; cases h
            obtain ⟨b', e, h1, h2, h3, h4⟩ := iho _ hk
            exact ⟨b', e, by simp [h1], by simp [h2], by simp [h3], h4⟩
      · have hb' : ∀ t, 1 ≤ t → t < j + 1 → (setU b j (some x)).at t = (acc ++ [x])[(t - 1).toNat]? := by
          intro t h1 h2
          rw [setU_at]
          by_cases ht : t = j
          · rw [if_pos ht, getElem?_acc_eq (by omega)]
          · rw [if_neg ht, getElem?_acc_lt h1 (by omega)]; exact hb t h1 (by omega)
        obtain ⟨ihe, iho⟩ := filterLoop_spec f a rest (setU b j (some x)) (i + 1) (j + 1) (acc ++ [x]) hr hb'
          (by simp; omega)
        simp only [if_true]
        refine ⟨fun e h => ?_, fun ys h => ?_⟩
        · cases hk : keptSpec f rest with
          | error e' => rw [hk, bind_error] at h; cases h; exact ihe _ hk
          | ok r => rw [hk, bind_ok] at h; cases h
        · cases hk : keptSpec f rest with
          | error e' => rw [hk, bind_error] at h; cases h
          | ok r =>
            rw [hk, bind_ok, pure_ok] at h; cases h
            obtain ⟨b', e, h1, h2, h3, h4⟩ := iho _ hk
            refine ⟨b', by rw [e]; congr 2; simp; omega, by simp [h1], by simp [h2], by simp [h3],
              fun t ht1 ht2 => ?_⟩
            rw [h4 t ht1 (by simp at ht2; omega)]; simp

/-- The `filter!(f, a)` loop: slot `i` is read before any write reaches it, and the kept
elements are written, in order, to slots `j, j+1, …` (`j ≤ i`). -/
theorem filterBangLoop_spec (f : α → R (Option Bool)) :
    ∀ (xs : List (Option α)) (a : Arr α) (i j : Int) (acc : List α),
    (∀ m (h : m < xs.length), a.at (i + m) = xs[m]) → j ≤ i →
    (∀ t, 1 ≤ t → t < j → a.at t = acc[(t - 1).toNat]?) → (acc.length : Int) = j - 1 →
    (∀ e, keptSpec f xs = .error e → filterBangLoop f a xs.length i j = .error e) ∧
    (∀ ys, keptSpec f xs = .ok ys → ∃ a', filterBangLoop f a xs.length i j = .ok (a', j + ys.length) ∧
      a'.mem.len = a.mem.len ∧ a'.off = a.off ∧ a'.dims = a.dims ∧
      ∀ t, 1 ≤ t → t < j + ys.length → a'.at t = (acc ++ ys)[(t - 1).toNat]?)
  | [], a, i, j, acc, _, _, hb, _ => by
    refine ⟨fun e h => by simp [keptSpec] at h, fun ys h => ?_⟩
    simp [keptSpec] at h; subst h
    refine ⟨a, by simp [filterBangLoop], rfl, rfl, rfl, fun t h1 h2 => ?_⟩
    simpa using hb t h1 (by simpa using h2)
  | none :: rest, a, i, j, acc, hx, _, _, _ => by
    have h0 : a.at i = none := by
      have := hx 0 (by simp); rw [show i + ((0 : Nat) : Int) = i by simp] at this; exact this
    have hl : (none :: rest).length = rest.length + 1 := rfl
    rw [hl]
    refine ⟨fun e h => ?_, fun ys h => by simp [keptSpec] at h⟩
    simp [keptSpec] at h; subst h
    simp [filterBangLoop, getU, h0]
  | some x :: rest, a, i, j, acc, hx, hji, hb, hacc => by
    have h0 : a.at i = some x := by
      have := hx 0 (by simp); rw [show i + ((0 : Nat) : Int) = i by simp] at this; exact this
    have hr : ∀ m (h : m < rest.length), (setU a j (some x)).at (i + 1 + m) = rest[m] := by
      intro m h
      have := hx (m + 1) (by simp; omega)
      rw [show i + ((m + 1 : Nat) : Int) = i + 1 + m by push_cast; omega] at this
      rw [setU_at, if_neg (by omega)]
      simpa using this
    have hl : (some x :: rest).length = rest.length + 1 := rfl
    rw [hl]
    simp only [filterBangLoop, getU, h0, bind_ok, keptSpec]
    cases hp : predBool f x with
    | error e =>
      refine ⟨fun e' h => ?_, fun ys h => by simp at h⟩
      simp at h; subst h; rfl
    | ok keep =>
      simp only [bind_ok]
      cases keep
      · have hb' : ∀ t, 1 ≤ t → t < j → (setU a j (some x)).at t = acc[(t - 1).toNat]? := by
          intro t h1 h2; rw [setU_at, if_neg (by omega)]; exact hb t h1 h2
        obtain ⟨ihe, iho⟩ := filterBangLoop_spec f rest (setU a j (some x)) (i + 1) j acc hr (by omega) hb' hacc
        simp only [Bool.false_eq_true, if_false]
        refine ⟨fun e h => ?_, fun ys h => ?_⟩
        · cases hk : keptSpec f rest with
          | error e' => rw [hk, bind_error] at h; cases h; exact ihe _ hk
          | ok r => rw [hk, bind_ok] at h; cases h
        · cases hk : keptSpec f rest with
          | error e' => rw [hk, bind_error] at h; cases h
          | ok r =>
            rw [hk, bind_ok, pure_ok] at h; cases h
            obtain ⟨b', e, h1, h2, h3, h4⟩ := iho _ hk
            exact ⟨b', e, by simp [h1], by simp [h2], by simp [h3], h4⟩
      · have hb' : ∀ t, 1 ≤ t → t < j + 1 → (setU a j (some x)).at t = (acc ++ [x])[(t - 1).toNat]? := by
          intro t h1 h2
          rw [setU_at]
          by_cases ht : t = j
          · rw [if_pos ht, getElem?_acc_eq (by omega)]
          · rw [if_neg ht, getElem?_acc_lt h1 (by omega)]; exact hb t h1 (by omega)
        obtain ⟨ihe, iho⟩ := filterBangLoop_spec f rest (setU a j (some x)) (i + 1) (j + 1) (acc ++ [x]) hr
          (by omega) hb' (by simp; omega)
        simp only [if_true]
        refine ⟨fun e h => ?_, fun ys h => ?_⟩
        · cases hk : keptSpec f rest with
          | error e' => rw [hk, bind_error] at h; cases h; exact ihe _ hk
          | ok r => rw [hk, bind_ok] at h; cases h
        · cases hk : keptSpec f rest with
          | error e' => rw [hk, bind_error] at h; cases h
          | ok r =>
            rw [hk, bind_ok, pure_ok] at h; cases h
            obtain ⟨b', e, h1, h2, h3, h4⟩ := iho _ hk
            refine ⟨b', by rw [e]; congr 2; simp; omega, by simp [h1], by simp [h2], by simp [h3],
              fun t ht1 ht2 => ?_⟩
            rw [h4 t ht1 (by simp at ht2; omega)]; simp

/-- Contents of a vector whose first `ys.length` slots hold `ys`. -/
theorem contents_of_slots {b : Arr α} {ys : List α} (hl : length b = ys.length)
    (hs : ∀ k : Int, 1 ≤ k → k ≤ ys.length → b.at k = ys[(k - 1).toNat]?) : contents b = ys.map some := by
  apply contents_ext (by simp [hl])
  intro k hk
  simp only [List.length_map] at hk
  rw [hs _ (by omega) (by omega)]
  simp [show ((k : Int) + 1 - 1).toNat = k by omega, hk]

/-- Resizing the concrete index vector keeps exactly its initialized prefix. -/
theorem linearVectorPrefix_resize (n : Int) (hmax : n < typemaxInt)
    (state : Arr Int) (j : Int) (pre : List Int)
    (hinv : linearVectorPrefix n state j pre) :
    ∃ resized, m1564 state (wrap64 (j - 1)) false = .ok resized ∧
      VecOK resized pre.length ∧ contents resized = pre.map some := by
  obtain ⟨hvec, hlen, hj, hslots⟩ := hinv
  have hw : wrap64 (j - 1) = (pre.length : Int) := by
    rw [show j - 1 = (pre.length : Int) by omega]
    apply wrap64_id <;> unfold typemaxInt at hmax <;> omega
  obtain ⟨resized, hr, hv, hkeep⟩ := resize_shrink hvec
    (nl := pre.length) (by omega) hlen
  refine ⟨resized, by simpa [hw] using hr, hv, ?_⟩
  apply contents_of_slots (length_vec resized _ hv.1)
  intro k hk1 hk2
  rw [hkeep k hk1 hk2]
  exact hslots k hk1 (by omega)

/-- Emptying and size-hinting the temporary index vector succeed for a
valid vector in the existing allocation model. -/
theorem linearVector_cleanup (state : Arr Int) (n : Int) (hvec : VecOK state n) :
    ∃ emptied final, m2155 state = .ok emptied ∧ m1617 emptied 0 false true = .ok final := by
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack hvec
  obtain ⟨emptied, he, hdims, hvalid, hmem, hslots⟩ :=
    m1296_spec hvec (delta := n) (by omega) (by omega)
  have hzero : VecOK emptied 0 := by
    refine ⟨by simpa using hdims, hvalid, ?_⟩
    unfold Small
    rw [hmem]
    exact hvec.2.2
  obtain ⟨final, hh, _, _⟩ := m1617_same hzero
  refine ⟨emptied, final, ?_, hh⟩
  simpa [m2155, hn] using he

/-- The linear branch with the concrete temporary vector meets the filtering
contract when source reads and vector indexing obey their interfaces. -/
theorem indexedFilterLinear_vector_spec
    (index : IndexedLinearArr α → Arr Int → R (List α))
    (f : α → R (Option Bool)) (a : IndexedLinearArr α) (decode : Int → α)
    (hn : 0 ≤ a.length) (hsmall : a.length ≤ 2 ^ 60)
    (hmax : a.length < typemaxInt)
    (hcount : a.length = a.eachindex.length)
    (hget : ∀ idx ∈ a.eachindex, a.get idx = .ok (decode idx))
    (hindex : ∀ (state : Arr Int) (selected : List Int), contents state = selected.map some →
      index a state = .ok (selected.map decode)) :
    indexedFilterLinear (linearVectorOps index) f a =
      keptSpec f ((a.eachindex.map decode).map some) := by
  let initial : Arr Int := ⟨Mem.undef a.length, 1, [a.length]⟩
  apply indexedFilterLinear_spec (linearVectorOps index) f a decode
    (linearVectorPrefix a.length) initial
  · change newArray [a.length] = .ok initial
    apply newArray_vec1 hn
    simpa using hsmall
  · exact linearVectorPrefix_initial a.length hn hsmall
  · exact hget
  · exact linearVectorOps_write index a hcount hmax
  · intro state j selected hinv
    obtain ⟨resized, hr, hv, hc⟩ := linearVectorPrefix_resize a.length hmax state j selected hinv
    obtain ⟨emptied, final, he, hh⟩ := linearVector_cleanup resized selected.length hv
    exact ⟨resized, emptied, hr, hindex resized selected hc, he, final, hh⟩

/-- `filter(f, a)` (docstring `base/array.jl:2995`) on an `Array` of any shape: a new `Vector`
holding, in order, the elements for which `f` is `true`; reading an `#undef` element, a
non-`Bool` result of `f` and an exception of `f` are errors, met in iteration order. -/
def P3020 : Prop := ∀ {α : Type} (f : α → R (Option Bool)) (a : Arr α), Valid a → length a ≤ 2 ^ 58 →
    (∀ e, keptSpec f (contents a) = .error e → m3020 f a = .error e) ∧
    (∀ ys, keptSpec f (contents a) = .ok ys → ∃ b, m3020 f a = .ok b ∧ VecOK b ys.length ∧ contents b = ys.map some)

theorem p3020 : P3020 := by
  intro α f a hva hl
  have hn0 : 0 ≤ length a := hva.2.1
  have h58 : length a ≤ 288230376151711744 := hl
  have hx : ∀ m (h : m < (contents a).length), a.at (1 + m) = (contents a)[m] := by
    intro m h; rw [getElem_contents, Int.add_comm]
  obtain ⟨ihe, iho⟩ := filterLoop_spec f a (contents a) ⟨Mem.undef (length a), 1, [length a]⟩ 1 1 []
    hx (fun t h1 h2 => by omega) (by simp)
  unfold m3020
  rw [newArray_vec1 hn0 (by omega), bind_ok, ← contents_length]
  refine ⟨fun e h => by rw [ihe e h, bind_error], fun ys h => ?_⟩
  obtain ⟨b', e, h1, h2, h3, h4⟩ := iho ys h
  have hyl := keptSpec_length f _ _ h
  simp only [contents_length] at hyl
  rw [e, bind_ok]; dsimp only
  simp only [Mem.undef_len] at h1 h2
  have h60 : (2 : Int) ^ 60 = 1152921504606846976 := by rfl
  have hb' : VecOK b' (length a) := ⟨h3, ⟨by omega, by rw [length_vec b' _ h3]; omega,
    by rw [length_vec b' _ h3]; omega⟩, by unfold Small; rw [h1, h60]; omega⟩
  obtain ⟨b2, e2, hv2, hk2⟩ := resize_shrink hb' (nl := ys.length) (by omega) (by omega)
  rw [show 1 + (ys.length : Int) - 1 = ys.length by omega, e2, bind_ok, length_vec b2 _ hv2.1]
  obtain ⟨b3, e3, hv3, hk3⟩ := m1617_same hv2
  refine ⟨b3, e3, hv3, contents_of_slots (length_vec b3 _ hv3.1) fun k k1 k2 => ?_⟩
  rw [hk3 k k1 k2, hk2 k k1 k2, h4 k k1 (by omega)]
  simp

/-- The `deleteat!(a, lo:lastindex(a))` contract used by `filter!` on vector types other than
`Vector`: the first `lo - 1` slots stay and the vector is valid. -/
def DelRangeOK (delRange : Arr α → Int → Int → R (Arr α)) : Prop :=
  ∀ b m lo, VecOK b m → 1 ≤ lo → lo ≤ m →
    ∃ b', delRange b lo m = .ok b' ∧ VecOK b' (lo - 1) ∧ ∀ k, 1 ≤ k → k < lo → b'.at k = b.at k

/-- `filter!(f, a)` (docstring `base/array.jl:3048`) on a vector: `a` is updated to hold, in
order, the elements for which `f` is `true`, and returned; errors as for `filter`. -/
def P3066 : Prop := ∀ {α : Type} (f : α → R (Option Bool)) (isVector : Bool)
    (delRange : Arr α → Int → Int → R (Arr α)) (a : Arr α) (n : Int), DelRangeOK delRange →
    VecOK a n →
    (∀ e, keptSpec f (contents a) = .error e → m3066 f isVector delRange a = .error e) ∧
    (∀ ys, keptSpec f (contents a) = .ok ys →
      ∃ a', m3066 f isVector delRange a = .ok a' ∧ VecOK a' ys.length ∧ contents a' = ys.map some)

theorem p3066 : P3066 := by
  intro α f isVector dr a n hdr ha
  obtain ⟨hn, ho, hn0, hw, hs, hv⟩ := vecOK_unpack ha
  have hx : ∀ m (h : m < (contents a).length), a.at (1 + m) = (contents a)[m] := by
    intro m h; rw [getElem_contents, Int.add_comm]
  obtain ⟨ihe, iho⟩ := filterBangLoop_spec f (contents a) a 1 1 [] hx (Int.le_refl 1)
    (fun t h1 h2 => by omega) (by simp)
  unfold m3066
  rw [← contents_length]
  refine ⟨fun e h => by rw [ihe e h, bind_error], fun ys h => ?_⟩
  obtain ⟨a1, e, h1, h2, h3, h4⟩ := iho ys h
  have hyl := keptSpec_length f _ _ h
  simp only [contents_length, hn] at hyl
  rw [e, bind_ok]; dsimp only
  have ha1 : VecOK a1 n := ⟨by unfold IsVec; rw [h3]; exact hv, ⟨by rw [h2]; exact ho, by simp [length, h3, hv]; omega,
    by simp [length, h3, hv, h1, h2]; omega⟩, by unfold Small; rw [h1]; exact ha.2.2⟩
  have hs1 : ∀ k : Int, 1 ≤ k → k ≤ ys.length → a1.at k = ys[(k - 1).toNat]? := by
    intro k k1 k2; rw [h4 k k1 (by omega)]; simp
  rw [length_vec a1 n ha1.1]
  by_cases hall : 1 + (ys.length : Int) > n
  · rw [if_pos hall]
    have : (ys.length : Int) = n := by omega
    exact ⟨a1, rfl, by rw [this]; exact ha1, contents_of_slots (by rw [length_vec a1 n ha1.1]; omega) hs1⟩
  · rw [if_neg hall]
    cases isVector
    · simp only [Bool.false_eq_true, if_false]
      obtain ⟨b, eb, hvb, hkb⟩ := hdr a1 n (1 + ys.length) ha1 (by omega) (by omega)
      rw [show 1 + (ys.length : Int) - 1 = ys.length by omega] at hvb
      refine ⟨b, eb, hvb, contents_of_slots (length_vec b _ hvb.1) fun k k1 k2 => ?_⟩
      rw [hkb k k1 (by omega)]; exact hs1 k k1 k2
    · simp only [if_true]
      obtain ⟨b2, e2, hv2, hk2⟩ := resize_shrink ha1 (nl := ys.length) (by omega) (by omega)
      rw [show 1 + (ys.length : Int) - 1 = ys.length by omega, e2, bind_ok]
      obtain ⟨b3, e3, hv3, hk3⟩ := m1617_same hv2
      refine ⟨b3, e3, hv3, contents_of_slots (length_vec b3 _ hv3.1) fun k k1 k2 => ?_⟩
      rw [hk3 k k1 k2, hk2 k k1 k2]; exact hs1 k k1 k2

/-- `filter(f)` (docstring `base/array.jl:3077`) is a function equivalent to `x -> filter(f, x)`:
called on an `Array` it meets the `filter(f, a)` contract. -/
def P3105 : Prop := ∀ {α : Type} (f : α → R (Option Bool)) (a : Arr α), Valid a → length a ≤ 2 ^ 58 →
    (∀ e, keptSpec f (contents a) = .error e → (m3105 f).call a = .error e) ∧
    (∀ ys, keptSpec f (contents a) = .ok ys →
      ∃ b, (m3105 f).call a = .ok b ∧ VecOK b ys.length ∧ contents b = ys.map some)

theorem p3105 : P3105 := fun f a h1 h2 => p3020 f a h1 h2

/-- `filter(f, a)` on any `AbstractArray` (docstring `base/array.jl:2995`): the elements for which
`f` is `true`, in order; an error when `f` throws or returns a non-`Bool` for some element.
`inferBool` is whether inference finds `f`'s return type to be `Bool`. -/
def P3032 : Prop := ∀ {α : Type} (f : α → R (Option Bool)) (inferBool : Bool) (a : AbsArr α),
    (∀ ys, keptSpec f (a.elems.map some) = .ok ys → m3032 f inferBool a = .ok ys) ∧
    (∀ e, keptSpec f (a.elems.map some) = .error e → ∃ e', m3032 f inferBool a = .error e')

/-- The same contract for the historical implementation. -/
def P3032Historical : Prop := ∀ {α : Type} (f : α → R (Option Bool)) (inferBool : Bool) (a : AbsArr α),
    (∀ ys, keptSpec f (a.elems.map some) = .ok ys → m3032Historical f inferBool a = .ok ys) ∧
    (∀ e, keptSpec f (a.elems.map some) = .error e → ∃ e', m3032Historical f inferBool a = .error e')

/-- The empty `IndexCartesian` array of `repro/multidimcov-filter-cartesian-empty.jl`, filtered
with a predicate whose inferred return type is not `Bool`. -/
theorem filter_cartesian_empty :
    m3032Historical (fun _ : Unit => .ok (some true)) false ⟨[], false⟩ = .error .typeError := rfl

theorem p3032_refuted : ¬ P3032Historical := by
  intro h
  have := (h (fun _ : Unit => .ok (some true)) false ⟨[], false⟩).1 [] rfl
  rw [filter_cartesian_empty] at this
  cases this

end JuliaLean.MultidimCov.ArrayV2
