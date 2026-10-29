import JuliaLean.MultidimCov.SubarrayV2Props

/-!
Views of views: `unsafe_view(V::SubArray, I...)` and `_maybe_reindex`
(`base/subarray.jl:267-280`), with `reindex` over index objects (lines
292-312) and the `getindex` methods of index objects that it calls
(`base/indices.jl:350-428`, `base/range.jl:1000-1063`, and the generic
`getindex(::AbstractArray, I...)` of `base/abstractarray.jl`).
-/

namespace JuliaLean.MultidimCov.SubarrayV2

open JuliaLean.MultidimCov.ArrayV2 (wrap64)

/-- Positions `0 ≤ r` decomposed column-major over axes. -/
def subOfOff : List Ax → Int → List Int
  | [], _ => []
  | a :: as, r => (a.lo + r % a.len) :: subOfOff as (r / a.len)

/-- `CartesianIndices(axes)[k]` for a linear index `k`. -/
def ind2sub (axs : List Ax) (k : Int) : List Int :=
  match axs with
  | [_] => [k]
  | _ => subOfOff axs (k - 1)

/-- `getindex(V, I::Int...)` on a `SubArray`: one index on a fast view (lines
330-344), `N` indices (lines 316-321), or one index on a slow view of rank
`N ≠ 1` (the `IndexCartesian` fallback, which converts with `CartesianIndices`). -/
def getCart (V : Sub α) (J : List Int) : SR α :=
  match J with
  | [i] =>
      if V.L then getindexFastDispatch V i
      else if V.N = 1 then getindexSlow V [i]
      else do
        checkboundsLin V i
        getindexSlow V (ind2sub (subAxes V) i)
  | _ => getindexSlow V J

/-- An `SR` read as stored element (`#undef` for a failed read). -/
def SR.toElt (x : SR α) : Option α :=
  match x with
  | .ok v => some v
  | .error _ => none

/-- A `SubArray` used as the parent of another `SubArray`
(`IndexStyle(::Type{<:FastSubArray}) = IndexLinear()`, line 433). -/
def parOfSub (V : Sub α) : Par α where
  ty := ⟨"SubArray", V.T⟩
  axes := subAxes V
  linear := V.L
  lin := fun k => (getCart V [k]).toElt
  cart := fun pos => (getCart V pos).toElt

/-- All subscripts of the axes, column-major. -/
def allIdx : List Ax → List (List Int)
  | [] => [[]]
  | a :: as =>
      (allIdx as).flatMap (fun rest =>
        ((List.range a.len.toNat).map (fun (k : Nat) => (a.lo + (k : Int)) :: rest)))

/-- Generic `getindex(p::AbstractArray, subs...)` of an `Int`- or
`CartesianIndex`-valued array index object with non-scalar subindices: an
`Array` over the axes of the subindices (a `MethodError` from `similar` when an
axis does not start at 1), holding `p` at the manual's positions. -/
def gather (p : Idx) (subs : List Idx) : SR Idx :=
  let axs := viewAxes subs
  if axs.all (fun a => a.lo = 1) then
    let vals := (allIdx axs).map (fun K => (specPos subs K).bind (fun q => idxAt p q))
    match p with
    | .carr k _ _ =>
        if vals.all Option.isSome then .ok (.carr k (axs.map (fun a => a.len.toNat)) (vals.filterMap id))
        else .error .bounds
    | _ =>
        if vals.all Option.isSome then
          .ok (.arr (axs.map (fun a => a.len.toNat)) ((vals.filterMap id).filterMap List.head?))
        else .error .bounds
  else .error .method

/-- `first(s)` and `length(s)` of a range index (`Int`). -/
def rFirst (s : Idx) : Int := fv s
def rLen (s : Idx) : Int := (axes1Idx s).len

/-- `p[s]` for a one-dimensional index object `p` and one subindex `s` under
`@inbounds`, as the index objects `to_indices` hands to the parent. -/
def idxGetIdx (p s : Idx) : SR (List Idx) :=
  match s with
  | .int j => (idxGetInt p [j]).map (fun v => v.map .int)
  | _ =>
    match p with
    -- `getindex(::Slice, ::AbstractUnitRange/StepRange/IdentityUnitRange)` returns the subindex
    -- (base/indices.jl:351,352,410); same for `IdentityUnitRange` (380, 390, 404).
    | .slice _ | .ident _ => if s.isRange then .ok [s] else (gather p [s]).map (fun x => [x])
    | .oneto _ =>
        match s with
        | .oneto m => .ok [.oneto m]                                         -- range.jl:1017
        | .ident _ => .ok [s]                                                -- indices.jl:423
        | .slice _ | .unit _ =>                                              -- range.jl:1002
            let start := iadd 1 (isub (rFirst s) 1)
            .ok [.unit ⟨start, iadd start (isub (rLen s) 1)⟩]
        | .step a st n => .ok [.step (iadd 1 (isub a 1)) st n]              -- range.jl:1023
        | _ => (gather p [s]).map (fun x => [x])
    | .unit r =>
        match s with
        | .oneto _ | .ident _ | .slice _ | .unit _ =>                        -- range.jl:1002
            let start := iadd r.lo (isub (rFirst s) 1)
            .ok [.unit ⟨start, iadd start (isub (rLen s) 1)⟩]
        | .step a st n => .ok [.step (iadd r.lo (isub a 1)) st n]           -- range.jl:1023
        | _ => (gather p [s]).map (fun x => [x])
    | .step a st _ =>
        if s.isRange then                                                    -- range.jl:1040
          .ok [.step (iadd a (imul (isub (rFirst s) 1) st)) (imul st (idxStep s)) (rLen s)]
        else (gather p [s]).map (fun x => [x])
    | _ => (gather p [s]).map (fun x => [x])

/-- `reindex(idxs, subidxs)` with index-object subindices, lines 292-312. -/
def reindexV : List Idx → List Idx → SR (List Idx)
  | [], [] => .ok []                                                  -- 292
  | [], _ :: _ => .error .method
  | .int n :: ps, ss => do                                            -- 295-296
      let r ← reindexV ps ss
      pure (.int n :: r)
  | .slice _ :: ps, s :: ss => do                                     -- 299-300
      let r ← reindexV ps ss
      pure (s :: r)
  | p :: ps, ss =>
      let d := idxRank p
      if d = 1 then
        match ss with
        | s :: ss' => do                                              -- 303-304
            let v ← idxGetIdx p s
            let r ← reindexV ps ss'
            pure (v ++ r)
        | [] => .error .bounds
      else if ss.length < d then .error .bounds                       -- 307, 311
      else do                                                         -- 307-308, 311-312
        let sub := ss.take d
        let v ← if allScalar sub then
            (idxGetInt p (sub.map fv)).map (fun c => c.map .int)
          else (gather p sub).map (fun x => [x])
        let r ← reindexV ps (ss.drop d)
        pure (v ++ r)

/-- `_maybe_reindex(V, I, A)`, lines 270-280. -/
def maybeReindex3 (V : Sub α) (I : List Idx) : List Idx → SR (Sub α)
  | [] => do                                                          -- 276-280
      let idxs ← reindexV V.indices I
      subArray V.parent idxs
  | .carr k dims xs :: rest =>
      if k = 1 then maybeReindex3 V I rest                            -- 273-274
      else subArray (parOfSub V) I                                    -- 270-271
  | _ :: rest => maybeReindex3 V I rest                               -- 275

/-- `_maybe_reindex(V, I) = _maybe_reindex(V, I, I)`, line 269. -/
def maybeReindex2 (V : Sub α) (I : List Idx) : SR (Sub α) := maybeReindex3 V I I

/-- `unsafe_view(V::SubArray, I::Vararg{ViewIndex,N})`, lines 267-268. -/
def unsafeViewSub (V : Sub α) (I : List Idx) : SR (Sub α) := maybeReindex2 V I

/-! ## The view-of-view contract -/

/-- `view` semantics for a view of a view, for a given implementation `vv` of
`unsafe_view(V, J...)`: for a valid fast or slow view `V = SubArray(A, I)` and
in-bounds indices `J` of `V`, the result has the axes of `J` and its element at
`K` is `V[J...][K...]` as the manual defines it (the `view` docstring,
`base/subarray.jl:175-183`). -/
def ViewOfViewOK (vv : Sub Int → List Idx → SR (Sub Int)) : Prop :=
  ∀ (p : Par Int) (I J : List Idx) (V : Sub Int), PValid p → IdxsOK p.axes I →
    subArray p I = .ok V → IdxsOK (subAxes V) J →
    ∃ W, vv V J = .ok W ∧ subAxes W = viewAxes J ∧
      ∀ K, inAxes (viewAxes J) K → ∃ q, specPos J K = some q ∧ getCart W K = getCart V q

/-- Row 267: `unsafe_view(V::SubArray, I...)` meets the view contract. -/
def P267 : Prop := ViewOfViewOK unsafeViewSub

/-- Row 269: `_maybe_reindex(V, I)` meets the view contract. -/
def P269 : Prop := ViewOfViewOK maybeReindex2

/-- A 3×4 `Matrix{Int}` holding its own linear indices. -/
def mat34 : Par Int where
  ty := ⟨"Matrix{Int64}", "Int64"⟩
  axes := [⟨1, 3⟩, ⟨1, 4⟩]
  linear := true
  lin := fun k => some k
  cart := fun pos => some (linearIndex [⟨1, 3⟩, ⟨1, 4⟩] pos)

theorem mat34_valid : PValid mat34 := by
  refine ⟨rfl, ?_, by decide, fun _ _ => rfl⟩
  intro a ha
  simp [mat34] at ha
  rcases ha with rfl | rfl <;> simp [AxOK]

/-- `V = view(M, IdentityUnitRange(2:3), 1)`. -/
def vIdent : List Idx := [.ident ⟨2, 3⟩, .int 1]

theorem vIdent_view : ∃ V, subArray mat34 vIdent = .ok V ∧ subAxes V = [⟨2, 3⟩] ∧
    getCart V [2] = .ok 2 := by
  refine ⟨_, rfl, ?_, ?_⟩
  · rfl
  · decide

/-- The counterexample of #62906: `view(V, :)` is `SubArray(M, (Slice(IUR(2:3)), 1))`,
whose element 2 is `M[3]` instead of `V[2] == M[2]`. -/
theorem viewOfView_counterexample (vv : Sub Int → List Idx → SR (Sub Int))
    (hvv : (subArray mat34 vIdent).bind (fun V =>
      (vv V [.slice ⟨2, 3⟩]).map (fun W => (subAxes W, getCart W [2]))) = .ok ([⟨2, 3⟩], .ok 3)) :
    ¬ ViewOfViewOK vv := by
  intro h
  obtain ⟨V, hV, hax, hget⟩ := vIdent_view
  have hJ : IdxsOK (subAxes V) [.slice ⟨2, 3⟩] := by rw [hax]; exact ⟨rfl, trivial⟩
  obtain ⟨W, hW, _, hK⟩ := h mat34 vIdent [.slice ⟨2, 3⟩] V mat34_valid
    ⟨⟨by decide, fun _ => ⟨by decide, by decide⟩⟩, ⟨by decide, by decide⟩, trivial⟩ hV hJ
  obtain ⟨q, hq, hval⟩ := hK [2] ⟨by decide, by decide, trivial⟩
  have hq' : q = [2] := by simp [specPos, idxRank, idxAxes, idxAt, Ax.mem] at hq; exact hq.symm
  subst hq'
  rw [hV] at hvv
  simp only [Except.bind, hW, Except.map, Except.ok.injEq, Prod.mk.injEq] at hvv
  rw [hvv.2, hget] at hval
  cases hval

theorem p267_refuted : ¬ P267 := viewOfView_counterexample _ (by decide)

theorem p269_refuted : ¬ P269 := viewOfView_counterexample _ (by decide)

/-- The linear-layout promise for all bounds-valid stored indices. -/
def P478General : Prop := ∀ {α : Type} (p : Par α) (I : List Idx), PValid p →
    IdxsOKGeneral p.axes I → viewindexing I = .linear →
    ∃ s o, computeStride1 p I = .ok s ∧ computeOffset1 p s I = .ok o ∧
      ∀ J, inAxes (viewAxes I) J → ∃ pos, specPos I J = some pos ∧ inAxes p.axes pos ∧
        reindexLinearRaw I o s (linearIndex (viewAxes I) J) = linearIndex p.axes pos

def partialSlice : List Idx := [.slice ⟨2, 3⟩, .int 1]

theorem p478General_refuted : ¬ P478General := by
  intro h
  have hidx : IdxsOKGeneral mat34.axes partialSlice := by
    simp [IdxsOKGeneral, IdxOKGeneral, IdxOK, mat34, partialSlice]
  have hstyle : viewindexing partialSlice = .linear := by decide
  obtain ⟨s, o, hs, ho, hpos⟩ := h mat34 partialSlice mat34_valid hidx hstyle
  have hs0 : computeStride1 mat34 partialSlice = .ok 1 := by decide
  rw [hs0] at hs
  cases hs
  have ho0 : computeOffset1 mat34 1 partialSlice = .ok 1 := by decide
  rw [ho0] at ho
  cases ho
  obtain ⟨pos, hp, _, he⟩ := hpos [2] (by decide)
  have hp0 : specPos partialSlice [2] = some [2, 1] := by decide
  rw [hp0] at hp
  cases hp
  revert he
  decide

def P34General : Prop := ∀ {α : Type} (p : Par α) (I : List Idx), PValid p →
    IdxsOKGeneral p.axes I → viewindexing I = .linear →
    ∃ V, subLinear p I (indexDimsum I) = .ok V ∧ V.T = eltypeOf p.ty ∧ V.P = p.ty ∧
      V.N = (viewAxes I).length ∧ V.L = true ∧ V.parent = p ∧ V.indices = I ∧
      ∀ J, inAxes (viewAxes I) J → ∃ pos, specPos I J = some pos ∧ inAxes p.axes pos ∧
        reindexLinear V (linearIndex (viewAxes I) J) = linearIndex p.axes pos

def partialView : Sub Int :=
  ⟨eltypeOf mat34.ty, 1, mat34.ty, true, mat34, partialSlice, 1, 1⟩

theorem p34General_refuted : ¬ P34General := by
  intro h
  have hidx : IdxsOKGeneral mat34.axes partialSlice := by
    simp [IdxsOKGeneral, IdxOKGeneral, IdxOK, mat34, partialSlice]
  have hstyle : viewindexing partialSlice = .linear := by decide
  obtain ⟨V, hV, _, _, _, _, _, _, hpos⟩ := h mat34 partialSlice mat34_valid hidx hstyle
  have hV0 : subLinear mat34 partialSlice (indexDimsum partialSlice) = .ok partialView := by rfl
  rw [hV0] at hV
  cases hV
  obtain ⟨pos, hp, _, he⟩ := hpos [2] (by decide)
  have hp0 : specPos partialSlice [2] = some [2, 1] := by decide
  rw [hp0] at hp
  cases hp
  revert he
  decide

def FastCaseGeneral (p : Par α) (I : List Idx) : Prop :=
  PValid p ∧ IdxsOKGeneral p.axes I ∧ viewindexing I = .linear

def P330General : Prop := ∀ {α : Type} (p : Par α) (I : List Idx), FastCaseGeneral p I →
    ∃ V, subArray p I = .ok V ∧ V.L = true ∧
      (∀ J, inAxes (subAxes V) J → ∃ pos, specPos I J = some pos ∧
        getindexFast V (linearIndex (subAxes V) J) = readElt (p.atPos pos)) ∧
      ∀ i, (linearAxis (subAxes V)).mem i = false → getindexFast V i = .error .bounds

def P339General : Prop := ∀ {α : Type} (p : Par α) (I : List Idx), FastCaseGeneral p I →
    (viewAxes I).length = 1 →
    ∃ V, subArray p I = .ok V ∧ V.L = true ∧ V.N = 1 ∧
      (∀ j, inAxes (subAxes V) [j] → ∃ pos, specPos I [j] = some pos ∧
        getindexFastVec V j = readElt (p.atPos pos)) ∧
      ∀ i, (linearAxis (subAxes V)).mem i = false → getindexFastVec V i = .error .bounds

theorem partialFastCase : FastCaseGeneral mat34 partialSlice := by
  refine ⟨mat34_valid, ?_, by decide⟩
  simp [IdxsOKGeneral, IdxOKGeneral, IdxOK, mat34, partialSlice]

theorem p330General_refuted : ¬ P330General := by
  intro h
  obtain ⟨V, hV, _, hread, _⟩ := h mat34 partialSlice partialFastCase
  have hV0 : subArray mat34 partialSlice = .ok partialView := by rfl
  rw [hV0] at hV
  cases hV
  obtain ⟨pos, hp, he⟩ := hread [2] (by decide)
  have hp0 : specPos partialSlice [2] = some [2, 1] := by decide
  rw [hp0] at hp
  cases hp
  revert he
  decide

theorem p339General_refuted : ¬ P339General := by
  intro h
  obtain ⟨V, hV, _, _, hread, _⟩ := h mat34 partialSlice partialFastCase (by decide)
  have hV0 : subArray mat34 partialSlice = .ok partialView := by rfl
  rw [hV0] at hV
  cases hV
  obtain ⟨pos, hp, he⟩ := hread 2 (by decide)
  have hp0 : specPos partialSlice [2] = some [2, 1] := by decide
  rw [hp0] at hp
  cases hp
  revert he
  decide

def P398General : Prop := ∀ {α : Type} (p : Par α) (I : List Idx), FastCaseGeneral p I →
    (viewAxes I).length = 1 →
    ∃ V, subArray p I = .ok V ∧
      (∀ j (x : α), inAxes (subAxes V) [j] → ∃ pos V', specPos I [j] = some pos ∧
        setindexFastVec V x j = .ok V' ∧ V'.indices = V.indices ∧
        ∀ q, inAxes p.axes q → V'.parent.atPos q = if q = pos then some x else p.atPos q) ∧
      ∀ i (x : α), (linearAxis (subAxes V)).mem i = false → setindexFastVec V x i = .error .bounds

theorem p398General_refuted : ¬ P398General := by
  intro h
  obtain ⟨V, hV, hwrite, _⟩ := h mat34 partialSlice partialFastCase (by decide)
  have hV0 : subArray mat34 partialSlice = .ok partialView := by rfl
  rw [hV0] at hV
  cases hV
  obtain ⟨pos, V', hp, hset, _, hvalues⟩ := hwrite 2 0 (by decide)
  have hp0 : specPos partialSlice [2] = some [2, 1] := by decide
  rw [hp0] at hp
  cases hp
  have hset0 : setindexFastVec partialView 0 2 =
      .ok { partialView with parent := partialView.parent.setLin 3 0 } := by rfl
  rw [hset0] at hset
  cases hset
  have bad := hvalues [2, 1] (by decide)
  revert bad
  decide

def P511General : Prop := ∀ {α : Type} (p : Par α) (I : List Idx) (pptr : Int → Int),
    FastCaseGeneral p I → contiguous I = true →
    ∃ V, subArray p I = .ok V ∧ ∀ J, inAxes (subAxes V) J →
      ∃ pos, specPos I J = some pos ∧
        pointerFastContig pptr V (linearIndex (subAxes V) J) = pptr (linearIndex p.axes pos)

theorem p511General_refuted : ¬ P511General := by
  intro h
  obtain ⟨V, hV, hptr⟩ := h mat34 partialSlice id partialFastCase (by decide)
  have hV0 : subArray mat34 partialSlice = .ok partialView := by rfl
  rw [hV0] at hV
  cases hV
  obtain ⟨pos, hp, he⟩ := hptr [2] (by decide)
  have hp0 : specPos partialSlice [2] = some [2, 1] := by decide
  rw [hp0] at hp
  cases hp
  revert he
  decide

def P54General : Prop :=
  (∀ (P : List Int) (rest : List Idx), viewindexing (P.map .int ++ rest) = viewindexing rest) ∧
  ∀ {α : Type} (p : Par α) (I : List Idx), PValid p → IdxsOKGeneral p.axes I →
    viewindexing I = .linear →
    ∃ o s, computeLinearLayout p I = .ok (o, s) ∧
      ∀ J, inAxes (viewAxes I) J → ∃ pos, specPos I J = some pos ∧ inAxes p.axes pos ∧
        reindexLinearRaw I o s (linearIndex (viewAxes I) J) = linearIndex p.axes pos

theorem p54General_refuted : ¬ P54General := by
  intro h
  obtain ⟨o, s, hl, hpos⟩ :=
    h.2 mat34 partialSlice mat34_valid partialFastCase.2.1 partialFastCase.2.2
  have hl0 : computeLinearLayout mat34 partialSlice = .ok (1, 1) := by decide
  rw [hl0] at hl
  cases hl
  obtain ⟨pos, hp, _, he⟩ := hpos [2] (by decide)
  have hp0 : specPos partialSlice [2] = some [2, 1] := by decide
  rw [hp0] at hp
  cases hp
  revert he
  decide

def P426General : Prop := ∀ {α : Type} (p : Par α) (I : List Idx), FastCaseGeneral p I →
    (viewAxes I).length = 1 →
    ∃ V, subArray p I = .ok V ∧
      (∀ j, inAxes (subAxes V) [j] → ∃ pos, specPos I [j] = some pos ∧
        isassignedFastVec V j = (p.atPos pos).isSome) ∧
      ∀ i, (linearAxis (subAxes V)).mem i = false → isassignedFastVec V i = false

def assignedMat34 : Par Int where
  ty := mat34.ty
  axes := mat34.axes
  linear := true
  lin := fun k => if k = 2 then none else some k
  cart := fun pos =>
    let k := linearIndex [⟨1, 3⟩, ⟨1, 4⟩] pos
    if k = 2 then none else some k

theorem assignedMat34_valid : PValid assignedMat34 := by
  refine ⟨rfl, ?_, by decide, fun _ _ => rfl⟩
  intro a ha
  simp [assignedMat34, mat34] at ha
  rcases ha with rfl | rfl <;> simp [AxOK]

def assignedPartialView : Sub Int :=
  ⟨eltypeOf assignedMat34.ty, 1, assignedMat34.ty, true, assignedMat34, partialSlice, 1, 1⟩

theorem p426General_refuted : ¬ P426General := by
  intro h
  have hcase : FastCaseGeneral assignedMat34 partialSlice := by
    refine ⟨assignedMat34_valid, ?_, by decide⟩
    simp [IdxsOKGeneral, IdxOKGeneral, IdxOK, assignedMat34, mat34, partialSlice]
  obtain ⟨V, hV, hread, _⟩ := h assignedMat34 partialSlice hcase (by decide)
  have hV0 : subArray assignedMat34 partialSlice = .ok assignedPartialView := by rfl
  rw [hV0] at hV
  cases hV
  obtain ⟨pos, hp, he⟩ := hread 2 (by decide)
  have hp0 : specPos partialSlice [2] = some [2, 1] := by decide
  rw [hp0] at hp
  cases hp
  revert he
  decide

def P510General : Prop := ∀ {α : Type} (p : Par α) (I : List Idx) (pptr : Int → Int),
    FastCaseGeneral p I → contiguous I = false →
    ∃ V, subArray p I = .ok V ∧ ∀ J, inAxes (subAxes V) J →
      ∃ pos, specPos I J = some pos ∧
        pointerFast pptr V (linearIndex (subAxes V) J) = pptr (linearIndex p.axes pos)

def partialColumn : List Idx := [.int 1, .slice ⟨2, 3⟩]
def partialColumnView : Sub Int :=
  ⟨eltypeOf mat34.ty, 1, mat34.ty, true, mat34, partialColumn, 1, 3⟩

theorem p510General_refuted : ¬ P510General := by
  intro h
  have hcase : FastCaseGeneral mat34 partialColumn := by
    refine ⟨mat34_valid, ?_, by decide⟩
    simp [IdxsOKGeneral, IdxOKGeneral, IdxOK, mat34, partialColumn]
  obtain ⟨V, hV, hptr⟩ := h mat34 partialColumn id hcase (by decide)
  have hV0 : subArray mat34 partialColumn = .ok partialColumnView := by rfl
  rw [hV0] at hV
  cases hV
  obtain ⟨pos, hp, he⟩ := hptr [2] (by decide)
  have hp0 : specPos partialColumn [2] = some [1, 2] := by decide
  rw [hp0] at hp
  cases hp
  revert he
  decide

end JuliaLean.MultidimCov.SubarrayV2
