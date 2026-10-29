import JuliaLean.MultidimCov.SubarrayV2Cart

/-!
Properties of the `base/subarray.jl` construction, layout and access methods,
stated from the documentation of views and linear indexing (see
`SubarrayV2Linear.lean` and `SubarrayV2Cart.lean` for the definitions of the
specification: `viewAxes`, `specPos`, `linearIndex`).
-/

namespace JuliaLean.MultidimCov.SubarrayV2

open JuliaLean.MultidimCov.ArrayV2 (wrap64)

theorem axesOf_eq (i : Idx) : axesOf i = idxAxes i := by cases i <;> rfl

theorem indicesSub_eq : ∀ (I : List Idx), indicesSub I = viewAxes I
  | [] => rfl
  | i :: I => by
      cases i <;> simp [indicesSub, viewAxes_cons, axesOf_eq, indicesSub_eq I, idxAxes]

theorem subAxes_eq (V : Sub α) : subAxes V = viewAxes V.indices := indicesSub_eq _

theorem indexDimsum_length (I : List Idx) : (indexDimsum I).length = (viewAxes I).length := by
  simp [indexDimsum, viewAxes, List.length_flatMap, idxRank]

theorem indexNdims_lengthC : ∀ (I : List Idx) (axs : List Ax), IdxsOKC axs I →
    (indexNdims I).length = axs.length
  | [], axs, h => by simp [IdxsOKC] at h; subst h; rfl
  | i :: I, axs, h => by
      cases i with
      | carr k dims xs =>
          obtain ⟨a1, a2, he, hl, _, _, hr⟩ := h
          have := indexNdims_lengthC I a2 hr
          simp [indexNdims, idxConsumes] at this ⊢
          rw [he, List.length_append, hl, this]
      | _ =>
        match axs, h with
        | a :: axs, h =>
          have := indexNdims_lengthC I axs h.2
          simp [indexNdims, idxConsumes] at this ⊢; omega
        | [], h => simp [IdxsOKC] at h

theorem IdxsOK_C : ∀ (axs : List Ax) (I : List Idx), IdxsOK axs I → IdxsOKC axs I
  | [], [], _ => rfl
  | a :: axs, i :: I, h => by
      cases i with
      | carr _ _ _ => exact h.1.elim
      | _ => exact ⟨h.1, IdxsOK_C axs I h.2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem check_ok (p : Par α) (I : List Idx) (h : IdxsOKC p.axes I) :
    checkParentIndexMatch (.arr p.axes.length) I = .ok () := by
  simp [checkParentIndexMatch, checkMatchShape, indexNdims_lengthC _ _ h, checkMatch47]

theorem PValid.allOK {p : Par α} (hp : PValid p) : ∀ a ∈ p.axes, AxOK a := hp.2.1

/-! ## Construction -/

/-- Row 30: Cartesian construction. The view has element type `eltype(P)` of the
parent type `P`, rank `N` = the number of output dimensions, stores the parent
and indices, is not linear, and its `getindex` reads the element the manual
assigns to `A[I...][J...]`. A rank mismatch is the documented `ArgumentError`. -/
def P30 : Prop := ∀ {α : Type} (p : Par α) (I : List Idx) (dims : List Bool),
    subCartesian p I dims =
      (if (indexNdims I).length = p.axes.length then
        .ok ⟨eltypeOf p.ty, dims.length, p.ty, false, p, I, 0, 0⟩
      else .error (.argument s!"number of indices ({(indexNdims I).length}) must match the parent dimensionality ({p.axes.length})")) ∧
    ((∀ a ∈ p.axes, AxOK a) → IdxsOKC p.axes I →
      ∃ V, subCartesian p I (indexDimsum I) = .ok V ∧ V.N = (viewAxes I).length ∧
        ∀ J, inAxes (viewAxes I) J → ∃ pos, specPos I J = some pos ∧
          getindexSlow V J = readElt (p.atPos pos))

theorem p30 : P30 := by
  intro α p I dims
  refine ⟨?_, ?_⟩
  · unfold subCartesian subInner checkParentIndexMatch checkMatchShape
    by_cases h : (indexNdims I).length = p.axes.length
    · simp [h, checkMatch47, typeOf]
    · have h' : ¬ p.axes.length = (indexNdims I).length := fun e => h e.symm
      simp [h, h', checkMatch48, ndimsObj]
  · intro hax hok
    refine ⟨⟨eltypeOf p.ty, (indexDimsum I).length, p.ty, false, p, I, 0, 0⟩, ?_, indexDimsum_length I, ?_⟩
    · simp [subCartesian, subInner, check_ok p I hok, typeOf]
    · intro J hJ
      obtain ⟨pos, h1, h2, _⟩ := reindexS_spec I p.axes J hax hok hJ
      refine ⟨pos, h1, ?_⟩
      have hb : inAxesB (indicesSub I) J = true := by rw [indicesSub_eq]; exact (inAxesB_iff _ _).2 hJ
      simp [getindexSlow, checkboundsCart, subAxes, hb, h2]

theorem subLinear_ok (p : Par α) (I : List Idx) (hp : PValid p) (hI : IdxsOK p.axes I)
    (hv : viewindexing I = .linear) :
    ∃ o s, computeLinearLayout p I = .ok (o, s) ∧
      subLinear p I (indexDimsum I) = .ok ⟨eltypeOf p.ty, (indexDimsum I).length, p.ty, true, p, I, o, s⟩ ∧
      ∀ J, inAxes (viewAxes I) J → ∃ pos, specPos I J = some pos ∧ inAxes p.axes pos ∧
        reindexLinearRaw I o s (linearIndex (viewAxes I) J) = linearIndex p.axes pos := by
  obtain ⟨o, s, h1, h2⟩ := fast_layout p I hp hI hv
  refine ⟨o, s, h1, ?_, h2⟩
  simp [subLinear, h1, subInner, check_ok p I (IdxsOK_C _ _ hI), typeOf]

theorem subArray_fast (p : Par α) (I : List Idx) (hp : PValid p) (hI : IdxsOK p.axes I)
    (hv : viewindexing I = .linear) :
    ∃ o s, subArray p I = .ok ⟨eltypeOf p.ty, (indexDimsum I).length, p.ty, true, p, I, o, s⟩ ∧
      ∀ J, inAxes (viewAxes I) J → ∃ pos, specPos I J = some pos ∧ inAxes p.axes pos ∧
        reindexLinearRaw I o s (linearIndex (viewAxes I) J) = linearIndex p.axes pos := by
  obtain ⟨o, s, _, h2, h3⟩ := subLinear_ok p I hp hI hv
  refine ⟨o, s, ?_, h3⟩
  have hs : p.style = .linear := by simp [Par.style, hp.1]
  simp [subArray, hv, hs, Style.combine, ensureIndexable, h2]

/-- Row 34: linear construction stores `offset1`/`stride1` such that the linear
index `LinearIndices(V)[J]` of every element is mapped by `_reindexlinear` to
`LinearIndices(parent)[p]` for the parent position `p` of `A[I...][J...]`. -/
def P34 : Prop := ∀ {α : Type} (p : Par α) (I : List Idx), PValid p → IdxsOK p.axes I →
    viewindexing I = .linear →
    ∃ V, subLinear p I (indexDimsum I) = .ok V ∧ V.T = eltypeOf p.ty ∧ V.P = p.ty ∧
      V.N = (viewAxes I).length ∧ V.L = true ∧ V.parent = p ∧ V.indices = I ∧
      ∀ J, inAxes (viewAxes I) J → ∃ pos, specPos I J = some pos ∧ inAxes p.axes pos ∧
        reindexLinear V (linearIndex (viewAxes I) J) = linearIndex p.axes pos

theorem p34 : P34 := by
  intro α p I hp hI hv
  obtain ⟨o, s, _, h2, h3⟩ := subLinear_ok p I hp hI hv
  exact ⟨_, h2, rfl, rfl, indexDimsum_length I, rfl, rfl, rfl, h3⟩

/-- Row 47: the matching-rank method returns `nothing` for every parent whose rank
is the number of consumed indices. -/
def P47 : Prop := (∀ (n : Nat) (shape : List Bool), n = shape.length → checkMatchShape (.arr n) shape = .ok ()) ∧
    ∀ {α : Type} (p : Par α) (I : List Idx), (indexNdims I).length = p.axes.length →
      checkParentIndexMatch (.arr p.axes.length) I = .ok ()

theorem p47 : P47 := ⟨fun n shape h => by simp [checkMatchShape, h, checkMatch47],
  fun p I h => by simp [checkParentIndexMatch, checkMatchShape, checkMatch47, h]⟩

/-- Row 48: any other parent is rejected with
`ArgumentError("number of indices (N) must match the parent dimensionality (d)")`,
where `d = ndims(parent)` (0 for a number); `ndims` failing propagates. -/
def P48 : Prop := ∀ (shape : List Bool),
    (∀ d : Nat, d ≠ shape.length → checkMatchShape (.arr d) shape =
      .error (.argument s!"number of indices ({shape.length}) must match the parent dimensionality ({d})")) ∧
    checkMatchShape .num shape =
      .error (.argument s!"number of indices ({shape.length}) must match the parent dimensionality ({(0 : Nat)})") ∧
    checkMatchShape .other shape = .error .method

theorem p48 : P48 := fun shape =>
  ⟨fun d h => by simp [checkMatchShape, h, checkMatch48, ndimsObj],
   by simp [checkMatchShape, checkMatch48, ndimsObj],
   by simp [checkMatchShape, checkMatch48, ndimsObj]⟩

/-- Row 54: leading scalars do not change `viewindexing`, and an `IndexLinear`
classification always yields a correct linear layout. -/
def P54 : Prop := (∀ (P : List Int) (rest : List Idx), viewindexing (P.map .int ++ rest) = viewindexing rest) ∧
    ∀ {α : Type} (p : Par α) (I : List Idx), PValid p → IdxsOK p.axes I → viewindexing I = .linear →
      ∃ o s, computeLinearLayout p I = .ok (o, s) ∧
        ∀ J, inAxes (viewAxes I) J → ∃ pos, specPos I J = some pos ∧ inAxes p.axes pos ∧
          reindexLinearRaw I o s (linearIndex (viewAxes I) J) = linearIndex p.axes pos

theorem p54 : P54 := by
  refine ⟨?_, fun p I hp hI hv => fast_layout p I hp hI hv⟩
  intro P rest
  induction P with
  | nil => rfl

  | cons n P ih => simpa [viewindexing] using ih
/-- The scalar overload classifies the remaining index tuple. -/
def P54Scalar : Prop := ∀ n rest, viewindexing (.int n :: rest) = viewindexing rest

theorem p54Scalar : P54Scalar := by
  intro n rest
  exact p54.1 [n] rest

/-! ## Layout computations -/

/-- Row 478: `compute_offset1` gives the offset that makes linear indexing agree
with the parent position of every element. -/
def P478 : Prop := ∀ {α : Type} (p : Par α) (I : List Idx), PValid p → IdxsOK p.axes I →
    viewindexing I = .linear →
    ∃ s o, computeStride1 p I = .ok s ∧ computeOffset1 p s I = .ok o ∧
      ∀ J, inAxes (viewAxes I) J → ∃ pos, specPos I J = some pos ∧ inAxes p.axes pos ∧
        reindexLinearRaw I o s (linearIndex (viewAxes I) J) = linearIndex p.axes pos

theorem p478 : P478 := by
  intro α p I hp hI hv
  obtain ⟨o, s, h1, h2⟩ := fast_layout p I hp hI hv
  unfold computeLinearLayout at h1
  cases hs : computeStride1 p I with
  | error e => rw [hs] at h1; cases h1
  | ok s' =>
    rw [hs, sbind_ok] at h1
    cases ho : computeOffset1 p s' I with
    | error e => rw [ho] at h1; cases h1
    | ok o' =>
      rw [ho] at h1
      simp at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact ⟨s', o', rfl, ho, h2⟩

/-- Row 486: `compute_linindex(parent, I)` is `LinearIndices(parent)[first.(I)...]`
(modulo `2^64`), or the first failing `first`. -/
def P486 : Prop := ∀ {α : Type} (p : Par α) (I : List Idx), (∀ a ∈ p.axes, AxOK a) →
    axesLen p.axes ≤ 2^62 → p.axes.length = I.length →
    computeLinindex p I = (I.mapM idxFirst).map (fun fs => wrap64 (linearIndex p.axes fs)) ∧
    ∀ fs, I.mapM idxFirst = .ok fs → inAxes p.axes fs → computeLinindex p I = .ok (linearIndex p.axes fs)

theorem p486 : P486 := by
  intro α p I hax hlen0 hl
  have hF : -2^63 ≤ firstLinear p.axes ∧ firstLinear p.axes < 2^63 := by
    match hx : p.axes with
    | [a] =>
        have := hax a (by rw [hx]; simp)
        simp [firstLinear]; unfold AxOK at this; omega
    | [] => simp [firstLinear]
    | _ :: _ :: _ => simp [firstLinear]
  have h := computeLinindex_eq p I hl hF
  refine ⟨h, fun fs hfs hin => ?_⟩
  rw [h, hfs]
  have hr : -2^63 ≤ linearIndex p.axes fs ∧ linearIndex p.axes fs < 2^63 := by
    match hx : p.axes, fs, hin with
    | [a], [x], hin =>
        have := hax a (by rw [hx]; simp)
        obtain ⟨h1, h2, _⟩ := hin
        simp only [linearIndex]; unfold AxOK at this; omega
    | [], [], _ => simp [linearIndex, linOff]
    | a :: b :: as, x :: y :: ps, hin =>
        have hb := linOff_bounds (a :: b :: as) (x :: y :: ps) hin
        rw [hx] at hlen0
        simp only [linearIndex]; omega
  simp [Except.map, w_id hr.1 hr.2]

theorem linindexRec_two (f s : Int) (ip : List Ax) (i j : Idx) (rest : List Idx)
    (hl : ip.length = (i :: j :: rest).length) :
    computeLinindexRec (wrap64 f) (wrap64 s) ip (i :: j :: rest) =
      ((i :: j :: rest).mapM idxFirst).map (fun fs => wrap64 (f + s * linOff ip fs)) :=
  linindexRec_eq _ ip f s hl

/-- Row 491: with at least two indices left, `compute_linindex` adds each index's
first value minus the axis start, times the running stride product (modulo
`2^64`); a failing `Int(first(I[k]))` propagates in order. -/
def P491 : Prop := ∀ (f s : Int) (ip : List Ax) (i j : Idx) (rest : List Idx),
    ip.length = (i :: j :: rest).length →
    computeLinindexRec (wrap64 f) (wrap64 s) ip (i :: j :: rest) =
      ((i :: j :: rest).mapM idxFirst).map (fun fs => wrap64 (f + s * linOff ip fs))

theorem p491 : P491 := fun f s ip i j rest hl => linindexRec_two f s ip i j rest hl

/-- Row 496: the last index adds `(first(I[1]) - first(IP[1])) * s`. -/
def P496 : Prop := ∀ (f s : Int) (a : Ax) (i : Idx),
    computeLinindexRec (wrap64 f) (wrap64 s) [a] [i] =
      (idxFirst i).map (fun fi => wrap64 (f + s * (fi - a.lo)))

theorem p496 : P496 := by
  intro f s a i
  rw [linindexRec_eq [i] [a] f s rfl]
  simp only [List.mapM_cons, List.mapM_nil]
  cases idxFirst i with
  | error e => rfl
  | ok fi => simp [Except.map, linOff]

/-! ## Access through a fast view -/

theorem linOff_inj : ∀ (axs : List Ax) (p q : List Int), inAxes axs p → inAxes axs q →
    linOff axs p = linOff axs q → p = q
  | [], [], [], _, _, _ => rfl
  | a :: axs, x :: p, y :: q, hp, hq, h => by
      rw [linOff_cons, linOff_cons] at h
      obtain ⟨hx1, hx2, hp'⟩ := hp
      obtain ⟨hy1, hy2, hq'⟩ := hq
      have bp := linOff_bounds axs p hp'
      have bq := linOff_bounds axs q hq'
      have hl := Ax.len_eq a (by omega)
      have hxy : x = y ∧ linOff axs p = linOff axs q := by
        rcases Int.lt_trichotomy (linOff axs p) (linOff axs q) with hlt | heq | hgt
        · have : a.len * (linOff axs p + 1) ≤ a.len * linOff axs q :=
            Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
          rw [Int.mul_add, Int.mul_one] at this; omega
        · rw [heq] at h; exact ⟨by omega, heq⟩
        · have : a.len * (linOff axs q + 1) ≤ a.len * linOff axs p :=
            Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
          rw [Int.mul_add, Int.mul_one] at this; omega
      rw [hxy.1, linOff_inj axs p q hp' hq' hxy.2]
  | [], _ :: _, _, hp, _, _ => hp.elim
  | _ :: _, [], _, hp, _, _ => hp.elim
  | [], [], _ :: _, _, hq, _ => hq.elim
  | _ :: _, _ :: _, [], _, hq, _ => hq.elim

theorem linearIndex_inj (axs : List Ax) (p q : List Int) (hp : inAxes axs p) (hq : inAxes axs q)
    (h : linearIndex axs p = linearIndex axs q) : p = q := by
  match axs, p, q, hp, hq with
  | [a], [x], [y], _, _ => simp [linearIndex] at h; rw [h]
  | [], [], [], _, _ => rfl
  | a :: b :: as, x :: x' :: p, y :: y' :: q, hp, hq =>
      simp only [linearIndex] at h
      exact linOff_inj _ _ _ hp hq (by omega)

/-- Hypotheses shared by the fast-access properties: a valid `IndexLinear`
parent and in-bounds indices that `viewindexing` classifies as linear. -/
def FastCase (p : Par α) (I : List Idx) : Prop :=
  PValid p ∧ IdxsOK p.axes I ∧ viewindexing I = .linear

theorem fast_access (p : Par α) (I : List Idx) (h : FastCase p I) :
    ∃ V, subArray p I = .ok V ∧ V.L = true ∧ V.parent = p ∧ V.indices = I ∧
      V.N = (viewAxes I).length ∧ subAxes V = viewAxes I ∧
      ∀ J, inAxes (viewAxes I) J → ∃ pos, specPos I J = some pos ∧ inAxes p.axes pos ∧
        reindexLinear V (linearIndex (viewAxes I) J) = linearIndex p.axes pos := by
  obtain ⟨o, s, h1, h2⟩ := subArray_fast p I h.1 h.2.1 h.2.2
  exact ⟨_, h1, rfl, rfl, rfl, indexDimsum_length I, subAxes_eq _, h2⟩

/-- Row 330: `V[LinearIndices(V)[J]]` on a fast view is the element of
`A[I...][J...]`; any other linear index is a `BoundsError`. -/
def P330 : Prop := ∀ {α : Type} (p : Par α) (I : List Idx), FastCase p I →
    ∃ V, subArray p I = .ok V ∧ V.L = true ∧
      (∀ J, inAxes (subAxes V) J → ∃ pos, specPos I J = some pos ∧
        getindexFast V (linearIndex (subAxes V) J) = readElt (p.atPos pos)) ∧
      ∀ i, (linearAxis (subAxes V)).mem i = false → getindexFast V i = .error .bounds

theorem p330 : P330 := by
  intro α p I h
  obtain ⟨V, hV, hL, hp, hI, _, hax, hJ⟩ := fast_access p I h
  refine ⟨V, hV, hL, ?_, ?_⟩
  · intro J hin
    rw [hax] at hin ⊢
    obtain ⟨pos, h1, h2, h3⟩ := hJ J hin
    refine ⟨pos, h1, ?_⟩
    have hb : checkboundsLin V (linearIndex (viewAxes I) J) = .ok () := by
      simp [checkboundsLin, hax, linearIndex_mem _ _ hin]
    simp only [getindexFast, hb, sbind_ok, Par.atLin, h3, hp, Par.atPos, h.1.2.2.2 pos h2]
  · intro i hi
    simp [getindexFast, checkboundsLin, hi]

/-- Row 339: the same for one-dimensional fast views (`FastSubArray{<:Any,1}`). -/
def P339 : Prop := ∀ {α : Type} (p : Par α) (I : List Idx), FastCase p I → (viewAxes I).length = 1 →
    ∃ V, subArray p I = .ok V ∧ V.L = true ∧ V.N = 1 ∧
      (∀ j, inAxes (subAxes V) [j] → ∃ pos, specPos I [j] = some pos ∧
        getindexFastVec V j = readElt (p.atPos pos)) ∧
      ∀ i, (linearAxis (subAxes V)).mem i = false → getindexFastVec V i = .error .bounds

theorem p339 : P339 := by
  intro α p I h h1
  obtain ⟨V, hV, hL, hp, hI, hN, hax, hJ⟩ := fast_access p I h
  refine ⟨V, hV, hL, by rw [hN, h1], ?_, ?_⟩
  · intro j hin
    rw [hax] at hin
    obtain ⟨pos, h1', h2, h3⟩ := hJ [j] hin
    refine ⟨pos, h1', ?_⟩
    have hl : linearIndex (viewAxes I) [j] = j := by
      match hva : viewAxes I, h1 with
      | [a], _ => rfl
    rw [hl] at h3
    have hb : checkboundsLin V j = .ok () := by
      have := linearIndex_mem _ _ hin
      rw [hl] at this
      simp [checkboundsLin, hax, this]
    simp only [getindexFastVec, hb, sbind_ok, Par.atLin, h3, hp, Par.atPos, h.1.2.2.2 pos h2]
  · intro i hi
    simp [getindexFastVec, checkboundsLin, hi]

/-- Row 398: `V[j] = x` on a one-dimensional fast view writes exactly the parent
element of `A[I...][j]` and returns the view; out of bounds is a `BoundsError`. -/
def P398 : Prop := ∀ {α : Type} (p : Par α) (I : List Idx), FastCase p I → (viewAxes I).length = 1 →
    ∃ V, subArray p I = .ok V ∧
      (∀ j (x : α), inAxes (subAxes V) [j] → ∃ pos V', specPos I [j] = some pos ∧
        setindexFastVec V x j = .ok V' ∧ V'.indices = V.indices ∧
        ∀ q, inAxes p.axes q → V'.parent.atPos q = if q = pos then some x else p.atPos q) ∧
      ∀ i (x : α), (linearAxis (subAxes V)).mem i = false → setindexFastVec V x i = .error .bounds

theorem p398 : P398 := by
  intro α p I h h1
  obtain ⟨V, hV, _, hp, _, _, hax, hJ⟩ := fast_access p I h
  refine ⟨V, hV, ?_, ?_⟩
  · intro j x hin
    rw [hax] at hin
    obtain ⟨pos, h1', h2, h3⟩ := hJ [j] hin
    have hl : linearIndex (viewAxes I) [j] = j := by
      match hva : viewAxes I, h1 with
      | [a], _ => rfl
    rw [hl] at h3
    have hb : checkboundsLin V j = .ok () := by
      have := linearIndex_mem _ _ hin
      rw [hl] at this
      simp [checkboundsLin, hax, this]
    refine ⟨pos, { V with parent := V.parent.setLin (reindexLinear V j) x }, h1',
      by simp only [setindexFastVec, hb, sbind_ok]; rfl, rfl, ?_⟩
    intro q hq
    show (V.parent.setLin (reindexLinear V j) x).cart q = _
    rw [h3, hp]
    simp only [Par.setLin, Par.atPos]
    by_cases hqp : q = pos
    · simp [hqp]
    · have : linearIndex p.axes q ≠ linearIndex p.axes pos :=
        fun e => hqp (linearIndex_inj _ _ _ hq h2 e)
      simp [this, hqp]
  · intro i x hi
    simp [setindexFastVec, checkboundsLin, hi]

/-- Row 426: `isassigned(V, j)` on a one-dimensional fast view reports whether
the parent element of `A[I...][j]` is assigned, and is `false` out of bounds. -/
def P426 : Prop := ∀ {α : Type} (p : Par α) (I : List Idx), FastCase p I → (viewAxes I).length = 1 →
    ∃ V, subArray p I = .ok V ∧
      (∀ j, inAxes (subAxes V) [j] → ∃ pos, specPos I [j] = some pos ∧
        isassignedFastVec V j = (p.atPos pos).isSome) ∧
      ∀ i, (linearAxis (subAxes V)).mem i = false → isassignedFastVec V i = false

theorem p426 : P426 := by
  intro α p I h h1
  obtain ⟨V, hV, _, hp, _, _, hax, hJ⟩ := fast_access p I h
  refine ⟨V, hV, ?_, ?_⟩
  · intro j hin
    rw [hax] at hin
    obtain ⟨pos, h1', h2, h3⟩ := hJ [j] hin
    have hl : linearIndex (viewAxes I) [j] = j := by
      match hva : viewAxes I, h1 with
      | [a], _ => rfl
    rw [hl] at h3
    have hm := linearIndex_mem _ _ hin
    rw [hl] at hm
    refine ⟨pos, h1', ?_⟩
    simp [isassignedFastVec, hax, hm, Par.assignedLin, h3, hp, Par.atPos, h.1.2.2.2 pos h2]
  · intro i hi
    simp [isassignedFastVec, hi]

/-- Row 510: on a fast view that is not contiguous, `pointer(V, i)` is
`pointer(parent, k)` for the parent linear index `k` of element `i`. -/
def P510 : Prop := ∀ {α : Type} (p : Par α) (I : List Idx) (pptr : Int → Int), FastCase p I →
    contiguous I = false →
    ∃ V, subArray p I = .ok V ∧ ∀ J, inAxes (subAxes V) J → ∃ pos, specPos I J = some pos ∧
      pointerFast pptr V (linearIndex (subAxes V) J) = pptr (linearIndex p.axes pos)

theorem p510 : P510 := by
  intro α p I pptr h hc
  obtain ⟨V, hV, _, _, hI, _, hax, hJ⟩ := fast_access p I h
  refine ⟨V, hV, fun J hin => ?_⟩
  rw [hax] at hin ⊢
  obtain ⟨pos, h1, _, h3⟩ := hJ J hin
  refine ⟨pos, h1, ?_⟩
  rw [reindexLinear_raw, hI] at h3
  simp only [reindexLinearRaw, hc, Bool.false_eq_true, ite_false] at h3
  rw [pointerFast, h3]

/-- Row 511: on a contiguous fast view, `pointer(V, i)` is `pointer(parent, k)`
for the parent linear index `k` of element `i`. -/
def P511 : Prop := ∀ {α : Type} (p : Par α) (I : List Idx) (pptr : Int → Int), FastCase p I →
    contiguous I = true →
    ∃ V, subArray p I = .ok V ∧ ∀ J, inAxes (subAxes V) J → ∃ pos, specPos I J = some pos ∧
      pointerFastContig pptr V (linearIndex (subAxes V) J) = pptr (linearIndex p.axes pos)

theorem p511 : P511 := by
  intro α p I pptr h hc
  obtain ⟨V, hV, _, _, hI, _, hax, hJ⟩ := fast_access p I h
  refine ⟨V, hV, fun J hin => ?_⟩
  rw [hax] at hin ⊢
  obtain ⟨pos, h1, _, h3⟩ := hJ J hin
  refine ⟨pos, h1, ?_⟩
  rw [reindexLinear_raw, hI] at h3
  simp only [reindexLinearRaw, hc, ite_true] at h3
  simp only [pointerFastContig, h3]

/-! ## Reindexing, strides, axes -/

/-- Row 292: `reindex((), ())` is `()`, there is no method for leftover
subindices, and `reindex` composes indices as the manual defines. -/
def P292 : Prop := reindexS [] [] = .ok [] ∧ (∀ j J, reindexS [] (j :: J) = .error .method) ∧
    ∀ (I : List Idx) (axs : List Ax) (J : List Int), (∀ a ∈ axs, AxOK a) → IdxsOKC axs I →
      inAxes (viewAxes I) J → ∃ pos, specPos I J = some pos ∧ reindexS I J = .ok pos ∧ inAxes axs pos

theorem p292 : P292 := ⟨rfl, fun _ _ => rfl, reindexS_spec⟩

/-- Row 443: `strides(V)` throws `ArgumentError("strides is invalid for SubArrays
with indices of type T")` at the first index that is neither a scalar nor a range. -/
def P443 : Prop := ∀ (strds : List Int) (i : Idx) (rest : List Idx), i.isScalar = false →
    i.isRange = false →
    substrides strds (i :: rest) =
      .error (.argument s!"strides is invalid for SubArrays with indices of type {idxTypeName i}")

theorem p443 : P443 := by
  intro strds i rest h1 h2
  cases i <;> simp [Idx.isScalar, Idx.isRange] at h1 h2 <;> (unfold substrides; simp [Idx.isRange])

/-- Row 525: `axes(V)` lists the axes of the stored non-scalar indices in order
(one-based for `OneTo`, `UnitRange`, `StepRange`, arrays and logical masks; the
range itself for `Slice` and `IdentityUnitRange`). -/
def P525 : Prop := ∀ {α : Type} (V : Sub α), subAxes V = viewAxes V.indices

theorem p525 : P525 := fun V => subAxes_eq V

/-- Row 534: `axes1(V)` is `axes(V, 1)`: the first axis of `axes(V)`, or `OneTo(1)`
for a zero-dimensional view. -/
def P534 : Prop := ∀ {α : Type} (V : Sub α), V.N = (subAxes V).length →
    axes1Sub V = some ((subAxes V).headD (oneAx 1))

theorem axes1SubRec_eq : ∀ (I : List Idx), (viewAxes I) ≠ [] →
    axes1SubRec I = some ((viewAxes I).headD (oneAx 1))
  | [], h => absurd rfl h
  | i :: I, h => by
      rw [viewAxes_cons] at h ⊢
      by_cases hs : i.isScalar = true
      · cases i <;> simp [Idx.isScalar] at hs
        simpa [axes1SubRec, idxAxes] using axes1SubRec_eq I (by simpa [idxAxes] using h)
      · have hrec : axes1SubRec (i :: I) =
            if idxRank i = 0 then axes1SubRec I else some ((axesOf i).headD (oneAx 1)) := by
          cases i <;> simp [Idx.isScalar] at hs <;> rfl
        rw [hrec]
        by_cases h0 : idxAxes i = []
        · have hr : idxRank i = 0 := by simp [idxRank, h0]
          rw [if_pos hr]
          rw [h0] at h ⊢
          simp only [List.nil_append] at h ⊢
          exact axes1SubRec_eq I h
        · obtain ⟨a, as, has⟩ := List.exists_cons_of_ne_nil h0
          have hr : idxRank i ≠ 0 := by simp [idxRank, has]
          rw [if_neg hr, axesOf_eq, has]
          rfl

theorem p534 : P534 := by
  intro α V hN
  unfold axes1Sub
  by_cases h0 : V.N = 0
  · rw [if_pos h0]
    rw [h0] at hN
    have : subAxes V = [] := List.eq_nil_of_length_eq_zero hN.symm
    rw [this]; rfl
  · rw [if_neg h0, subAxes_eq]
    exact axes1SubRec_eq _ (by
      intro he; rw [subAxes_eq, he] at hN; exact h0 (by simpa using hN))

end JuliaLean.MultidimCov.SubarrayV2
