import JuliaLean.MultidimCov.SubarrayV2Model

/-!
The linear-layout invariant of fast `SubArray`s.

For an `IndexLinear` parent and an index tuple that `viewindexing` classifies
as `IndexLinear`, `SubArray(parent, I)` stores `offset1`/`stride1` such that the
linear index `LinearIndices(V)[J]` of every element `J` of the view is mapped by
`_reindexlinear` to `LinearIndices(parent)[p]`, where `p` is the parent
position of `A[I...][J...]` given by the manual (`specPos`). This is the
promise of linear indexing (`LinearIndices` docstring, `base/indices.jl:476-505`:
indexing with a linear index refers to the same element as the corresponding
Cartesian index), applied to views.

Preconditions are those `view` establishes (`checkbounds(A, I...)`, line 224):
every index lies in its parent axis; a `Slice` spans its parent axis (the
`Slice` docstring, `base/indices.jl:331-336`: "a complete slice of a
dimension"); axes fit in `Int`.
-/

namespace JuliaLean.MultidimCov.SubarrayV2

open JuliaLean.MultidimCov.ArrayV2 (wrap64)

/-! ### `Int` wrapping algebra -/

theorem w_add_l (a b : Int) : wrap64 (wrap64 a + b) = wrap64 (a + b) := by unfold wrap64; omega
theorem w_add_r (a b : Int) : wrap64 (a + wrap64 b) = wrap64 (a + b) := by unfold wrap64; omega
theorem w_sub_l (a b : Int) : wrap64 (wrap64 a - b) = wrap64 (a - b) := by unfold wrap64; omega
theorem w_sub_r (a b : Int) : wrap64 (a - wrap64 b) = wrap64 (a - b) := by unfold wrap64; omega

theorem w_mul_l (a b : Int) : wrap64 (wrap64 a * b) = wrap64 (a * b) := by
  unfold wrap64
  have h : (a + 2^63) % 2^64 - 2^63 = a - 2^64 * ((a + 2^63) / 2^64) := by
    rw [Int.emod_def]; omega
  rw [h, Int.sub_mul, Int.mul_assoc]
  have key : (a * b - 2^64 * (((a + 2^63) / 2^64) * b) + 2^63) % 2^64 = (a*b + 2^63) % 2^64 := by
    rw [show a * b - 2^64 * (((a + 2^63) / 2^64) * b) + 2^63
        = (a*b + 2^63) + 2^64 * (-(((a + 2^63) / 2^64)*b)) by omega]
    exact Int.add_mul_emod_self_left _ _ _
  omega

theorem w_mul_r (a b : Int) : wrap64 (a * wrap64 b) = wrap64 (a * b) := by
  rw [Int.mul_comm, w_mul_l, Int.mul_comm]

theorem w_id {x : Int} (h0 : -2^63 ≤ x) (h1 : x < 2^63) : wrap64 x = x := by
  unfold wrap64; rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega

theorem w_one : wrap64 1 = 1 := w_id (by omega) (by omega)

theorem iadd_ww (a b : Int) : iadd (wrap64 a) (wrap64 b) = wrap64 (a + b) := by
  unfold iadd; rw [w_add_l, w_add_r]
theorem isub_ww (a b : Int) : isub (wrap64 a) (wrap64 b) = wrap64 (a - b) := by
  unfold isub; rw [w_sub_l, w_sub_r]
theorem imul_ww (a b : Int) : imul (wrap64 a) (wrap64 b) = wrap64 (a * b) := by
  unfold imul; rw [w_mul_l, w_mul_r]
theorem iadd_w (a b : Int) : iadd (wrap64 a) b = wrap64 (a + b) := by unfold iadd; rw [w_add_l]
theorem imul_w (a b : Int) : imul (wrap64 a) b = wrap64 (a * b) := by unfold imul; rw [w_mul_l]
theorem isub_w (a b : Int) : isub a b = wrap64 (a - b) := rfl

/-! ### Validity of parents and indices -/

/-- A well-formed axis whose bounds fit comfortably in `Int`. -/
def AxOK (a : Ax) : Prop := a.lo ≤ a.hi + 1 ∧ -2^62 ≤ a.lo ∧ a.hi ≤ 2^62

/-- An `IndexLinear` parent with well-formed axes and fewer than `2^62` elements,
whose Cartesian and linear indexing agree (`LinearIndices` docstring). -/
def PValid (p : Par α) : Prop :=
  p.linear = true ∧ (∀ a ∈ p.axes, AxOK a) ∧ axesLen p.axes ≤ 2^62 ∧
    ∀ pos, inAxes p.axes pos → p.cart pos = p.lin (linearIndex p.axes pos)

/-- `checkbounds` of one index against its parent axis, plus the index object's
own invariants: a `Slice` spans the axis, ranges are normalized. -/
def IdxOK (ax : Ax) : Idx → Prop
  | .int n => ax.lo ≤ n ∧ n ≤ ax.hi
  | .slice a => a = ax
  | .ident a => a.lo ≤ a.hi + 1 ∧ (a.lo ≤ a.hi → ax.lo ≤ a.lo ∧ a.hi ≤ ax.hi)
  | .oneto n => 0 ≤ n ∧ (1 ≤ n → ax.lo ≤ 1 ∧ n ≤ ax.hi)
  | .unit a => a.lo ≤ a.hi + 1 ∧ (a.lo ≤ a.hi → ax.lo ≤ a.lo ∧ a.hi ≤ ax.hi)
  | .step s st n => st ≠ 0 ∧ 0 ≤ n ∧
      (1 ≤ n → ax.lo ≤ s ∧ s ≤ ax.hi ∧ ax.lo ≤ s + (n - 1) * st ∧ s + (n - 1) * st ≤ ax.hi)
  | .arr dims xs => xs.length = dims.prod ∧ ∀ x ∈ xs, ax.lo ≤ x ∧ x ≤ ax.hi
  | .mask bs => (bs.length : Int) = ax.len ∧ ax.lo = 1
  | .carr _ _ _ => False

/-- `IdxOK` for every index against its own parent dimension. -/
def IdxsOK : List Ax → List Idx → Prop
  | [], [] => True
  | a :: as, i :: is => IdxOK a i ∧ IdxsOK as is
  | _, _ => False

/-- Bounds-valid indices include a Slice over any in-bounds subrange. -/
def IdxOKGeneral (ax : Ax) (idx : Idx) : Prop :=
  match idx with
  | .slice a => a.lo ≤ a.hi + 1 ∧ (a.lo ≤ a.hi → ax.lo ≤ a.lo ∧ a.hi ≤ ax.hi)
  | _ => IdxOK ax idx

def IdxsOKGeneral : List Ax → List Idx → Prop
  | [], [] => True
  | a :: as, i :: is => IdxOKGeneral a i ∧ IdxsOKGeneral as is
  | _, _ => False

theorem IdxsOK.length : ∀ {as : List Ax} {is : List Idx}, IdxsOK as is → as.length = is.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [IdxsOK.length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-! ### Shapes of linear-style index tuples -/

/-- Step of the leading extended index as `compute_stride1` uses it (`Slice`: 1). -/
def strideOf : Idx → Int
  | .slice _ => 1
  | i => idxStep i

theorem allScalar_cons (i : Idx) (l : List Idx) : allScalar (i :: l) = (i.isScalar && allScalar l) := by
  simp [allScalar]

theorem allScalar_ints : ∀ (Q : List Int), allScalar (Q.map .int) = true
  | [] => rfl
  | _ :: Q => by simp [allScalar_cons, Idx.isScalar, allScalar_ints Q]

theorem allScalar_eq : ∀ (l : List Idx), allScalar l = true → ∃ Q : List Int, l = Q.map .int
  | [] , _ => ⟨[], rfl⟩
  | i :: l, h => by
      rw [allScalar_cons] at h
      cases i <;> simp [Idx.isScalar] at h
      rename_i n
      obtain ⟨Q, hQ⟩ := allScalar_eq l h
      exact ⟨n :: Q, by simp [hQ]⟩

/-- A chain of `Slice`s, then at most one unit range, then scalars, with at least
two extended indices (lines 56-59). -/
def SliceChain (I : List Idx) : Prop :=
  ∃ (as : List Ax) (us : List Idx) (Q : List Int), I = as.map .slice ++ us ++ Q.map .int ∧
    as ≠ [] ∧ us.length ≤ 1 ∧ (∀ u ∈ us, u.isUnitRange = true) ∧ 2 ≤ as.length + us.length

theorem vi_slice_nonslice (a : Ax) (j : Idx) (rest' : List Idx) (hj : j.isSlice = false) :
    viewindexing (.slice a :: j :: rest') =
      (if j.isUnitRange && allScalar rest' then .linear
       else if allScalar (j :: rest') then .linear else .cartesian) := by
  cases j <;> simp [Idx.isSlice] at hj <;> simp [viewindexing]

theorem slice_shape : ∀ (rest : List Idx) (a : Ax), viewindexing (.slice a :: rest) = .linear →
    allScalar rest = true ∨ SliceChain (.slice a :: rest)
  | [], _, _ => Or.inl rfl
  | j :: rest', a, h => by
      by_cases hj : j.isSlice = true
      · cases j <;> simp [Idx.isSlice] at hj
        rename_i b
        by_cases hs : allScalar rest' = true
        · obtain ⟨Q, hQ⟩ := allScalar_eq rest' hs
          exact Or.inr ⟨[a, b], [], Q, by simp [hQ], by simp, by simp, by simp, by simp⟩
        · have e : viewindexing (.slice a :: .slice b :: rest') =
              (if allScalar rest' = true then .linear else viewindexing (.slice b :: rest')) := rfl
          have hv : viewindexing (.slice b :: rest') = .linear := by
            rw [e, if_neg hs] at h; exact h
          rcases slice_shape rest' b hv with h1 | ⟨as, us, Q, he, hne, hu1, hu, h2⟩
          · exact absurd h1 hs
          · refine Or.inr ⟨a :: as, us, Q, ?_, by simp, hu1, hu, by simp; omega⟩
            rw [he]; simp
      · rw [vi_slice_nonslice a j rest' (by simpa using hj)] at h
        by_cases h1 : (j.isUnitRange && allScalar rest') = true
        · simp only [Bool.and_eq_true] at h1
          obtain ⟨Q, hQ⟩ := allScalar_eq rest' h1.2
          exact Or.inr ⟨[a], [j], Q, by simp [hQ], by simp, by simp, by simp [h1.1], by simp⟩
        · rw [if_neg h1] at h
          by_cases h2 : allScalar (j :: rest') = true
          · exact Or.inl h2
          · rw [if_neg h2] at h; cases h

/-- Linear-style tuples: leading scalars `P`, extended indices, trailing scalars `Q`. -/
inductive LinShape : List Idx → Prop
  | scalars (P : List Int) : LinShape (P.map .int)
  | range (P : List Int) (r : Idx) (Q : List Int) :
      r.isRange = true → LinShape (P.map .int ++ r :: Q.map .int)
  | slices (P : List Int) (as : List Ax) (us : List Idx) (Q : List Int) :
      as ≠ [] → us.length ≤ 1 → (∀ u ∈ us, u.isUnitRange = true) → 2 ≤ as.length + us.length →
      LinShape (P.map .int ++ (as.map .slice ++ us ++ Q.map .int))

theorem LinShape.cons_int (n : Int) {I : List Idx} (h : LinShape I) : LinShape (.int n :: I) := by
  cases h with
  | scalars P => exact LinShape.scalars (n :: P)
  | range P r Q hr => simpa using LinShape.range (n :: P) r Q hr
  | slices P as us Q h1 h2 h3 h4 => simpa using LinShape.slices (n :: P) as us Q h1 h2 h3 h4

theorem vi_shape : ∀ (I : List Idx), viewindexing I = .linear → LinShape I
  | [], _ => LinShape.scalars []
  | i :: rest, h => by
      cases i with
      | int n =>
          simp [viewindexing] at h
          exact (vi_shape rest h).cons_int n
      | slice a =>
          rcases slice_shape rest a h with h1 | ⟨as, us, Q, he, h1, h2, h3, h4⟩
          · obtain ⟨Q, hQ⟩ := allScalar_eq rest h1
            rw [hQ]; simpa using LinShape.range [] (.slice a) Q rfl
          · rw [he]; simpa using LinShape.slices [] as us Q h1 h2 h3 h4
      | _ =>
          simp only [viewindexing] at h
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true] at hc
            obtain ⟨Q, hQ⟩ := allScalar_eq rest hc.2
            rw [hQ]; simpa using LinShape.range [] _ Q hc.1
          · cases h

/-! ### First values and `compute_linindex` -/

/-- `first(i)` of a scalar or range index. -/
def fv : Idx → Int
  | .int n => n
  | .slice a => a.lo
  | .ident a => a.lo
  | .oneto _ => 1
  | .unit a => a.lo
  | .step s _ _ => s
  | _ => 0

theorem idxFirst_fv (i : Idx) (h : i.isScalar = true ∨ i.isRange = true) : idxFirst i = .ok (fv i) := by
  cases i <;> simp [Idx.isScalar, Idx.isRange] at h <;> rfl

theorem fillToLength_eq (t : List Ax) (v : Ax) (n : Nat) (h : t.length = n) :
    fillToLength t v n = .ok t := by
  subst h; simp [fillToLength]

theorem axesLen_cons (a : Ax) (as : List Ax) : axesLen (a :: as) = a.len * axesLen as := by
  simp [axesLen]

theorem linOff_cons (a : Ax) (as : List Ax) (p : Int) (ps : List Int) :
    linOff (a :: as) (p :: ps) = (p - a.lo) + a.len * linOff as ps := rfl

/-- Lines 491-501: with running sum `f` and stride product `s`, `compute_linindex`
adds `(first(I[k]) - first(IP[k])) * s * prod(length(IP[1:k-1]))` over all
indices (modulo `2^64`), and propagates the first failing `Int(first(I[k]))`. -/
theorem linindexRec_eq : ∀ (I : List Idx) (ip : List Ax) (f s : Int), ip.length = I.length →
    computeLinindexRec (wrap64 f) (wrap64 s) ip I =
      (I.mapM idxFirst).map (fun fs => wrap64 (f + s * linOff ip fs))
  | [], ip, f, s, hl => by
      cases ip with
      | nil => simp [computeLinindexRec, linOff, Except.map]
      | cons _ _ => simp at hl
  | [i], ip, f, s, hl => by
      cases ip with
      | nil => simp at hl
      | cons a ip' =>
        cases ip' with
        | cons _ _ => simp at hl
        | nil =>
          simp only [computeLinindexRec, List.mapM_cons, List.mapM_nil]
          cases hi : idxFirst i with
          | error e => rfl
          | ok fi =>
            simp only [sbind_ok, axHead, Except.map, spure]
            simp only [iadd, imul, isub, w_add_l, w_add_r, w_mul_l, w_mul_r, w_sub_l, w_sub_r,
              linOff_cons]
            simp only [linOff]
            congr 2
            grind
  | i :: j :: rest, ip, f, s, hl => by
      cases ip with
      | nil => simp at hl
      | cons a ip' =>
        have hl' : ip'.length = (j :: rest).length := by simpa using hl
        rw [computeLinindexRec, List.mapM_cons]
        cases hi : idxFirst i with
        | error e => rfl
        | ok fi =>
          simp only [sbind_ok, axHead, List.tail_cons]
          have e1 : iadd (wrap64 f) (imul (isub fi a.lo) (wrap64 s)) = wrap64 (f + (fi - a.lo) * s) := by
            simp only [iadd, imul, isub, w_add_l, w_add_r, w_mul_l, w_mul_r]
          have e2 : imul (wrap64 s) a.len = wrap64 (s * a.len) := imul_w s a.len
          rw [e1, e2, linindexRec_eq (j :: rest) ip' _ _ hl']
          cases hr : (j :: rest).mapM idxFirst with
          | error e => rfl
          | ok fs =>
            show Except.ok (wrap64 (f + (fi - a.lo) * s + s * a.len * linOff ip' fs)) =
              Except.ok (wrap64 (f + s * linOff (a :: ip') (fi :: fs)))
            rw [linOff_cons]
            congr 2
            grind

theorem mapM_first_ok : ∀ (I : List Idx), (∀ i ∈ I, i.isScalar = true ∨ i.isRange = true) →
    I.mapM idxFirst = .ok (I.map fv)
  | [], _ => rfl
  | i :: I, h => by
      simp only [List.mapM_cons, idxFirst_fv i (h i (by simp)), sbind_ok,
        mapM_first_ok I (fun x hx => h x (by simp [hx])), spure, List.map_cons]

/-- `first(LinearIndices(A)) + offset` is `LinearIndices(A)[pos...]`. -/
theorem firstLinear_linOff (axs : List Ax) (ps : List Int) (h : axs.length = ps.length) :
    firstLinear axs + linOff axs ps = linearIndex axs ps := by
  match axs, ps, h with
  | [], [], _ => simp [firstLinear, linOff, linearIndex]
  | [a], [p], _ => simp [firstLinear, linOff, linearIndex]; omega
  | a :: b :: as, p :: q :: ps, _ => simp [firstLinear, linearIndex]

theorem mapM_length : ∀ (I : List Idx) (fs : List Int), I.mapM idxFirst = .ok fs → fs.length = I.length
  | [], fs, h => by simp [List.mapM_nil] at h; cases h; rfl
  | i :: I, fs, h => by
      simp only [List.mapM_cons] at h
      cases hi : idxFirst i with
      | error e => rw [hi] at h; cases h
      | ok x =>
        rw [hi, sbind_ok] at h
        cases hr : I.mapM idxFirst with
        | error e => rw [hr] at h; cases h
        | ok xs =>
          rw [hr, sbind_ok, spure] at h
          cases h
          simp [mapM_length I xs hr]

theorem computeLinindex_eq (p : Par α) (I : List Idx) (hl : p.axes.length = I.length)
    (hF : -2^63 ≤ firstLinear p.axes ∧ firstLinear p.axes < 2^63) :
    computeLinindex p I = (I.mapM idxFirst).map (fun fs => wrap64 (linearIndex p.axes fs) ) := by
  unfold computeLinindex
  rw [fillToLength_eq _ _ _ hl, sbind_ok]
  have h := linindexRec_eq I p.axes (firstLinear p.axes) 1 hl
  rw [w_id hF.1 hF.2, w_one] at h
  rw [h]
  cases hm : I.mapM idxFirst with
  | error e => rfl
  | ok fs =>
    have hlen : p.axes.length = fs.length := by
      rw [hl]; exact (mapM_length I fs hm).symm
    simp [Except.map, ← firstLinear_linOff p.axes fs hlen]

/-! ### `compute_stride1` -/

theorem stride_all_scalar (s : Int) (ip : List Ax) : ∀ (I : List Idx), allScalar I = true →
    computeStride1Rec s ip I = .ok s
  | [], _ => by simp [computeStride1Rec]
  | i :: I, h => by
      unfold computeStride1Rec
      rw [if_pos h]

theorem allScalar_append (l1 l2 : List Idx) : allScalar (l1 ++ l2) = (allScalar l1 && allScalar l2) := by
  simp [allScalar, List.all_append]

theorem stride_prefix : ∀ (P : List Int) (axP ip : List Ax) (C : List Idx) (s : Int),
    axP.length = P.length → allScalar C = false →
    computeStride1Rec (wrap64 s) (axP ++ ip) (P.map .int ++ C) =
      computeStride1Rec (wrap64 (s * axesLen axP)) ip C
  | [], [], ip, C, s, _, _ => by simp [axesLen]
  | n :: P, a :: axP, ip, C, s, hl, hC => by
      have hns : allScalar (Idx.int n :: (P.map .int ++ C)) = false := by
        simp [allScalar_cons, Idx.isScalar, allScalar_append, allScalar_ints, hC]
      simp only [List.map_cons, List.cons_append]
      simp only [computeStride1Rec, hns, Bool.false_eq_true, ite_false]
      rw [imul_w, stride_prefix P axP ip C (s * a.len) (by simpa using hl) hC, axesLen_cons,
        Int.mul_assoc]
  | [], _ :: _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _ => by simp at hl

theorem stride_head (t : Idx) (rest : List Idx) (ip : List Ax) (s : Int) (ht : t.isRange = true) :
    computeStride1Rec (wrap64 s) ip (t :: rest) = .ok (wrap64 (s * strideOf t)) := by
  cases t <;> simp [Idx.isRange] at ht <;>
    simp [computeStride1Rec, allScalar_cons, Idx.isScalar, strideOf, idxStep, Idx.isRange, imul_w]

/-! ### Positions -/

theorem specPos_ints : ∀ (Q : List Int), specPos (Q.map .int) [] = some Q
  | [] => rfl
  | n :: Q => by
      simp [specPos, idxRank, idxAxes, idxAt, specPos_ints Q]

theorem specPos_prefix : ∀ (P : List Int) (R : List Idx) (J : List Int),
    specPos (P.map .int ++ R) J = (specPos R J).map (P ++ ·)
  | [], R, J => by simp
  | n :: P, R, J => by
      simp only [List.map_cons, List.cons_append]
      rw [specPos]
      simp [idxRank, idxAxes, idxAt, specPos_prefix P R J, Option.map_map]
      cases specPos R J <;> rfl

/-- Value of a range index at a subscript: `first + step * (j - first(axes1))`. -/
def rangeVal (c : Idx) (j : Int) : Int := fv c + strideOf c * (j - (axes1Idx c).lo)

theorem idxRank_range (c : Idx) (h : c.isRange = true) : idxRank c = 1 := by
  cases c <;> simp [Idx.isRange] at h <;> rfl

theorem idxAxes_range (c : Idx) (h : c.isRange = true) : idxAxes c = [axes1Idx c] := by
  cases c <;> simp [Idx.isRange] at h <;> rfl

theorem idxAt_range (c : Idx) (h : c.isRange = true) (j : Int)
    (hj : (axes1Idx c).lo ≤ j ∧ j ≤ (axes1Idx c).hi) : idxAt c [j] = some [rangeVal c j] := by
  cases c <;> simp [Idx.isRange] at h
  all_goals simp [axes1Idx, idxAxes, oneAx] at hj
  all_goals simp [idxAt, rangeVal, fv, strideOf, idxStep, axes1Idx, idxAxes, oneAx, Ax.mem, hj]
  all_goals first | omega | (simp [Int.mul_comm]) | skip

/-- Parent positions of an extended core `C` at subscripts `J`. -/
def corePos : List Idx → List Int → List Int
  | c :: C, j :: J => rangeVal c j :: corePos C J
  | _, _ => []

theorem specPos_core : ∀ (C : List Idx) (Q : List Int) (J : List Int), (∀ c ∈ C, c.isRange = true) →
    inAxes (C.map axes1Idx) J → specPos (C ++ Q.map .int) J = some (corePos C J ++ Q)
  | [], Q, [], _, _ => by simpa [corePos] using specPos_ints Q
  | [], _, _ :: _, _, hJ => hJ.elim
  | c :: C, Q, [], _, hJ => hJ.elim
  | c :: C, Q, j :: J, hC, hJ => by
      have hc := hC c (by simp)
      obtain ⟨h1, h2, h3⟩ := hJ
      rw [List.cons_append, specPos, idxRank_range c hc]
      simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]
      rw [idxAt_range c hc j ⟨h1, h2⟩, specPos_core C Q J (fun x hx => hC x (by simp [hx])) h3]
      simp [corePos]

theorem viewAxes_cons (i : Idx) (I : List Idx) : viewAxes (i :: I) = idxAxes i ++ viewAxes I := by
  simp [viewAxes]

theorem viewAxes_ints (Q : List Int) (R : List Idx) : viewAxes (Q.map .int ++ R) = viewAxes R := by
  induction Q with
  | nil => rfl
  | cons n Q ih => simp only [List.map_cons, List.cons_append, viewAxes_cons]; simpa [idxAxes] using ih

theorem viewAxes_core (C : List Idx) (Q : List Int) (hC : ∀ c ∈ C, c.isRange = true) :
    viewAxes (C ++ Q.map .int) = C.map axes1Idx := by
  induction C with
  | nil =>
    induction Q with
    | nil => rfl
    | cons n Q ih => simpa [viewAxes_cons, idxAxes] using ih
  | cons c C ih =>
    rw [List.cons_append, viewAxes_cons, idxAxes_range c (hC c (by simp)),
      ih (fun x hx => hC x (by simp [hx]))]
    rfl

/-! ### Offsets -/

theorem linOff_append : ∀ (as1 : List Ax) (ps1 : List Int) (as2 : List Ax) (ps2 : List Int),
    as1.length = ps1.length →
    linOff (as1 ++ as2) (ps1 ++ ps2) = linOff as1 ps1 + axesLen as1 * linOff as2 ps2
  | [], [], as2, ps2, _ => by simp [linOff, axesLen]
  | a :: as1, p :: ps1, as2, ps2, h => by
      simp only [List.cons_append, linOff_cons, axesLen_cons]
      rw [linOff_append as1 ps1 as2 ps2 (by simpa using h)]
      grind
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

/-- All but the last core axis have the length of the view axis above them. -/
def LensOK : List Ax → List Idx → Prop
  | [], [] => True
  | [_], [_] => True
  | a :: b :: as, c :: d :: cs => a.len = (axes1Idx c).len ∧ LensOK (b :: as) (d :: cs)
  | _, _ => False

theorem core_diff (σ : Int) : ∀ (C : List Idx) (axC : List Ax) (J : List Int),
    LensOK axC C → (∀ c ∈ C, strideOf c = σ) → J.length = C.length →
    linOff axC (corePos C J) - linOff axC (C.map fv) = σ * linOff (C.map axes1Idx) J
  | [], axC, J, hL, _, hl => by
      match axC, J with
      | [], [] => simp [linOff, corePos]
      | [], _ :: _ => simp at hl
      | _ :: _, _ => simp [LensOK] at hL
  | [c], axC, J, hL, hs, hl => by
      match axC, J with
      | [a], [j] =>
          have h1 := hs c (by simp)
          simp [corePos, linOff, rangeVal, h1]
          omega
      | [], _ => simp [LensOK] at hL
      | _ :: _ :: _, _ => simp [LensOK] at hL
      | [_], [] => simp at hl
      | [_], _ :: _ :: _ => simp at hl
  | c :: d :: cs, axC, J, hL, hs, hl => by
      match axC, J with
      | a :: b :: as, j :: k :: J' =>
          obtain ⟨hlen, hL'⟩ := hL
          have ih := core_diff σ (d :: cs) (b :: as) (k :: J') hL'
            (fun x hx => hs x (List.mem_cons_of_mem _ hx)) (by simpa using hl)
          have hr : rangeVal c j = fv c + σ * (j - (axes1Idx c).lo) := by
            simp [rangeVal, hs c (by simp)]
          simp only [corePos, List.map_cons, linOff_cons] at ih ⊢
          rw [hlen, hr]
          grind
      | [], _ => simp [LensOK] at hL
      | [_], _ => simp [LensOK] at hL
      | _ :: _ :: _, [] => simp at hl
      | _ :: _ :: _, [_] => simp at hl

/-! ### Bounds -/

theorem inAxes_length : ∀ {as : List Ax} {ps : List Int}, inAxes as ps → as.length = ps.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [inAxes_length h.2.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem inAxes_append : ∀ {a1 : List Ax} {p1 : List Int} {a2 : List Ax} {p2 : List Int},
    inAxes a1 p1 → inAxes a2 p2 → inAxes (a1 ++ a2) (p1 ++ p2)
  | [], [], _, _, _, h2 => by simpa using h2
  | _ :: _, _ :: _, _, _, h1, h2 => ⟨h1.1, h1.2.1, inAxes_append h1.2.2 h2⟩
  | [], _ :: _, _, _, h1, _ => h1.elim
  | _ :: _, [], _, _, h1, _ => h1.elim

theorem IdxsOK_append : ∀ (I1 I2 : List Idx) (axs : List Ax), IdxsOK axs (I1 ++ I2) →
    ∃ a1 a2, axs = a1 ++ a2 ∧ a1.length = I1.length ∧ IdxsOK a1 I1 ∧ IdxsOK a2 I2
  | [], I2, axs, h => ⟨[], axs, rfl, rfl, trivial, h⟩
  | i :: I1, I2, [], h => h.elim
  | i :: I1, I2, a :: axs, h => by
      obtain ⟨a1, a2, he, hl, h1, h2⟩ := IdxsOK_append I1 I2 axs h.2
      exact ⟨a :: a1, a2, by simp [he], by simp [hl], ⟨h.1, h1⟩, h2⟩

theorem IdxsOK_ints : ∀ (axs : List Ax) (P : List Int), IdxsOK axs (P.map .int) → inAxes axs P
  | [], [], _ => trivial
  | a :: axs, n :: P, h => ⟨h.1.1, h.1.2, IdxsOK_ints axs P h.2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem Ax.len_eq (a : Ax) (h : a.lo ≤ a.hi + 1) : a.len = a.hi - a.lo + 1 := by
  unfold Ax.len; split <;> omega

theorem rangeVal_in (ax : Ax) (c : Idx) (hc : c.isRange = true) (hok : IdxOK ax c) (j : Int)
    (hj : (axes1Idx c).lo ≤ j ∧ j ≤ (axes1Idx c).hi) :
    ax.lo ≤ rangeVal c j ∧ rangeVal c j ≤ ax.hi := by
  cases c <;> simp [Idx.isRange] at hc
  · -- slice
    simp [IdxOK] at hok; subst hok
    simp [axes1Idx, idxAxes] at hj
    simp [rangeVal, fv, strideOf, axes1Idx, idxAxes]; omega
  · -- oneto
    simp [IdxOK] at hok
    simp [axes1Idx, idxAxes, oneAx] at hj
    have := hok.2 (by omega)
    simp [rangeVal, fv, strideOf, idxStep, axes1Idx, idxAxes, oneAx]; omega
  · -- unit
    rename_i a
    simp [IdxOK] at hok
    simp [axes1Idx, idxAxes, oneAx] at hj
    have hlen := Ax.len_eq a hok.1
    have := hok.2 (by omega)
    simp [rangeVal, fv, strideOf, idxStep, axes1Idx, idxAxes, oneAx]; omega
  · -- ident
    simp [IdxOK] at hok
    simp [axes1Idx, idxAxes] at hj
    have := hok.2 (by omega)
    simp [rangeVal, fv, strideOf, idxStep, axes1Idx, idxAxes]; omega
  · -- step
    rename_i s0 st n
    simp [IdxOK] at hok
    simp [axes1Idx, idxAxes, oneAx] at hj
    obtain ⟨hst, hn, hb⟩ := hok
    obtain ⟨b1, b2, b3, b4⟩ := hb (by omega)
    simp [rangeVal, fv, strideOf, idxStep, axes1Idx, idxAxes, oneAx]
    rcases Int.lt_or_gt_of_ne hst with hneg | hpos
    · have m1 : st * (n - 1) ≤ st * (j - 1) :=
        Int.mul_le_mul_of_nonpos_left (by omega) (by omega)
      have m2 : st * (j - 1) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
      rw [Int.mul_comm (n - 1) st] at b3 b4
      omega
    · have m1 : st * (j - 1) ≤ st * (n - 1) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have m2 : 0 ≤ st * (j - 1) := Int.mul_nonneg (by omega) (by omega)
      rw [Int.mul_comm (n - 1) st] at b3 b4
      omega

theorem corePos_in : ∀ (axC : List Ax) (C : List Idx) (J : List Int), IdxsOK axC C →
    (∀ c ∈ C, c.isRange = true) → inAxes (C.map axes1Idx) J → inAxes axC (corePos C J)
  | [], [], [], _, _, _ => trivial
  | ax :: axC, c :: C, j :: J, hok, hC, hJ => by
      have h := rangeVal_in ax c (hC c (by simp)) hok.1 j ⟨hJ.1, hJ.2.1⟩
      exact ⟨h.1, h.2, corePos_in axC C J hok.2 (fun x hx => hC x (List.mem_cons_of_mem _ hx)) hJ.2.2⟩
  | [], _ :: _, _, hok, _, _ => hok.elim
  | _ :: _, [], _, hok, _, _ => hok.elim
  | _ :: _, _ :: _, [], _, _, hJ => hJ.elim
  | [], [], _ :: _, _, _, hJ => hJ.elim

theorem linOff_bounds : ∀ (axs : List Ax) (ps : List Int), inAxes axs ps →
    0 ≤ linOff axs ps ∧ linOff axs ps < axesLen axs
  | [], [], _ => by simp [linOff, axesLen]
  | a :: axs, p :: ps, h => by
      obtain ⟨h1, h2, h3⟩ := h
      have ih := linOff_bounds axs ps h3
      have hl := Ax.len_eq a (by omega)
      rw [linOff_cons, axesLen_cons]
      have m0 : 0 ≤ a.len * linOff axs ps := Int.mul_nonneg (by omega) ih.1
      have m1 : a.len * linOff axs ps ≤ a.len * (axesLen axs - 1) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have m2 : a.len * (axesLen axs - 1) = a.len * axesLen axs - a.len := by
        rw [Int.mul_sub, Int.mul_one]
      omega
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem linearIndex_mem (axs : List Ax) (J : List Int) (h : inAxes axs J) :
    (linearAxis axs).mem (linearIndex axs J) = true := by
  match axs, J, h with
  | [a], [j], h => simp [linearAxis, linearIndex, Ax.mem, h.1, h.2.1]
  | [], [], _ => simp [linearAxis, linearIndex, Ax.mem, linOff, axesLen]
  | a :: b :: as, j :: k :: J, h =>
      have hb := linOff_bounds (a :: b :: as) (j :: k :: J) h
      show (decide (1 ≤ 1 + linOff (a :: b :: as) (j :: k :: J)) &&
        decide (1 + linOff (a :: b :: as) (j :: k :: J) ≤ axesLen (a :: b :: as))) = true
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega

theorem linearIndex_sub_lo (axs : List Ax) (J : List Int) (h : axs.length = J.length) :
    linearIndex axs J - (linearAxis axs).lo = linOff axs J := by
  match axs, J, h with
  | [a], [j], _ => simp [linearAxis, linearIndex, linOff]
  | [], [], _ => simp [linearAxis, linearIndex, linOff]
  | a :: b :: as, j :: k :: J, _ => simp [linearAxis, linearIndex]; omega

theorem linearIndex_range (p : Par α) (hp : PValid p) (pos : List Int) (h : inAxes p.axes pos) :
    -2^63 ≤ linearIndex p.axes pos ∧ linearIndex p.axes pos < 2^63 := by
  obtain ⟨_, hax, hlen, _⟩ := hp
  match hx : p.axes, pos, h with
  | [a], [x], h =>
      have := hax a (by rw [hx]; simp)
      obtain ⟨h1, h2, _⟩ := h
      simp only [linearIndex]; unfold AxOK at this; omega
  | [], [], _ => simp [linearIndex, linOff]
  | a :: b :: as, x :: y :: ps, h =>
      have hb := linOff_bounds (a :: b :: as) (x :: y :: ps) h
      rw [hx] at hlen
      simp only [linearIndex]; omega

/-! ### Assembly -/

/-- `_reindexlinear` from the stored fields. -/
def reindexLinearRaw (I : List Idx) (o s i : Int) : Int :=
  if contiguous I then iadd o i else iadd o (imul s i)

theorem reindexLinear_raw (V : Sub α) (i : Int) :
    reindexLinear V i = reindexLinearRaw V.indices V.offset1 V.stride1 i := rfl

theorem assemble (p : Par α) (hp : PValid p) (P : List Int) (C : List Idx) (Q : List Int)
    (axP axC axQ : List Ax) (hax : p.axes = axP ++ (axC ++ axQ)) (hlP : axP.length = P.length)
    (hP : inAxes axP P) (hQ : inAxes axQ Q) (hOK : IdxsOK axC C)
    (hC : ∀ c ∈ C, c.isRange = true) (σT : Int) (hσ : ∀ c ∈ C, strideOf c = σT) (hL : LensOK axC C)
    (hcontig : contiguous (P.map .int ++ (C ++ Q.map .int)) = true → axesLen axP * σT = 1)
    (J : List Int) (hJ : inAxes (C.map axes1Idx) J) :
    ∃ pos, specPos (P.map .int ++ (C ++ Q.map .int)) J = some pos ∧ inAxes p.axes pos ∧
      reindexLinearRaw (P.map .int ++ (C ++ Q.map .int))
        (wrap64 (linearIndex p.axes (P ++ (C.map fv ++ Q)) -
          axesLen axP * σT * (linearAxis (C.map axes1Idx)).lo))
        (wrap64 (axesLen axP * σT)) (linearIndex (C.map axes1Idx) J) = linearIndex p.axes pos := by
  have hcl : axC.length = C.length := IdxsOK.length hOK
  have hJl : (C.map axes1Idx).length = J.length := inAxes_length hJ
  have hcore := corePos_in axC C J hOK hC hJ
  have hcpl : (corePos C J).length = C.length := inAxes_length hcore ▸ hcl.symm ▸ rfl
  refine ⟨P ++ (corePos C J ++ Q), ?_, ?_, ?_⟩
  · rw [specPos_prefix, specPos_core C Q J hC hJ]; rfl
  · rw [hax]; exact inAxes_append hP (inAxes_append hcore hQ)
  · have hpos : inAxes p.axes (P ++ (corePos C J ++ Q)) := by
      rw [hax]; exact inAxes_append hP (inAxes_append hcore hQ)
    have hr := linearIndex_range p hp _ hpos
    have hlen1 : p.axes.length = (P ++ (corePos C J ++ Q)).length := inAxes_length hpos
    have hlen2 : p.axes.length = (P ++ (C.map fv ++ Q)).length := by
      rw [hlen1]; simp [hcpl]
    have hQl : axQ.length = Q.length := inAxes_length hQ
    -- linear index difference
    have hdiff : linearIndex p.axes (P ++ (corePos C J ++ Q)) =
        linearIndex p.axes (P ++ (C.map fv ++ Q)) +
          axesLen axP * σT * (linearIndex (C.map axes1Idx) J - (linearAxis (C.map axes1Idx)).lo) := by
      rw [← firstLinear_linOff _ _ hlen1, ← firstLinear_linOff _ _ hlen2, hax,
        linOff_append axP P _ _ hlP, linOff_append axP P _ _ hlP,
        linOff_append axC _ axQ Q (by rw [hcl, hcpl]), linOff_append axC _ axQ Q (by simp [hcl]),
        linearIndex_sub_lo _ _ hJl]
      have hd := core_diff σT C axC J hL hσ (by rw [← hJl]; simp)
      have : linOff axC (corePos C J) = linOff axC (C.map fv) + σT * linOff (C.map axes1Idx) J := by
        omega
      rw [this]
      grind
    unfold reindexLinearRaw
    split
    · rename_i hc
      have h1 := hcontig hc
      rw [iadd_w, h1]
      rw [h1] at hdiff
      have e : linearIndex p.axes (P ++ (C.map fv ++ Q)) - 1 * (linearAxis (C.map axes1Idx)).lo +
          linearIndex (C.map axes1Idx) J = linearIndex p.axes (P ++ (corePos C J ++ Q)) := by
        rw [hdiff]; omega
      rw [e]
      exact w_id hr.1 hr.2
    · rw [imul_w, iadd_ww, hdiff]
      rw [show linearIndex p.axes (P ++ (C.map fv ++ Q)) -
            axesLen axP * σT * (linearAxis (C.map axes1Idx)).lo +
            axesLen axP * σT * linearIndex (C.map axes1Idx) J =
          linearIndex p.axes (P ++ (C.map fv ++ Q)) +
            axesLen axP * σT * (linearIndex (C.map axes1Idx) J - (linearAxis (C.map axes1Idx)).lo) by
        rw [Int.mul_sub]; omega]
      rw [← hdiff]
      exact w_id hr.1 hr.2

/-! ### Offsets per shape -/

theorem computeOffset1_gen (p : Par α) (s : Int) (I : List Idx)
    (h : ¬ ∃ a r, p.axes = [a] ∧ I = [r] ∧ r.isRange = true) :
    computeOffset1 p s I = computeOffset1Dims p s (findExtendedDims 1 I) (findExtendedInds I) I := by
  unfold computeOffset1
  cases hax : p.axes with
  | nil => rfl
  | cons a t =>
    cases t with
    | cons _ _ => rfl
    | nil =>
      cases I with
      | nil => rfl
      | cons r t2 =>
        cases t2 with
        | cons _ _ => rfl
        | nil =>
          by_cases hr : r.isRange = true
          · exact absurd ⟨a, r, hax, rfl, hr⟩ h
          · simp [hr]

theorem offsetDims_many (p : Par α) (s : Int) (dims : List Int) (inds : List Idx) (I : List Idx)
    (h : inds.length ≠ 1) :
    computeOffset1Dims p s dims inds I = (computeLinindex p I).bind (fun li => .ok (isub li s)) := by
  unfold computeOffset1Dims
  split
  · simp at h
  · simp at h
  · rfl

theorem findExtendedInds_ints (P : List Int) (R : List Idx) :
    findExtendedInds (P.map .int ++ R) = findExtendedInds R := by
  induction P with
  | nil => rfl
  | cons n P ih => simpa [findExtendedInds] using ih

theorem findExtendedInds_core : ∀ (C : List Idx) (Q : List Int), (∀ c ∈ C, c.isScalar = false) →
    findExtendedInds (C ++ Q.map .int) = C
  | [], Q, _ => by simpa [findExtendedInds] using findExtendedInds_ints Q []
  | c :: C, Q, h => by
      have hc := h c (by simp)
      have ih := findExtendedInds_core C Q (fun x hx => h x (List.mem_cons_of_mem _ hx))
      cases c <;> simp [Idx.isScalar] at hc <;> simp [findExtendedInds, ih]

theorem findExtendedDims_ints (P : List Int) : ∀ (d : Int) (R : List Idx),
    findExtendedDims d (P.map .int ++ R) = findExtendedDims (d + P.length) R := by
  induction P with
  | nil => intro d R; simp
  | cons n P ih => intro d R; simp [findExtendedDims, ih]; congr 1; omega

theorem findExtendedDims_one (d : Int) (r : Idx) (Q : List Int) (hr : r.isScalar = false) :
    findExtendedDims d (r :: Q.map .int) = [d] := by
  have : ∀ (e : Int), findExtendedDims e (Q.map .int) = [] := by
    intro e; simpa [findExtendedDims] using findExtendedDims_ints Q e []
  cases r <;> simp [Idx.isScalar] at hr <;> simp [findExtendedDims, this]

theorem isRange_not_scalar (c : Idx) (h : c.isRange = true) : c.isScalar = false := by
  cases c <;> simp [Idx.isRange, Idx.isScalar] at h ⊢

theorem unitRange_range (c : Idx) (h : c.isUnitRange = true) : c.isRange = true := by
  cases c <;> simp [Idx.isUnitRange, Idx.isRange] at h ⊢

theorem unitRange_stride (c : Idx) (h : c.isUnitRange = true) : strideOf c = 1 := by
  cases c <;> simp [Idx.isUnitRange] at h <;> rfl

theorem firstLinear_range (p : Par α) (hp : PValid p) :
    -2^63 ≤ firstLinear p.axes ∧ firstLinear p.axes < 2^63 := by
  obtain ⟨_, hax, _, _⟩ := hp
  match hx : p.axes with
  | [a] =>
      have := hax a (by rw [hx]; simp)
      simp [firstLinear]; unfold AxOK at this; omega
  | [] => simp [firstLinear]
  | _ :: _ :: _ => simp [firstLinear]

theorem sr_ok_ints (P : List Int) (R : List Idx) (hR : ∀ c ∈ R, c.isScalar = true ∨ c.isRange = true) :
    ∀ i ∈ P.map .int ++ R, i.isScalar = true ∨ i.isRange = true := by
  intro i hi
  rcases List.mem_append.mp hi with h | h
  · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h; simp [Idx.isScalar]
  · exact hR i h

theorem LensOK_short : ∀ {axC : List Ax} {C : List Idx}, axC.length = C.length → C.length ≤ 1 →
    LensOK axC C
  | [], [], _, _ => trivial
  | [_], [_], _, _ => trivial
  | _, _ :: _ :: _, _, h => by simp at h
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | _ :: _ :: _, [_], h, _ => by simp at h

theorem IdxsOK_slices : ∀ (as : List Ax) (us : List Idx) (axC : List Ax),
    IdxsOK axC (as.map .slice ++ us) → us.length ≤ 1 → LensOK axC (as.map .slice ++ us)
  | [], us, axC, h, hl => LensOK_short (IdxsOK.length h) (by simpa using hl)
  | a :: as, us, axC, h, hl => by
      simp only [List.map_cons, List.cons_append] at h ⊢
      match axC, h with
      | [], h => simp [IdxsOK] at h
      | ax :: axC', h =>
        have hrest := IdxsOK_slices as us axC' h.2 hl
        have hsl : a = ax := h.1
        have hlen := IdxsOK.length h.2
        revert hrest hlen
        cases (as.map .slice ++ us) with
        | nil =>
          intro _ hlen
          cases axC' with
          | nil => trivial
          | cons _ _ => simp at hlen
        | cons d ds =>
          intro hrest hlen
          cases axC' with
          | nil => simp at hlen
          | cons b axC'' => exact ⟨by simp [hsl, axes1Idx, idxAxes], hrest⟩

theorem map_fv_ints (P : List Int) : (P.map .int).map fv = P := by
  simp [List.map_map, Function.comp_def, fv]

theorem map_fv_shape (P : List Int) (C : List Idx) (Q : List Int) :
    (P.map Idx.int ++ (C ++ Q.map Idx.int)).map fv = P ++ (C.map fv ++ Q) := by
  simp only [List.map_append, map_fv_ints]

theorem contig_shape (P : List Int) (C : List Idx) (Q : List Int) (c : Idx) (C' : List Idx)
    (hC : C = c :: C') (hc : c.isScalar = false)
    (h : contiguous (P.map .int ++ (C ++ Q.map .int)) = true) : P = [] ∧ c.isUnitRange = true := by
  subst hC
  cases P with
  | nil =>
    refine ⟨rfl, ?_⟩
    simp only [List.map_nil, List.nil_append, List.cons_append, contiguous] at h
    rw [allScalar_cons, hc] at h
    simpa using h
  | cons n P' =>
    exfalso
    simp only [List.map_cons, List.cons_append, contiguous] at h
    rw [allScalar_cons] at h
    simp only [Idx.isUnitRange, Idx.isScalar, Bool.false_or, Bool.true_and] at h
    rw [allScalar_append, allScalar_cons, hc] at h
    simp at h

theorem axisAt_mid (axP : List Ax) (ax : Ax) (rest : List Ax) (P : List Int) (hl : axP.length = P.length) :
    axisAt (axP ++ (ax :: rest)) (1 + (P.length : Int)) = ax := by
  unfold axisAt
  rw [show (1 + (P.length : Int) - 1).toNat = axP.length by omega]
  simp

theorem stride_shape (p : Par α) (P : List Int) (C : List Idx) (Q : List Int) (axP rest : List Ax)
    (hax : p.axes = axP ++ rest) (hlP : axP.length = P.length)
    (hl : p.axes.length = (P.map Idx.int ++ (C ++ Q.map Idx.int)).length)
    (c : Idx) (C' : List Idx) (hC : C = c :: C') (hc : c.isRange = true) :
    computeStride1 p (P.map .int ++ (C ++ Q.map .int)) = .ok (wrap64 (axesLen axP * strideOf c)) := by
  unfold computeStride1
  rw [fillToLength_eq _ _ _ hl, sbind_ok, hax]
  have hns : allScalar (C ++ Q.map .int) = false := by
    rw [hC, List.cons_append, allScalar_cons, isRange_not_scalar c hc]; rfl
  have h1 := stride_prefix P axP rest (C ++ Q.map .int) 1 hlP hns
  rw [w_one] at h1
  rw [h1, hC, List.cons_append, stride_head c _ rest _ hc, Int.one_mul]

/-! ### The invariant -/

theorem fast_layout (p : Par α) (I : List Idx) (hp : PValid p) (hI : IdxsOK p.axes I)
    (hv : viewindexing I = .linear) :
    ∃ o s, computeLinearLayout p I = .ok (o, s) ∧
      ∀ J, inAxes (viewAxes I) J → ∃ pos, specPos I J = some pos ∧ inAxes p.axes pos ∧
        reindexLinearRaw I o s (linearIndex (viewAxes I) J) = linearIndex p.axes pos := by
  have hl : p.axes.length = I.length := IdxsOK.length hI
  have hF := firstLinear_range p hp
  rcases vi_shape I hv with ⟨P⟩ | ⟨P, r, Q, hr⟩ | ⟨P, as, us, Q, h1, h2, h3, h4⟩
  · -- all scalars
    have hli := computeLinindex_eq p (P.map .int) hl hF
    have hm : (P.map .int).mapM idxFirst = .ok P := by
      rw [mapM_first_ok _ (by simpa using sr_ok_ints P [] (by simp))]
      simp [List.map_map, Function.comp_def, fv]
    rw [hm] at hli
    have hst : computeStride1 p (P.map .int) = .ok 1 := by
      unfold computeStride1; rw [fillToLength_eq _ _ _ hl, sbind_ok]
      exact stride_all_scalar 1 _ _ (allScalar_ints P)
    have hoff : computeOffset1 p 1 (P.map .int) = .ok (isub (wrap64 (linearIndex p.axes P)) 1) := by
      rw [computeOffset1_gen]
      · have h0 : findExtendedInds (P.map .int) = [] := by simpa [findExtendedInds] using findExtendedInds_ints P []
        rw [h0, offsetDims_many _ _ _ _ _ (by simp), hli]
        simp [Except.map, List.map_map]
        rfl
      · rintro ⟨a, r, _, hI1, hr1⟩
        cases P with
        | nil => simp at hI1
        | cons n P' =>
          cases P' with
          | nil => simp at hI1; subst hI1; simp [Idx.isRange] at hr1
          | cons _ _ => simp at hI1
    refine ⟨isub (wrap64 (linearIndex p.axes P)) 1, 1, ?_, ?_⟩
    · simp [computeLinearLayout, hst, hoff]
    · intro J hJ
      have hva : viewAxes (P.map .int) = [] := by simpa [viewAxes] using viewAxes_ints P []
      rw [hva] at hJ
      cases J with
      | cons _ _ => exact hJ.elim
      | nil =>
        have hpos := IdxsOK_ints p.axes P hI
        refine ⟨P, by simpa using specPos_ints P, hpos, ?_⟩
        have hr := linearIndex_range p hp P hpos
        have hc : contiguous (P.map .int) = true := by
          cases P with
          | nil => rfl
          | cons n P' =>
            show ((Idx.int n).isUnitRange || allScalar (List.map Idx.int (n :: P'))) = true
            rw [allScalar_ints]; simp
        rw [hva]
        have h1 : linearIndex [] [] = 1 := rfl
        simp only [reindexLinearRaw, hc, ite_true, h1]
        simp only [iadd, isub, w_add_l]
        rw [show wrap64 (linearIndex p.axes P) - 1 + 1 = wrap64 (linearIndex p.axes P) by omega,
          w_id hr.1 hr.2, w_id hr.1 hr.2]
  · -- one range index between scalars
    have hshape : P.map .int ++ r :: Q.map .int = P.map .int ++ ([r] ++ Q.map .int) := rfl
    rw [hshape] at hI hl ⊢
    obtain ⟨axP, rest, hax, hlP, hokP, hrest⟩ := IdxsOK_append _ _ _ hI
    obtain ⟨axC, axQ, hrest', hlC, hokC, hokQ⟩ := IdxsOK_append _ _ _ hrest
    have hlP' : axP.length = P.length := by simpa using hlP
    obtain ⟨ax, hax1⟩ : ∃ ax, axC = [ax] := by
      match axC, hlC with
      | [ax], _ => exact ⟨ax, rfl⟩
    subst hax1
    have hst := stride_shape p P [r] Q axP rest hax hlP' hl r [] rfl hr
    have hlm := computeLinindex_eq p _ hl hF
    rw [mapM_first_ok _ (sr_ok_ints P _ (by
      intro c hc
      rcases List.mem_append.mp hc with h | h
      · simp at h; subst h; exact Or.inr hr
      · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h; exact Or.inl rfl)), map_fv_shape] at hlm
    have hfull : p.axes = axP ++ ([ax] ++ axQ) := by rw [hax, hrest']
    have hoff : computeOffset1 p (wrap64 (axesLen axP * strideOf r)) (P.map .int ++ ([r] ++ Q.map .int)) =
        .ok (wrap64 (linearIndex p.axes (P ++ ([r].map fv ++ Q)) -
          axesLen axP * strideOf r * (linearAxis ([r].map axes1Idx)).lo)) := by
      by_cases h1d : ∃ a r', p.axes = [a] ∧ P.map .int ++ ([r] ++ Q.map .int) = [r'] ∧ r'.isRange = true
      · obtain ⟨a, r', ha, hI1, _⟩ := h1d
        have hP0 : P = [] := by
          cases P with
          | nil => rfl
          | cons _ _ => simp at hI1
        have hQ0 : Q = [] := by
          subst hP0; cases Q with
          | nil => rfl
          | cons _ _ => simp at hI1
        subst hP0; subst hQ0
        have hlen0 : axP = [] := by
          cases axP with
          | nil => rfl
          | cons _ _ => simp at hlP'
        subst hlen0
        simp only [List.map_nil, List.nil_append, List.map_cons, List.append_nil] at ha ⊢
        unfold computeOffset1
        rw [ha]
        simp only [hr, ite_true, idxFirst_fv r (Or.inr hr), sbind_ok]
        simp [linearIndex, linearAxis, isub, imul, w_sub_r, w_mul_l, axesLen]
      · rw [computeOffset1_gen _ _ _ h1d, findExtendedInds_ints, findExtendedInds_core [r] Q
          (by intro c hc; simp at hc; subst hc; exact isRange_not_scalar _ hr),
          findExtendedDims_ints, show (1 : Int) + P.length = 1 + (P.length : Int) from rfl,
          List.singleton_append, findExtendedDims_one _ r Q (isRange_not_scalar r hr)]
        simp only [List.singleton_append, List.map_cons, List.map_nil, Except.map] at hlm hfull ⊢
        cases r with
        | slice b =>
          simp only [computeOffset1Dims, hlm, sbind_ok]
          rw [hfull, axisAt_mid axP ax axQ P hlP']
          have hb : b = ax := hokC.1
          subst hb
          simp only [isub, imul, w_sub_r, w_mul_l, w_sub_l, linearAxis, axes1Idx, idxAxes, strideOf,
            List.headD]
        | int _ => simp [Idx.isRange] at hr
        | arr _ _ => simp [Idx.isRange] at hr
        | mask _ => simp [Idx.isRange] at hr
        | carr _ _ _ => simp [Idx.isRange] at hr
        | _ =>
          simp only [computeOffset1Dims, hr, ite_true, hlm, sbind_ok, isub, imul, w_sub_r, w_mul_l,
            w_sub_l, linearAxis]
    refine ⟨_, _, (by unfold computeLinearLayout; rw [hst, sbind_ok, hoff]; rfl), ?_⟩
    intro J hJ
    rw [viewAxes_ints, viewAxes_core [r] Q (by simpa using hr)] at hJ ⊢
    exact assemble p hp P [r] Q axP [ax] axQ hfull hlP' (IdxsOK_ints _ _ hokP)
      (IdxsOK_ints _ _ hokQ) hokC (by simpa using hr) (strideOf r) (by simp) trivial
      (fun hc => by
        obtain ⟨h0, hu⟩ := contig_shape P [r] Q r [] rfl (isRange_not_scalar r hr) hc
        subst h0
        have : axP = [] := by cases axP with | nil => rfl | cons _ _ => simp at hlP'
        subst this
        simp [axesLen, unitRange_stride r hu]) J hJ
  · -- a chain of slices, then at most one unit range
    obtain ⟨a0, as', has⟩ : ∃ a0 as', as = a0 :: as' := by
      cases as with
      | nil => exact absurd rfl h1
      | cons a0 as' => exact ⟨a0, as', rfl⟩
    have hCr : ∀ c ∈ as.map Idx.slice ++ us, c.isRange = true := by
      intro c hc
      rcases List.mem_append.mp hc with h | h
      · obtain ⟨a, _, rfl⟩ := List.mem_map.mp h; rfl
      · exact unitRange_range c (h3 c h)
    have hσ : ∀ c ∈ as.map Idx.slice ++ us, strideOf c = 1 := by
      intro c hc
      rcases List.mem_append.mp hc with h | h
      · obtain ⟨a, _, rfl⟩ := List.mem_map.mp h; rfl
      · exact unitRange_stride c (h3 c h)
    obtain ⟨axP, rest, hax, hlP, hokP, hrest⟩ := IdxsOK_append _ _ _ hI
    obtain ⟨axC, axQ, hrest', hlC, hokC, hokQ⟩ := IdxsOK_append _ _ _ hrest
    have hlP' : axP.length = P.length := by simpa using hlP
    have hfull : p.axes = axP ++ (axC ++ axQ) := by rw [hax, hrest']
    have hCe : as.map Idx.slice ++ us = Idx.slice a0 :: (as'.map Idx.slice ++ us) := by rw [has]; rfl
    have hst := stride_shape p P (as.map Idx.slice ++ us) Q axP rest hax hlP' hl (Idx.slice a0) _ hCe rfl
    have hlm := computeLinindex_eq p _ hl hF
    rw [mapM_first_ok _ (sr_ok_ints P _ (by
      intro c hc
      rcases List.mem_append.mp hc with h | h
      · exact Or.inr (hCr c h)
      · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h; exact Or.inl rfl)), map_fv_shape] at hlm
    have hlen2 : 2 ≤ (as.map Idx.slice ++ us).length := by simpa using h4
    have hoff : computeOffset1 p (wrap64 (axesLen axP * strideOf (Idx.slice a0)))
        (P.map .int ++ (as.map Idx.slice ++ us ++ Q.map .int)) =
        .ok (wrap64 (linearIndex p.axes (P ++ ((as.map Idx.slice ++ us).map fv ++ Q)) -
          axesLen axP * strideOf (Idx.slice a0) * (linearAxis ((as.map Idx.slice ++ us).map axes1Idx)).lo)) := by
      rw [computeOffset1_gen]
      · rw [findExtendedInds_ints, findExtendedInds_core _ Q
          (fun c hc => isRange_not_scalar c (hCr c hc)),
          offsetDims_many _ _ _ _ _ (by omega), hlm]
        have hla : ((as.map Idx.slice ++ us).map axes1Idx).length ≥ 2 := by simpa using hlen2
        have hlo : (linearAxis ((as.map Idx.slice ++ us).map axes1Idx)).lo = 1 := by
          match hm : (as.map Idx.slice ++ us).map axes1Idx, hla with
          | _ :: _ :: _, _ => rfl
        rw [hlo]
        simp [Except.map, isub, w_sub_r, strideOf, Except.bind, w_sub_l]
      · rintro ⟨a, r', _, hI1, _⟩
        have := congrArg List.length hI1
        simp at this; omega
    refine ⟨_, _, (by unfold computeLinearLayout; rw [hst, sbind_ok, hoff]; rfl), ?_⟩
    intro J hJ
    rw [viewAxes_ints, viewAxes_core _ Q hCr] at hJ ⊢
    exact assemble p hp P (as.map Idx.slice ++ us) Q axP axC axQ hfull hlP' (IdxsOK_ints _ _ hokP)
      (IdxsOK_ints _ _ hokQ) hokC hCr (strideOf (Idx.slice a0)) hσ
      (IdxsOK_slices as us axC hokC h2)
      (fun hc => by
        obtain ⟨h0, _⟩ := contig_shape P _ Q (Idx.slice a0) _ hCe rfl hc
        subst h0
        have : axP = [] := by cases axP with | nil => rfl | cons _ _ => simp at hlP'
        subst this
        simp [axesLen, strideOf]) J hJ

end JuliaLean.MultidimCov.SubarrayV2
