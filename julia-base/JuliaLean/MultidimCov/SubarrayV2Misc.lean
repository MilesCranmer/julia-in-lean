import JuliaLean.MultidimCov.SubarrayV2View

/-!
Remaining `base/subarray.jl` rows: the nested `SubArray` of `_maybe_reindex`
(line 270), `_splatmap` (line 114) and `_maybe_reshape_parent` (lines 165-168).
-/

namespace JuliaLean.MultidimCov.SubarrayV2

theorem LinShape_elems : ∀ {I : List Idx}, LinShape I → ∀ c ∈ I, c.isScalar = true ∨ c.isRange = true
  | _, .scalars P, c, hc => by
      obtain ⟨n, _, rfl⟩ := List.mem_map.mp hc; exact Or.inl rfl
  | _, .range P r Q hr, c, hc => by
      rcases List.mem_append.mp hc with h | h
      · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h; exact Or.inl rfl
      · rcases List.mem_cons.mp h with h | h
        · subst h; exact Or.inr hr
        · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h; exact Or.inl rfl
  | _, .slices P as us Q _ _ h3 _, c, hc => by
      rcases List.mem_append.mp hc with h | h
      · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h; exact Or.inl rfl
      · rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · obtain ⟨a, _, rfl⟩ := List.mem_map.mp h; exact Or.inr rfl
          · exact Or.inr (unitRange_range c (h3 c h))
        · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h; exact Or.inl rfl

/-- An index tuple holding an array of `CartesianIndex` is never `IndexLinear`. -/
theorem vi_carr (I : List Idx) (k : Nat) (dims : List Nat) (xs : List (List Int))
    (h : Idx.carr k dims xs ∈ I) : viewindexing I = .cartesian := by
  cases hv : viewindexing I with
  | cartesian => rfl
  | linear =>
    rcases LinShape_elems (vi_shape I hv) _ h with h1 | h1 <;> simp [Idx.isScalar, Idx.isRange] at h1

/-- Row 270: a `CartesianIndex{k}` array (`k ≠ 1`) among the new indices keeps a
nested `SubArray` whose parent is `V` itself; that view is `IndexCartesian`,
stores `V` and `I`, and its element at `K` is `V`'s element at the manual's
position of `I[K]`. -/
def P270 : Prop := ∀ {α : Type} (V : Sub α) (I : List Idx) (k : Nat) (dims : List Nat)
    (xs : List (List Int)) (rest : List Idx), k ≠ 1 →
    maybeReindex3 V I (.carr k dims xs :: rest) = subArray (parOfSub V) I ∧
    ((∀ a ∈ subAxes V, AxOK a) → IdxsOKC (subAxes V) I → Idx.carr k dims xs ∈ I →
      ∃ W, maybeReindex3 V I (.carr k dims xs :: rest) = .ok W ∧ W.parent = parOfSub V ∧
        W.indices = I ∧ W.L = false ∧
        ∀ K, inAxes (viewAxes I) K → ∃ q, specPos I K = some q ∧
          getindexSlow W K = readElt (getCart V q).toElt)

theorem p270 : P270 := by
  intro α V I k dims xs rest hk
  have h1 : maybeReindex3 V I (.carr k dims xs :: rest) = subArray (parOfSub V) I := by
    simp [maybeReindex3, hk]
  refine ⟨h1, fun hax hok hmem => ?_⟩
  rw [h1]
  have hc : Style.combine (viewindexing I) (parOfSub V).style = .cartesian := by
    rw [vi_carr I k dims xs hmem]; rfl
  obtain ⟨_, hK0⟩ := p30 (parOfSub V) I (indexDimsum I)
  obtain ⟨W, hW, _, hK⟩ := hK0 hax hok
  have hW' := hW
  simp only [subCartesian, subInner, check_ok (parOfSub V) I hok, sbind_ok, pure, Except.pure,
    Except.ok.injEq] at hW'
  refine ⟨W, ?_, ?_, ?_, ?_, fun K hK' => ?_⟩
  · simp [subArray, hc, ensureIndexable, hW]
  · rw [← hW']
  · rw [← hW']
  · rw [← hW']
  · obtain ⟨q, hq, hg⟩ := hK K hK'
    exact ⟨q, hq, by rw [hg]; rfl⟩

/-! ## `_splatmap`, lines 113-114 -/

/-- `_splatmap(f, ::Tuple{})` (line 113) and `_splatmap(f, t::Tuple)` (line 114). -/
def splatmap {β γ : Type} (f : β → SR (List γ)) : List β → SR (List γ)
  | [] => .ok []                                                      -- 113
  | t :: ts => do                                                     -- 114
      let a ← f t
      let b ← splatmap f ts
      pure (a ++ b)

/-- Row 114: `_splatmap(f, t)` is `(f(t[1])..., f(t[2])..., ...)`, the
concatenation of `f` over `t` in order, stopping at the first exception of `f`. -/
def P114 : Prop := ∀ {β γ : Type} (f : β → SR (List γ)) (t : List β),
    splatmap f t = (t.mapM f).map List.flatten

theorem p114 : P114 := by
  intro β γ f t
  induction t with
  | nil => rfl
  | cons x t ih =>
    simp only [splatmap, List.mapM_cons]
    cases f x with
    | error e => rfl
    | ok a =>
      simp only [sbind_ok]
      rw [ih]
      cases t.mapM f with
      | error e => rfl
      | ok b => rfl

/-! ## `_maybe_reshape_parent`, lines 165-168 -/

/-- `length(l) * ...` over trailing axes, `base/reshapedarray.jl:194-195`. -/
def rdimsTrailing (inds : List Ax) : Int := inds.foldr (fun a n => a.len * n) 1

/-- `rdims(out, inds)`, `base/reshapedarray.jl:196-205`. -/
def rdims : List Ax → List Ax → List Ax
  | [], _ => []                                                       -- 197-199
  | out, [] => out                                                    -- 200-201
  | [_], [i] => [i]                                                   -- 202
  | [_], inds => [oneAx (rdimsTrailing inds)]                         -- 203
  | o :: out, i :: inds =>
      if out.length = inds.length then i :: inds                      -- 204
      else i :: rdims out inds                                        -- 205
termination_by out => out.length

/-- `reshape(parent, ::Val{N})`, `base/reshapedarray.jl:186-189`: the parent itself
at its own rank, else a `ReshapedArray` over `rdims(Val(N), axes(parent))`
(a `MethodError` when an axis does not start at 1), whose elements are the
parent's in column-major order. -/
def reshapeVal (p : Par α) (n : Nat) : SR (Par α) :=
  if p.axes.length = n then .ok p                                     -- 186
  else
    let shp := rdims (List.replicate n (oneAx 1)) p.axes              -- 188
    if shp.all (fun a => a.lo = 1) then
      .ok { ty := ⟨"ReshapedArray", p.ty.elt⟩, axes := shp, linear := p.linear,
            lin := fun k => p.cart (ind2sub p.axes k),
            cart := fun pos => p.cart (ind2sub p.axes (linearIndex shp pos)) }
    else .error .method

/-- `_maybe_reshape_parent(A, ::NTuple{N,Bool})`, lines 165-168. -/
def maybeReshapeParent (p : Par α) (shape : List Bool) : SR (Par α) :=
  if shape.length = 1 then
    if p.axes.length = 1 then reshapeVal p 1                          -- 166
    else reshapeVal p 1                                               -- 165
  else if p.axes.length = shape.length then .ok p                     -- 167
  else reshapeVal p shape.length                                      -- 168

/-- Row 167: a parent whose rank equals the number of effective indices is
returned as the parent itself (lines 166-167; `reshape(A, Val(N))` of an
`N`-dimensional `A` is `A`). -/
def P167 : Prop := ∀ {α : Type} (p : Par α) (shape : List Bool), p.axes.length = shape.length →
    maybeReshapeParent p shape = .ok p

theorem p167 : P167 := by
  intro α p shape h
  unfold maybeReshapeParent
  by_cases h1 : shape.length = 1
  · rw [if_pos h1, if_pos (by omega)]; simp [reshapeVal, h, h1]
  · rw [if_neg h1, if_pos h]

end JuliaLean.MultidimCov.SubarrayV2
