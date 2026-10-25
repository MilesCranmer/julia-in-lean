import JuliaLean.BroadcastViews.Alias

/-! Properties of broadcast assignment between aliasing views, and their refutations. -/

namespace JuliaLean.BroadcastViews

open JuliaLean

/-- Every subscript tuple lies inside a parent of size `dims`. -/
abbrev InBounds (dims : List Nat) (ps : List (List Int)) : Prop :=
  ps.all (fun p => p.length == dims.length && (p.zip dims).all (fun q => 1 ≤ q.1 && q.1 ≤ (q.2 : Int))) = true

/-- `dest .= src` for two views of the same parent with the same number of elements equals
assigning a fresh copy of `src`, whenever `dest` does not select a parent element twice. -/
def AliasAssignFresh : Prop :=
  ∀ (dims : List Nat) (mem : List Int) (I J : List Idx),
    mem.length = dims.foldr (· * ·) 1 →
    InBounds dims (positions I) → InBounds dims (positions J) →
    (positions I).length = (positions J).length →
    ((positions I).map (linIdx dims)).Nodup →
    bcAssign dims mem I J = .ok (freshAssign dims mem I J)

/-- `dest .= dest .+ c` for a view `dest` equals computing `dest .+ c` into a fresh array and then
assigning it, as `P[I...] .+= c` does. -/
def SelfAssignFresh : Prop :=
  ∀ (dims : List Nat) (mem : List Int) (I : List Idx) (c : Int),
    mem.length = dims.foldr (· * ·) 1 → InBounds dims (positions I) →
    bcSelfAdd dims mem I c = freshSelfAdd dims mem I c

/-- `M = [1 2 3; 4 5 6; 7 8 9]`; `@views M[1, :] .= M[[CartesianIndex(3,3), CartesianIndex(2,2),
CartesianIndex(1,1)]]` writes row `[9, 5, 9]` (column-major memory below), while assigning a copy
writes `[9, 5, 1]`: `_indicesmightoverlap((1, 1:3), (cartesian array,))` tests `1 in [CartesianIndex…]`,
which is false. -/
theorem cartesianAlias_example :
    indicesMightOverlap [.scalar 1, .urange 1 3] [.carts 2 [[3, 3], [2, 2], [1, 1]]] = .ok false ∧
    bcAssign [3, 3] [1, 4, 7, 2, 5, 8, 3, 6, 9] [.scalar 1, .urange 1 3] [.carts 2 [[3, 3], [2, 2], [1, 1]]] =
      .ok [9, 4, 7, 5, 5, 8, 9, 6, 9] ∧
    freshAssign [3, 3] [1, 4, 7, 2, 5, 8, 3, 6, 9] [.scalar 1, .urange 1 3] [.carts 2 [[3, 3], [2, 2], [1, 1]]] =
      [9, 4, 7, 5, 5, 8, 1, 6, 9] := by
  decide

theorem aliasAssignFresh_refuted : ¬ AliasAssignFresh := by
  intro h
  have := h [3, 3] [1, 4, 7, 2, 5, 8, 3, 6, 9] [.scalar 1, .urange 1 3] [.carts 2 [[3, 3], [2, 2], [1, 1]]]
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [cartesianAlias_example.2.1, cartesianAlias_example.2.2] at this
  exact absurd this (by decide)

/-- `x = [10, 20, 30]; @views x[[1, 1, 2]] .+= 1` gives `[12, 21, 30]`; `x[[1, 1, 2]] .+= 1` gives
`[11, 21, 30]`. -/
theorem selfAssign_example :
    bcSelfAdd [3] [10, 20, 30] [.ints [1, 1, 2]] 1 = [12, 21, 30] ∧
    freshSelfAdd [3] [10, 20, 30] [.ints [1, 1, 2]] 1 = [11, 21, 30] := by
  decide

theorem selfAssignFresh_refuted : ¬ SelfAssignFresh := by
  intro h
  have := h [3] [10, 20, 30] [.ints [1, 1, 2]] 1 (by decide) (by decide)
  rw [selfAssign_example.1, selfAssign_example.2] at this
  exact absurd this (by decide)

/-- No index is an array of `CartesianIndex`. -/
def noCarts (I : List Idx) : Bool := I.all (fun | .carts _ _ => false | _ => true)

/-- Without arrays of `CartesianIndex`, `_indicesmightoverlap` is conservative: whenever two
index tuples of the same parent select a common parent element it returns `true`, so
`mightalias` reports the overlap. -/
def OverlapConservativeNoCarts : Prop :=
  ∀ (I J : List Idx), noCarts I = true → noCarts J = true → I.length = J.length →
    ∀ p, p ∈ positions I → p ∈ positions J → indicesMightOverlap I J = .ok true

private theorem mem_positions_cons {p : List Int} {i : Idx} {is : List Idx} :
    p ∈ positions (i :: is) → ∃ s ∈ i.subs, ∃ q ∈ positions is, p = s ++ q := by
  intro h
  simp only [positions, List.mem_flatMap, List.mem_map] at h
  obtain ⟨q, hq, s, hs, rfl⟩ := h
  exact ⟨s, hs, q, hq, rfl⟩

private theorem subs_noncart {i : Idx} (hi : ∀ n xs, i ≠ .carts n xs) {s : List Int} (hs : s ∈ i.subs) :
    ∃ k, s = [k] ∧ Elem.int k ∈ i.elems := by
  have hsub : i.subs = i.elems.filterMap (fun | .int k => some [k] | .cart _ => none) := by
    cases i with
    | carts n xs => exact absurd rfl (hi n xs)
    | _ => rfl
  rw [hsub, List.mem_filterMap] at hs
  obtain ⟨e, he, hes⟩ := hs
  cases e with
  | int k => simp at hes; exact ⟨k, hes.symm, he⟩
  | cart _ => simp at hes

private theorem eqb_refl (x : Elem) : x.eqb x = true := by
  cases x <;> simp [Elem.eqb]

private theorem inIdx_of_mem {x : Elem} {A : Idx} (h : x ∈ A.elems) : inIdx x A = true := by
  unfold inIdx
  exact List.any_eq_true.mpr ⟨x, h, eqb_refl x⟩

private theorem mem_urange {k lo hi : Int} (h : Elem.int k ∈ (Idx.urange lo hi).elems) : lo ≤ k ∧ k ≤ hi := by
  simp only [Idx.elems, List.map_map, List.mem_map, List.mem_range, Function.comp_def, Elem.int.injEq] at h
  obtain ⟨m, hm, rfl⟩ := h
  omega

private theorem mem_scalar {k x : Int} (h : Elem.int k ∈ (Idx.scalar x).elems) : k = x := by
  simpa [Idx.elems] using h

/-- The array × array branch of `_indicesmightoverlap` passes when both indices contain `k`. -/
private theorem arr_branch {k : Int} {A B : Idx} {next : R Bool} (hA : Elem.int k ∈ A.elems)
    (hB : Elem.int k ∈ B.elems) (hn : next = .ok true) :
    (match A.elems, B.elems with
      | [x], _ => if inIdx x B then next else .ok false
      | _, [y] => if inIdx y A then next else .ok false
      | _, _ => .ok true) = .ok true := by
  generalize hea : A.elems = ea at hA
  generalize heb : B.elems = eb at hB
  match ea, eb with
  | [x], _ =>
    have hx : x = .int k := (List.mem_singleton.mp hA).symm
    subst hx
    show (if inIdx (.int k) B = true then next else .ok false) = .ok true
    simp [inIdx_of_mem (heb ▸ hB), hn]
  | [], [y] => simp at hA
  | _ :: _ :: _, [y] =>
    have hy : y = .int k := (List.mem_singleton.mp hB).symm
    subst hy
    show (if inIdx (.int k) A = true then next else .ok false) = .ok true
    simp [inIdx_of_mem (hea ▸ hA), hn]
  | [], [] => simp at hA
  | [], _ :: _ :: _ => simp at hA
  | _ :: _ :: _, [] => simp at hB
  | _ :: _ :: _, _ :: _ :: _ => rfl

theorem overlapConservativeNoCarts : OverlapConservativeNoCarts := by
  intro I
  induction I with
  | nil =>
    intro J _ _ hl p _ _
    cases J with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons a as ih =>
    intro J hI hJ hl p hpI hpJ
    cases J with
    | nil => simp at hl
    | cons b bs =>
      simp only [noCarts, List.all_cons, Bool.and_eq_true] at hI hJ
      have ha : ∀ n xs, a ≠ .carts n xs := by intro n xs h; subst h; simp at hI
      have hb : ∀ n xs, b ≠ .carts n xs := by intro n xs h; subst h; simp at hJ
      obtain ⟨s, hs, q, hq, rfl⟩ := mem_positions_cons hpI
      obtain ⟨s', hs', q', hq', heq⟩ := mem_positions_cons hpJ
      obtain ⟨k, rfl, hk⟩ := subs_noncart ha hs
      obtain ⟨k', rfl, hk'⟩ := subs_noncart hb hs'
      simp only [List.singleton_append, List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hn := ih bs hI.2 hJ.2 (by simpa using hl) q hq hq'
      cases a with
      | carts n xs => exact absurd rfl (ha n xs)
      | scalar x =>
        have hx := mem_scalar hk
        subst hx
        cases b with
        | carts n xs => exact absurd rfl (hb n xs)
        | scalar y =>
          have hy := mem_scalar hk'
          subst hy
          simp [indicesMightOverlap, hn]
        | _ => simp only [indicesMightOverlap, if_pos (inIdx_of_mem hk'), hn]
      | urange alo ahi =>
        cases b with
        | carts n xs => exact absurd rfl (hb n xs)
        | scalar y =>
          have hy := mem_scalar hk'
          subst hy
          simp only [indicesMightOverlap, if_pos (inIdx_of_mem hk), hn]
        | urange blo bhi =>
          have h1 := mem_urange hk
          have h2 := mem_urange hk'
          simp only [indicesMightOverlap]
          rw [if_pos (by omega), hn]
        | srange _ _ _ =>
          simp only [indicesMightOverlap]
          rw [if_pos (List.any_eq_true.mpr ⟨_, hk, inIdx_of_mem hk'⟩), hn]
        | ints _ => exact arr_branch hk hk' hn
      | srange _ _ _ =>
        cases b with
        | carts n xs => exact absurd rfl (hb n xs)
        | scalar y =>
          have hy := mem_scalar hk'
          subst hy
          simp only [indicesMightOverlap, if_pos (inIdx_of_mem hk), hn]
        | urange _ _ | srange _ _ _ =>
          simp only [indicesMightOverlap]
          rw [if_pos (List.any_eq_true.mpr ⟨_, hk, inIdx_of_mem hk'⟩), hn]
        | ints _ => exact arr_branch hk hk' hn
      | ints _ =>
        cases b with
        | carts n xs => exact absurd rfl (hb n xs)
        | scalar y =>
          have hy := mem_scalar hk'
          subst hy
          simp only [indicesMightOverlap, if_pos (inIdx_of_mem hk), hn]
        | _ => exact arr_branch hk hk' hn


end JuliaLean.BroadcastViews
