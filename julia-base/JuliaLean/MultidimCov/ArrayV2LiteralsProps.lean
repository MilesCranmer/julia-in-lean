import JuliaLean.MultidimCov.ArrayV2Literals

/-! Contracts of the models in `ArrayV2Literals`. -/

namespace JuliaLean.MultidimCov.ArrayV2

open JuliaLean (IntTy)
open JuliaLean.Promotion (NumTy promoteType expectedPromotion promoteTypeTable_proven)

/-! ### Lemmas -/

theorem convWrites_spec (conv : β → R α) (w : Arr α → β → Int → R (Arr α))
    (hw : ∀ a x j, 1 ≤ j → j ≤ length a → w a x j = (conv x >>= fun y => .ok (setU a j (some y)))) :
    ∀ (xs : List β) (a : Arr α) (i : Int), 1 ≤ i → i - 1 + xs.length ≤ length a →
      (∀ e, convList conv xs = .error e → convWrites w a i xs = .error e) ∧
      (∀ ys, convList conv xs = .ok ys → convWrites w a i xs = .ok (safeWrites a i ys))
  | [], a, i, _, _ => ⟨fun e h => by simp [convList] at h, fun ys h => by
      simp only [convList, Except.ok.injEq] at h; subst h; rfl⟩
  | x :: xs, a, i, h1, h2 => by
    simp only [List.length_cons] at h2
    refine ⟨fun e h => ?_, fun ys h => ?_⟩
    · unfold convList at h; simp only [convWrites]; rw [hw a x i h1 (by omega)]
      cases hx : conv x with
      | error e' => rw [hx, bind_error] at h; cases h; rfl
      | ok y =>
        rw [hx, bind_ok] at h
        cases hxs : convList conv xs with
        | error e'' =>
          rw [hxs, bind_error] at h; cases h
          simp only [bind_ok]
          exact (convWrites_spec conv w hw xs (setU a i (some y)) (i + 1) (by omega)
            (by rw [length_setU]; omega)).1 _ hxs
        | ok zs => rw [hxs, bind_ok] at h; cases h
    · unfold convList at h; simp only [convWrites]; rw [hw a x i h1 (by omega)]
      cases hx : conv x with
      | error e' => rw [hx, bind_error] at h; cases h
      | ok y =>
        rw [hx, bind_ok] at h
        cases hxs : convList conv xs with
        | error e'' => rw [hxs, bind_error] at h; cases h
        | ok zs =>
          rw [hxs, bind_ok, pure_ok, Except.ok.injEq] at h; subst h
          simp only [bind_ok]
          exact (convWrites_spec conv w hw xs (setU a i (some y)) (i + 1) (by omega)
            (by rw [length_setU]; omega)).2 _ hxs

theorem hw1059 (conv : β → R α) : ∀ (a : Arr α) (x : β) (j : Int), 1 ≤ j → j ≤ length a →
    m1059 conv a x j = (conv x >>= fun y => .ok (setU a j (some y))) := fun _ _ _ _ _ => rfl

theorem hw1031 (conv : β → R α) : ∀ (a : Arr α) (x : β) (j : Int), 1 ≤ j → j ≤ length a →
    m1031 conv a x j = (conv x >>= fun y => .ok (setU a j (some y))) := by
  intro a x j h1 h2
  unfold m1031
  cases conv x with
  | error e => rfl
  | ok y => simp only [bind_ok]; unfold m1036; rw [if_neg (by rw [inBounds_iff]; simp; omega)]

theorem contents_safeWrites_full {b : Arr α} {ys : List α} (hl : length b = ys.length) :
    contents (safeWrites b 1 ys) = ys.map some := by
  apply contents_ext (by rw [length_safeWrites, hl]; simp)
  intro k hk
  simp only [List.length_map] at hk
  rw [show (k : Int) + 1 = 1 + k by omega, safeWrites_at k hk]; simp

theorem newArray_vec {n : Int} (h0 : 0 ≤ n) (h1 : n ≤ typemaxInt) :
    ∃ b : Arr α, newArray [n] = .ok b ∧ IsVec b n ∧ length b = n := by
  obtain ⟨b, e, hd, _, _⟩ := newArray_ok (α := α) (dims := [n]) (by simpa using h0) (by simpa using h1)
  exact ⟨b, e, hd, by simp [length, hd]⟩

/-! ### `DimensionMismatch()`, `vect`, typed literals, `vcat()`, `hcat()` -/

/-- `vect(X::T...)` (base/array.jl:159) is the vector of its arguments in order. -/
def P159 : Prop := ∀ {α : Type} (xs : List α), xs.length ≤ typemaxInt →
    ∃ v, m159 xs = .ok v ∧ IsVec v xs.length ∧ contents v = xs.map some

theorem p159 : P159 := by
  intro α xs h
  obtain ⟨b, e, hv, hl⟩ := newArray_vec (α := α) (n := xs.length) (by omega) h
  exact ⟨_, by unfold m159; rw [e, bind_ok]; rfl, by unfold IsVec at hv ⊢; rw [(safeWrites_spec xs b 1).1]; exact hv,
    contents_safeWrites_full hl⟩

/-- `T[vals...]` / `getindex(T, vals...)` (docstring base/array.jl:425-444): a
`Vector{T}` holding `convert(T, v)` for each value in order, for tuples of one
type and of mixed types alike; the first failing conversion propagates. -/
def P445 : Prop := ∀ {α β : Type} (conv : β → R α) (homog : Bool) (vals : List β), vals.length ≤ typemaxInt →
    (∀ e, convList conv vals = .error e → m445 conv homog vals = .error e) ∧
    (∀ ys, convList conv vals = .ok ys → ∃ a, m445 conv homog vals = .ok a ∧ IsVec a vals.length ∧
      contents a = ys.map some)

theorem p445 : P445 := by
  intro α β conv homog vals h
  obtain ⟨b, e, hv, hl⟩ := newArray_vec (α := α) (n := vals.length) (by omega) h
  have hw : ∀ w, (∀ a x j, 1 ≤ j → j ≤ length a → w a x j = (conv x >>= fun y => .ok (setU a j (some y)))) →
      (∀ e, convList conv vals = .error e → convWrites w b 1 vals = .error e) ∧
      (∀ ys, convList conv vals = .ok ys → convWrites w b 1 vals = .ok (safeWrites b 1 ys)) :=
    fun w hw => convWrites_spec conv w hw vals b 1 (by omega) (by omega)
  have hc : ∀ ys, convList conv vals = .ok ys → length b = ys.length := by
    intro ys hys; rw [hl, ← convList_length conv vals ys hys]
  refine ⟨fun er her => ?_, fun ys hys => ⟨safeWrites b 1 ys, ?_, ?_, contents_safeWrites_full (hc ys hys)⟩⟩
  · unfold m445; rw [e, bind_ok]
    cases homog
    · exact (hw _ (hw1031 conv)).1 er her
    · exact (hw _ (hw1059 conv)).1 er her
  · unfold m445; rw [e, bind_ok]
    cases homog
    · exact (hw _ (hw1031 conv)).2 ys hys
    · exact (hw _ (hw1059 conv)).2 ys hys
  · unfold IsVec at hv ⊢; rw [(safeWrites_spec ys b 1).1]; exact hv

/-- Whether value `v` is exactly representable in `T` (for the float types: an
integer of magnitude at most `2^11`, exact in `Float16`, `Float32` and `Float64`). -/
def fitsTy (T : NumTy) (v : Int) : Prop :=
  match T with
  | .bool => v = 0 ∨ v = 1
  | .int t => t.min ≤ v ∧ v ≤ t.max
  | .flt _ => -2048 ≤ v ∧ v ≤ 2048

/-- `T` is `Bool` or a `BitInteger` (conversion to it can throw `InexactError`). -/
def isExactTy : NumTy → Prop
  | .flt _ => False
  | _ => True

theorem promoteTypeof_eq (x : NV) : ∀ xs : List NV, promoteTypeof (x :: xs) = some (promotedTy x xs)
  | [] => rfl
  | y :: ys => by
    simp only [promoteTypeof, promoteTypeof_eq y ys, promotedTy]
    exact promoteTypeTable_proven _ _

theorem nconv_fits (T : NumTy) (x : NV) (h : fitsTy T x.v) : nconv T x = .ok ⟨T, x.v⟩ := by
  cases T <;> simp only [nconv, fitsTy] at h ⊢ <;> simp [h]

theorem nconv_nofit (T : NumTy) (hT : isExactTy T) (x : NV) (h : ¬ fitsTy T x.v) : nconv T x = .error .inexact := by
  cases T <;> simp only [nconv, fitsTy, isExactTy] at h hT ⊢ <;> simp_all

theorem convList_nconv (T : NumTy) : ∀ xs : List NV,
    ((∀ z ∈ xs, fitsTy T z.v) → convList (nconv T) xs = .ok (xs.map fun z => ⟨T, z.v⟩)) ∧
    (isExactTy T → (∃ z ∈ xs, ¬ fitsTy T z.v) → convList (nconv T) xs = .error .inexact)
  | [] => ⟨fun _ => rfl, fun _ ⟨_, h, _⟩ => by simp at h⟩
  | x :: xs => by
    obtain ⟨ih1, ih2⟩ := convList_nconv T xs
    refine ⟨fun h => ?_, fun hT ⟨z, hz, hf⟩ => ?_⟩
    · simp only [convList, nconv_fits T x (h x (by simp)), bind_ok, ih1 (fun z hz => h z (by simp [hz])),
        pure_ok, List.map_cons]
    · by_cases hx : fitsTy T x.v
      · simp only [List.mem_cons] at hz
        rcases hz with hz | hz
        · subst hz; exact absurd hx hf
        · simp only [convList, nconv_fits T x hx, bind_ok, ih2 hT ⟨z, hz, hf⟩, bind_error]
      · simp only [convList, nconv_nofit T hT x hx, bind_error]

/-- `vect(X...)` (docstring base/array.jl:168-182): the element type is the
documented promotion of the argument types and the elements are the arguments
converted to it; an argument not representable there (a negative value with an
unsigned result type) throws `InexactError`. -/
def P183 : Prop := ∀ (x : NV) (xs : List NV), xs.length < typemaxInt →
    let T := promotedTy x xs
    ((∀ z ∈ x :: xs, fitsTy T z.v) → ∃ a, m183 (x :: xs) = .ok ⟨T, a⟩ ∧ IsVec a (xs.length + 1) ∧
      contents a = (x :: xs).map fun z => some ⟨T, z.v⟩) ∧
    (isExactTy T → (∃ z ∈ x :: xs, ¬ fitsTy T z.v) → m183 (x :: xs) = .error .inexact)

theorem p183 : P183 := by
  intro x xs hl T
  have hp := promoteTypeof_eq x xs
  refine ⟨fun h => ?_, fun hT h => ?_⟩
  · obtain ⟨_, h2⟩ := p445 (nconv T) ((x :: xs).all fun z => z.ty == ((x :: xs).headD ⟨T, 0⟩).ty) (x :: xs)
      (by simp; omega)
    obtain ⟨a, e, hv, hc⟩ := h2 _ ((convList_nconv T (x :: xs)).1 h)
    refine ⟨a, ?_, by simpa using hv, by rw [hc]; simp⟩
    unfold m183; rw [hp]; simp only []; rw [e, bind_ok]; rfl
  · obtain ⟨h1, _⟩ := p445 (nconv T) ((x :: xs).all fun z => z.ty == ((x :: xs).headD ⟨T, 0⟩).ty) (x :: xs)
      (by simp; omega)
    unfold m183; rw [hp]; simp only []
    rw [h1 _ ((convList_nconv T (x :: xs)).2 hT h), bind_error]

/-- `DimensionMismatch()` has the empty message; `vcat()` and `hcat()` are an
empty `Vector{Any}` (element type `none` = `Any`): reading any index throws
`BoundsError`. -/
def P2337 : Prop := P14 ∧ ∀ i : Int,
    (∃ a, m2337 = .ok (none, a) ∧ IsVec a 0 ∧ contents a = [] ∧ getL a i = .error .bounds) ∧
    (∃ a, m2338 = .ok (none, a) ∧ IsVec a 0 ∧ contents a = [] ∧ getL a i = .error .bounds)

theorem p2337 : P2337 := by
  obtain ⟨b, e, hv, hl⟩ := newArray_vec (α := NV) (n := 0) (by omega) (by unfold typemaxInt; omega)
  have hc : contents b = [] := by simp [contents, hl]
  have hg : ∀ i, getL b i = .error .bounds := by
    intro i; unfold getL; rw [if_neg (by simp [inBounds, hl]; omega)]
  exact ⟨p14, fun i => ⟨⟨b, by unfold m2337; rw [e, bind_ok]; rfl, hv, hc, hg i⟩,
    ⟨b, by unfold m2338; rw [e, bind_ok]; rfl, hv, hc, hg i⟩⟩⟩

/-! ### `fill`, `zeros`, `ones` -/

/-- The length of a `DimOrInd` axis. -/
def lenOf : DimArg → Int
  | .int d => d
  | .oneTo n => n
  | .other f l => max 0 (l - f + 1)

theorem toDim_lenOf : ∀ dims : List DimArg, (∀ d ∈ dims, d.isIntOrOneTo = true) →
    dims.map DimArg.toDim = dims.map lenOf
  | [], _ => rfl
  | d :: ds, h => by
    have := h d (by simp)
    simp only [List.map_cons, toDim_lenOf ds (fun x hx => h x (by simp [hx]))]
    cases d <;> simp_all [DimArg.toDim, lenOf, DimArg.isIntOrOneTo, m482, m483]

theorem newArray_neg' {dims : List Int} (h : ∃ d ∈ dims, d < 0) : (newArray dims : R (Arr α)) = .error .argument :=
  newArray_neg h

theorem fresh_fill {α β : Type} {dims : List Int} (h0 : ∀ d ∈ dims, 0 ≤ d) (h1 : dims.foldr (· * ·) 1 ≤ typemaxInt)
    (conv : β → R α) (x : β) (y : α) (hy : conv x = .ok y) :
    ∃ a, (do let a ← newArray dims; m368 conv a x) = .ok a ∧ a.dims = dims ∧
      contents a = List.replicate (dims.foldr (· * ·) 1).toNat (some y) := by
  obtain ⟨b, e, hd, ⟨_, hl, _⟩, _⟩ := newArray_ok (α := α) h0 h1
  obtain ⟨_, h2, _⟩ := p368 conv b x hl
  obtain ⟨a, e2, hd2, hc2⟩ := h2 y hy
  refine ⟨a, by rw [e, bind_ok]; exact e2, by rw [hd2, hd], ?_⟩
  rw [hc2]; congr; simp [length, hd]

/-- `fill(v, dims)` (docstring base/array.jl:485-580): with `Integer`/`OneTo` axes
(`to_dim(d) = d`, `to_dim(OneTo(n)) = n`) the result has those lengths as size and
every element is `v`; a negative length is an `ArgumentError`; an axis that is
another unit range is a `MethodError` (`similar(Array{T,N}, axes)` has no method). -/
def P583 : Prop := ∀ {α : Type} (v : α) (dims : List DimArg),
    ((∀ d ∈ dims, d.isIntOrOneTo = true) → (∀ d ∈ dims, 0 ≤ lenOf d) → (dims.map lenOf).foldr (· * ·) 1 ≤ typemaxInt →
      ∃ a, m583 v dims = .ok a ∧ a.dims = dims.map lenOf ∧
        contents a = List.replicate ((dims.map lenOf).foldr (· * ·) 1).toNat (some v)) ∧
    ((∀ d ∈ dims, d.isIntOrOneTo = true) → (∃ d ∈ dims, lenOf d < 0) → m583 v dims = .error .argument) ∧
    ((∃ d ∈ dims, d.isIntOrOneTo = false) → m583 v dims = .error .method)

theorem p583 : P583 := by
  intro α v dims
  refine ⟨fun h1 h2 h3 => ?_, fun h1 h2 => ?_, fun h => ?_⟩
  · have hm := toDim_lenOf dims h1
    have h0 : ∀ d ∈ dims.map lenOf, 0 ≤ d := by simpa using h2
    obtain ⟨a, e, hd, hc⟩ := fresh_fill h0 h3 (fun x => (.ok x : R α)) v v rfl
    refine ⟨a, ?_, hd, hc⟩
    unfold m583 fillTuple
    split
    · rw [hm]; exact e
    · rw [if_pos (List.all_eq_true.mpr fun d hd => h1 d hd)]; unfold m584; rw [hm]; exact e
  · have hm := toDim_lenOf dims h1
    have hneg : ∃ d ∈ dims.map lenOf, d < 0 := by
      obtain ⟨d, hd, hl⟩ := h2; exact ⟨lenOf d, List.mem_map.mpr ⟨d, hd, rfl⟩, hl⟩
    unfold m583 fillTuple
    split
    · rw [hm, m585, newArray_neg hneg, bind_error]
    · rw [if_pos (List.all_eq_true.mpr fun d hd => h1 d hd)]; unfold m584; rw [hm, m585, newArray_neg hneg, bind_error]
  · obtain ⟨d, hd, hf⟩ := h
    have h1 : dims.all DimArg.isInt = false := by
      rw [List.all_eq_false]; exact ⟨d, hd, by cases d <;> simp_all [DimArg.isInt, DimArg.isIntOrOneTo]⟩
    have h2 : dims.all DimArg.isIntOrOneTo = false := by rw [List.all_eq_false]; exact ⟨d, hd, by simp [hf]⟩
    unfold m583 fillTuple m586 similarShape
    rw [if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h2]), bind_error]

theorem felt_conv (one : Bool) (T : NumTy) : nconv T (felt one T) = .ok (felt one T) := by
  have hb : ∀ t : IntTy, t.min ≤ 0 ∧ 1 ≤ t.max := by intro t; cases t <;> decide
  cases T with
  | bool => cases one <;> rfl
  | int t =>
    have := hb t
    cases one
    · show (if t.min ≤ 0 ∧ 0 ≤ t.max then _ else _) = _; rw [if_pos (by omega)]; rfl
    · show (if t.min ≤ 1 ∧ 1 ≤ t.max then _ else _) = _; rw [if_pos (by omega)]; rfl
  | flt F => rfl

/-- `zeros`/`ones` (docstrings base/array.jl:589-628): an `Array` with element type
`T` (`Float64` by default) of the requested `Integer`/`OneTo` lengths (`()` gives a
zero-dimensional array), every element `zero(T)`/`one(T)`; a negative length is an
`ArgumentError`; another unit range axis is a `MethodError`. -/
def P633 : Prop := ∀ (one : Bool) (T : NumTy) (dims : List DimArg),
    let el : NV := ⟨T, if one then 1 else 0⟩
    m633 one dims = m634 one (.flt .f64) dims ∧ m635 one dims = m634 one (.flt .f64) dims ∧
    ((∀ d ∈ dims, d.isIntOrOneTo = true) → (∀ d ∈ dims, 0 ≤ lenOf d) → (dims.map lenOf).foldr (· * ·) 1 ≤ typemaxInt →
      ∃ a, m634 one T dims = .ok ⟨T, a⟩ ∧ a.dims = dims.map lenOf ∧
        contents a = List.replicate ((dims.map lenOf).foldr (· * ·) 1).toNat (some el)) ∧
    ((∀ d ∈ dims, d.isIntOrOneTo = true) → (∃ d ∈ dims, lenOf d < 0) → m634 one T dims = .error .argument) ∧
    ((∃ d ∈ dims, d.isIntOrOneTo = false) → m634 one T dims = .error .method)

theorem p633 : P633 := by
  intro one T dims el
  have hf := felt_conv one T
  refine ⟨rfl, rfl, fun h1 h2 h3 => ?_, fun h1 h2 => ?_, fun h => ?_⟩
  · have hm := toDim_lenOf dims h1
    have h0 : ∀ d ∈ dims.map lenOf, 0 ≤ d := by simpa using h2
    obtain ⟨a, e, hd, hc⟩ := fresh_fill h0 h3 (nconv T) (felt one T) (felt one T) hf
    have key : m637 one T (dims.map lenOf) = .ok ⟨T, a⟩ := by
      unfold m637
      revert e; cases newArray (dims.map lenOf) with
      | error e' => intro e; cases e
      | ok b => intro e; simp only [bind_ok] at e ⊢; rw [e]; rfl
    refine ⟨a, ?_, hd, hc⟩
    unfold m634 zerosT
    split
    · rename_i h0'; subst h0'
      unfold m642; simp only [List.map_nil] at e
      revert e; cases newArray ([] : List Int) with
      | error e' => intro e; cases e
      | ok b => intro e; simp only [bind_ok] at e ⊢; rw [e]; rfl
    · split
      · rw [hm]; exact key
      · rw [if_pos (List.all_eq_true.mpr fun d hd => h1 d hd)]; unfold m636; rw [hm]; exact key
  · have hm := toDim_lenOf dims h1
    have hneg : ∃ d ∈ dims.map lenOf, d < 0 := by
      obtain ⟨d, hd, hl⟩ := h2; exact ⟨lenOf d, List.mem_map.mpr ⟨d, hd, rfl⟩, hl⟩
    have hne : dims ≠ [] := by rintro rfl; obtain ⟨d, hd, _⟩ := h2; simp at hd
    unfold m634 zerosT
    rw [if_neg hne]
    split
    · rw [hm, m637, newArray_neg hneg, bind_error]
    · rw [if_pos (List.all_eq_true.mpr fun d hd => h1 d hd)]; unfold m636; rw [hm, m637, newArray_neg hneg, bind_error]
  · obtain ⟨d, hd, hf'⟩ := h
    have hne : dims ≠ [] := by rintro rfl; simp at hd
    have h1 : dims.all DimArg.isInt = false := by
      rw [List.all_eq_false]; exact ⟨d, hd, by cases d <;> simp_all [DimArg.isInt, DimArg.isIntOrOneTo]⟩
    have h2 : dims.all DimArg.isIntOrOneTo = false := by rw [List.all_eq_false]; exact ⟨d, hd, by simp [hf']⟩
    unfold m634 zerosT m647 similarShape
    rw [if_neg hne, if_neg (by simp [h1]), if_neg (by simp [h2]), if_neg (by simp [h2]), bind_error]

/-! ### `asize_from`, `_cat` -/

theorem m188_eq (a : Arr α) (hd : (a.dims.length : Int) ≤ typemaxInt) :
    ∀ (k : Nat) (n : Int), (a.dims.length + 1 - n).toNat = k → 1 ≤ n →
    m188 a n = .ok (a.dims.drop (n - 1).toNat)
  | 0, n, hk, hn => by
    rw [m188, if_pos (by omega)]; congr 1; exact (List.drop_of_length_le (by omega)).symm
  | k + 1, n, hk, hn => by
    unfold typemaxInt at hd
    rw [m188, if_neg (by omega), m188_eq a hd k (n + 1) (by omega) (by omega)]
    unfold sizeDim
    rw [toInt_ok' (by omega) (by omega), bind_ok, if_pos (by omega), if_pos hn, bind_ok, bind_ok, pure_ok]
    have hlt : (n - 1).toNat < a.dims.length := by omega
    rw [List.drop_eq_getElem_cons hlt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    simp only [Option.getD_some]
    congr 3; omega

/-- `asize_from(a, n)` is `size(a)[n:end]`: the sizes `size(a, n), …, size(a, ndims(a))`,
empty for `n > ndims(a)`; as for the tuple slice, an `n < 1` throws `BoundsError` (from
`size(a, n)`), and an `n` outside `Int` throws `InexactError` from `Int(n)`. -/
def P188 : Prop := ∀ {α : Type} (a : Arr α) (n : Int), (a.dims.length : Int) ≤ typemaxInt →
    (1 ≤ n → m188 a n = .ok (a.dims.drop (n - 1).toNat)) ∧
    (typeminInt ≤ n → n ≤ 0 → m188 a n = .error .bounds) ∧
    (n < typeminInt → m188 a n = .error .inexact)

theorem p188 : P188 := by
  intro α a n hd
  refine ⟨fun hn => m188_eq a hd _ n rfl hn, fun h0 h1 => ?_, fun h => ?_⟩
  · unfold typeminInt at h0
    rw [m188, if_neg (by omega)]
    unfold sizeDim
    rw [toInt_ok' (by omega) (by omega), bind_ok, if_pos (by omega), if_neg (by omega), bind_error]
  · unfold typeminInt at h
    rw [m188, if_neg (by omega)]
    unfold sizeDim toInt typeminInt typemaxInt
    rw [if_neg (by omega), bind_error, bind_error]

theorem prod_ones (k : Nat) (m : Int) : (List.replicate k (1 : Int) ++ [m]).foldr (· * ·) 1 = m := by
  induction k with
  | zero => simp
  | succ k ih => simp only [List.replicate_succ, List.cons_append, List.foldr_cons, ih, Int.one_mul]

theorem contents_redims (a : Arr α) (d : List Int) (h : d.foldr (· * ·) 1 = length a) :
    contents { a with dims := d } = contents a := by
  simp only [contents, length] at h ⊢; rw [h]; rfl

/-- `cat(x::Integer...; dims=n)` via `_cat(n, x...)`: for `n ≥ 1` the values of
`[x...]` (promoted) in an array of size `(1, …, 1, length(x))` with `n`
dimensions; `n < 1` is an `ArgumentError`, as for `cat` of arrays. -/
def P2368 : Prop := ∀ (n : Int) (x : NV) (xs' : List NV), xs'.length + 1 < typemaxInt →
    (∀ z ∈ x :: xs', fitsTy (promotedTy x xs') z.v) →
    (1 ≤ n → ∃ a, m2368 n (x :: xs') = .ok (some (promotedTy x xs'), a) ∧
      a.dims = List.replicate (n - 1).toNat 1 ++ [((x :: xs').length : Int)] ∧
      contents a = (x :: xs').map fun z => some ⟨promotedTy x xs', z.v⟩) ∧
    (n < 1 → m2368 n (x :: xs') = .error .argument)

theorem p2368 : P2368 := by
  intro n x xs' hl hf
  have hl' : (xs'.length : Int) < typemaxInt := by omega
  obtain ⟨h1', _⟩ := p183 x xs' hl'
  obtain ⟨a, e1, hv, hc⟩ := h1' hf
  have hla : length a = ((x :: xs').length : Int) := by rw [length_vec a _ hv]; simp
  refine ⟨fun h1 => ⟨{ a with dims := List.replicate (n - 1).toNat 1 ++ [((x :: xs').length : Int)] }, ?_, rfl, ?_⟩,
    fun h1 => ?_⟩
  · unfold m2368; simp only [e1, bind_ok, pure_ok]; rw [if_neg (by omega)]
    unfold reshapeArr; rw [prod_ones, if_pos hla.symm]; rfl
  · rw [contents_redims _ _ (by rw [prod_ones, hla]), hc]
  · unfold m2368; simp only [e1, bind_ok, pure_ok]; rw [if_pos (by omega)]

/-! ### Copy constructors and `convert` -/

theorem readWrite_map (conv : β → R α) : ∀ (xs : List β) (a : Arr α) (i : Int),
    convWrites (readWrite conv) a i (xs.map some) = convWrites (m1031 conv) a i xs
  | [], _, _ => rfl
  | x :: xs, a, i => by
    simp only [List.map_cons, convWrites, readWrite]
    cases m1031 conv a x i with
    | error e => rfl
    | ok b => simp only [bind_ok]; exact readWrite_map conv xs b (i + 1)

theorem axcheck_ok (dims : List Int) (h : ∀ d ∈ dims, 0 ≤ d) :
    ((dims.length == (dims.map fun d => ((1 : Int), d)).length) &&
      (List.zip (dims.map fun d => max 0 (d - 1 + 1)) (dims.map fun d => ((1 : Int), d))).all
        (fun p => axEq p.1 p.2)) = true := by
  induction dims with
  | nil => rfl
  | cons d ds ih =>
    have hd := h d (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    simp only [List.length_map, beq_self_eq_true, Bool.true_and] at this ⊢
    simp only [List.map_cons, List.zip_cons_cons, List.all_cons, this, Bool.and_true]
    simp [axEq]; omega

/-- `Array{T,N}(x)` (constructors "should make copies", base/array.jl:663-664): for
a source with axes `1:n` the result is a new array of `size(x)` holding
`convert(T, x[i])` in order, a failing conversion propagating; a non-empty axis
that does not start at 1 is a `DimensionMismatch`. -/
def P664 : Prop := ∀ {α β : Type} (conv : β → R α) (ls : List Int) (xs : List β),
    (∀ l ∈ ls, 0 ≤ l) → ls.foldr (· * ·) 1 = (xs.length : Int) → xs.length ≤ typemaxInt →
    let x : SrcArr β := ⟨ls.map fun l => (1, l), xs.map some⟩
    (∀ e, convList conv xs = .error e → m664 conv x = .error e) ∧
    (∀ ys, convList conv xs = .ok ys → ∃ a, m664 conv x = .ok a ∧ a.dims = ls ∧ contents a = ys.map some) ∧
    (∀ (f l : Int) (pre post : List (Int × Int)), f ≠ 1 → f ≤ l →
      0 ≤ (SrcArr.size ⟨pre ++ (f, l) :: post, xs.map some⟩).foldr (· * ·) 1 →
      (SrcArr.size ⟨pre ++ (f, l) :: post, xs.map some⟩).foldr (· * ·) 1 ≤ typemaxInt →
      m664 conv ⟨pre ++ (f, l) :: post, xs.map some⟩ = .error .dimensionMismatch)

theorem size_ones (ls : List Int) (h : ∀ l ∈ ls, 0 ≤ l) :
    SrcArr.size (⟨ls.map fun l => ((1 : Int), l), xs⟩ : SrcArr β) = ls := by
  simp only [SrcArr.size, List.map_map]
  conv => rhs; rw [← List.map_id ls]
  apply List.map_congr_left
  intro l hl; simp only [Function.comp, id]; have := h l hl; omega

theorem p664 : P664 := by
  intro α β conv ls xs h0 hp hl x
  have hs : x.size = ls := size_ones ls h0
  obtain ⟨b, e, hd, ⟨_, hlb, _⟩, _⟩ := newArray_ok (α := α) (dims := ls) h0 (by rw [hp]; exact hl)
  have hlen : length b = xs.length := by simp [length, hd, hp]
  have hck : copytoAxcheck conv b x = convWrites (m1031 conv) b 1 xs := by
    unfold copytoAxcheck
    rw [if_pos]
    · exact readWrite_map conv xs b 1
    · rw [hd]
      have := axcheck_ok ls h0
      have hs' : (ls.map fun d => max 0 (d - 1 + 1)) = ls := by
        conv => rhs; rw [← List.map_id ls]
        apply List.map_congr_left; intro d hd'; simp only [id]; have := h0 d hd'; omega
      rw [hs'] at this; exact this
  have hm : m664 conv x = convWrites (m1031 conv) b 1 xs := by
    unfold m664; rw [hs, e, bind_ok, hck]
  have hw := convWrites_spec conv (m1031 conv) (hw1031 conv) xs b 1 (by omega) (by omega)
  refine ⟨fun er her => by rw [hm]; exact hw.1 er her, fun ys hys => ?_, fun f l pre post hf hfl hp0 hp1 => ?_⟩
  · refine ⟨safeWrites b 1 ys, by rw [hm]; exact hw.2 ys hys, by rw [(safeWrites_spec ys b 1).1, hd],
      contents_safeWrites_full (by rw [hlen, convList_length conv xs ys hys])⟩
  · have hnn : ∀ d ∈ SrcArr.size ⟨pre ++ (f, l) :: post, xs.map some⟩, 0 ≤ d := by
      intro d hd; simp only [SrcArr.size, List.mem_map] at hd; obtain ⟨_, _, rfl⟩ := hd; omega
    obtain ⟨b2, e2, hd2, _, _⟩ := newArray_ok (α := α) hnn hp1
    unfold m664; rw [e2, bind_ok]
    unfold copytoAxcheck; rw [if_neg]
    rw [hd2]
    simp only [SrcArr.size, Bool.and_eq_true, beq_iff_eq, List.length_map, List.all_eq_true, not_and,
      Classical.not_forall]
    intro _
    refine ⟨(max 0 (l - f + 1), (f, l)), ?_, ?_⟩
    · rw [List.mem_iff_getElem]
      refine ⟨pre.length, by simp, ?_⟩
      simp [List.getElem_zip, List.getElem_map, List.getElem_append_right]
    · simp [axEq]; omega

/-- `AbstractArray{T,N}(A)` for an `Array` `A` (base/array.jl:665): a copy of `A`'s
size holding `convert(T, A[i])` in order; a failing conversion propagates. -/
def P665 : Prop := ∀ {α β : Type} (conv : β → R α) (A : Arr β) (xs : List β),
    (∀ d ∈ A.dims, 0 ≤ d) → 0 ≤ length A → length A ≤ typemaxInt → contents A = xs.map some →
    (∀ e, convList conv xs = .error e → m665 conv A = .error e) ∧
    (∀ ys, convList conv xs = .ok ys → ∃ a, m665 conv A = .ok a ∧ a.dims = A.dims ∧ contents a = ys.map some)

theorem p665 : P665 := by
  intro α β conv A xs h0 hl0 hl hc
  have hlen : (xs.length : Int) = length A := by
    have := congrArg List.length hc; simp at this; omega
  obtain ⟨b, e, hd, ⟨_, _, _⟩, _⟩ := newArray_ok (α := α) (dims := A.dims) h0 hl
  have hlb : length b = xs.length := by simp [length, hd]; rw [hlen]; rfl
  have hm : m665 conv A = convWrites (m1031 conv) b 1 xs := by
    unfold m665 m419; rw [e, bind_ok]
    unfold copytoAxcheck; rw [hc, if_pos]
    · exact readWrite_map conv xs b 1
    · rw [hd]
      have := axcheck_ok A.dims h0
      have hs : (A.dims.map fun d => max 0 (d - 1 + 1)) = A.dims := by
        conv => rhs; rw [← List.map_id A.dims]
        apply List.map_congr_left; intro d hd'; simp only [id]; have := h0 d hd'; omega
      rw [hs] at this; exact this
  have hw := convWrites_spec conv (m1031 conv) (hw1031 conv) xs b 1 (by omega) (by omega)
  refine ⟨fun er her => by rw [hm]; exact hw.1 er her, fun ys hys => ?_⟩
  exact ⟨safeWrites b 1 ys, by rw [hm]; exact hw.2 ys hys, by rw [(safeWrites_spec ys b 1).1, hd],
    contents_safeWrites_full (by rw [hlb, convList_length conv xs ys hys])⟩

/-- `convert(Array{T}, a)` (base/array.jl:657): `a` itself when its element type is
already `T`; otherwise a new array of the same size whose elements are `a`'s
values in `T`, or `InexactError` when one does not fit `T`. -/
def P657 : Prop := ∀ (T : NumTy) (x : TArr) (xs : List NV), (∀ d ∈ x.a.dims, 0 ≤ d) → 0 ≤ length x.a →
    length x.a ≤ typemaxInt →
    contents x.a = xs.map some →
    (x.ty = T → m657 T x = .ok x) ∧
    (x.ty ≠ T → (∀ z ∈ xs, fitsTy T z.v) → ∃ a, m657 T x = .ok ⟨T, a⟩ ∧ a.dims = x.a.dims ∧
      contents a = xs.map fun z => some ⟨T, z.v⟩) ∧
    (x.ty ≠ T → isExactTy T → (∃ z ∈ xs, ¬ fitsTy T z.v) → m657 T x = .error .inexact)

theorem p657 : P657 := by
  intro T x xs h0 hl0 hl hc
  have hlen : (xs.length : Int) = length x.a := by
    have := congrArg List.length hc; simp at this; omega
  have hsz := size_ones (xs := (contents x.a)) x.a.dims h0
  have hp : x.a.dims.foldr (· * ·) 1 = (xs.length : Int) := by rw [hlen]; rfl
  have h664 := p664 (nconv T) x.a.dims xs h0 hp (by omega)
  simp only [] at h664
  rw [← hc] at h664
  refine ⟨fun h => by unfold m657; rw [if_pos h], fun hne hf => ?_, fun hne hT hf => ?_⟩
  · obtain ⟨a, e, hd, hca⟩ := h664.2.1 _ ((convList_nconv T xs).1 hf)
    refine ⟨a, ?_, hd, by rw [hca]; simp⟩
    unfold m657; rw [if_neg hne, e, bind_ok]; rfl
  · unfold m657; rw [if_neg hne, h664.1 _ ((convList_nconv T xs).2 hT hf), bind_error]

end JuliaLean.MultidimCov.ArrayV2
