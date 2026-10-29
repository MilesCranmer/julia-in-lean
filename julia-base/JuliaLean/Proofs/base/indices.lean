import JuliaLean.base.indices
import JuliaLean.base.array
import JuliaLean.Proofs.base.int
import JuliaLean.Proofs.base.promotion
import JuliaLean.Registry.Types

/-!
# Properties of `base/indices.jl`

Specifications of the methods modelled in `JuliaLean.base.indices`, stated as the docstrings,
the manual or obvious invariants promise them, with their proofs and refutations.

Callees from other Julia files are the model's typed parameters. Where a property needs their
behaviour it assumes only their documented interface laws: `RangeLaws` for the `range.jl`
methods on `Base.OneTo` and `UnitRange`, and laws such as "`checkbounds(A, i)` succeeds exactly
when `i` lies in `eachindex(A)`" stated next to each property.

Specification vocabulary: `fitsInt z` says `Int` can represent `z`; an axis value is described
by its `(first, last)` pair, and the values of a unit range `a:b` are the integers from `a` to `b`.
-/

namespace JuliaLean.Proofs.base.indices

open JuliaLean JuliaLean.base.indices JuliaLean.base.promotion JuliaLean.Registry

/-! ## Specification vocabulary -/

/-- `Int` can represent the integer `z`. -/
def fitsInt (z : Int) : Prop := IntTy.min .i64 ≤ z ∧ z ≤ IntTy.max .i64

instance (z : Int) : Decidable (fitsInt z) := by unfold fitsInt; exact inferInstance

/-- The documented behaviour of the `range.jl` methods on `Base.OneTo(n)` and `a:b`:
`OneTo(n)` holds `1, …, n`, `a:b` holds `a, …, b`, and `axes1` of a range is `OneTo(length)`
(`OneTo` is its own axis). -/
structure RangeLaws (R : RangeCallees) : Prop where
  first_oneTo : ∀ n, R.first (.oneTo n) = int 1
  last_oneTo : ∀ n, R.last (.oneTo n) = n
  first_unitRange : ∀ a b, R.first (.unitRange a b) = a
  last_unitRange : ∀ a b, R.last (.unitRange a b) = b
  length_oneTo : ∀ n, R.length (.oneTo n) = n
  length_unitRange : ∀ a b, R.length (.unitRange a b) = int (b.val - a.val + 1)
  axes1_oneTo : ∀ n, R.axes1 (.oneTo n) = .oneTo n
  axes1_unitRange : ∀ a b, R.axes1 (.unitRange a b) = .oneTo (int (b.val - a.val + 1))

/-- The `range.jl` callees with exactly the documented behaviour. -/
def lawfulRange : RangeCallees where
  first | .oneTo _ => int 1 | .unitRange a _ => a
  last | .oneTo n => n | .unitRange _ b => b
  length | .oneTo n => n | .unitRange a b => int (b.val - a.val + 1)
  axes1 | .oneTo n => .oneTo n | .unitRange a b => .oneTo (int (b.val - a.val + 1))

theorem lawfulRange_laws : RangeLaws lawfulRange := by
  constructor <;> intros <;> rfl

theorem int_val_of_fits {z : Int} (h : fitsInt z) : (int z).val = z := by
  simp only [int, JInt.lit, JInt.wrap]
  exact wrapInt_of_inRange .i64 z h

theorem fits_val (x : I64) : fitsInt x.val := x.property

/-! ## Index styles -/

theorem IndexStyle_styles_linear (a b : IndexStyle) :
    IndexStyle_styles a b = .linear ↔ a = .linear ∧ b = .linear := by
  cases a <;> cases b <;>
    simp [IndexStyle_styles, IndexStyle_IndexLinear_IndexLinear,
      IndexStyle_IndexStyle_IndexStyle, IndexLinear, IndexCartesian]

/-- `IndexStyle` documentation: the default for a new array type is `IndexCartesian()`;
`Array`, ranges and `LinearIndices` are `IndexLinear()`; a type's own `IndexStyle` method is
used; two styles combine to `IndexLinear()` exactly when both are linear, and so does
`IndexStyle(A, B)` for two arrays; `IndexStyle(Union{}, x...)` has no method: it throws a
`MethodError` for `IndexStyle` that records the arguments `(Union{}, x...)`, whatever they are. -/
def IndexStyleCombination : Prop :=
  IndexStyle_Type (.custom none) = .cartesian ∧
  IndexStyle_Type .array = .linear ∧
  IndexStyle_Type .abstractRange = .linear ∧
  IndexStyle_Type .linearIndices = .linear ∧
  IndexStyle_Type .bottom = .linear ∧
  (∀ s, IndexStyle_Type (.custom (some s)) = s) ∧
  (∀ a b : IndexStyle, IndexStyle_styles a b = .linear ↔ a = .linear ∧ b = .linear) ∧
  (∀ {A : Type} (typeof : A → ArrayType) (a b : A),
    IndexStyle_arrays typeof a [b] = .linear ↔
      IndexStyle_Type (typeof a) = .linear ∧ IndexStyle_Type (typeof b) = .linear) ∧
  (∀ {V : Type} (slurp : List V),
    IndexStyle_Type_Union_slurp (α := IndexStyle) slurp =
      .error ⟨"IndexStyle", .type "Union{}" :: slurp.map .value⟩)

theorem indexStyleCombination_proven : IndexStyleCombination := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, IndexStyle_styles_linear, ?_, fun _ => rfl⟩
  intro A typeof a b
  simp only [IndexStyle_arrays, IndexStyle_AbstractArray_AbstractArray,
    IndexStyle_AbstractArray]
  exact IndexStyle_styles_linear _ _

/-- `IndexStyle(A, B...)` for any number of arrays is `IndexLinear()` exactly when every
argument's style is `IndexLinear()`. -/
def IndexStyleAllLinear : Prop :=
  ∀ {A : Type} (typeof : A → ArrayType) (a : A) (bs : List A),
    IndexStyle_arrays typeof a bs = .linear ↔ ∀ x ∈ a :: bs, IndexStyle_Type (typeof x) = .linear

theorem indexStyleAllLinear_proven : IndexStyleAllLinear := by
  intro A typeof a bs
  induction bs generalizing a with
  | nil => simp [IndexStyle_arrays, IndexStyle_AbstractArray]
  | cons b rest ih =>
    cases rest with
    | nil =>
      simp only [IndexStyle_arrays, IndexStyle_AbstractArray_AbstractArray,
        IndexStyle_AbstractArray, IndexStyle_styles_linear]
      simp
    | cons c cs =>
      simp only [IndexStyle_arrays, IndexStyle_AbstractArray_Vararg, IndexStyle_AbstractArray,
        IndexStyle_styles_linear]
      have h := ih b
      rw [h]
      simp

/-! ## Index conversion -/

/-- The documented behaviour of `convert(Int, i)` on an `Integer` type `I` whose mathematical
values `val` gives (`int.jl` for BitIntegers, `gmp.jl` for `BigInt`, any user `Integer`): the
`Int` with the same value, or `InexactError` when `Int` cannot represent it. -/
def ConvertIntLaw {I : Type} (val : I → Int) (convert_Int : I → IndexResult I64) : Prop :=
  ∀ i, convert_Int i =
    if h : fitsInt (val i) then .ok ⟨val i, h⟩ else .error (.core (.inexactError "Int64"))

theorem convert_Int_BitInteger_law (t : IntTy) :
    ConvertIntLaw (·.val) (convert_Int_BitInteger (t := t)) := by
  intro i
  by_cases h : fitsInt i.val
  · rw [dif_pos h]
    simp [convert_Int_BitInteger, JuliaLean.base.int.convert, JInt.convert, fitsInt] at h ⊢
    simp [h, Except.mapError]
  · rw [dif_neg h]
    simp only [fitsInt] at h
    simp [convert_Int_BitInteger, JuliaLean.base.int.convert, JInt.convert, h,
      Except.mapError, IntTy.name]

theorem convert_ok {I : Type} {val : I → Int} {conv : I → IndexResult I64}
    (hc : ConvertIntLaw val conv) (i : I) (h : fitsInt (val i)) : conv i = .ok ⟨val i, h⟩ := by
  rw [hc i, dif_pos h]

theorem convert_error {I : Type} {val : I → Int} {conv : I → IndexResult I64}
    (hc : ConvertIntLaw val conv) (i : I) (h : ¬ fitsInt (val i)) :
    conv i = .error (.core (.inexactError "Int64")) := by
  rw [hc i, dif_neg h]

theorem to_index_ok {t : IntTy} (i : JInt t) (h : fitsInt i.val) :
    to_index i = .ok ⟨i.val, h⟩ :=
  convert_ok (convert_Int_BitInteger_law t) i h

theorem to_index_error {t : IntTy} (i : JInt t) (h : ¬ fitsInt i.val) :
    to_index i = .error (.core (.inexactError "Int64")) :=
  convert_error (convert_Int_BitInteger_law t) i h

/-- `to_index` docstring: an index of any `Integer` type (every BitInteger, `BigInt`, or a user
type with the documented `convert(Int, i)`) becomes the `Int` with the same value, and one
`Int` cannot represent throws `InexactError`; for BitIntegers this is the `int.jl` conversion.
`to_index(A, i)` defaults to `to_index(i)`. `Bool` and `Colon` are not indices
(`ArgumentError`), nor is an array of arrays or colons, nor any other type: those throw
`ArgumentError` naming the offending index and its type. -/
def ToIndexConversion : Prop :=
  (∀ {I : Type} (val : I → Int) (convert_Int : I → IndexResult I64),
    ConvertIntLaw val convert_Int → ∀ i : I,
      (fitsInt (val i) → ∃ k, to_index_Integer convert_Int i = .ok k ∧ k.val = val i) ∧
      (¬ fitsInt (val i) →
        to_index_Integer convert_Int i = .error (.core (.inexactError "Int64")))) ∧
  (∀ t : IntTy, ConvertIntLaw (·.val) (convert_Int_BitInteger (t := t))) ∧
  (∀ {A I : Type} (val : I → Int) (convert_Int : I → IndexResult I64),
    ConvertIntLaw val convert_Int → ∀ (a : A) (i : I),
      to_index_A_i (to_index_Integer convert_Int) a i = to_index_Integer convert_Int i) ∧
  (∀ b : Bool, to_index_Bool b =
    .error (.argumentError ("invalid index: " ++ toString b ++ " of type Bool"))) ∧
  (∃ m, to_index_Colon = .error (.argumentError m)) ∧
  (∀ {I O : Type} (limitrepr : I → String) (typeof : I → PType) (i : I), ∃ parts,
    to_index_Any (O := O) limitrepr typeof i = .error ⟨⟨parts⟩⟩ ∧
      LazyPart.string (limitrepr i) ∈ parts ∧ LazyPart.type (typeof i) ∈ parts) ∧
  (∀ {M O : Type} (limitrepr : M → String) (typeof : M → PType) (I : M), ∃ parts,
    to_index_AbstractArray_AbstractArray (O := O) limitrepr typeof I = .error ⟨⟨parts⟩⟩ ∧
      LazyPart.string (limitrepr I) ∈ parts ∧ LazyPart.type (typeof I) ∈ parts)

theorem toIndexConversion_proven : ToIndexConversion := by
  refine ⟨fun val conv hc i => ⟨fun h => ⟨_, convert_ok hc i h, rfl⟩,
      fun h => convert_error hc i h⟩, convert_Int_BitInteger_law,
    fun _ _ _ _ _ => rfl, fun _ => rfl, ⟨_, rfl⟩, fun _ _ _ => ⟨_, rfl, by simp, by simp⟩,
    fun _ _ _ => ⟨_, rfl, by simp, by simp⟩⟩

theorem to_index_Array_UInt_val (i : JInt .u64) :
    (to_index_Array_UInt i).val = wrapInt .i64 i.val := by
  unfold to_index_Array_UInt
  exact JuliaLean.Proofs.base.int.bitcast_val .i64 i _

/-- Indexing a vector `v` with an integer of any BitInteger type that `to_index(v, i)` accepts
(every `UInt`, and every value `Int` represents) returns `v[i]` when `1 ≤ i ≤ length(v)` and
throws `BoundsError` otherwise (`checkbounds` docstring; `to_index`, including the `UInt`
reinterpretation at `base/indices.jl:247`). -/
def GetindexCheckbounds : Prop :=
  ∀ {α : Type} (v : List α) (t : IntTy) (i : JInt t),
    (t = .u64 ∨ fitsInt i.val) → fitsInt v.length →
    ∃ k, to_index_Array t v i = .ok k ∧
      (if 1 ≤ i.val ∧ i.val ≤ v.length then
        ∃ x, v[(i.val - 1).toNat]? = some x ∧ JuliaLean.base.array.vectorGet v k = .ok x
      else JuliaLean.base.array.vectorGet v k = .error .bounds)

theorem vectorGet_spec {α : Type} (v : List α) (k : I64) :
    (if 1 ≤ k.val ∧ k.val ≤ v.length then
        ∃ x, v[(k.val - 1).toNat]? = some x ∧ JuliaLean.base.array.vectorGet v k = .ok x
      else JuliaLean.base.array.vectorGet v k = .error .bounds) := by
  unfold JuliaLean.base.array.vectorGet
  split
  · rename_i h
    have hl : (k.val - 1).toNat < v.length := by omega
    have hl' : k.val.toNat - 1 < v.length := by omega
    have he : (k.val - 1).toNat = k.val.toNat - 1 := by omega
    refine ⟨v[(k.val - 1).toNat], ?_, ?_⟩
    · simp [hl]
    · simp [h, hl']
  · rename_i h
    simp [h]

theorem getindexCheckbounds_proven : GetindexCheckbounds := by
  intro α v t i hacc hlen
  rcases (Classical.em (t = .u64)).symm with ht | ht
  · have hfit := hacc.resolve_left ht
    have hrw : to_index_Array t v i = to_index i := by
      cases t <;> first | rfl | exact absurd rfl ht
    refine ⟨⟨i.val, hfit⟩, by rw [hrw, to_index_ok i hfit], ?_⟩
    exact vectorGet_spec v ⟨i.val, hfit⟩
  cases ht
  -- `UInt64`: reinterpretation
  refine ⟨to_index_Array_UInt i, rfl, ?_⟩
  have hv := to_index_Array_UInt_val i
  have hi : (0 : Int) ≤ i.val ∧ i.val ≤ 18446744073709551615 := i.property
  have hlen' : (v.length : Int) ≤ 9223372036854775807 := hlen.2
  clear hlen
  have spec := vectorGet_spec v (to_index_Array_UInt i)
  by_cases hin : 1 ≤ i.val ∧ i.val ≤ v.length
  · have heq : (to_index_Array_UInt i).val = i.val := by
      rw [hv]; simp only [wrapInt, IntTy.signed, IntTy.bits]; simp; omega
    rw [if_pos hin]
    rw [heq, if_pos hin] at spec
    exact spec
  · rw [if_neg hin]
    have hk : ¬ (1 ≤ (to_index_Array_UInt i).val ∧ (to_index_Array_UInt i).val ≤ v.length) := by
      rw [hv]; simp only [wrapInt, IntTy.signed, IntTy.bits]; simp; omega
    rw [if_neg hk] at spec
    exact spec

/-- `LinearIndices(v)[i]` through the generic `getindex`: `to_indices(L, (i,))`
(`base/indices.jl:311, 322`) and then `getindex(::LinearIndices, ::Int)`. -/
def linearGetindexInteger {R J : Type} (checkbounds : LinearIndices R → I64 → IndexResult Unit)
    (eachindex : IndexStyle → LinearIndices R → J) (safe_tail : List J → List J)
    (L : LinearIndices R) {t : IntTy} (i : JInt t) : IndexResult I64 := do
  let J ← to_indices_A_Tuple1 eachindex
    (to_indices_A_inds_Tuple (to_index_A_i to_index) safe_tail) L i
  match J with
  | [k] => getindex_LinearIndices_Int checkbounds L k
  | _ => .error .boundsError

/-- `checkbounds`, `BoundsError` and `to_index` docstrings: an index for which
`checkbounds(Bool, A, i)` is false is out of bounds, and indexing `A` with it throws
`BoundsError` ("an indexing operation into an array tried to access an out-of-bounds
element"), the error `checkbounds(A, i)` throws, unless converting the index to an `Int`
(`to_index`: "Convert index `i` to an `Int`") fails first with `InexactError`. A vector `v` and
`LinearIndices(v)` have the same axes and the same `checkbounds`, so indexing both with the
same integer `i` of any BitInteger type outside `1:length(v)` throws the same one of these two
exceptions. -/
def OutOfRangeBoundsError : Prop :=
  ∀ {α R J : Type} (v : List α) (L : LinearIndices R)
    (checkbounds : LinearIndices R → I64 → IndexResult Unit)
    (eachindex : IndexStyle → LinearIndices R → J) (safe_tail : List J → List J)
    (t : IntTy) (i : JInt t),
    (∀ k, checkbounds L k =
      if 1 ≤ k.val ∧ k.val ≤ v.length then .ok () else .error .boundsError) →
    ¬ (1 ≤ i.val ∧ i.val ≤ v.length) →
    ((∃ k, to_index_Array t v i = .ok k ∧ JuliaLean.base.array.vectorGet v k = .error .bounds) ∧
        linearGetindexInteger checkbounds eachindex safe_tail L i = .error .boundsError) ∨
      (∃ s, to_index_Array t v i = .error (.core (.inexactError s)) ∧
        linearGetindexInteger checkbounds eachindex safe_tail L i =
          .error (.core (.inexactError s)))

/-- `v[UInt(2)^63]` throws `BoundsError` (the `Array` method reinterprets the `UInt`), while
`LinearIndices(v)[UInt(2)^63]` throws `InexactError`. -/
theorem outOfRangeBoundsError_refuted : ¬ OutOfRangeBoundsError := by
  intro h
  let i : JInt .u64 := ⟨2 ^ 63, by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]⟩
  have hfit : ¬ fitsInt i.val := by simp [i, fitsInt, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
  have hA : to_index_Array .u64 [(), (), ()] i = .ok (to_index_Array_UInt i) := rfl
  rcases h [(), (), ()] (⟨[]⟩ : LinearIndices Unit)
    (fun _ k => if 1 ≤ k.val ∧ k.val ≤ 3 then .ok () else .error .boundsError)
    (fun _ _ => ()) id .u64 i (fun _ => rfl) (by simp [i]) with ⟨-, hl⟩ | ⟨s, hv, -⟩
  · simp [linearGetindexInteger, to_indices_A_Tuple1, to_indices_A_inds_Tuple, to_index_A_i,
      to_index_error i hfit, bind, Except.bind] at hl
  · rw [hA] at hv
    cases hv

/-! ## Index tuple conversion -/

/-- `to_indices` docstring: a tuple of integer indices of any `Integer` type (BitIntegers,
`BigInt`, user integers with the documented `convert(Int, i)`) is converted element by element
with `to_index`, in order and without bounds checking, so every value survives unchanged when
`Int` represents it and the first unrepresentable one throws `InexactError`; a tuple of `Int`s
is returned as is, also through the per-dimension walk `to_indices(A, inds, I)`; the empty
tuple converts to the empty tuple. -/
def ToIndicesIntegers : Prop :=
  (∀ {A J I : Type} (val : I → Int) (convert_Int : I → IndexResult I64),
    ConvertIntLaw val convert_Int → ∀ (safe_tail : List J → List J) (a : A) (I' : List I),
    (∀ i ∈ I', fitsInt (val i)) →
    ∃ out, to_indices_A_Integers
        (to_indices_A_inds_Tuple (to_index_A_i (to_index_Integer convert_Int)) safe_tail)
        a I' = .ok out ∧ out.map (·.val) = I'.map val) ∧
  (∀ {A J I : Type} (val : I → Int) (convert_Int : I → IndexResult I64),
    ConvertIntLaw val convert_Int → ∀ (safe_tail : List J → List J) (a : A) (I' : List I),
    (∃ i ∈ I', ¬ fitsInt (val i)) →
    to_indices_A_Integers
        (to_indices_A_inds_Tuple (to_index_A_i (to_index_Integer convert_Int)) safe_tail) a I' =
      .error (.core (.inexactError "Int64"))) ∧
  (∀ {A J : Type} (safe_tail : List J → List J) (a : A) (inds : List J) (I' : List I64),
    to_indices_A_inds_Tuple (to_index_A_i to_index) safe_tail a inds I' = .ok I' ∧
    to_indices_A_Ints a I' = I') ∧
  (∀ {A J O : Type} (a : A) (inds : List J),
    to_indices_A_Tuple0 (O := O) a = [] ∧ to_indices_A_inds_Tuple0 (O := O) a inds = [])

theorem to_indices_walk_fits {A J I : Type} {val : I → Int} {conv : I → IndexResult I64}
    (hc : ConvertIntLaw val conv) (safe_tail : List J → List J) (a : A) :
    ∀ (I' : List I) (inds : List J), (∀ i ∈ I', fitsInt (val i)) →
      ∃ out, to_indices_A_inds_Tuple (to_index_A_i (to_index_Integer conv)) safe_tail a inds I' =
        .ok out ∧ out.map (·.val) = I'.map val
  | [], _, _ => ⟨[], rfl, rfl⟩
  | i :: rest, inds, h => by
    obtain ⟨out, hout, hval⟩ :=
      to_indices_walk_fits hc safe_tail a rest (safe_tail inds) (fun j hj => h j (by simp [hj]))
    refine ⟨⟨val i, h i (by simp)⟩ :: out, ?_, ?_⟩
    · simp [to_indices_A_inds_Tuple, to_index_A_i, to_index_Integer,
        convert_ok hc i (h i (by simp)), hout, bind, Except.bind, pure, Except.pure]
    · simp [hval]

theorem to_indices_walk_error {A J I : Type} {val : I → Int} {conv : I → IndexResult I64}
    (hc : ConvertIntLaw val conv) (safe_tail : List J → List J) (a : A) :
    ∀ (I' : List I) (inds : List J), (∃ i ∈ I', ¬ fitsInt (val i)) →
      to_indices_A_inds_Tuple (to_index_A_i (to_index_Integer conv)) safe_tail a inds I' =
        .error (.core (.inexactError "Int64"))
  | [], _, ⟨_, hmem, _⟩ => by simp at hmem
  | i :: rest, inds, h => by
    by_cases hi : fitsInt (val i)
    · have hrest : ∃ j ∈ rest, ¬ fitsInt (val j) := by
        obtain ⟨j, hj, hn⟩ := h
        simp at hj
        rcases hj with rfl | hj
        · exact absurd hi hn
        · exact ⟨j, hj, hn⟩
      simp [to_indices_A_inds_Tuple, to_index_A_i, to_index_Integer, convert_ok hc i hi,
        to_indices_walk_error hc safe_tail a rest (safe_tail inds) hrest, bind, Except.bind]
    · simp [to_indices_A_inds_Tuple, to_index_A_i, to_index_Integer, convert_error hc i hi,
        bind, Except.bind]

theorem to_indices_walk_Int {A J : Type} (safe_tail : List J → List J) (a : A) :
    ∀ (I : List I64) (inds : List J),
      to_indices_A_inds_Tuple (to_index_A_i to_index) safe_tail a inds I = .ok I
  | [], _ => rfl
  | i :: rest, inds => by
    simp [to_indices_A_inds_Tuple, to_index_A_i, to_index_ok i (fits_val i),
      to_indices_walk_Int safe_tail a rest (safe_tail inds), bind, Except.bind, pure,
      Except.pure]

theorem toIndicesIntegers_proven : ToIndicesIntegers :=
  ⟨fun _ _ hc safe_tail a I h => to_indices_walk_fits hc safe_tail a I [] h,
   fun _ _ hc safe_tail a I h => to_indices_walk_error hc safe_tail a I [] h,
   fun safe_tail a inds I => ⟨to_indices_walk_Int safe_tail a I inds, rfl⟩,
   fun _ _ => ⟨rfl, rfl⟩⟩

/-! ## Shape promotion -/

theorem List_forM_cons {m : Type → Type} [Monad m] {α : Type} (x : α) (xs : List α)
    (f : α → m PUnit) : (x :: xs).forM f = (f x >>= fun _ => xs.forM f) := rfl

theorem List_forM_append {α : Type} (l₁ l₂ : List α) (f : α → IndexResult Unit) :
    (l₁ ++ l₂).forM f = (l₁.forM f >>= fun _ => l₂.forM f) := by
  induction l₁ with
  | nil => show l₂.forM f = (pure () >>= fun _ => l₂.forM f); rw [pure_bind]
  | cons x xs ih =>
    rw [List.cons_append, List_forM_cons, List_forM_cons, ih, bind_assoc]

theorem forM_congr_mem {l : List Nat} {f g : Nat → IndexResult Unit}
    (h : ∀ i ∈ l, f i = g i) : l.forM f = l.forM g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List_forM_cons, List_forM_cons, h x (by simp),
      ih (fun i hi => h i (by simp [hi]))]

theorem forM_ite (l : List Nat) (P : Nat → Prop) [DecidablePred P] (e : Nat → IndexError) :
    l.forM (fun i => if P i then (Except.error (e i) : IndexResult Unit) else pure ()) =
      match l.find? (fun i => decide (P i)) with
      | some i => .error (e i)
      | none => .ok () := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List_forM_cons]
    by_cases hx : P x
    · simp [hx, List.find?_cons, bind, Except.bind]
    · simp only [hx, if_false, List.find?_cons, decide_false]
      rw [← ih, pure_bind]

theorem find_range' (p : Nat → Bool) : ∀ (s n : Nat),
    match (List.range' s n).find? p with
    | some k => s ≤ k ∧ k < s + n ∧ p k = true ∧ ∀ j, s ≤ j → j < k → p j = false
    | none => ∀ j, s ≤ j → j < s + n → p j = false
  | s, 0 => by simp only [List.range'_zero, List.find?_nil]; intro j h1 h2; omega
  | s, n + 1 => by
    have ih := find_range' p (s + 1) n
    simp only [List.range'_succ, List.find?_cons]
    by_cases hs : p s = true
    · simp only [hs]
      exact ⟨Nat.le_refl s, by omega, by simp [hs], fun j h1 h2 => by omega⟩
    · simp only [Bool.not_eq_true] at hs
      simp only [hs]
      split at ih
      · rename_i k hk
        rw [hk]
        obtain ⟨h1, h2, h3, h4⟩ := ih
        refine ⟨by omega, by omega, h3, fun j hj1 hj2 => ?_⟩
        by_cases hj : j = s
        · subst hj; exact hs
        · exact h4 j (by omega) hj2
      · rename_i hk
        rw [hk]
        intro j hj1 hj2
        by_cases hj : j = s
        · subst hj; exact hs
        · exact ih j (by omega) (by omega)

/-- Dimension `k` (1-based) of the longer shape `long` is incompatible with the shorter shape
`short`: within `short` the sizes differ, beyond it the size is not 1. -/
def DimBad (long short : List I64) (k : Nat) : Prop :=
  if k ≤ short.length then long[k - 1]? ≠ short[k - 1]? else long[k - 1]? ≠ some (int 1)

instance (long short : List I64) (k : Nat) : Decidable (DimBad long short k) := by
  unfold DimBad; exact inferInstance

/-- `long` and `short` are compatible: equal sizes in the common dimensions and trailing
singleton dimensions. -/
def DimsCompatible (long short : List I64) : Prop :=
  ∀ k, 1 ≤ k → k ≤ long.length → ¬ DimBad long short k

/-- `k` is the first incompatible dimension. -/
def FirstMismatch (long short : List I64) (k : Nat) : Prop :=
  1 ≤ k ∧ k ≤ long.length ∧ DimBad long short k ∧ ∀ j, 1 ≤ j → j < k → ¬ DimBad long short j

/-- The documented mismatch message: both shapes as printed tuples (the second omitted when the
mismatch is a trailing dimension) and the mismatching dimension. -/
def dimsMessage (printTuple : List I64 → String) (a : List I64) (b : Option (List I64))
    (k : Nat) : String :=
  "a has " ++ "size " ++ printTuple a ++
    (match b with | some b => ", b has " ++ "size " ++ printTuple b | none => "") ++
    ", mismatch at dim " ++ toString (int k).val

/-- The documented behaviour of `IOBuffer()`, `print` and `takestring!`: a new buffer is
empty, and `takestring!` returns everything printed so far, in order; printing a tuple `t`
writes `text t` and printing an `Int` writes its decimal digits. -/
structure PrintLaws {A B : Type} (C : ShapeCallees A B) (text : List A → String) : Prop where
  empty : C.takestring C.IOBuffer = ""
  string : ∀ b s, C.takestring (C.printString b s) = C.takestring b ++ s
  tuple : ∀ b t, C.takestring (C.printTuple b t) = C.takestring b ++ text t
  int : ∀ b n, C.takestring (C.printInt b n) = C.takestring b ++ toString n.val

/-- The tuple entries of `promote_shape` on `Dims` are `Int`s: never `OneTo`, always `Int`;
and printing obeys `PrintLaws`. -/
def DimsEntries {B : Type} (C : ShapeCallees I64 B) (text : List I64 → String) : Prop :=
  C.isOneTo = (fun _ => false) ∧ C.isInt = (fun _ => true) ∧ PrintLaws C text

theorem throw_dims {B : Type} (C : ShapeCallees I64 B) (text : List I64 → String)
    (hC : DimsEntries C text) (a : List I64) (ha : a ≠ [])
    (b : Option (List I64)) (k : Nat) :
    throw_promote_shape_mismatch C a b (some (int k)) =
      .error (.dimensionMismatch (dimsMessage text a b k)) := by
  obtain ⟨hO, hI, hP⟩ := hC
  obtain ⟨x, xs, rfl⟩ : ∃ x xs, a = x :: xs := by
    cases a with
    | nil => exact absurd rfl ha
    | cons x xs => exact ⟨x, xs, rfl⟩
  cases b <;> simp [throw_promote_shape_mismatch, hO, hI, hP.empty, hP.string, hP.tuple,
    hP.int, dimsMessage, String.append_assoc]

theorem getElem!_eq {α : Type} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
    l[i]! = l[i] := by
  simp [h]

/-- The checks of `promote_shape(a::Dims, b::Dims)` once `a` is the longer shape. -/
theorem promote_shape_Dims_long {B : Type} (C : ShapeCallees I64 B) (text : List I64 → String)
    (hC : DimsEntries C text) (a b : Dims)
    (h : ¬ a.length < b.length) :
    promote_shape_Dims C a b =
      match (List.range' 1 a.length).find? (fun k => decide (DimBad a b k)) with
      | some k => .error (.dimensionMismatch
          (dimsMessage text a (if k ≤ b.length then some b else none) k))
      | none => .ok a := by
  rw [promote_shape_Dims, if_neg h]
  have hlen : b.length ≤ a.length := by omega
  let err : Nat → IndexError := fun k =>
    .dimensionMismatch (dimsMessage text a (if k ≤ b.length then some b else none) k)
  have e1 : (List.range' 1 b.length).forM (fun i =>
      if a[i - 1]! ≠ b[i - 1]! then throw_promote_shape_mismatch C a (some b) (some (int i))
      else pure ()) =
      (List.range' 1 b.length).forM (fun i =>
        if DimBad a b i then (Except.error (err i) : IndexResult Unit) else pure ()) := by
    apply forM_congr_mem
    intro i hi
    simp only [List.mem_range'_1] at hi
    have ha' : i - 1 < a.length := by omega
    have hb' : i - 1 < b.length := by omega
    have hbad : DimBad a b i ↔ a[i - 1]! ≠ b[i - 1]! := by
      simp only [DimBad, if_pos (show i ≤ b.length by omega), getElem!_eq a _ ha',
        getElem!_eq b _ hb', List.getElem?_eq_getElem ha', List.getElem?_eq_getElem hb',
        ne_eq, Option.some.injEq]
    by_cases hd : a[i - 1]! ≠ b[i - 1]!
    · have hne : a ≠ [] := by intro h0; simp [h0] at ha'
      rw [if_pos hd, if_pos (hbad.mpr hd), throw_dims C text hC a hne]
      simp [err, show i ≤ b.length by omega]
    · rw [if_neg hd, if_neg (fun h => hd (hbad.mp h))]
  have e2 : (List.range' (b.length + 1) (a.length - b.length)).forM (fun i =>
      if a[i - 1]! ≠ int 1 then throw_promote_shape_mismatch C a none (some (int i))
      else pure ()) =
      (List.range' (b.length + 1) (a.length - b.length)).forM (fun i =>
        if DimBad a b i then (Except.error (err i) : IndexResult Unit) else pure ()) := by
    apply forM_congr_mem
    intro i hi
    simp only [List.mem_range'_1] at hi
    have ha' : i - 1 < a.length := by omega
    have hbad : DimBad a b i ↔ a[i - 1]! ≠ int 1 := by
      simp only [DimBad, if_neg (show ¬ i ≤ b.length by omega), getElem!_eq a _ ha',
        List.getElem?_eq_getElem ha', ne_eq, Option.some.injEq]
    by_cases hd : a[i - 1]! ≠ int 1
    · have hne : a ≠ [] := by intro h0; simp [h0] at ha'
      rw [if_pos hd, if_pos (hbad.mpr hd), throw_dims C text hC a hne]
      simp [err, show ¬ i ≤ b.length by omega]
    · rw [if_neg hd, if_neg (fun h => hd (hbad.mp h))]
  rw [e1, e2]
  have happ : List.range' 1 b.length ++ List.range' (b.length + 1) (a.length - b.length) =
      List.range' 1 a.length := by
    rw [show b.length + 1 = 1 + 1 * b.length by omega, List.range'_append]
    congr 1; omega
  have hcomb : ((List.range' 1 b.length).forM (fun i =>
        if DimBad a b i then (Except.error (err i) : IndexResult Unit) else pure ()) >>= fun _ =>
      (List.range' (b.length + 1) (a.length - b.length)).forM (fun i =>
        if DimBad a b i then (Except.error (err i) : IndexResult Unit) else pure ())) =
      (List.range' 1 a.length).forM (fun i =>
        if DimBad a b i then (Except.error (err i) : IndexResult Unit) else pure ()) := by
    rw [← happ, List_forM_append]
  rw [← bind_assoc, hcomb, forM_ite]
  split <;> rfl

/-- `promote_shape` docstring: two `Dims` shapes are compatible when they agree in their common
dimensions and the longer one has only trailing singleton dimensions; then the longer shape is
returned. Otherwise `DimensionMismatch` is thrown, naming the first incompatible dimension and
printing both shapes (only the longer one for a trailing dimension). The fixed-length methods
for one- and two-dimensional shapes agree with this rule, and `promote_shape((), ())` is `()`. -/
def PromoteShapeDims : Prop :=
  (∀ {B : Type} (C : ShapeCallees I64 B) (text : List I64 → String), DimsEntries C text → ∀ a b : Dims,
    let long := if a.length < b.length then b else a
    let short := if a.length < b.length then a else b
    (DimsCompatible long short → promote_shape_Dims C a b = .ok long) ∧
    (∀ k, FirstMismatch long short k → promote_shape_Dims C a b = .error (.dimensionMismatch
      (dimsMessage text long (if k ≤ short.length then some short else none) k)))) ∧
  promote_shape_Tuple0_Tuple0 (α := I64) = []

theorem promote_shape_Dims_spec {B : Type} (C : ShapeCallees I64 B) (text : List I64 → String)
    (hC : DimsEntries C text) (a b : Dims)
    (h : ¬ a.length < b.length) :
    (DimsCompatible a b → promote_shape_Dims C a b = .ok a) ∧
    (∀ k, FirstMismatch a b k → promote_shape_Dims C a b = .error (.dimensionMismatch
      (dimsMessage text a (if k ≤ b.length then some b else none) k))) := by
  rw [promote_shape_Dims_long C text hC a b h]
  have hf := find_range' (fun k => decide (DimBad a b k)) 1 a.length
  split at hf
  · rename_i k hk
    obtain ⟨h1, h2, h3, h4⟩ := hf
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h3 h4
    refine ⟨fun hc => absurd h3 (hc k h1 (by omega)), fun j hj => ?_⟩
    obtain ⟨j1, j2, j3, j4⟩ := hj
    have : j = k := by
      rcases Nat.lt_trichotomy j k with hlt | heq | hgt
      · exact absurd j3 (h4 j j1 hlt)
      · exact heq
      · exact absurd h3 (j4 k h1 hgt)
    subst this
    rfl
  · rename_i hk
    simp only [decide_eq_false_iff_not] at hf
    refine ⟨fun _ => rfl, fun k hk' => ?_⟩
    obtain ⟨k1, k2, k3, _⟩ := hk'
    exact absurd k3 (hf k k1 (by omega))

theorem promoteShapeDims_proven : PromoteShapeDims := by
  refine ⟨fun {B} C text hC a b => ?_, rfl⟩
  by_cases h : a.length < b.length
  · simp only [if_pos h]
    have hs : promote_shape_Dims C a b = promote_shape_Dims C b a := by
      rw [promote_shape_Dims, if_pos h]
    rw [hs]
    exact promote_shape_Dims_spec C text hC b a (by omega)
  · simp only [if_neg h]
    exact promote_shape_Dims_spec C text hC a b h

/-- The outcome of a fixed-length `promote_shape` method matches the general `Dims` method:
the same shape when it succeeds, `DimensionMismatch` from both otherwise. -/
def SameOutcome {α : Type} (x : IndexResult α) (y : IndexResult Dims) (f : α → Dims) : Prop :=
  match x with
  | .ok v => y = .ok (f v)
  | .error e => (∃ m, e = .dimensionMismatch m) ∧ ∃ m, y = .error (.dimensionMismatch m)

/-- `promote_shape` on `Tuple{Int}` and `Tuple{Int,Int}` shapes (`base/indices.jl:139-154`)
behaves as the general method on the same shapes. -/
def PromoteShapeFixed : Prop :=
  ∀ {B : Type} (C : ShapeCallees I64 B) (text : List I64 → String), DimsEntries C text →
    (∀ a b : I64, SameOutcome (promote_shape_Int_Int C a b) (promote_shape_Dims C [a] [b])
      (fun x => [x])) ∧
    (∀ (a : I64 × I64) (b : I64), SameOutcome (promote_shape_IntInt_Int C a b)
      (promote_shape_Dims C [a.1, a.2] [b]) (fun x => [x.1, x.2])) ∧
    (∀ (a : I64) (b : I64 × I64), SameOutcome (promote_shape_Int_IntInt C a b)
      (promote_shape_Dims C [a] [b.1, b.2]) (fun x => [x.1, x.2])) ∧
    (∀ a b : I64 × I64, SameOutcome (promote_shape_IntInt_IntInt C a b)
      (promote_shape_Dims C [a.1, a.2] [b.1, b.2]) (fun x => [x.1, x.2]))

theorem throw_dims_none {B : Type} (C : ShapeCallees I64 B) (text : List I64 → String)
    (hC : DimsEntries C text) (x : I64) (xs : List I64)
    (b : Option (List I64)) :
    throw_promote_shape_mismatch C (x :: xs) b none = .error (.dimensionMismatch
      ("a has " ++ "size " ++ text (x :: xs) ++
        (match b with | some b => ", b has " ++ "size " ++ text b | none => ""))) := by
  obtain ⟨hO, hI, hP⟩ := hC
  cases b <;> simp [throw_promote_shape_mismatch, hO, hI, hP.empty, hP.string, hP.tuple,
    String.append_assoc]

theorem promoteShapeFixed_proven : PromoteShapeFixed := by
  intro B C text hC
  refine ⟨fun a b => ?_, fun ⟨a1, a2⟩ b => ?_, fun a ⟨b1, b2⟩ => ?_, fun ⟨a1, a2⟩ ⟨b1, b2⟩ => ?_⟩
  · rw [promote_shape_Dims_long C text hC [a] [b] (by simp)]
    by_cases h : a = b <;>
      simp [promote_shape_Int_Int, h, throw_dims_none C text hC, SameOutcome, DimBad, List.range',
        bind, Except.bind, pure, Except.pure]
  · rw [promote_shape_Dims_long C text hC [a1, a2] [b] (by simp)]
    by_cases h1 : a1 = b <;> by_cases h2 : a2 = int 1 <;>
      simp [promote_shape_IntInt_Int, h1, h2, throw_dims_none C text hC, SameOutcome, DimBad,
        List.range', bind, Except.bind, pure, Except.pure]
  · rw [show promote_shape_Dims C [a] [b1, b2] = promote_shape_Dims C [b1, b2] [a] by
      rw [promote_shape_Dims]; simp]
    rw [promote_shape_Dims_long C text hC [b1, b2] [a] (by simp)]
    by_cases h1 : b1 = a <;> by_cases h2 : b2 = int 1 <;>
      simp [promote_shape_Int_IntInt, promote_shape_IntInt_Int, h1, h2, throw_dims_none C text hC,
        SameOutcome, DimBad, List.range', bind, Except.bind, pure, Except.pure]
  · rw [promote_shape_Dims_long C text hC [a1, a2] [b1, b2] (by simp)]
    by_cases h1 : a1 = b1 <;> by_cases h2 : a2 = b2 <;>
      simp [promote_shape_IntInt_IntInt, h1, h2, throw_dims_none C text hC, SameOutcome, DimBad,
        List.range', bind, Except.bind, pure, Except.pure]

/-! ## Shape promotion of axes -/

theorem forM_ite_ok (l : List Nat) (P : Nat → Prop) [DecidablePred P]
    (X : Nat → IndexResult Unit) (hX : ∀ i, ∃ e, X i = .error e) :
    l.forM (fun i => if P i then X i else pure ()) = .ok () ↔ ∀ i ∈ l, ¬ P i := by
  induction l with
  | nil => simp; rfl
  | cons x xs ih =>
    rw [List_forM_cons]
    by_cases hx : P x
    · obtain ⟨e, he⟩ := hX x
      simp only [hx, if_true, he]
      constructor
      · intro h; cases h
      · intro h; exact absurd hx (h x (by simp))
    · simp only [hx, if_false, pure_bind, ih]
      constructor
      · intro h i hi
        simp at hi
        rcases hi with rfl | hi
        · exact hx
        · exact h i hi
      · intro h i hi; exact h i (by simp [hi])

theorem except_cases {α : Type} (r : IndexResult α) : (∃ v, r = .ok v) ∨ ∃ e, r = .error e := by
  cases r with
  | ok v => exact .inl ⟨v, rfl⟩
  | error e => exact .inr ⟨e, rfl⟩

theorem throw_promote_shape_mismatch_error {A B : Type} (C : ShapeCallees A B) (a : List A)
    (b : Option (List A)) (i : Option I64) :
    ∃ e, throw_promote_shape_mismatch C a b i = .error e := by
  unfold throw_promote_shape_mismatch
  simp only [bind, Except.bind]
  repeat' split
  all_goals first | exact ⟨_, rfl⟩ | skip
  all_goals simp_all

/-- Axis tuples `long` and `short` are compatible: the axes agree (`==`) in the common
dimensions and every further axis of `long` equals `1:1`. -/
def AxesCompatible {R : Type} [Inhabited R] (eq : R → R → Bool) (one : R)
    (long short : List R) : Prop :=
  (∀ i, 1 ≤ i → i ≤ short.length → eq long[i - 1]! short[i - 1]! = true) ∧
  (∀ i, short.length < i → i ≤ long.length → eq long[i - 1]! one = true)

/-- `promote_shape` docstring for axes (`promote_shape(a::Indices, b::Indices)` and
`promote_shape(a::AbstractArray, b::AbstractArray)`, which compares `axes(a)` and `axes(b)`):
compatible axis tuples give the longer one, any other pair throws. -/
def PromoteShapeAxes : Prop :=
  ∀ {R X B : Type} [Inhabited R] (C : ShapeCallees R B) (eq : R → R → Bool) (one : R),
    C.colon (int 1) (int 1) = .ok one →
    (∀ a b : List R,
      let long := if a.length < b.length then b else a
      let short := if a.length < b.length then a else b
      (AxesCompatible eq one long short → promote_shape_Indices C eq a b = .ok long) ∧
      (¬ AxesCompatible eq one long short → ∃ e, promote_shape_Indices C eq a b = .error e)) ∧
    (∀ (axes : X → IndexResult (List R)) (x y : X) (ax ay : List R),
      axes x = .ok ax → axes y = .ok ay →
      let long := if ax.length < ay.length then ay else ax
      let short := if ax.length < ay.length then ax else ay
      (AxesCompatible eq one long short →
        promote_shape_AbstractArray_AbstractArray axes (promote_shape_Indices C eq) x y =
          .ok long) ∧
      (¬ AxesCompatible eq one long short → ∃ e,
        promote_shape_AbstractArray_AbstractArray axes (promote_shape_Indices C eq) x y =
          .error e))

theorem promote_shape_Indices_long {R B : Type} [Inhabited R] (C : ShapeCallees R B)
    (eq : R → R → Bool) (one : R) (hone : C.colon (int 1) (int 1) = .ok one) (a b : List R)
    (h : ¬ a.length < b.length) :
    (AxesCompatible eq one a b → promote_shape_Indices C eq a b = .ok a) ∧
    (¬ AxesCompatible eq one a b → ∃ e, promote_shape_Indices C eq a b = .error e) := by
  rw [promote_shape_Indices, if_neg h]
  have hl1 := forM_ite_ok (List.range' 1 b.length) (fun i => (!eq a[i - 1]! b[i - 1]!) = true)
    (fun i => throw_promote_shape_mismatch C a (some b) (some (int i)))
    (fun i => throw_promote_shape_mismatch_error _ _ _ _)
  have hl2 := forM_ite_ok (List.range' (b.length + 1) (a.length - b.length))
    (fun i => (!eq a[i - 1]! one) = true)
    (fun i => throw_promote_shape_mismatch C a none (some (int i)))
    (fun i => throw_promote_shape_mismatch_error _ _ _ _)
  have e2 : ((List.range' (b.length + 1) (a.length - b.length)).forM fun i => do
      if (!eq a[i - 1]! (← C.colon (int 1) (int 1))) = true then
        throw_promote_shape_mismatch C a none (some (int i))) =
      (List.range' (b.length + 1) (a.length - b.length)).forM (fun i =>
        if (!eq a[i - 1]! one) = true then throw_promote_shape_mismatch C a none (some (int i))
        else pure ()) := by
    apply forM_congr_mem
    intro i _
    simp only [hone, bind, Except.bind]
  rw [e2]
  constructor
  · intro ⟨hc1, hc2⟩
    have r1 := hl1.mpr (fun i hi => by
      simp only [List.mem_range'_1] at hi
      rw [hc1 i hi.1 (by omega)]; decide)
    have r2 := hl2.mpr (fun i hi => by
      simp only [List.mem_range'_1] at hi
      rw [hc2 i (by omega) (by omega)]; decide)
    rw [r1]
    simp only [bind, Except.bind]
    rw [r2]
    rfl
  · intro hnc
    rcases except_cases ((List.range' 1 b.length).forM fun i =>
        if (!eq a[i - 1]! b[i - 1]!) = true then
          throw_promote_shape_mismatch C a (some b) (some (int i)) else pure ()) with
      ⟨u, hu⟩ | ⟨e, he⟩
    · rcases except_cases ((List.range' (b.length + 1) (a.length - b.length)).forM fun i =>
          if (!eq a[i - 1]! one) = true then
            throw_promote_shape_mismatch C a none (some (int i)) else pure ()) with
        ⟨u2, hu2⟩ | ⟨e2, he2⟩
      · exfalso
        cases u; cases u2
        have c1 := hl1.mp hu
        have c2 := hl2.mp hu2
        apply hnc
        constructor
        · intro i h1 h2
          have := c1 i (by simp [List.mem_range'_1]; omega)
          simpa using this
        · intro i h1 h2
          have := c2 i (by simp [List.mem_range'_1]; omega)
          simpa using this
      · refine ⟨e2, ?_⟩
        rw [hu]
        simp only [bind, Except.bind]
        rw [he2]
    · refine ⟨e, ?_⟩
      rw [he]
      rfl

theorem promoteShapeAxes_proven : PromoteShapeAxes := by
  intro R X B _ C eq one hone
  have main : ∀ a b : List R,
      let long := if a.length < b.length then b else a
      let short := if a.length < b.length then a else b
      (AxesCompatible eq one long short → promote_shape_Indices C eq a b = .ok long) ∧
      (¬ AxesCompatible eq one long short → ∃ e, promote_shape_Indices C eq a b = .error e) := by
    intro a b
    by_cases h : a.length < b.length
    · simp only [if_pos h]
      have hs : promote_shape_Indices C eq a b = promote_shape_Indices C eq b a := by
        rw [promote_shape_Indices, if_pos h]
      rw [hs]
      exact promote_shape_Indices_long C eq one hone b a (by omega)
    · simp only [if_neg h]
      exact promote_shape_Indices_long C eq one hone a b h
  refine ⟨main, fun axes x y ax ay hx hy => ?_⟩
  have hr : promote_shape_AbstractArray_AbstractArray axes (promote_shape_Indices C eq) x y =
      promote_shape_Indices C eq ax ay := by
    simp [promote_shape_AbstractArray_AbstractArray, hx, hy, bind, Except.bind]
  rw [hr]
  exact main ax ay

/-! ## Mismatch messages for axes -/

/-- The tuple entries `throw_promote_shape_mismatch` sees when `promote_shape` compares axes:
axis ranges, or the `Int`s `lastindex` gives for `OneTo` axes (`lastindex(::Int)` is 1 and so
is `firstindex`); and the `IOBuffer` operations, of a buffer type `B`. -/
def axisShapeCallees {B : Type} (R : RangeCallees) (colon : I64 → I64 → AxisRange) (io : B)
    (printString : B → String → B) (printTuple : B → List (IntegerOrRange I64 AxisRange) → B)
    (printInt : B → I64 → B) (takestring : B → String) :
    ShapeCallees (IntegerOrRange I64 AxisRange) B where
  isOneTo
    | .range (.base (.oneTo _)) => true
    | _ => false
  isInt
    | .integer _ => true
    | .range _ => false
  ofInt := .integer
  lastindex
    | .integer _ => .ok (int 1)
    | .range r => .ok (r.lastindex R)
  firstindex
    | .integer _ => .ok (int 1)
    | .range r => .ok (r.firstindex R)
  colon a b := .ok (.range (colon a b))
  IOBuffer := io
  printString := printString
  printTuple := printTuple
  printInt := printInt
  takestring := takestring

/-- The values of each axis, as `(first, last)`. -/
def axisValues (R : RangeCallees) (rs : List AxisRange) : List (I64 × I64) :=
  rs.map fun r => (r.first R, r.last R)

/-- An axis is a `Base.OneTo`. -/
def isOneToAxis : AxisRange → Bool
  | .base (.oneTo _) => true
  | _ => false

/-- Comment above `throw_promote_shape_mismatch`: the message is "consistent" and hides only
type details like `OneTo`. When the shapes are axis tuples (not all `OneTo`), the message reads
`a has axes A, b has axes B, mismatch at dim k`, where `A` and `B` print each argument's axes
as ranges with the same values (`first` and `last`) as those axes. Printing obeys
`PrintLaws` with any tuple printer `text`. -/
def PromoteShapeMessage : Prop :=
  ∀ (R : RangeCallees), RangeLaws R → ∀ (colon : I64 → I64 → AxisRange),
    (∀ a b, (colon a b).first R = a ∧ (colon a b).last R = b) →
    ∀ {B : Type} (io : B) (printString : B → String → B)
      (printTuple : B → List (IntegerOrRange I64 AxisRange) → B) (printInt : B → I64 → B)
      (takestring : B → String) (text : List (IntegerOrRange I64 AxisRange) → String),
      PrintLaws (axisShapeCallees R colon io printString printTuple printInt takestring) text →
    ∀ (a b : List AxisRange) (k : I64), ¬ (a.all isOneToAxis ∧ b.all isOneToAxis) →
      ∃ a' b', axisValues R a' = axisValues R a ∧ axisValues R b' = axisValues R b ∧
        throw_promote_shape_mismatch
            (axisShapeCallees R colon io printString printTuple printInt takestring)
            (a.map .range) (some (b.map .range)) (some k) =
          .error (.dimensionMismatch ("a has axes " ++ text (a'.map .range) ++ ", b has axes " ++
            text (b'.map .range) ++ ", mismatch at dim " ++ toString k.val))

/-- The message of a `DimensionMismatch`. -/
def mismatchText : IndexResult Unit → Option String
  | .error (.dimensionMismatch m) => some m
  | _ => none

/-- A tuple printer that writes `two` for an axis starting at 2 and `other` otherwise. -/
def startPrinter (t : List (IntegerOrRange I64 AxisRange)) : String :=
  String.join (t.map fun
    | .integer _ => "int"
    | .range r => if (r.first lawfulRange).val = 2 then "two" else "other")

theorem startPrinter_values (x : List AxisRange) :
    startPrinter (x.map .range) =
      String.join ((axisValues lawfulRange x).map fun p => if p.1.val = 2 then "two" else "other") := by
  simp [startPrinter, axisValues, List.map_map, Function.comp_def]

/-- `promote_shape((Base.OneTo(3),), (2:4,))` reports `b has axes (1:3,)` for the axis `2:4`:
`firstindex(2:4):lastindex(2:4)` is `1:3`. -/
theorem promoteShapeMessage_refuted : ¬ PromoteShapeMessage := by
  intro h
  obtain ⟨a', b', ha, hb, heq⟩ := h lawfulRange lawfulRange_laws
    (fun a b => .base (.unitRange a b)) (fun _ _ => ⟨rfl, rfl⟩) ""
    (· ++ ·) (fun s t => s ++ startPrinter t) (fun s n => s ++ toString n.val) id startPrinter
    ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    [.base (.oneTo (int 3))] [.base (.unitRange (int 2) (int 4))] (int 1) (by decide)
  rw [startPrinter_values, startPrinter_values, ha, hb] at heq
  have := congrArg mismatchText heq
  revert this
  decide +kernel

/-! ## Indexed-assignment shape checks -/

instance {t : IntTy} : Inhabited (JInt t) := ⟨JInt.wrap t 0⟩

/-- `_shapes_match` compatibility: equal entries where both shapes have one, and only 1s
beyond the shorter shape. -/
def ShapesCompatible (a b : List Int) : Prop :=
  (∀ (k : Nat) (x y : Int), a[k]? = some x → b[k]? = some y → x = y) ∧
  (∀ x ∈ a.drop b.length, x = 1) ∧ (∀ y ∈ b.drop a.length, y = 1)

theorem shapes_match_iff {A B : Type} (eq : A → B → Bool) (isA : A → Bool) (isB : B → Bool)
    (va : A → Int) (vb : B → Int) (heq : ∀ x y, eq x y = decide (va x = vb y))
    (hA : ∀ x, isA x = decide (va x = 1)) (hB : ∀ y, isB y = decide (vb y = 1)) :
    ∀ (a : List A) (b : List B),
      _shapes_match eq isA isB a b = true ↔ ShapesCompatible (a.map va) (b.map vb)
  | [], [] => by simp [_shapes_match, _shapes_match_Tuple0_Tuple0, ShapesCompatible]
  | x :: xs, [] => by
    simp [_shapes_match, _shapes_match_Tuple_Tuple0, ShapesCompatible, hA]
  | [], y :: ys => by
    simp [_shapes_match, _shapes_match_Tuple0_Tuple, ShapesCompatible, hB]
  | x :: xs, y :: ys => by
    have ih := shapes_match_iff eq isA isB va vb heq hA hB xs ys
    simp only [_shapes_match, Bool.and_eq_true, heq, decide_eq_true_eq, ih]
    constructor
    · rintro ⟨hxy, h1, h2, h3⟩
      refine ⟨fun k u w hu hw => ?_, by simpa using h2, by simpa using h3⟩
      cases k with
      | zero => simp at hu hw; rw [← hu, ← hw, hxy]
      | succ k => simp at hu hw; exact h1 k u w (by simpa using hu) (by simpa using hw)
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1 0 (va x) (vb y) (by simp) (by simp), fun k u w hu hw => ?_,
        by simpa using h2, by simpa using h3⟩
      exact h1 (k + 1) u w (by simpa using hu) (by simpa using hw)

/-- The value laws of the callees on shape entries of an `Integer` type `I` with values `val`
(any integer type, `BigInt` included): `==` and `isone` compare values. -/
structure SetindexLaws {X I : Type} (C : SetindexCallees X I) (val : I → Int) : Prop where
  eqLength : ∀ n i, C.eqLength n i = decide (n.val = val i)
  eqDim : ∀ n i, C.eqDim n i = decide (n.val = val i)
  isoneDim : ∀ n, C.isoneDim n = decide (n.val = 1)
  isone : ∀ i, C.isone i = decide (val i = 1)

theorem throw_setindex_mismatch_dm {X I α : Type} [Inhabited I] (C : SetindexCallees X I)
    (x : X) (I' : List I) :
    ∃ m, throw_setindex_mismatch (α := α) C x I' = .error (.dimensionMismatch m) := by
  unfold throw_setindex_mismatch
  split <;> exact ⟨_, rfl⟩

/-- Indexed assignment `A[I...] = X` checks the shape of `X` against the destination
(`setindex_shape_check`, for shape entries of any `Integer` type): with a single index, or into
a vector, the element counts must be equal; otherwise the sizes must agree up to trailing
singleton dimensions. A passing check returns `true`; a mismatch throws `DimensionMismatch`; a
non-array value with a tuple of destinations throws `ArgumentError`. -/
def SetindexShapeCheck : Prop :=
  ∀ {X I : Type} [Inhabited I] (C : SetindexCallees X I) (val : I → Int), SetindexLaws C val →
    ∀ x : X,
    (∀ i : I,
      (setindex_shape_check_Integer C x i = .ok true ↔ (C.length x).val = val i) ∧
      (setindex_shape_check_Integer C x i ≠ .ok true →
        ∃ m, setindex_shape_check_Integer C x i = .error (.dimensionMismatch m))) ∧
    (∀ shape : List I,
      (setindex_shape_check_Tuple C x shape = .ok true ↔
        if C.ndims x = 1 ∨ shape.length = 1 then (C.length x).val = val (C.prod shape)
        else ShapesCompatible ((C.size x).map (·.val)) (shape.map val)) ∧
      (setindex_shape_check_Tuple C x shape ≠ .ok true →
        ∃ m, setindex_shape_check_Tuple C x shape = .error (.dimensionMismatch m))) ∧
    (∀ shape : List I, ∃ m,
      setindex_shape_check_Any_Tuple (α := Bool) x shape = .error (.argumentError m))

theorem setindex_tuple_cases {X I : Type} [Inhabited I] (C : SetindexCallees X I) (x : X)
    (shape : List I) :
    setindex_shape_check_Tuple C x shape = .ok true ∨
      ∃ m, setindex_shape_check_Tuple C x shape = .error (.dimensionMismatch m) := by
  unfold setindex_shape_check_Tuple
  dsimp only
  split <;> split <;>
    first | exact .inl rfl | exact .inr (throw_setindex_mismatch_dm C x shape)

theorem setindexShapeCheck_proven : SetindexShapeCheck := by
  intro X I _ C val hC x
  refine ⟨fun i => ⟨?_, ?_⟩, fun shape => ⟨?_, ?_⟩, fun _ => ⟨_, rfl⟩⟩
  · unfold setindex_shape_check_Integer
    rw [hC.eqLength]
    by_cases h : (C.length x).val = val i
    · simp [h]; rfl
    · obtain ⟨m, hm⟩ := throw_setindex_mismatch_dm (α := Bool) C x [i]
      simp [h, hm]
  · intro hne
    unfold setindex_shape_check_Integer at hne ⊢
    split
    · rename_i h; simp [h] at hne; exact absurd rfl hne
    · exact throw_setindex_mismatch_dm C x [i]
  · unfold setindex_shape_check_Tuple
    have hsm := shapes_match_iff C.eqDim C.isoneDim C.isone (·.val) val hC.eqDim
      hC.isoneDim hC.isone (C.size x) shape
    by_cases hc : C.ndims x = 1 ∨ shape.length = 1
    · simp only [hc, if_true, hC.eqLength]
      by_cases h : (C.length x).val = val (C.prod shape)
      · simp [h]; rfl
      · obtain ⟨m, hm⟩ := throw_setindex_mismatch_dm (α := Bool) C x shape
        simp [h, hm]
    · simp only [hc, if_false]
      by_cases h : _shapes_match C.eqDim C.isoneDim C.isone (C.size x) shape = true
      · simp only [h, if_true]; exact ⟨fun _ => hsm.mp h, fun _ => rfl⟩
      · obtain ⟨m, hm⟩ := throw_setindex_mismatch_dm (α := Bool) C x shape
        simp only [Bool.not_eq_true] at h
        simp only [h, hm]
        constructor
        · intro e; cases e
        · intro hcomp; rw [← hsm] at hcomp; simp [h] at hcomp
  · intro hne
    rcases setindex_tuple_cases C x shape with h | h
    · exact absurd h hne
    · exact h

/-! ## `Slice` and `IdentityUnitRange` -/

/-- `i` lies in `eachindex(r)`, i.e. between `firstindex(r)` and `lastindex(r)`. -/
def InAxes (R : RangeCallees) (r : AxisRange) (i : Int) : Prop :=
  (r.firstindex R).val ≤ i ∧ i ≤ (r.lastindex R).val

instance (R : RangeCallees) (r : AxisRange) (i : Int) : Decidable (InAxes R r i) := by
  unfold InAxes; exact inferInstance

/-- `checkbounds(A, i)` docstring: it succeeds exactly when the scalar index `i` lies in
`eachindex(A)` and throws `BoundsError` otherwise. -/
def ScalarCheckbounds {T I : Type} (R : RangeCallees) (wrap : T → AxisRange) (val : I → Int)
    (checkbounds : T → I → IndexResult Unit) : Prop :=
  ∀ S i, checkbounds S i = if InAxes R (wrap S) (val i) then .ok () else .error .boundsError

theorem slice_axes (R : RangeCallees) (hR : RangeLaws R) (S : Slice BaseRange) :
    (AxisRange.slice S).firstindex R = (AxisRange.slice S).first R ∧
    (AxisRange.slice S).lastindex R = (AxisRange.slice S).last R := by
  obtain ⟨r⟩ := S
  cases r <;> simp [AxisRange.firstindex, AxisRange.lastindex, AxisRange.axes1, AxisRange.first,
    AxisRange.last, axes1_Slice_OneTo, axes1_Slice, first_Slice, last_Slice,
    first_IdentityUnitRange, last_IdentityUnitRange, hR.axes1_oneTo]

theorem identity_axes (R : RangeCallees) (hR : RangeLaws R) (S : IdentityUnitRange BaseRange) :
    (AxisRange.identity S).firstindex R = (AxisRange.identity S).first R ∧
    (AxisRange.identity S).lastindex R = (AxisRange.identity S).last R := by
  obtain ⟨r⟩ := S
  cases r <;> simp [AxisRange.firstindex, AxisRange.lastindex, AxisRange.axes1, AxisRange.first,
    AxisRange.last, axes1_IdentityUnitRange_OneTo, axes1_IdentityUnitRange,
    first_IdentityUnitRange, last_IdentityUnitRange, hR.axes1_oneTo]

/-- `Slice` docstring: a `Slice` is a unit range with the same indices as the range it wraps,
so its axis has the values `first(S):last(S)` (`axes`/`axes1`, `first`, `last`), and indexing
it with an `Int` returns that exact integer inside the axis and throws `BoundsError` outside.
Indexing with an in-bounds range of `Int`s (`AbstractUnitRange`, `StepRange` or
`IdentityUnitRange`) returns that range, so each of its elements maps to itself. -/
def SliceContract : Prop :=
  ∀ (R : RangeCallees), RangeLaws R →
    ∀ (checkbounds : Slice BaseRange → I64 → IndexResult Unit),
      ScalarCheckbounds R .slice (·.val) checkbounds →
    ∀ S : Slice BaseRange,
      ((AxisRange.slice S).firstindex R = first_Slice R.first S ∧
        (AxisRange.slice S).lastindex R = last_Slice R.last S) ∧
      (∀ i : I64, getindex_Slice_Int checkbounds S i =
        if (first_Slice R.first S).val ≤ i.val ∧ i.val ≤ (last_Slice R.last S).val then .ok i
        else .error .boundsError) ∧
      (∀ {I : Type} (checkboundsI : Slice BaseRange → I → IndexResult Unit) (i : I),
        checkboundsI S i = .ok () →
          getindex_Slice_AbstractUnitRange checkboundsI S i = .ok i ∧
          getindex_Slice_StepRange checkboundsI S i = .ok i) ∧
      (∀ {U : Type} (checkboundsI : Slice BaseRange → IdentityUnitRange U → IndexResult Unit)
        (i : IdentityUnitRange U), checkboundsI S i = .ok () →
          getindex_Slice_IdentityUnitRange checkboundsI S i = .ok i)

theorem sliceContract_proven : SliceContract := by
  intro R hR cb hcb S
  have hax := slice_axes R hR S
  refine ⟨hax, fun i => ?_, fun cbI i h => ⟨?_, ?_⟩, fun cbI i h => ?_⟩
  · have hiff : InAxes R (.slice S) i.val ↔
        (first_Slice R.first S).val ≤ i.val ∧ i.val ≤ (last_Slice R.last S).val := by
      unfold InAxes; rw [hax.1, hax.2]; exact Iff.rfl
    have hcbi : cb S i = if InAxes R (.slice S) i.val then .ok () else .error .boundsError :=
      hcb S i
    rw [getindex_Slice_Int, hcbi]
    by_cases hc : InAxes R (.slice S) i.val
    · rw [if_pos hc, if_pos (hiff.mp hc)]; rfl
    · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h))]; rfl
  all_goals simp [getindex_Slice_AbstractUnitRange, getindex_Slice_StepRange,
    getindex_Slice_IdentityUnitRange, h, bind, Except.bind, pure, Except.pure]

/-- The value of an integer index, given the values `val` of its non-`Int` type. -/
def integerIndexVal {I : Type} (val : I → Int) : IntegerIndex I → Int
  | .int i => i.val
  | .other i => val i

/-- `Slice` docstring: "indexing into Slice objects with an integer always returns that exact
integer", for an integer in the axis of any `Integer` type: `Int`, another BitInteger, `BigInt`
or a user integer, whose values `val` gives. Julia selects `getindex(S::Slice, i::Int)` for an
`Int`; for every other integer type it selects the generic `range.jl` method
`getindex(r::AbstractRange, i::Integer)`, which returns `first(r) + (i - 1)` after
`checkbounds`. -/
def SliceIntegerIndex : Prop :=
  ∀ (R : RangeCallees), RangeLaws R →
    ∀ (checkbounds : Slice BaseRange → I64 → IndexResult Unit),
      ScalarCheckbounds R .slice (·.val) checkbounds →
    ∀ {I : Type} (val : I → Int) (checkboundsI : Slice BaseRange → I → IndexResult Unit),
      ScalarCheckbounds R .slice val checkboundsI →
    ∀ (getindex_AbstractRange : Slice BaseRange → I → IndexResult I64),
      (∀ S i, getindex_AbstractRange S i = (do
        checkboundsI S i
        pure (int (((AxisRange.slice S).first R).val + val i - 1)))) →
    ∀ (S : Slice BaseRange) (i : IntegerIndex I), InAxes R (.slice S) (integerIndexVal val i) →
      ∃ k, getindex_Slice_Integer checkbounds getindex_AbstractRange S i = .ok k ∧
        k.val = integerIndexVal val i

/-- `Base.Slice(3:5)[Int8(3)]` is `5`. -/
theorem sliceIntegerIndex_refuted : ¬ SliceIntegerIndex := by
  intro h
  let cb : Slice BaseRange → I64 → IndexResult Unit := fun S i =>
    if InAxes lawfulRange (.slice S) i.val then .ok () else .error .boundsError
  let cbI : Slice BaseRange → JInt .i8 → IndexResult Unit := fun S i =>
    if InAxes lawfulRange (.slice S) i.val then .ok () else .error .boundsError
  let i : JInt .i8 := ⟨3, by decide⟩
  obtain ⟨k, hk, hv⟩ := h lawfulRange lawfulRange_laws cb (fun _ _ => rfl) (·.val) cbI
    (fun _ _ => rfl) _ (fun _ _ => rfl) ⟨.unitRange (int 3) (int 5)⟩ (.other i)
    (by decide +kernel)
  have hin : InAxes lawfulRange (.slice ⟨.unitRange (int 3) (int 5)⟩) i.val := by decide +kernel
  simp only [getindex_Slice_Integer, cbI, hin, if_true, bind, Except.bind, pure,
    Except.pure, Except.ok.injEq] at hk
  rw [← hk] at hv
  revert hv
  decide +kernel

/-- The values of a `Bool` unit range `a:b`, and those values as `Int`s (`false == 0`,
`true == 1`). -/
def boolRangeMask : Bool × Bool → List Bool
  | (false, true) => [false, true]
  | (true, false) => []
  | (a, _) => [a]

def boolRangeInts (m : Bool × Bool) : List Int := (boolRangeMask m).map fun b => if b then 1 else 0

/-- The values of an axis value, `first:last`. -/
def axisRangeValues (R : RangeCallees) (r : AxisRange) : List Int :=
  (List.range ((r.last R).val - (r.first R).val + 1).toNat).map
    fun k : Nat => (r.first R).val + (k : Int)

/-- Logical indexing: the values at the positions where the mask is `true`. -/
def logicalSelection (values : List Int) (mask : List Bool) : List Int :=
  (values.zip mask).filterMap fun (v, b) => if b then some v else none

/-- Logical indexing (manual, "Logical indexing"): indexing a `Slice` with a `Bool` unit range
whose length matches the slice selects the values at the `true` positions. -/
def SliceBoolRange : Prop :=
  ∀ (R : RangeCallees), RangeLaws R →
    ∀ (checkbounds : Slice BaseRange → Bool × Bool → IndexResult Unit) (S : Slice BaseRange)
      (m : Bool × Bool), (boolRangeMask m).length = (axisRangeValues R (.slice S)).length →
      checkbounds S m = .ok () →
      ∃ out, getindex_Slice_AbstractUnitRange checkbounds S m = .ok out ∧
        boolRangeInts out = logicalSelection (axisRangeValues R (.slice S)) (boolRangeMask m)

/-- `Base.Slice(Base.OneTo(2))[false:true]` is `false:true`, not `[2]`. -/
theorem sliceBoolRange_refuted : ¬ SliceBoolRange := by
  intro h
  obtain ⟨out, hout, hv⟩ := h lawfulRange lawfulRange_laws (fun _ _ => .ok ())
    ⟨.oneTo (int 2)⟩ (false, true) (by decide +kernel) rfl
  simp only [getindex_Slice_AbstractUnitRange, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at hout
  subst hout
  revert hv
  decide +kernel

/-- `IdentityUnitRange` docstring: `range[i] == i`. Its axis has the values of the wrapped
range (it is its own axis); indexing with an integer of any BitInteger type in the axis
returns the `Int` with that value, and throws `BoundsError` outside; a `Bool` is not an index
(`ArgumentError`). Indexing with an in-bounds range of `Int`s returns a range with the same
values (`convert` keeps the values), and with an in-bounds `IdentityUnitRange` (also into a
`Slice` or an `AbstractOneTo`) returns it unchanged. -/
def IdentityContract : Prop :=
  ∀ (R : RangeCallees), RangeLaws R →
    (∀ S : IdentityUnitRange BaseRange,
      (AxisRange.identity S).firstindex R = first_IdentityUnitRange R.first S ∧
      (AxisRange.identity S).lastindex R = last_IdentityUnitRange R.last S ∧
      ((AxisRange.identity S).axes1 R = (AxisRange.identity S) ∨
        (∃ n, S.indices = .oneTo n ∧ (AxisRange.identity S).axes1 R = .base (.oneTo n)))) ∧
    (∀ {I : Type} (val : I → Int) (convert_Int : I → IndexResult I64),
      ConvertIntLaw val convert_Int →
      ∀ (checkbounds : IdentityUnitRange BaseRange → I → IndexResult Unit),
      ScalarCheckbounds R .identity val checkbounds →
      ∀ (S : IdentityUnitRange BaseRange) (i : I),
        (InAxes R (.identity S) (val i) →
          ∃ k, getindex_IdentityUnitRange_Integer checkbounds convert_Int S i = .ok k ∧
            k.val = val i) ∧
        (¬ InAxes R (.identity S) (val i) →
          getindex_IdentityUnitRange_Integer checkbounds convert_Int S i = .error .boundsError)) ∧
    (∀ (S : IdentityUnitRange BaseRange) (b : Bool), ∃ m,
      getindex_IdentityUnitRange_Bool S b = .error (.argumentError m)) ∧
    (∀ (checkbounds : IdentityUnitRange BaseRange → BaseRange → IndexResult Unit)
      (convert_Int : BaseRange → IndexResult BaseRange),
      (∀ r, ∃ r', convert_Int r = .ok r' ∧ R.first r' = R.first r ∧ R.last r' = R.last r) →
      ∀ S r, checkbounds S r = .ok () →
        (∃ r', getindex_IdentityUnitRange_AbstractUnitRange checkbounds convert_Int S r = .ok r' ∧
          R.first r' = R.first r ∧ R.last r' = R.last r) ∧
        (∃ r', getindex_IdentityUnitRange_StepRange checkbounds convert_Int S r = .ok r' ∧
          R.first r' = R.first r ∧ R.last r' = R.last r)) ∧
    (∀ {U : Type} (S : IdentityUnitRange BaseRange) (i : IdentityUnitRange U)
      (checkbounds : IdentityUnitRange BaseRange → IdentityUnitRange U → IndexResult Unit)
      (checkboundsS : Slice BaseRange → IdentityUnitRange U → IndexResult Unit)
      (checkboundsO : BaseRange → IdentityUnitRange U → IndexResult Unit),
      checkbounds S i = .ok () → checkboundsS ⟨S.indices⟩ i = .ok () →
      checkboundsO S.indices i = .ok () →
        getindex_IdentityUnitRange_IdentityUnitRange checkbounds S i = .ok i ∧
        getindex_Slice_IdentityUnitRange checkboundsS ⟨S.indices⟩ i = .ok i ∧
        getindex_AbstractOneTo_IdentityUnitRange checkboundsO S.indices i = .ok i)

theorem identityContract_proven : IdentityContract := by
  intro R hR
  refine ⟨fun S => ?_, fun val conv hconv cb hcb S i => ⟨fun hin => ?_, fun hout => ?_⟩,
    fun _ _ => ⟨_, rfl⟩,
    fun cb conv hconv S r h => ⟨?_, ?_⟩, fun S i cb cbS cbO h1 h2 h3 => ?_⟩
  · have hax := identity_axes R hR S
    refine ⟨hax.1, hax.2, ?_⟩
    obtain ⟨r⟩ := S
    cases r with
    | oneTo n => exact .inr ⟨n, rfl, rfl⟩
    | unitRange a b => exact .inl rfl
  · have hfit : fitsInt (val i) := by
      have h1 := fits_val ((AxisRange.identity S).firstindex R)
      have h2 := fits_val ((AxisRange.identity S).lastindex R)
      unfold InAxes at hin
      unfold fitsInt at *
      omega
    refine ⟨⟨val i, hfit⟩, ?_, rfl⟩
    simp only [getindex_IdentityUnitRange_Integer, hcb S i, hin, if_true, bind, Except.bind,
      convert_ok hconv i hfit]
  · simp [getindex_IdentityUnitRange_Integer, hcb S i, hout, bind, Except.bind]
  · obtain ⟨r', hr', h1, h2⟩ := hconv r
    exact ⟨r', by simp [getindex_IdentityUnitRange_AbstractUnitRange, h, hr', bind,
      Except.bind], h1, h2⟩
  · obtain ⟨r', hr', h1, h2⟩ := hconv r
    exact ⟨r', by simp [getindex_IdentityUnitRange_StepRange, h, hr', bind, Except.bind], h1, h2⟩
  · simp [getindex_IdentityUnitRange_IdentityUnitRange, getindex_Slice_IdentityUnitRange,
      getindex_AbstractOneTo_IdentityUnitRange, h1, h2, h3, bind, Except.bind, pure, Except.pure]

/-- Logical indexing of an `IdentityUnitRange` with a `Bool` unit range of matching length
(`base/indices.jl:385-389`) selects the values at the `true` positions; `range(start; length)`
(`range.jl`) holds `start, start+1, …` (`length` a `Bool` converted to `Int`). -/
def IdentityBoolUnitRange : Prop :=
  ∀ (R : RangeCallees), RangeLaws R →
    ∀ (range_length : I64 → Bool → IndexResult (List Int)),
      (∀ s n, range_length s n =
        .ok ((List.range (if n then 1 else 0)).map fun k : Nat => s.val + (k : Int))) →
    ∀ (checkbounds : IdentityUnitRange BaseRange → Bool × Bool → IndexResult Unit)
      (S : IdentityUnitRange BaseRange) (m : Bool × Bool),
      (boolRangeMask m).length = (axisRangeValues R (.identity S)).length →
      checkbounds S m = .ok () →
      getindex_IdentityUnitRange_AbstractUnitRange_Bool checkbounds R.first R.last (·.1) (·.2)
          range_length S m =
        .ok (logicalSelection (axisRangeValues R (.identity S)) (boolRangeMask m))

theorem identityBoolUnitRange_proven : IdentityBoolUnitRange := by
  intro R hR rl hrl cb S m hlen hcb
  simp only [getindex_IdentityUnitRange_AbstractUnitRange_Bool, hcb, bind, Except.bind]
  simp only [axisRangeValues, AxisRange.first, AxisRange.last, first_IdentityUnitRange,
    last_IdentityUnitRange, List.length_map, List.length_range] at hlen ⊢
  generalize R.first S.indices = f at hlen ⊢
  generalize R.last S.indices = l at hlen ⊢
  obtain ⟨a, b⟩ := m
  cases a <;> cases b
  · have hn : (l.val - f.val + 1).toNat = 1 := by simp [boolRangeMask] at hlen; omega
    rw [hn]
    simp [hrl, logicalSelection, boolRangeMask, List.range, List.range.loop]
  · have hn : (l.val - f.val + 1).toNat = 2 := by simp [boolRangeMask] at hlen; omega
    have hl : l.val = f.val + 1 := by omega
    rw [hn]
    simp [hrl, logicalSelection, boolRangeMask, List.range, List.range.loop, hl]
  · have hn : (l.val - f.val + 1).toNat = 0 := by simp [boolRangeMask] at hlen; omega
    rw [hn]
    simp [hrl, logicalSelection, boolRangeMask, List.range, List.range.loop]
  · have hn : (l.val - f.val + 1).toNat = 1 := by simp [boolRangeMask] at hlen; omega
    rw [hn]
    simp [hrl, logicalSelection, boolRangeMask, List.range, List.range.loop]

/-- The values of a `StepRange{Bool,Int}` `a:s:b` (with `b` its normalised `last`). -/
def stepMask (m : Bool × Int × Bool) : List Bool :=
  let a : Int := if m.1 then 1 else 0
  let b : Int := if m.2.2 then 1 else 0
  let s := m.2.1
  if s = 0 then [] else
    (List.range ((b - a) / s + 1).toNat).map fun k : Nat => a + (k : Int) * s ≠ 0

/-- Logical indexing of an `IdentityUnitRange` with a `Bool` step range `StepRange{Bool,S}`
of matching length, for a step of any signed `Integer` type `S` with values `sval`
(`base/indices.jl:395-399`), selects the values at the `true` positions;
`range(start; length, step)` (`range.jl`) holds `start, start+step, …`, and `Int(step)` is the
documented `convert(Int, step)`. -/
def IdentityBoolStepRange : Prop :=
  ∀ (R : RangeCallees), RangeLaws R →
    ∀ (range_length_step : I64 → Bool → I64 → IndexResult (List Int)),
      (∀ s n st, range_length_step s n st =
        .ok ((List.range (if n then 1 else 0)).map fun k : Nat => s.val + (k : Int) * st.val)) →
    ∀ {S : Type} (sval : S → Int) (Int' : S → IndexResult I64), ConvertIntLaw sval Int' →
    ∀ (checkbounds : IdentityUnitRange BaseRange → Bool × S × Bool → IndexResult Unit)
      (S' : IdentityUnitRange BaseRange) (m : Bool × S × Bool),
      (stepMask (m.1, sval m.2.1, m.2.2)).length = (axisRangeValues R (.identity S')).length →
      checkbounds S' m = .ok () →
      getindex_IdentityUnitRange_StepRange_Bool checkbounds R.first R.last (·.1) (·.2.2)
          (·.2.1) Int' range_length_step S' m =
        .ok (logicalSelection (axisRangeValues R (.identity S'))
          (stepMask (m.1, sval m.2.1, m.2.2)))

/-- `Base.IdentityUnitRange(1:2)[StepRange(true, -1, false)]` is empty, not `[1]`. -/
theorem identityBoolStepRange_refuted : ¬ IdentityBoolStepRange := by
  intro h
  have := h lawfulRange lawfulRange_laws _ (fun _ _ _ => rfl) (·.val) convert_Int_BitInteger
    (convert_Int_BitInteger_law .i64) (fun _ _ => .ok ())
    ⟨.unitRange (int 1) (int 2)⟩ (true, int (-1), false) (by decide +kernel) rfl
  rw [getindex_IdentityUnitRange_StepRange_Bool,
    convert_ok (convert_Int_BitInteger_law .i64) _ (fits_val _)] at this
  simp only [bind, Except.bind, Except.ok.injEq] at this
  revert this
  decide +kernel

/-! ## `LinearIndices` -/

/-- The callees of `LinearIndices(inds)` on a tuple of integers (of an `Integer` type `I` with
values `val`) and `Int` ranges, with their documented behaviour: `oneto(n)` (`range.jl`) is
`Base.OneTo(n)` and `a:b` is `UnitRange(a, b)`; the constructor `LinearIndices` then converts
each entry to an `AbstractUnitRange{Int}` (`base/indices.jl:483` with `convert`), which keeps
the values of an `Int` range and turns `OneTo(n)` into `Base.OneTo{Int}(n)`, or throws
`InexactError` when `Int` cannot represent `n`. -/
structure ConvertLaws {I S : Type} (val : I → Int) (oneto : I → S) (colon : I64 → I64 → S)
    (LinearIndices_S : List S → IndexResult (LinearIndices AxisRange))
    (toAxis : S → IndexResult AxisRange) : Prop where
  construct : ∀ l, LinearIndices_S l = (l.mapM toAxis).map (⟨·⟩)
  oneto_fits : ∀ n (h : fitsInt (val n)), toAxis (oneto n) = .ok (.base (.oneTo ⟨val n, h⟩))
  oneto_inexact : ∀ n, ¬ fitsInt (val n) → toAxis (oneto n) = .error (.core (.inexactError "Int64"))
  colon : ∀ a b, toAxis (colon a b) = .ok (.base (.unitRange a b))

/-- The `(first, last)` of an entry's expected axis: `1:n` for an integer, the axis of a range. -/
def expectedAxis {I : Type} (R : RangeCallees) (val : I → Int) :
    IntegerOrRange I AxisRange → Int × Int
  | .integer n => (1, val n)
  | .range r => (((r.axes1 R).first R).val, ((r.axes1 R).last R).val)

/-- The values of each axis, as integers `(first, last)`. -/
def axisInts (R : RangeCallees) (rs : List AxisRange) : List (Int × Int) :=
  rs.map fun r => ((r.first R).val, (r.last R).val)

/-- `LinearIndices` docstring: `LinearIndices((istart:istop, jstart:jstop, ...))` returns a
`LinearIndices` with the specified shape or axes, also when integers (of any `Integer` type
that `Int` can represent) and ranges are mixed: an integer `n` gives the axis `1:n` and a range
keeps its own axis. -/
def LinearIndicesMixedAxes : Prop :=
  ∀ (R : RangeCallees), RangeLaws R →
    ∀ {I S : Type} (val : I → Int) (oneto : I → S) (colon : I64 → I64 → S)
      (LinearIndices_S : List S → IndexResult (LinearIndices AxisRange))
      (toAxis : S → IndexResult AxisRange), ConvertLaws val oneto colon LinearIndices_S toAxis →
    ∀ inds : List (IntegerOrRange I AxisRange),
      (∀ n, IntegerOrRange.integer n ∈ inds → fitsInt (val n)) →
      ∃ L, LinearIndices_IntegerOrRanges
          (_convert2ind oneto (AxisRange.first R) (AxisRange.last R) colon) LinearIndices_S
          inds = .ok L ∧
        axisInts R (axes_LinearIndices (AxisRange.axes1 R) L) = inds.map (expectedAxis R val)

theorem mapM_ok_id {α : Type} (f : α → IndexResult α) (hf : ∀ r, f r = .ok r) :
    ∀ l : List α, l.mapM f = .ok l
  | [] => rfl
  | x :: xs => by
    simp [List.mapM_cons, hf, mapM_ok_id f hf xs, bind, Except.bind, pure, Except.pure]

theorem mapM_ok_pure {α : Type} (l : List α) : l.mapM (Except.ok : α → IndexResult α) = .ok l :=
  mapM_ok_id _ (fun _ => rfl) l

/-- `axes(LinearIndices((Base.IdentityUnitRange(3:5), 2)))[1]` is `Base.OneTo(3)`, not `3:5`. -/
theorem linearIndicesMixedAxes_refuted : ¬ LinearIndicesMixedAxes := by
  intro h
  obtain ⟨L, hL, hax⟩ := h lawfulRange lawfulRange_laws (I := I64) (S := AxisRange) (·.val)
    (fun n => .base (.oneTo n)) (fun a b => .base (.unitRange a b)) (fun l => .ok ⟨l⟩) .ok
    ⟨fun l => by rw [mapM_ok_pure]; rfl, fun n h => rfl, fun n h => absurd (fits_val n) h,
      fun _ _ => rfl⟩
    [.range (.identity ⟨.unitRange (int 3) (int 5)⟩), .integer (int 2)]
    (fun n _ => fits_val n)
  simp only [LinearIndices_IntegerOrRanges, Except.ok.injEq] at hL
  subst hL
  revert hax
  decide +kernel

/-- `LinearIndices` docstring: `LinearIndices(sz)` of a shape of integers (of any `Integer`
type) has the axes `1:sz[k]`, and throws `InexactError` when `Int` cannot represent a size;
`LinearIndices((r1, r2, ...))` of ranges has the axes of those ranges (`convert` to
`AbstractUnitRange{Int}` keeps an `Int` range), and `LinearIndices(A)` "has the same shape and
axes as `A`" when every axis of `A` is its own axis. -/
def LinearIndicesConstructors : Prop :=
  ∀ (R : RangeCallees), RangeLaws R →
    (∀ {I S : Type} (val : I → Int) (oneto : I → S) (colon : I64 → I64 → S)
      (LinearIndices_S : List S → IndexResult (LinearIndices AxisRange))
      (toAxis : S → IndexResult AxisRange), ConvertLaws val oneto colon LinearIndices_S toAxis → ∀ sz : List I,
        ((∀ n ∈ sz, fitsInt (val n)) → ∃ L,
          LinearIndices_IntegerOrRanges (R := AxisRange)
            (_convert2ind oneto (AxisRange.first R) (AxisRange.last R) colon) LinearIndices_S
            (sz.map .integer) = .ok L ∧
          axisInts R (axes_LinearIndices (AxisRange.axes1 R) L) = sz.map fun n => (1, val n)) ∧
        ((∃ n ∈ sz, ¬ fitsInt (val n)) →
          LinearIndices_IntegerOrRanges (R := AxisRange)
            (_convert2ind oneto (AxisRange.first R) (AxisRange.last R) colon) LinearIndices_S
            (sz.map .integer) = .error (.core (.inexactError "Int64")))) ∧
    (∀ (convert_Int : AxisRange → IndexResult AxisRange), (∀ r, convert_Int r = .ok r) →
      ∀ rs : List AxisRange, ∃ L, LinearIndices_AbstractUnitRanges convert_Int rs = .ok L ∧
        axisValues R (axes_LinearIndices (AxisRange.axes1 R) L) =
          axisValues R (rs.map (AxisRange.axes1 R))) ∧
    (∀ {X : Type} (convert_Int : AxisRange → IndexResult AxisRange), (∀ r, convert_Int r = .ok r) →
      ∀ (axes : X → List AxisRange) (A : X),
        (∀ r ∈ axes A, (r.axes1 R).first R = r.first R ∧ (r.axes1 R).last R = r.last R) →
        ∃ L, LinearIndices_AbstractArray axes
            (LinearIndices_AbstractUnitRanges convert_Int) A = .ok L ∧
          axisValues R (axes_LinearIndices (AxisRange.axes1 R) L) = axisValues R (axes A))

theorem sizes_fit {I S : Type} {val : I → Int} {oneto : I → S} {colon : I64 → I64 → S}
    {LS : List S → IndexResult (LinearIndices AxisRange)} {toAxis : S → IndexResult AxisRange}
    (hC : ConvertLaws val oneto colon LS toAxis)
    (R : RangeCallees) (hR : RangeLaws R) :
    ∀ sz : List I, (∀ n ∈ sz, fitsInt (val n)) →
      ∃ axs, ((sz.map (IntegerOrRange.integer (R := AxisRange))).map
          (_convert2ind oneto (AxisRange.first R) (AxisRange.last R) colon)).mapM toAxis =
          .ok axs ∧
        axisInts R (axs.map (AxisRange.axes1 R)) = sz.map fun n => (1, val n)
  | [], _ => ⟨[], rfl, rfl⟩
  | n :: ns, h => by
    obtain ⟨axs, hm, hv⟩ := sizes_fit hC R hR ns (fun m hm => h m (by simp [hm]))
    have hn := h n (by simp)
    refine ⟨.base (.oneTo ⟨val n, hn⟩) :: axs, ?_, ?_⟩
    · simp only [List.map_cons, List.mapM_cons, _convert2ind, _convert2ind_Integer,
        hC.oneto_fits n hn, hm, bind, Except.bind, pure, Except.pure]
    · simp only [List.map_cons, axisInts, List.cons.injEq] at hv ⊢
      refine ⟨?_, hv⟩
      simp [AxisRange.axes1, AxisRange.first, AxisRange.last, hR.axes1_oneTo, hR.first_oneTo,
        hR.last_oneTo, int_val_of_fits (show fitsInt 1 by decide)]

theorem sizes_inexact {I S : Type} {val : I → Int} {oneto : I → S} {colon : I64 → I64 → S}
    {LS : List S → IndexResult (LinearIndices AxisRange)} {toAxis : S → IndexResult AxisRange}
    (hC : ConvertLaws val oneto colon LS toAxis)
    (R : RangeCallees) :
    ∀ sz : List I, (∃ n ∈ sz, ¬ fitsInt (val n)) →
      ((sz.map (IntegerOrRange.integer (R := AxisRange))).map
          (_convert2ind oneto (AxisRange.first R) (AxisRange.last R) colon)).mapM toAxis =
        .error (.core (.inexactError "Int64"))
  | [], ⟨_, hm, _⟩ => by simp at hm
  | n :: ns, h => by
    by_cases hn : fitsInt (val n)
    · have hrest : ∃ m ∈ ns, ¬ fitsInt (val m) := by
        obtain ⟨m, hm, hnf⟩ := h
        simp at hm
        rcases hm with rfl | hm
        · exact absurd hn hnf
        · exact ⟨m, hm, hnf⟩
      simp only [List.map_cons, List.mapM_cons, _convert2ind, _convert2ind_Integer,
        hC.oneto_fits n hn, sizes_inexact hC R ns hrest, bind, Except.bind]
    · simp only [List.map_cons, List.mapM_cons, _convert2ind, _convert2ind_Integer,
        hC.oneto_inexact n hn, bind, Except.bind]

theorem linearIndicesConstructors_proven : LinearIndicesConstructors := by
  intro R hR
  refine ⟨fun val oneto colon LS toAxis hC sz => ⟨fun hfit => ?_, fun hbad => ?_⟩,
    fun conv hconv rs => ?_, fun conv hconv axes A hself => ?_⟩
  · obtain ⟨axs, hm, hv⟩ := sizes_fit hC R hR sz hfit
    refine ⟨⟨axs⟩, ?_, ?_⟩
    · simp only [LinearIndices_IntegerOrRanges, hC.construct, hm]; rfl
    · simpa [axes_LinearIndices] using hv
  · simp only [LinearIndices_IntegerOrRanges, hC.construct, sizes_inexact hC R sz hbad]; rfl
  · refine ⟨⟨rs⟩, by simp [LinearIndices_AbstractUnitRanges, mapM_ok_id conv hconv, bind,
      Except.bind, pure, Except.pure], ?_⟩
    simp [axes_LinearIndices, axisValues]
  · refine ⟨⟨axes A⟩, by simp [LinearIndices_AbstractArray, LinearIndices_AbstractUnitRanges,
      mapM_ok_id conv hconv, bind, Except.bind, pure, Except.pure], ?_⟩
    simp only [axes_LinearIndices, axisValues, List.map_map]
    apply List.map_congr_left
    intro r hr
    simp [(hself r hr).1, (hself r hr).2]

/-- The length of each axis, `last - first + 1`. -/
def axisLengths (R : RangeCallees) (rs : List AxisRange) : List Int :=
  rs.map fun r => (r.last R).val - (r.first R).val + 1

/-- `LinearIndices` docstring: for a vector the linear indices are `axes(A, 1)`; for any other
array they run from 1 to `length(A)` (`first`, `last`), where `length(A)` is the product of the
axis lengths (`abstractarray.jl`). Indexing with an `Int` returns that index inside these
bounds and throws `BoundsError` outside (`checkbounds` accepts exactly
`eachindex(IndexLinear(), L)`), and `isassigned` holds exactly inside them. `IndexStyle` of a
`LinearIndices` is `IndexLinear()`. -/
def LinearIndicesValues : Prop :=
  ∀ (R : RangeCallees), RangeLaws R →
    ∀ (lengthL : LinearIndices AxisRange → I64)
      (checkbounds : LinearIndices AxisRange → I64 → IndexResult Unit)
      (checkbounds_Bool : LinearIndices AxisRange → I64 → Bool),
      (∀ L, fitsInt (axisLengths R (axes_LinearIndices (AxisRange.axes1 R) L)).prod →
        (lengthL L).val = (axisLengths R (axes_LinearIndices (AxisRange.axes1 R) L)).prod) →
      (∀ L i, checkbounds L i =
        if (first_LinearIndices_dispatch R L).val ≤ i.val ∧
          i.val ≤ (last_LinearIndices_dispatch R lengthL L).val then .ok ()
        else .error .boundsError) →
      (∀ L i, checkbounds_Bool L i = decide ((first_LinearIndices_dispatch R L).val ≤ i.val ∧
          i.val ≤ (last_LinearIndices_dispatch R lengthL L).val)) →
    ∀ (axs : List AxisRange),
      (∀ r ∈ axs, (r.axes1 R).first R = r.first R ∧ (r.axes1 R).last R = r.last R) →
      let L : LinearIndices AxisRange := ⟨axs⟩
      (axs.length = 1 → ∀ r, axs = [r] →
        first_LinearIndices_dispatch R L = r.first R ∧
        last_LinearIndices_dispatch R lengthL L = r.last R) ∧
      (axs.length ≠ 1 →
        first_LinearIndices_dispatch R L = int 1 ∧
        (fitsInt (axisLengths R axs).prod →
          (last_LinearIndices_dispatch R lengthL L).val = (axisLengths R axs).prod)) ∧
      (∀ i : I64, getindex_LinearIndices_Int checkbounds L i =
        (if (first_LinearIndices_dispatch R L).val ≤ i.val ∧
          i.val ≤ (last_LinearIndices_dispatch R lengthL L).val then .ok i
        else .error .boundsError) ∧
        (isassigned_LinearIndices checkbounds_Bool L i = true ↔
          (first_LinearIndices_dispatch R L).val ≤ i.val ∧
            i.val ≤ (last_LinearIndices_dispatch R lengthL L).val)) ∧
      IndexStyle_Type .linearIndices = .linear

theorem linearIndicesValues_proven : LinearIndicesValues := by
  intro R hR lengthL cb cbB hlen hcb hcbB axs hself
  have hsame : axisLengths R (axes_LinearIndices (AxisRange.axes1 R) ⟨axs⟩) = axisLengths R axs := by
    simp only [axisLengths, axes_LinearIndices, List.map_map]
    apply List.map_congr_left
    intro r hr
    simp [(hself r hr).1, (hself r hr).2]
  refine ⟨fun _ r hr => ?_, fun hn => ⟨?_, fun hfit => ?_⟩, fun i => ⟨?_, ?_⟩, rfl⟩
  · subst hr
    have := hself r (by simp)
    simp [first_LinearIndices_dispatch, last_LinearIndices_dispatch, first_LinearIndices_1,
      last_LinearIndices_1, this.1, this.2]
  · simp [first_LinearIndices_dispatch, hn, first_LinearIndices]
  · simp only [last_LinearIndices_dispatch, hn, if_false, last_LinearIndices]
    rw [hlen _ (by rw [hsame]; exact hfit), hsame]
  · simp only [getindex_LinearIndices_Int, hcb]
    split <;> rfl
  · simp [isassigned_LinearIndices, hcbB]

/-- Iterating the values of `iterate(L, i)` from state `s`, for at most `fuel` steps. -/
def iterValues (next : I64 → Option (I64 × I64)) : Nat → I64 → List I64
  | 0, _ => []
  | fuel + 1, s => match next s with
    | none => []
    | some (v, s') => v :: iterValues next fuel s'

theorem iterate_LinearIndices_eq {R : Type} (lengthL : LinearIndices R → I64)
    (L : LinearIndices R) (i : I64) :
    iterate_LinearIndices lengthL L i =
      if (lengthL L).val < i.val then none else some (i, int (i.val + 1)) := by
  unfold iterate_LinearIndices
  rw [JuliaLean.Proofs.base.int.ltSignedExact_proven .i64 rfl]
  have hadd := JuliaLean.Proofs.base.int.addWraps_proven .i64 i (int 1)
  have h1 : (int 1).val = 1 := rfl
  by_cases h : (lengthL L).val < i.val
  · simp [h]
  · simp only [h, decide_false, if_false, Bool.false_eq_true]
    congr 2
    apply Subtype.ext
    rw [hadd, h1]
    rfl

/-- `LinearIndices` iteration (`base/indices.jl:523`, the method for every rank except 1, whose
iteration is that of its axis, `:522`) produces the linear indices `1, 2, …, length(L)`, the
values of `L` in order, and then ends, for every such `LinearIndices` shorter than
`typemax(Int)`. -/
def LinearIndicesIterate : Prop :=
  ∀ {R : Type} (lengthL : LinearIndices R → I64) (L : LinearIndices R), L.indices.length ≠ 1 →
    0 ≤ (lengthL L).val → (lengthL L).val < IntTy.max .i64 →
      iterValues (fun s => iterate_LinearIndices lengthL L s) ((lengthL L).val.toNat + 1)
          (int 1) =
        (List.range (lengthL L).val.toNat).map (fun k : Nat => int ((k : Int) + 1))

theorem iterValues_step {R : Type} (lengthL : LinearIndices R → I64) (L : LinearIndices R)
    (k : Nat) (s : I64) :
    iterValues (fun s => iterate_LinearIndices lengthL L s) (k + 1) s =
      if (lengthL L).val < s.val then []
      else s :: iterValues (fun s => iterate_LinearIndices lengthL L s) k (int (s.val + 1)) := by
  show (match iterate_LinearIndices lengthL L s with
    | none => []
    | some (v, s') => v :: iterValues (fun s => iterate_LinearIndices lengthL L s) k s') = _
  rw [iterate_LinearIndices_eq]
  by_cases h : (lengthL L).val < s.val
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem iterValues_from {R : Type} (lengthL : LinearIndices R → I64) (L : LinearIndices R)
    (n : Nat) (hn : (lengthL L).val = n) (hlen : (n : Int) < IntTy.max .i64) :
    ∀ (j : Nat), j ≤ n + 1 → 1 ≤ j →
      iterValues (fun s => iterate_LinearIndices lengthL L s) (n + 2 - j) (int j) =
        (List.range (n + 1 - j)).map (fun k : Nat => int ((k : Int) + j)) := by
  have hmin : IntTy.min .i64 ≤ 0 := by decide
  intro j hj hj1
  have hjv : (int j).val = j := int_val_of_fits ⟨by omega, by omega⟩
  generalize hm : n + 1 - j = m
  induction m generalizing j with
  | zero =>
    have hlt : (lengthL L).val < (int j).val := by rw [hn, hjv]; omega
    rw [show n + 2 - j = 0 + 1 by omega, iterValues_step, if_pos hlt]
    rfl
  | succ m ih =>
    have hfuel : n + 2 - j = (n + 2 - (j + 1)) + 1 := by omega
    have hle : ¬ (lengthL L).val < (int j).val := by rw [hn, hjv]; omega
    rw [hfuel]
    rw [iterValues_step, if_neg hle, hjv, show ((j : Int) + 1) = ((j + 1 : Nat) : Int) by omega,
      ih (j + 1) (by omega) (by omega) (int_val_of_fits ⟨by omega, by omega⟩) (by omega)]
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    rw [List.cons.injEq]
    refine ⟨by simp, ?_⟩
    apply List.map_congr_left
    intro k _
    simp only [Function.comp]
    exact congrArg int (by push_cast; omega)

theorem linearIndicesIterate_proven : LinearIndicesIterate := by
  intro R lengthL L _ h0 hlen
  obtain ⟨n, hn⟩ : ∃ n : Nat, (lengthL L).val = n :=
    ⟨(lengthL L).val.toNat, (Int.toNat_of_nonneg h0).symm⟩
  have hlen' : (n : Int) < IntTy.max .i64 := by
    rw [← hn]; exact hlen
  have := iterValues_from lengthL L n hn hlen' 1 (by omega) (by omega)
  rw [hn, Int.toNat_natCast]
  simpa using this

/-- Iteration protocol (manual, "Iteration"): after `iterate(L, s)` returns the last element
`length(L)` with the next state, `iterate` from that state returns `nothing`. Here
`length(L)` is the product of the axis lengths. -/
def LinearIndicesIterateEnds : Prop :=
  ∀ (R : RangeCallees), RangeLaws R → ∀ (lengthL : LinearIndices AxisRange → I64),
    (∀ L, fitsInt (axisLengths R (axes_LinearIndices (AxisRange.axes1 R) L)).prod →
      (lengthL L).val = (axisLengths R (axes_LinearIndices (AxisRange.axes1 R) L)).prod) →
    ∀ (L : LinearIndices AxisRange) (s : I64), 1 ≤ (lengthL L).val →
      iterate_LinearIndices lengthL L (lengthL L) = some (lengthL L, s) →
      iterate_LinearIndices lengthL L s = none

/-- `LinearIndices((typemax(Int), 1))`: the state after `typemax(Int)` wraps to `typemin(Int)`
and iteration continues. -/
theorem linearIndicesIterateEnds_refuted : ¬ LinearIndicesIterateEnds := by
  intro h
  let L : LinearIndices AxisRange := ⟨[.base (.oneTo (int 9223372036854775807)), .base (.oneTo (int 1))]⟩
  let lengthL : LinearIndices AxisRange → I64 := fun L =>
    int (axisLengths lawfulRange (axes_LinearIndices (AxisRange.axes1 lawfulRange) L)).prod
  have hv : lengthL L = int 9223372036854775807 := by decide +kernel
  have := h lawfulRange lawfulRange_laws lengthL (fun _ hf => int_val_of_fits hf) L
    (int (9223372036854775807 + 1)) (by rw [hv]; decide)
    (by rw [iterate_LinearIndices_eq, hv]; decide)
  rw [iterate_LinearIndices_eq, hv] at this
  revert this
  decide +kernel

theorem int_val (x : I64) : int x.val = x :=
  Subtype.ext (int_val_of_fits (fits_val x))

/-- `range.jl`: indexing a unit range `r` with a unit range `a:b` gives the unit range of
`r[k] = first(r) + k - 1` for `k` in `a:b`. -/
def RangeGetindexLaw (R : RangeCallees) (getindex_R : AxisRange → BaseRange → IndexResult BaseRange) :
    Prop :=
  ∀ r a b, getindex_R r (.unitRange a b) = .ok (.unitRange
    (int ((r.first R).val + a.val - 1)) (int ((r.first R).val + b.val - 1)))

/-- `LinearIndices` docstring: a `LinearIndices` holds the linear index of each entry, so
`L[a:b]` for `a:b` inside `first(L):last(L)` is `[L[k] for k in a:b]`, which is `a:b` because
`L[k] == k` (`getindex(::LinearIndices, ::Int)`). -/
def LinearIndicesRangeIndex : Prop :=
  ∀ (R : RangeCallees), RangeLaws R →
    ∀ (getindex_R : AxisRange → BaseRange → IndexResult BaseRange), RangeGetindexLaw R getindex_R →
    ∀ (lengthL : LinearIndices AxisRange → I64) (colon : I64 → I64 → AxisRange),
      (∀ a b, colon a b = .base (.unitRange a b)) →
    ∀ (checkbounds : LinearIndices AxisRange → BaseRange → IndexResult Unit)
      (L : LinearIndices AxisRange) (a b : I64), a.val ≤ b.val →
      (first_LinearIndices_dispatch R L).val ≤ a.val →
      b.val ≤ (last_LinearIndices_dispatch R lengthL L).val →
      checkbounds L (.unitRange a b) = .ok () →
      ∃ out, getindex_LinearIndices_AbstractRange checkbounds getindex_R
          (first_LinearIndices_dispatch R) (last_LinearIndices_dispatch R lengthL) colon L
          (.unitRange a b) = .ok out ∧ R.first out = a ∧ R.last out = b

/-- `LinearIndices((3:5,))[2:3]` is `4:5`, not `2:3`: the vector method indexes the stored
range `3:5` instead of the linear indices `1:3`. -/
theorem linearIndicesRangeIndex_refuted : ¬ LinearIndicesRangeIndex := by
  intro h
  obtain ⟨out, hout, h1, _⟩ := h lawfulRange lawfulRange_laws
    (fun r i => match i with
      | .unitRange a b => .ok (.unitRange (int ((r.first lawfulRange).val + a.val - 1))
          (int ((r.first lawfulRange).val + b.val - 1)))
      | x => .ok x) (fun _ _ _ => rfl) (fun _ => int 0)
    (fun a b => .base (.unitRange a b)) (fun _ _ => rfl) (fun _ _ => .ok ())
    ⟨[.base (.unitRange (int 3) (int 5))]⟩ (int 2) (int 3) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) rfl
  simp only [getindex_LinearIndices_AbstractRange, bind, Except.bind] at hout
  rw [if_pos (by rfl), Except.ok.injEq] at hout
  subst hout
  revert h1
  decide +kernel

/-- For a `LinearIndices` of any rank other than 1, `L[a:b]` for `a:b` inside `1:length(L)`
is `a:b` (`base/indices.jl:514-518`, the `first(iter):last(iter)` branch). -/
def LinearIndicesRangeIndexND : Prop :=
  ∀ (R : RangeCallees), RangeLaws R →
    ∀ (getindex_R : AxisRange → BaseRange → IndexResult BaseRange), RangeGetindexLaw R getindex_R →
    ∀ (lengthL : LinearIndices AxisRange → I64) (colon : I64 → I64 → AxisRange),
      (∀ a b, colon a b = .base (.unitRange a b)) →
    ∀ (checkbounds : LinearIndices AxisRange → BaseRange → IndexResult Unit)
      (L : LinearIndices AxisRange) (a b : I64), L.indices.length ≠ 1 → a.val ≤ b.val →
      (first_LinearIndices_dispatch R L).val ≤ a.val →
      b.val ≤ (last_LinearIndices_dispatch R lengthL L).val →
      checkbounds L (.unitRange a b) = .ok () →
      ∃ out, getindex_LinearIndices_AbstractRange checkbounds getindex_R
          (first_LinearIndices_dispatch R) (last_LinearIndices_dispatch R lengthL) colon L
          (.unitRange a b) = .ok out ∧ R.first out = a ∧ R.last out = b

theorem linearIndicesRangeIndexND_proven : LinearIndicesRangeIndexND := by
  intro R hR gR hg lengthL colon hcolon cb L a b hn _ _ _ hcb
  have hfirst : first_LinearIndices_dispatch R L = int 1 := by
    simp [first_LinearIndices_dispatch, hn, first_LinearIndices]
  refine ⟨.unitRange a b, ?_, hR.first_unitRange a b, hR.last_unitRange a b⟩
  simp only [getindex_LinearIndices_AbstractRange, hcb, hn, if_false, hcolon, hg,
    AxisRange.first, hR.first_unitRange, hfirst, bind, Except.bind]
  have h1 : (int 1).val = 1 := rfl
  rw [hg]
  simp only [AxisRange.first, hR.first_unitRange, h1,
    show ∀ x : Int, 1 + x - 1 = x from fun x => by omega, int_val]

/-- `LinearIndices` docstring, for a vector `v` of length `n` (axis `Base.OneTo(n)`):
converting a Cartesian index back with `LinearIndices(v)` gives the linear index, and both
`CartesianIndices(v)[i]` and `LinearIndices(v)[i]` throw `BoundsError` outside `1:n`. -/
def LinearCartesianRoundTrip : Prop :=
  ∀ (R : RangeCallees), RangeLaws R → ∀ (n : I64), 0 ≤ n.val →
    ∀ (lengthL : LinearIndices AxisRange → I64)
      (checkbounds : LinearIndices AxisRange → I64 → IndexResult Unit),
      (∀ L i, checkbounds L i =
        if (first_LinearIndices_dispatch R L).val ≤ i.val ∧
          i.val ≤ (last_LinearIndices_dispatch R lengthL L).val then .ok ()
        else .error .boundsError) →
    ∀ (cartesianGet : I64 → IndexResult I64),
      (∀ k, cartesianGet k = if 1 ≤ k.val ∧ k.val ≤ n.val then .ok k else .error .boundsError) →
    ∀ (convert_Int : AxisRange → IndexResult AxisRange), (∀ r, convert_Int r = .ok r) →
    ∃ L, LinearIndices_AbstractArray (fun (_ : Unit) => [AxisRange.base (.oneTo n)])
        (LinearIndices_AbstractUnitRanges convert_Int) () = .ok L ∧
      ∀ k : I64, (do
        let c ← cartesianGet k
        getindex_LinearIndices_Int checkbounds L c) =
          if 1 ≤ k.val ∧ k.val ≤ n.val then .ok k else .error .boundsError

theorem linearCartesianRoundTrip_proven : LinearCartesianRoundTrip := by
  intro R hR n _ lengthL cb hcb cg hcg conv hconv
  refine ⟨⟨[.base (.oneTo n)]⟩, by simp [LinearIndices_AbstractArray,
    LinearIndices_AbstractUnitRanges, hconv, bind, Except.bind, pure, Except.pure], fun k => ?_⟩
  have hf : first_LinearIndices_dispatch R ⟨[.base (.oneTo n)]⟩ = int 1 := by
    simp [first_LinearIndices_dispatch, first_LinearIndices_1, AxisRange.axes1, AxisRange.first,
      hR.axes1_oneTo, hR.first_oneTo]
  have hl : last_LinearIndices_dispatch R lengthL ⟨[.base (.oneTo n)]⟩ = n := by
    simp [last_LinearIndices_dispatch, last_LinearIndices_1, AxisRange.axes1, AxisRange.last,
      hR.axes1_oneTo, hR.last_oneTo]
  have h1 : (int 1).val = 1 := rfl
  rw [hcg]
  by_cases hk : 1 ≤ k.val ∧ k.val ≤ n.val
  · simp [hk, getindex_LinearIndices_Int, hcb, hf, hl, h1, bind, Except.bind, pure, Except.pure]
  · simp [hk, bind, Except.bind]

/-! ## Promotion rules -/

def intType : PType := .data ⟨"Core", "Int64"⟩ "Int64" [] (some .any)
def oneToType : PType := .data ⟨"Base", "OneTo"⟩ "Base.OneTo" [intType] (some .any)
def unitRangeType : PType := .data ⟨"Base", "UnitRange"⟩ "UnitRange" [intType] (some .any)

/-- Promotion (manual, "Promotion": promotion converts values "to a single common type" and
"has nothing to do with the type hierarchy", i.e. it is not their abstract supertype): for two
`Slice` (or `IdentityUnitRange`) types whose wrapped range types promote to a common range type,
`promote_rule` gives a `Slice` (`IdentityUnitRange`) representation, not the join of the two
wrapper types. The callees follow their methods in `range.jl:1331-1334`: every `Slice` and
`IdentityUnitRange` has element type `Int`, so `el_same(T, a, b)` for `T` other than `Int` is
`promote_typejoin(a, b)`, and the type join of two different instances of a wrapper is not an
instance of it. -/
def SlicePromoteRule : Prop :=
  ∀ (promote_type : PType → PType → PType) (el_same : PType → PType → PType → PType)
    (promote_typejoin : PType → PType → PType),
    (∀ T X Y, pEqual T intType = false →
      el_same T (sliceType X) (sliceType Y) = promote_typejoin (sliceType X) (sliceType Y) ∧
      el_same T (identityUnitRangeType X) (identityUnitRangeType Y) =
        promote_typejoin (identityUnitRangeType X) (identityUnitRangeType Y)) →
    (∀ X Y Z, pEqual X Y = false →
      promote_typejoin (sliceType X) (sliceType Y) ≠ sliceType Z ∧
      promote_typejoin (identityUnitRangeType X) (identityUnitRangeType Y) ≠
        identityUnitRangeType Z) →
    ∀ T1 T2, pEqual (promote_type T1 T2) intType = false →
      (∃ X, promote_rule_Slice promote_type el_same T1 T2 = sliceType X) ∧
      (∃ X, promote_rule_IdentityUnitRange promote_type el_same T1 T2 = identityUnitRangeType X)

/-- `promote_type(Slice{OneTo{Int}}, Slice{UnitRange{Int}})` is the `UnionAll` `Base.Slice`. -/
theorem slicePromoteRule_refuted : ¬ SlicePromoteRule := by
  intro h
  obtain ⟨X, hX⟩ := (h (fun _ _ => unitRangeType) (fun _ a b => (fun _ _ => PType.any) a b)
    (fun _ _ => .any) (fun _ _ _ _ => ⟨rfl, rfl⟩)
    (fun _ _ _ _ => ⟨fun e => (by cases e), fun e => (by cases e)⟩) oneToType unitRangeType
    (by decide +kernel)).1
  simp [promote_rule_Slice, sliceType] at hX

/-- `NTuple{N, R}`: the tuple type of `N` entries `R`, `Tuple{}` for `N = 0`. -/
def ntupleType (N : Nat) (R : PType) : PType :=
  .data tupleTypeName "Tuple" (List.replicate N R) (some .any)

/-- The rank and the entry types of a `LinearIndices{N, Tuple{…}}` type. -/
def linearIndicesParams : PType → Option (String × List PType)
  | .data name _ [.parameter n, .data tname _ ps _] _ =>
    if name = ⟨"Base", "LinearIndices"⟩ ∧ tname = tupleTypeName then some (n, ps) else none
  | _ => none

theorem homogeneousTupleParams_ntuple (n : Nat) (R : PType) (hR : pIsVararg R = false) :
    homogeneousTupleParams (ntupleType (n + 1) R) = some (R, n) := by
  have hall : (List.replicate n R).all (pEqual R) = true := by
    rw [List.all_eq_true]
    intro x hx
    rw [List.eq_of_mem_replicate hx]
    exact JuliaLean.Proofs.base.promotion.pEqual_refl R
  simp [ntupleType, List.replicate_succ, homogeneousTupleParams, hR, hall]

/-- Promotion of `LinearIndices` (manual, "Promotion": both values are converted to the common
type). For ranks `N > 0`, the promotion rule for `LinearIndices{N,NTuple{N,R1}}` and
`LinearIndices{N,NTuple{N,R2}}` is a `LinearIndices` of the same rank `N` whose `N` ranges have
the promoted range type `promote_type(R1, R2)`. At rank 0 both tuple types are `Tuple{}`, which
`indices_promote_type` has no method for, so the rule throws that `MethodError`. Converting a
rank-`N` `LinearIndices` to a rank-`N` type with a range `convert` that keeps every range's
values (`convert(R, inds)`, `base/indices.jl:479`) keeps its rank and the values of its axes. -/
def LinearIndicesPromotion : Prop :=
  (∀ (promote_type : PType → PType → PType) (N : Nat) (R1 R2 : PType),
    0 < N → pIsVararg R1 = false → pIsVararg R2 = false →
    ∃ T, promote_rule_LinearIndices promote_type N (ntupleType N R1) (ntupleType N R2) = .ok T ∧
      linearIndicesParams T = some (toString N, List.replicate N (promote_type R1 R2))) ∧
  (∀ promote_type : PType → PType → PType,
    promote_rule_LinearIndices promote_type 0 (ntupleType 0 .any) (ntupleType 0 .any) =
      .error ⟨"indices_promote_type", [.value (ntupleType 0 .any), .value (ntupleType 0 .any)]⟩) ∧
  (∀ (R : RangeCallees) (N : Nat)
    (convert_R : {l : List AxisRange // l.length = N} →
      IndexResult {l : List AxisRange // l.length = N}),
    (∀ l, ∃ l', convert_R l = .ok l' ∧ axisValues R l'.1 = axisValues R l.1) →
    ∀ inds : {L : LinearIndices AxisRange // L.indices.length = N},
      ∃ out, convert_LinearIndices N convert_R inds = .ok out ∧
        out.1.indices.length = N ∧ axisValues R out.1.indices = axisValues R inds.1.indices)

theorem linearIndicesPromotion_proven : LinearIndicesPromotion := by
  refine ⟨fun pt N R1 R2 hN h1 h2 => ?_, fun pt => ?_, fun R N conv hconv inds => ?_⟩
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    refine ⟨linearIndicesType (n + 1) (homogeneousTupleType (pt R1 R2) n), ?_, ?_⟩
    · simp [promote_rule_LinearIndices, indices_promote_type_dispatch,
        homogeneousTupleParams_ntuple n R1 h1, homogeneousTupleParams_ntuple n R2 h2,
        indices_promote_type, bind, Except.bind, pure, Except.pure]
    · simp [linearIndicesType, homogeneousTupleType, linearIndicesParams]
  · rfl
  obtain ⟨l', hl', hv⟩ := hconv ⟨inds.1.indices, inds.2⟩
  refine ⟨⟨⟨l'.1⟩, l'.2⟩, ?_, l'.2, hv⟩
  simp [convert_LinearIndices, hl', bind, Except.bind, pure, Except.pure]

/-! Nothing to promise:
Dims@9: type alias for a tuple of `Int`s; no behaviour.
DimsInteger@10: type alias; no behaviour.
Indices@11: type alias; no behaviour.
IndexStyle@15: abstract type declaration; no behaviour.
IndexLinear@37: singleton trait type; its meaning is stated through `IndexStyle`.
IndexCartesian@66: singleton trait type; its meaning is stated through `IndexStyle`.
Slice@337: struct declaration; its methods carry the behaviour.
Slice@340: returns its argument, so a `Slice` is never wrapped twice; nothing beyond identity.
Slice@341: converts the wrapped range with the requested range type's constructor; the conversion is that constructor's behaviour.
size@349: forwards `length` of the wrapped range.
show@353: printing only.
iterate@354: forwards iteration to the wrapped range.
IdentityUnitRange@363: struct declaration; its methods carry the behaviour.
IdentityUnitRange@366: returns its argument; nothing beyond identity.
IdentityUnitRange@367: converts the wrapped range with the requested range type's constructor.
size@376: forwards `length` of the wrapped range.
unsafe_length@377: forwards `unsafe_length` of the wrapped range.
show@416: printing only.
iterate@417: forwards iteration to the wrapped range.
LinearIndices@476: struct declaration; its methods carry the behaviour.
LinearIndices@482: builds the rank-0 instance from the empty tuple; no axes to state.
copy@519: `LinearIndices` is immutable, so `copy` returns the same value.
iterate@522: forwards iteration of a one-dimensional `LinearIndices` to its axis.
show@531: printing only.
size@507: forwards `length` of each stored range.
to_index@260: wraps a Boolean array in `LogicalIndex` (multidimensional.jl), whose behaviour belongs to that type.
to_index@261: returns the index array unchanged.
to_index@262: returns the index array unchanged.
to_indices@310: forwards to `_to_indices` with the dropped-zero-dimension tuple; bootstrap plumbing.
to_indices@311: forwards a single index together with `eachindex(IndexLinear(), A)`; plumbing.
_to_indices@312: forwards to the per-dimension walk with `axes(A)`; plumbing.
_to_indices@313: forwards a single remaining index to `to_indices(A, J)`; plumbing.
_drop_zerodim@314: returns the empty tuple; in this file `_drop_zerodim` keeps every element (the `CartesianIndex{0}` method lives in multidimensional.jl).
_drop_zerodim@315: copies the tuple element by element; see `_drop_zerodim@314`.
-/

/-!
## Method → property table

| Julia method | Property |
|---|---|
| IndexStyle@94 | multidimcov-indices-repair-indexstyle; reducecov-indices-indexstyle |
| IndexStyle@95 | multidimcov-indices-repair-indexstyle |
| IndexStyle@96 | multidimcov-indices-repair-indexstyle |
| IndexStyle@97 | multidimcov-indices-repair-indexstyle |
| IndexStyle@98 | multidimcov-indices-repair-indexstyle |
| IndexStyle@99 | multidimcov-indices-repair-indexstyle |
| IndexStyle@101 | multidimcov-indices-repair-indexstyle; reducecov-indices-indexstyle |
| IndexStyle@102 | reducecov-indices-indexstyle |
| IndexStyle@103 | multidimcov-indices-repair-indexstyle; reducecov-indices-indexstyle |
| IndexStyle@104 | multidimcov-indices-repair-indexstyle; reducecov-indices-indexstyle |
| promote_shape@108 | multidimcov-indices-repair-shape |
| throw_promote_shape_mismatch@112 | multidimcov-indices-repair-shape; reducecov-promote-shape-message |
| _normalize@119 | reducecov-promote-shape-message |
| promote_shape@139 | indices-promote-shape-fixed |
| promote_shape@144 | indices-promote-shape-fixed |
| promote_shape@149 | indices-promote-shape-fixed |
| promote_shape@151 | indices-promote-shape-fixed |
| promote_shape@175 | multidimcov-indices-repair-shape |
| promote_shape@188 | indices-promote-shape-axes |
| promote_shape@192 | indices-promote-shape-axes |
| throw_setindex_mismatch@205 | indices-setindex-shape |
| setindex_shape_check@214 | indices-setindex-shape |
| _shapes_match@217-220 | indices-setindex-shape |
| setindex_shape_check@222 | indices-setindex-shape |
| setindex_shape_check@227 | indices-setindex-shape |
| to_index@243 | indices-to-index-conversion; indices-to-indices |
| to_index@247 | arrayops-getindex-checkbounds; arrayops-index-type-exception |
| to_index@258 | indices-to-index-conversion; arrayops-getindex-checkbounds; arrayops-index-type-exception |
| to_index@259 | indices-to-index-conversion |
| to_index@263 | indices-to-index-conversion |
| to_index@265 | indices-to-index-conversion |
| to_index@266 | indices-to-index-conversion |
| to_indices@318 | indices-to-indices |
| to_indices@319 | indices-to-indices |
| to_indices@320 | indices-to-indices |
| to_indices@321 | indices-to-indices |
| to_indices@322 | indices-to-indices; arrayops-index-type-exception |
| axes@343, axes1@344, axes1@345 | indices-slice-contract |
| first@347, last@348 | indices-slice-contract |
| getindex@350 | indices-slice-contract; reducecov-slice-integer-index |
| getindex@351 | indices-slice-contract; reducecov-slice-bool-range |
| getindex@352 | indices-slice-contract |
| axes@370, axes1@371, axes1@372, first@374, last@375 | indices-identity-contract |
| getindex@378, getindex@379, getindex@380, getindex@390 | indices-identity-contract |
| getindex@385 | indices-identity-bool-unitrange |
| getindex@395 | reducecov-identityrange-bool-step |
| getindex@404, getindex@410, getindex@423 | indices-identity-contract; indices-slice-contract |
| LinearIndices@483 | indices-linear-constructors |
| LinearIndices@485, _convert2ind@489, _convert2ind@490 | indices-linear-constructors; reducecov-linearindices-mixed-axes |
| LinearIndices@487 | indices-linear-constructors; arrayops-linear-cartesian-1d |
| promote_rule@499, promote_rule@501 | reducecov-slice-promote-rule |
| convert@479, indices_promote_type@492, promote_rule@497 | indices-linearindices-promotion |
| IndexStyle@505 | multidimcov-indices-repair-indexstyle; indices-linear-values |
| axes@506 | indices-linear-constructors; reducecov-linearindices-mixed-axes |
| isassigned@508 | indices-linear-values |
| getindex@509 | indices-linear-values; arrayops-linear-cartesian-1d; arrayops-index-type-exception |
| getindex@514 | reducecov-linearindices-range-index; indices-linearindices-range-index-nd |
| iterate@523 | indices-linearindices-iterate; indices-linearindices-iterate-end |
| first@526, first@527, last@528, last@529 | indices-linear-values; arrayops-linear-cartesian-1d |
-/

private def entry (id : String) (fns : List String) (statement source : String)
    (status : Status) (prop thm : Lean.Name) (issue notes : String := "") : Entry :=
  { id, juliaFile := "base/indices.jl", juliaFns := fns, statement, source, status, prop,
    thm := some thm, issue, notes }

def entries : List Entry := [
  entry "multidimcov-indices-repair-indexstyle"
    ["IndexStyle(A::AbstractArray)", "IndexStyle(::Type{Union{}})",
     "IndexStyle(::Type{Union{}}, slurp...)", "IndexStyle(::Type{<:AbstractArray})",
     "IndexStyle(::Type{<:Array})", "IndexStyle(::Type{<:AbstractRange})",
     "IndexStyle(::Type{<:LinearIndices})", "IndexStyle(A::AbstractArray, B::AbstractArray)",
     "IndexStyle(::IndexLinear, ::IndexLinear)", "IndexStyle(::IndexStyle, ::IndexStyle)"]
    "New array types default to IndexCartesian(); Array, ranges and LinearIndices are IndexLinear(); a type's own method is used; two styles, and two arrays, combine to IndexLinear() exactly when both are linear; IndexStyle(Union{}, x...) has no method and throws a MethodError recording the arguments (Union{}, x...) whatever their types."
    "IndexStyle docstring; base/indices.jl:94-104,505" .proven
    ``IndexStyleCombination ``indexStyleCombination_proven,
  entry "reducecov-indices-indexstyle"
    ["IndexStyle(A::AbstractArray, B::AbstractArray...)", "IndexStyle(A::AbstractArray, B::AbstractArray)",
     "IndexStyle(::IndexLinear, ::IndexLinear)", "IndexStyle(::IndexStyle, ::IndexStyle)"]
    "IndexStyle(A, B...) for any number of arrays is IndexLinear() exactly when every argument's style is IndexLinear()."
    "IndexStyle docstring; base/indices.jl:94,101-104" .proven
    ``IndexStyleAllLinear ``indexStyleAllLinear_proven,
  entry "multidimcov-indices-repair-shape"
    ["promote_shape(a::Dims, b::Dims)", "promote_shape(::Tuple{}, ::Tuple{})",
     "throw_promote_shape_mismatch"]
    "promote_shape of two Dims returns the longer shape when they agree in the common dimensions and the rest are 1, and otherwise throws DimensionMismatch printing both shapes and the first incompatible dimension."
    "promote_shape docstring; base/indices.jl:108-137,155-186" .proven
    ``PromoteShapeDims ``promoteShapeDims_proven,
  entry "indices-promote-shape-fixed"
    ["promote_shape(a::Tuple{Int,}, b::Tuple{Int,})", "promote_shape(a::Tuple{Int,Int}, b::Tuple{Int,})",
     "promote_shape(a::Tuple{Int,}, b::Tuple{Int,Int})", "promote_shape(a::Tuple{Int,Int}, b::Tuple{Int,Int})"]
    "The one- and two-dimensional promote_shape methods give the same shape as the general Dims method, or throw DimensionMismatch exactly when it does."
    "invariant (specialisations of promote_shape); base/indices.jl:138-154" .proven
    ``PromoteShapeFixed ``promoteShapeFixed_proven,
  entry "indices-promote-shape-axes"
    ["promote_shape(a::Indices, b::Indices)", "promote_shape(a::AbstractArray, b::AbstractArray)"]
    "promote_shape of axis tuples, and of two arrays through their axes, returns the longer axis tuple when the axes agree in the common dimensions and the rest equal 1:1, and throws otherwise."
    "promote_shape docstring; base/indices.jl:187-203" .proven
    ``PromoteShapeAxes ``promoteShapeAxes_proven,
  entry "reducecov-promote-shape-message"
    ["throw_promote_shape_mismatch", "_normalize", "promote_shape(a::Indices, b::Indices)"]
    "When promote_shape compares axis tuples, the DimensionMismatch message prints each argument's axes as ranges with the same values (first and last) as those axes, hiding only type details such as OneTo."
    "comment at base/indices.jl:110-111; promote_shape docstring" .refuted
    ``PromoteShapeMessage ``promoteShapeMessage_refuted
    "none found"
    "promote_shape((Base.OneTo(3),), (2:4,)) reports `a has axes (1:3,), b has axes (1:3,)`: _normalize uses firstindex(x):lastindex(x), which for 2:4 is 1:3.",
  entry "indices-setindex-shape"
    ["throw_setindex_mismatch", "setindex_shape_check(X::AbstractArray, i::Integer)",
     "_shapes_match", "setindex_shape_check(X::AbstractArray, shape::Tuple{Vararg{Integer}})",
     "setindex_shape_check(::Any, ::Tuple)"]
    "For shape entries of any Integer type (BigInt included), indexed assignment accepts (returns true for) a value whose element count matches a single index or a vector destination, or whose size matches the destination shape up to trailing singleton dimensions; otherwise it throws DimensionMismatch, and a non-array value for many destinations throws ArgumentError."
    "base/indices.jl:204-228" .proven
    ``SetindexShapeCheck ``setindexShapeCheck_proven,
  entry "indices-to-index-conversion"
    ["to_index(A, i)", "to_index(i::Integer)", "to_index(i::Bool)", "to_index(::Colon)",
     "to_index(I::AbstractArray{<:Union{AbstractArray, Colon}})", "to_index(i)"]
    "to_index converts an integer of any Integer type (BitIntegers, BigInt, user integers with the documented convert(Int, i)) to the Int with the same value and throws InexactError when Int cannot represent it; to_index(A, i) defaults to to_index(i); Bool, Colon, nested arrays and other unsupported index types throw ArgumentError naming the index and its type."
    "to_index docstrings; base/indices.jl:229-266" .proven
    ``ToIndexConversion ``toIndexConversion_proven,
  entry "arrayops-getindex-checkbounds"
    ["getindex(::Array, i::Integer)", "to_index(A::Array, i::UInt)", "to_index(i::Integer)",
     "checkbounds(Bool, A, i)"]
    "v[i] for an index of any BitInteger type that to_index accepts (every UInt, and values representable as Int) returns v[i] when 1 <= i <= length(v) and throws BoundsError otherwise."
    "base/abstractarray.jl (checkbounds docstring); base/indices.jl:244-258" .proven
    ``GetindexCheckbounds ``getindexCheckbounds_proven,
  entry "arrayops-index-type-exception"
    ["to_index(A::Array, i::UInt)", "to_index(i::Integer)", "to_indices(A, inds, I::Tuple{Any, Vararg})",
     "getindex(::LinearIndices, i::Int)", "getindex(::Array, i::Integer)"]
    "Indexing a vector v and LinearIndices(v), which have the same axes and checkbounds, with the same out-of-range integer of any BitInteger type throws the same exception: BoundsError, the error checkbounds(A, i) throws, or InexactError when converting the index to Int fails first."
    "checkbounds, BoundsError and to_index docstrings; base/indices.jl:247,258" .refuted
    ``OutOfRangeBoundsError ``outOfRangeBoundsError_refuted
    "none found (related: #35038 closed, to_index returning UInt; queries: to_index, to_index Int128, InexactError index, BoundsError reinterpret UInt, checkbounds)"
    "to_index(A::Array, i::UInt) reinterprets (indices.jl:247), so v[UInt(2)^63] throws BoundsError, but LinearIndices(v)[UInt(2)^63] goes through convert(Int, i) (indices.jl:258) and throws InexactError; v[Int128(2)^64] also throws InexactError. maybe_intended: to_index is documented to convert to Int.",
  entry "indices-to-indices"
    ["to_indices(A, I::Tuple{Vararg{Integer}})", "to_indices(A, I::Tuple{Vararg{Int}})",
     "to_indices(A, I::Tuple{})", "to_indices(A, inds, ::Tuple{})",
     "to_indices(A, inds, I::Tuple{Any, Vararg})", "to_index(A, i)"]
    "to_indices converts a tuple of integer indices of any Integer type (BigInt included) element by element with to_index, in order and without bounds checking, keeping every value Int represents and throwing InexactError otherwise; a tuple of Ints is returned unchanged and the empty tuple gives the empty tuple."
    "to_indices docstring; base/indices.jl:267-323" .proven
    ``ToIndicesIntegers ``toIndicesIntegers_proven,
  entry "indices-slice-contract"
    ["axes(S::Slice)", "axes1(S::Slice)", "axes1(S::Slice{<:AbstractOneTo})", "first(S::Slice)",
     "last(S::Slice)", "getindex(S::Slice, i::Int)", "getindex(S::Slice, i::AbstractUnitRange{<:Integer})",
     "getindex(S::Slice, i::StepRange{<:Integer})", "getindex(S::Slice, i::IdentityUnitRange)"]
    "A Slice has the same indices as values: its axis runs from first(S) to last(S), S[i] == i for every Int in the axis and BoundsError outside, and an in-bounds index range is returned unchanged."
    "Slice docstring; base/indices.jl:324-354,410-415" .proven
    ``SliceContract ``sliceContract_proven,
  entry "reducecov-slice-integer-index"
    ["getindex(S::Slice, i::Int)", "getindex(::AbstractRange, ::Integer)"]
    "Indexing a Slice by an integer of any Integer type (Int, other BitIntegers, BigInt, user integers) in its axis returns that exact integer."
    "Slice docstring; base/indices.jl:350" .refuted
    ``SliceIntegerIndex ``sliceIntegerIndex_refuted
    "none found"
    "Base.Slice(3:5)[Int8(3)] is 5, and so is Base.Slice(3:5)[big(3)]: only getindex(::Slice, ::Int) exists, and other integers reach the generic AbstractRange method first(r) + (i - 1).",
  entry "reducecov-slice-bool-range"
    ["getindex(S::Slice, i::AbstractUnitRange{<:Integer})"]
    "Logical indexing of a Slice with a Bool unit range of matching length selects the values at the true positions."
    "manual (logical indexing); base/indices.jl:351" .refuted
    ``SliceBoolRange ``sliceBoolRange_refuted
    "none found"
    "Base.Slice(Base.OneTo(2))[false:true] returns false:true instead of [2]: AbstractUnitRange{<:Integer} includes Bool.",
  entry "indices-identity-contract"
    ["axes(S::IdentityUnitRange)", "axes1(S::IdentityUnitRange)", "axes1(S::IdentityUnitRange{<:AbstractOneTo})",
     "first(S::IdentityUnitRange)", "last(S::IdentityUnitRange)", "getindex(S::IdentityUnitRange, i::Integer)",
     "getindex(S::IdentityUnitRange, i::Bool)", "getindex(S::IdentityUnitRange, i::AbstractUnitRange{<:Integer})",
     "getindex(S::IdentityUnitRange, i::StepRange{<:Integer})", "getindex(S::IdentityUnitRange, i::IdentityUnitRange)",
     "getindex(S::Slice, i::IdentityUnitRange)", "getindex(S::AbstractOneTo, I::IdentityUnitRange)"]
    "An IdentityUnitRange is its own axis and range[i] == i for an integer of any Integer type (BigInt included) in it (BoundsError outside, ArgumentError for Bool); range indices keep their values and identity-range indices are returned unchanged."
    "IdentityUnitRange docstring; base/indices.jl:355-427" .proven
    ``IdentityContract ``identityContract_proven,
  entry "indices-identity-bool-unitrange"
    ["getindex(S::IdentityUnitRange, i::AbstractUnitRange{Bool})"]
    "Logical indexing of an IdentityUnitRange with a Bool unit range of matching length selects the values at the true positions."
    "manual (logical indexing); base/indices.jl:385-389" .proven
    ``IdentityBoolUnitRange ``identityBoolUnitRange_proven,
  entry "reducecov-identityrange-bool-step"
    ["getindex(S::IdentityUnitRange, i::StepRange{Bool})"]
    "Logical indexing of an IdentityUnitRange with a Bool step range StepRange{Bool,S} of matching length, for a step of any Integer type S, selects the values at the true positions."
    "manual (logical indexing); base/indices.jl:395-399" .refuted
    ``IdentityBoolStepRange ``identityBoolStepRange_refuted
    "none found"
    "Base.IdentityUnitRange(1:2)[StepRange(true, -1, false)] is empty instead of [1]: the length is last(i) = false.",
  entry "reducecov-linearindices-mixed-axes"
    ["LinearIndices(inds::NTuple{N,Union{<:Integer,AbstractUnitRange{<:Integer}}})", "_convert2ind",
     "axes(iter::LinearIndices)"]
    "LinearIndices built from integers (of any Integer type Int represents) and ranges has axis 1:n for each integer n and keeps the axis of each supplied range."
    "LinearIndices docstring; base/indices.jl:485-490" .refuted
    ``LinearIndicesMixedAxes ``linearIndicesMixedAxes_refuted
    "none found"
    "axes(LinearIndices((Base.IdentityUnitRange(3:5), 2)))[1] is Base.OneTo(3): _convert2ind(ind) = first(ind):last(ind) drops the offset axis.",
  entry "indices-linear-constructors"
    ["LinearIndices(inds::NTuple{N,Union{<:Integer,AbstractUnitRange{<:Integer}}})",
     "LinearIndices(inds::NTuple{N,AbstractUnitRange{<:Integer}})", "LinearIndices(A::AbstractArray)",
     "_convert2ind", "axes(iter::LinearIndices)"]
    "LinearIndices(sz) of integers of any Integer type has axes 1:sz[k] (InexactError when Int cannot represent a size); LinearIndices of ranges has the axes of those ranges; LinearIndices(A) has the same axes as A."
    "LinearIndices docstring; base/indices.jl:483-490,506" .proven
    ``LinearIndicesConstructors ``linearIndicesConstructors_proven,
  entry "indices-linear-values"
    ["first(iter::LinearIndices)", "first(iter::LinearIndices{1})", "last(iter::LinearIndices)",
     "last(iter::LinearIndices{1})", "getindex(iter::LinearIndices, i::Int)", "isassigned(iter::LinearIndices, i::Int)",
     "IndexStyle(::Type{<:LinearIndices})"]
    "LinearIndices of a vector runs over axes(A, 1) and otherwise from 1 to length(A); L[i] == i inside these bounds, BoundsError outside, and isassigned holds exactly inside them."
    "LinearIndices docstring; base/indices.jl:505-529" .proven
    ``LinearIndicesValues ``linearIndicesValues_proven,
  entry "indices-linearindices-iterate"
    ["iterate(iter::LinearIndices, i=1)"]
    "Iterating a LinearIndices of rank other than 1 and length n < typemax(Int) gives 1, 2, ..., n and then ends."
    "LinearIndices docstring; iteration protocol (manual); base/indices.jl:523" .proven
    ``LinearIndicesIterate ``linearIndicesIterate_proven,
  entry "indices-linearindices-iterate-end"
    ["iterate(iter::LinearIndices, i=1)", "last(iter::LinearIndices)"]
    "After iterate(L, s) returns the last element length(L), iterate from the returned state returns nothing."
    "iteration protocol (manual); base/indices.jl:523" .refuted
    ``LinearIndicesIterateEnds ``linearIndicesIterateEnds_refuted
    "none found"
    "For LinearIndices((typemax(Int), 1)) the state after typemax(Int) wraps to typemin(Int), which is not > length(iter), so iteration yields typemin(Int).",
  entry "reducecov-linearindices-range-index"
    ["getindex(iter::LinearIndices, i::AbstractRange{<:Integer})"]
    "Indexing LinearIndices with an in-bounds unit range a:b returns the linear indices a:b."
    "LinearIndices docstring; base/indices.jl:514-518" .refuted
    ``LinearIndicesRangeIndex ``linearIndicesRangeIndex_refuted
    "none found"
    "LinearIndices((3:5,))[2:3] is 4:5: the vector branch indexes iter.indices[1] = 3:5 instead of its axis.",
  entry "indices-linearindices-range-index-nd"
    ["getindex(iter::LinearIndices, i::AbstractRange{<:Integer})", "first(iter::LinearIndices)"]
    "For LinearIndices of rank other than 1, indexing with an in-bounds unit range a:b returns a:b."
    "LinearIndices docstring; base/indices.jl:514-518" .proven
    ``LinearIndicesRangeIndexND ``linearIndicesRangeIndexND_proven,
  entry "arrayops-linear-cartesian-1d"
    ["LinearIndices(A::AbstractArray)", "getindex(iter::LinearIndices, i::Int)",
     "first(iter::LinearIndices{1})", "last(iter::LinearIndices{1})", "getindex(::CartesianIndices{1}, i)"]
    "For a vector of length n, LinearIndices(v)[CartesianIndices(v)[i]] == i for i in 1:n, and both conversions throw BoundsError outside 1:n."
    "LinearIndices docstring; base/indices.jl:487,509-513,527-529" .proven
    ``LinearCartesianRoundTrip ``linearCartesianRoundTrip_proven,
  entry "reducecov-slice-promote-rule"
    ["promote_rule(a::Type{Slice{T1}}, b::Type{Slice{T2}})",
     "promote_rule(a::Type{IdentityUnitRange{T1}}, b::Type{IdentityUnitRange{T2}})"]
    "Promotion converts to a common representation, not an abstract supertype: promoting two Slice (or IdentityUnitRange) types whose ranges promote gives a Slice (IdentityUnitRange) type, not the join of the wrappers."
    "manual (Conversion and Promotion: promotion has nothing to do with the type hierarchy); base/indices.jl:499-502" .refuted
    ``SlicePromoteRule ``slicePromoteRule_refuted
    "none found"
    "el_same(promote_type(T1, T2), a, b) compares range types with the element type Int, so it always falls back to promote_typejoin: promote_type(Slice{OneTo{Int}}, Slice{UnitRange{Int}}) is the UnionAll Base.Slice.",
  entry "indices-linearindices-promotion"
    ["promote_rule(::Type{LinearIndices{N,R1}}, ::Type{LinearIndices{N,R2}})",
     "indices_promote_type", "convert(::Type{LinearIndices{N,R}}, inds::LinearIndices{N})"]
    "Promoting two LinearIndices types of rank N > 0 gives a LinearIndices of rank N whose N ranges have the promoted range type; at rank 0 the rule throws the MethodError from indices_promote_type(Tuple{}, Tuple{}); converting to a LinearIndices type keeps the rank and the axis values."
    "manual (promotion); base/indices.jl:479-480,491-498" .proven
    ``LinearIndicesPromotion ``linearIndicesPromotion_proven
]

end JuliaLean.Proofs.base.indices
