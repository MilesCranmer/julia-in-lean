import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.reduce
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.int
import JuliaLean.base.float
import JuliaLean.Proofs.base.float
import JuliaLean.base.operators
import JuliaLean.base.essentials

/-!
# Properties of `base/reduce.jl`

The propositions state reduction order, typed widening, empty identities, extrema and counting
contracts. Three preserved runtime refutations have source-model counterexamples.
-/

namespace JuliaLean.Proofs.base.reduce

open JuliaLean JuliaLean.base.reduce JuliaLean.Registry

def FirstExtreme {A K : Type} (less : A → A → Bool) (entries : List (K × A)) (value : A) (key : K) : Prop :=
  ∃ before after, entries = before ++ ((key, value) :: after) ∧
    (∀ k x, (k, x) ∈ entries → less value x = false) ∧
    (∀ k x, (k, x) ∈ before → less x value = true)

/-! ## Left and right fold semantics -/

def FoldInitSpec : Prop :=
  ∀ {α β : Type} (elementType : {I : Type} → JIterator I → EltypeStatus)
    (f : α → β) (binary : β → β → β) (first : β → β)
    (empty : Jl β) (xs : List α) (init : β),
    mapfoldl elementType f (valueReducer binary first empty) (.values xs) (.value init) =
      .ok ((xs.map f).foldl binary init) ∧
    mapfoldr elementType (fun itr => .values (iteratorValues itr).reverse) f
      (valueReducer binary first empty) (.values xs) (.value init) =
      .ok ((xs.map f).foldr binary init)

def SingleElementResults : Prop :=
  ∀ {Input Output Acc : Type} (elementType : {I : Type} → JIterator I → EltypeStatus)
    (f : Input → Output) (binary : Acc → Output → Acc) (first : Output → Acc)
    (empty : Jl Acc) (x : Input),
    mapfoldl elementType f (valueReducer binary first empty) (.values [x]) .initial =
      .ok (first (f x)) ∧
    mapreduce_number f (valueReducer binary first empty) x = .value (first (f x))

/-! ## Pairwise reductions -/

def PairwiseFoldl : Prop :=
  ∀ {Index Input Output : Type} [LE Index] [LT Index] [DecidableLE Index] [DecidableEq Index]
    [ReductionIndex Index] (f : Input → Output) (binary : Output → Output → Output)
    (A : LinearArray Input Index) (ifirst ilast : Index) (blockSize : Nat)
    (indicesValid : ifirst ≤ ilast),
    (∀ x y z, binary (binary x y) z = binary x (binary y z)) →
      mapreduce_impl f (valueReducer binary id _empty_reduce_error)
        A ifirst ilast blockSize indicesValid =
        .value ((List.range (ReductionIndex.distance ifirst ilast)).foldl
          (fun acc offset => binary acc (f (A.get (ReductionIndex.offset ifirst (offset + 1)))))
          (f (A.get ifirst)))
/-! ## Public sum and product -/

def SumProdContents : Prop :=
  ∀ {Input Output Acc : Type} (elementType : {I : Type} → JIterator I → EltypeStatus)
    (f : Input → Output) (plus times : Acc → Output → Acc)
    (first : Output → Acc) (empty : Jl Acc) (xs : List Input) (init : Acc),
    sum_f elementType f (valueReducer (add_sum plus) (reduce_first_add_sum first) empty)
      (.values xs) (.value init) = .ok ((xs.map f).foldl plus init) ∧
    prod_f elementType f (valueReducer (mul_prod times) (reduce_first_mul_prod first) empty)
      (.values xs) (.value init) = .ok ((xs.map f).foldl times init)

def SumInitWidened : Prop :=
  ∀ (t s : IntTy) (xs : List (JInt t)),
    t.bits < 64 → s.bits < 64 → xs ≠ [] →
    ∃ w : IntTy, (w = .i64 ∨ w = .u64) ∧
      sum (fun _ => .hasEltype) id
        (valueReducer integerAddSum integerFirstSum _empty_reduce_error)
        (.values (xs.map (fun x => (⟨t, x⟩ : IntegerAccumulator))))
        (.value ⟨s, JuliaLean.base.int.lit s 0⟩) =
        .ok ⟨w, JInt.wrap w ((xs.map (fun x => x.val)).sum)⟩

def ProdInitWidened : Prop :=
  ∀ (t s : IntTy), t.bits < 64 → s.bits < 64 →
    ∃ w : IntTy,
      (t.signed = s.signed → w = if t.signed then .i64 else .u64) ∧
      ∀ (xs : List (JInt t)), xs ≠ [] →
        prod (fun _ => .hasEltype) id
          (valueReducer integerMulProd integerFirstProd _empty_reduce_error)
          (.values (xs.map (fun x => (⟨t, x⟩ : IntegerAccumulator))))
          (.value ⟨s, JuliaLean.base.int.lit s 1⟩) =
          .ok ⟨w, JInt.wrap w ((xs.map (fun x => x.val)).prod)⟩
def ExtremaContents : Prop :=
  ∀ {Input Output : Type} (elementType : {I : Type} → JIterator I → EltypeStatus)
    (f : Input → Output) (minOp maxOp : Output → Output → Output)
    (xs : List Input) (init : Output × Output),
    extrema_f elementType f (valueReducer (extrema_rf minOp maxOp) id _empty_reduce_error)
      (.values xs) (.value init) =
      .ok (((xs.map f).foldl minOp init.1), ((xs.map f).foldl maxOp init.2)) ∧
    minimum_f elementType f (valueReducer minOp id _empty_reduce_error)
      (.values xs) (.value init.1) = .ok ((xs.map f).foldl minOp init.1) ∧
    maximum_f elementType f (valueReducer maxOp id _empty_reduce_error)
      (.values xs) (.value init.2) = .ok ((xs.map f).foldl maxOp init.2)

def UnmappedSumProd : Prop :=
  ∀ {Input Acc : Type} (elementType : {I : Type} → JIterator I → EltypeStatus)
    (plus times : Acc → Input → Acc) (first : Input → Acc) (empty : Jl Acc)
    (xs : List Input) (init : Acc),
    sum elementType id (valueReducer (add_sum plus) (reduce_first_add_sum first) empty)
      (.values xs) (.value init) = .ok (xs.foldl plus init) ∧
    prod elementType id (valueReducer (mul_prod times) (reduce_first_mul_prod first) empty)
      (.values xs) (.value init) = .ok (xs.foldl times init)

/-! ## Empty collections -/

def EmptyReductions : Prop :=
  ∀ {α : Type} (plus times minOp maxOp : α → α → α) (zero one init : α)
    (pairs : JIterator α → JIterator (Nat × α)) (less greater : α → α → Bool),
    pairs (.values []) = .values [] →
    let elt : {I : Type} → JIterator I → EltypeStatus := fun _ => .hasEltype
    let add := valueReducer (add_sum plus) id (.ok zero)
    let mul := valueReducer (mul_prod times) id (.ok one)
    let min := valueReducer minOp id (_empty_reduce_error : Jl α)
    let max := valueReducer maxOp id (_empty_reduce_error : Jl α)
    let pair := valueReducer (extrema_rf minOp maxOp) id (_empty_reduce_error : Jl (α × α))
    sum elt id add (.values []) (.value init) = .ok init ∧
    prod elt id mul (.values []) (.value init) = .ok init ∧
    maximum elt id max (.values []) (.value init) = .ok init ∧
    minimum elt id min (.values []) (.value init) = .ok init ∧
    extrema elt id pair (.values []) (.value (init, init)) = .ok (init, init) ∧
    sum elt id add (.values []) .initial = .ok zero ∧
    prod elt id mul (.values []) .initial = .ok one ∧
    maximum elt id max (.values []) .initial = (_empty_reduce_error : Jl α) ∧
    minimum elt id min (.values []) .initial = (_empty_reduce_error : Jl α) ∧
    extrema elt id pair (.values []) .initial = (_empty_reduce_error : Jl (α × α)) ∧
    findmax elt pairs id less (.values []) = (_empty_reduce_error : Jl (α × Nat)) ∧
    findmin elt pairs id greater (.values []) = (_empty_reduce_error : Jl (α × Nat))

/-! ## Flattened iterators -/

def FlattenFoldl : Prop :=
  ∀ {α : Type} (elementType : {I : Type} → JIterator I → EltypeStatus)
    (binary : α → α → α) (first : α → α) (empty : Jl α)
    (nested : List (List α)) (init : α),
    foldl elementType id (valueReducer binary first empty) (.flatten (.values nested)) (.value init) =
      .ok (nested.flatten.foldl binary init) ∧
    ∀ x rest, nested.flatten = x :: rest →
      foldl elementType id (valueReducer binary first empty) (.flatten (.values nested)) .initial =
        .ok (rest.foldl binary (first x))

def FlattenSumAgrees : Prop :=
  ∀ {α : Type} (plus : α → α → α) (first : α → α) (zero : α)
    (nested : List (List α)),
    let op := valueReducer (add_sum plus) (reduce_first_add_sum first) (.ok zero)
    sum (fun _ => .hasEltype) id op (.flatten (.values nested)) .initial =
      sum (fun _ => .hasEltype) id op (.values nested.flatten) .initial

/-! ## Extrema and first-index behavior -/

structure StrictWeakOrder {A : Type} (less : A → A → Bool) : Prop where
  irrefl : ∀ a, less a a = false
  trans : ∀ a b c, less a b = true → less b c = true → less a c = true
  not_trans : ∀ a b c, less a b = false → less b c = false → less a c = false

def FindExtremaSpec : Prop :=
  ∀ {A K : Type} (elementType : {I : Type} → JIterator I → EltypeStatus)
    (pairs : JIterator A → JIterator (K × A))
    (less greater : A → A → Bool) (domain : JIterator A) (entries : List (K × A)),
    StrictWeakOrder less → StrictWeakOrder greater →
    pairs domain = .values entries → entries ≠ [] →
    (∃ vmax kmax, findmax elementType pairs id less domain = .ok (vmax, kmax) ∧
      FirstExtreme less entries vmax kmax ∧ argmax elementType pairs id less domain = .ok kmax) ∧
    (∃ vmin kmin, findmin elementType pairs id greater domain = .ok (vmin, kmin) ∧
      FirstExtreme greater entries vmin kmin ∧ argmin elementType pairs id greater domain = .ok kmin)

def FindmaxAgree : Prop :=
  ∀ {A K : Type} (elementType : {I : Type} → JIterator I → EltypeStatus)
    (pairs : JIterator A → JIterator (K × A))
    (less greater : A → A → Bool) (maxOp minOp : A → A → A)
    (E : A → A → Prop) (xs : List A) (entries : List (K × A)),
    StrictWeakOrder less → StrictWeakOrder greater → Equivalence E →
    (∀ a b c d, E a b → E c d → less a c = less b d) →
    (∀ a b c d, E a b → E c d → greater a c = greater b d) →
    (∀ a b, E (maxOp a b) (if less a b then b else a)) →
    (∀ a b, E (minOp a b) (if greater a b then b else a)) →
    pairs (.values xs) = .values entries → entries.map Prod.snd = xs → xs ≠ [] →
    (∀ v k, findmax elementType pairs id less (.values xs) = .ok (v, k) →
      ∃ m, maximum elementType id (valueReducer maxOp (reduce_first maxOp) _empty_reduce_error)
        (.values xs) .initial = .ok m ∧ E v m ∧ (k, v) ∈ entries) ∧
    (∀ v k, findmin elementType pairs id greater (.values xs) = .ok (v, k) →
      ∃ m, minimum elementType id (valueReducer minOp (reduce_first minOp) _empty_reduce_error)
        (.values xs) .initial = .ok m ∧ E v m ∧ (k, v) ∈ entries)

/-! ## Counting and low-level access -/

def FloatCountInitAgrees : Prop :=
  ∀ (plus : JuliaLean.base.float.FV .f64 → Bool → JuliaLean.base.float.FV .f64)
    (addWord : JuliaLean.base.float.FV .f64 → JInt .i64 → JuliaLean.base.float.FV .f64)
    (first : Bool → JuliaLean.base.float.FV .f64)
    (init : JuliaLean.base.float.FV .f64) (xs : List Bool),
    _simple_count_bool_array (add_sum_real plus) (add_sum_real addWord) (add_sum_real plus)
      (fun _ => .error (.methodError "rem")) ⟨xs⟩ init =
      count (count_f (_simple_count (fun _ => .hasEltype)
        (valueReducer (add_sum_real plus) (reduce_first_add_sum first)
          _empty_reduce_error))) id (.values xs) (.value init)

def IntegerCountInitAgrees : Prop :=
  ∀ (t : IntTy) (init : JInt t) (xs : List Bool),
    _simple_count_bool_array integerCountAdd integerCountWord integerCountAdd
      integerCountModulo ⟨xs⟩ ⟨t, init⟩ =
      count (count_f (_simple_count (fun _ => .hasEltype)
        (valueReducer integerCountAdd (fun b => integerFirstSum
          ⟨.i8, JuliaLean.base.int.ofBool .i8 b⟩) _empty_reduce_error)))
        id (.values xs) (.value ⟨t, init⟩)

def CountInitAgrees : Prop := IntegerCountInitAgrees ∧ FloatCountInitAgrees

def ReduceSafe : Prop :=
  (∀ {Index α : Type} [LE Index] [LT Index] [DecidableLE Index] [DecidableEq Index]
    [ReductionIndex Index] (A : LinearArray α Index) (lo hi : Index) (block : Nat)
    (valid : lo ≤ hi), A.first ≤ lo → hi ≤ A.last →
    let traced : LinearArray (Index × α) Index :=
      ⟨A.first, A.last, fun i => (i, A.get i), A.length⟩
    mapreduce_impl (fun p => [p.1]) (valueReducer List.append id _empty_reduce_error)
      traced lo hi block valid =
      .value ((List.range (ReductionIndex.distance lo hi + 1)).map
        (fun k => ReductionIndex.offset lo k)) ∧
    ∀ i ∈ (List.range (ReductionIndex.distance lo hi + 1)).map
      (fun k => ReductionIndex.offset lo k), A.first ≤ i ∧ i ≤ A.last) ∧
  (∀ (x : ArrayBool) (i : Nat),
    (1 ≤ i → i ≤ lengthBoolArray x / sizeofUInt →
      sizeofUInt * i ≤ lengthBoolArray x ∧
      ((ptrUIntOfPtr (pointerBoolArray x)).bytes.drop
        ((ptrUIntOfPtr (pointerBoolArray x)).offset + 8 * (i - 1))).take 8 =
        (x.elements.drop (8 * (i - 1))).take 8 ∧
      (((ptrUIntOfPtr (pointerBoolArray x)).bytes.drop
        ((ptrUIntOfPtr (pointerBoolArray x)).offset + 8 * (i - 1))).take 8).length = 8 ∧
      JuliaLean.base.int.count_ones
        (JuliaLean.base.int.and_int
          (unsafeLoadUInt (ptrUIntOfPtr (pointerBoolArray x)) i)
          (JuliaLean.base.int.remT .u64 (JInt.lit .u64 0x0101010101010101))) =
        JuliaLean.base.int.lit .i64 (((x.elements.drop (8 * (i - 1))).take 8).countP id)) ∧
    (sizeofUInt * (lengthBoolArray x / sizeofUInt) + 1 ≤ i → i ≤ lengthBoolArray x →
      1 ≤ i ∧ i - 1 < x.elements.length))
def ReduceNumberFirst : Prop :=
  ∀ {Input Acc : Type} (op : Reducer Acc Input) (x : Input),
    ∃ same : Input = Acc,
      FoldInit.value (same ▸ reduce_number op x) = reduce_first_dispatch op x

def BooleanReductionRules : Prop :=
  ∀ x y, and_all_bool Bool.and x y = (x && y) ∧
    or_any_bool Bool.or x y = (x || y)

def ReductionOperatorSemantics : Prop :=
  (∀ (s t : IntTy) (x : JInt s) (y : JInt t), s.bits < 64 → t.bits < 64 →
    integerAddSum ⟨s, x⟩ ⟨t, y⟩ =
      ⟨if s.signed = false ∧ t.signed = false then .u64 else .i64,
        JInt.wrap (if s.signed = false ∧ t.signed = false then .u64 else .i64) (x.val + y.val)⟩ ∧
    (s.signed = t.signed →
      integerMulProd ⟨s, x⟩ ⟨t, y⟩ =
        ⟨if s.signed then .i64 else .u64,
          JInt.wrap (if s.signed then .i64 else .u64) (x.val * y.val)⟩)) ∧
  (∀ {A B R Other : Type} (plus mul : A → B → R ⊕ Other) (x : A) (y : B),
    (∀ r, plus x y = .inl r → add_sum_real plus x y = .ok r) ∧
    (∀ bad, plus x y = .inr bad → add_sum_real plus x y = .error .typeError) ∧
    (∀ r, mul x y = .inl r → mul_prod_real mul x y = .ok r) ∧
    (∀ bad, mul x y = .inr bad → mul_prod_real mul x y = .error .typeError))
def AdapterSpec : Prop :=
  (∀ {A B C : Type} (f : A → B) (binary : C → B → C) (xs : List A) (init : C),
    xs.foldl (mappingRF_apply (mappingRF_constructor f binary)) init =
      (xs.map f).foldl binary init ∧
    xs.foldl (mappingRF_apply (mappingRF_type_constructor f binary)) init =
      (xs.map f).foldl binary init) ∧
  (∀ {A C : Type} (predicate : A → Bool) (binary : C → A → C) (xs : List A) (init : C),
    xs.foldl (filteringRF_apply ⟨predicate, binary⟩) init =
      (xs.filter predicate).foldl binary init) ∧
  (∀ {A C : Type} (binary : C → A → C) (first : A → C) (empty : Jl C)
    (xs : List A) (init : C),
    flatteningRF_apply ⟨valueReducer binary first empty⟩ (.value init) (.values xs) =
      .value (xs.foldl binary init)) ∧
  (∀ {A : Type} (binary : A → A → A) (xs : List A) (init : A),
    xs.reverse.foldl (flipArgs_apply ⟨binary⟩) init = xs.foldr binary init)

def CountPredicateSpec : Prop :=
  (∀ {A : Type} (predicate : A → Bool) (xs : List A) (init : JInt .i64),
    count_f (_simple_count (fun _ => .hasEltype)
      (valueReducer (add_sum_small id (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add)
        (reduce_first_add_sum (reduce_first_plus_bool (JuliaLean.base.int.ofBool .i64)))
        (reduce_empty_add_bool (fun _ => JuliaLean.base.int.lit .i64 0) (JInt .i64))))
      predicate (.values xs) (.value init) =
      .ok (JInt.wrap .i64 (init.val + (xs.countP predicate : Int)))) ∧
  (∀ (xs : List Bool) (init : JInt .i64),
    count (count_f (_simple_count (fun _ => .hasEltype)
      (valueReducer (add_sum_small id (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add)
        (reduce_first_add_sum (reduce_first_plus_bool (JuliaLean.base.int.ofBool .i64)))
        (reduce_empty_add_bool (fun _ => JuliaLean.base.int.lit .i64 0) (JInt .i64)))))
      id (.values xs) (.value init) =
      .ok (JInt.wrap .i64 (init.val + (xs.countP id : Int))))

def GenericReductionContents : Prop :=
  ∀ {A B : Type} (elementType : {I : Type} → JIterator I → EltypeStatus)
    (f : A → B) (binary : B → B → B) (xs : List A) (ys : List B) (init : B),
    mapreduce elementType f (valueReducer binary id _empty_reduce_error) (.values xs) (.value init) =
      .ok ((xs.map f).foldl binary init) ∧
    reduce elementType id (valueReducer binary id _empty_reduce_error) (.values ys) (.value init) =
      .ok (ys.foldl binary init) ∧
    foldl elementType id (valueReducer binary id _empty_reduce_error) (.values ys) (.value init) =
      .ok (ys.foldl binary init) ∧
    foldr elementType (fun itr => .values (iteratorValues itr).reverse) id
      (valueReducer binary id _empty_reduce_error) (.values ys) (.value init) =
      .ok (ys.foldr binary init)

theorem value_fold {A B : Type} (binary : A → B → A) (first : B → A)
    (xs : List B) (init : A) :
    xs.foldl (fun (state : FoldInit A) x => match state with
      | .initial => FoldInit.value (first x)
      | .value a => .value (binary a x)) (.value init) = .value (xs.foldl binary init) := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldl_cons] using ih (binary init x)

theorem mapfoldl_values {A B C : Type} [EmptyMappingOps C]
    (elementType : {I : Type} → JIterator I → EltypeStatus)
    (f : A → B) (binary : C → B → C) (first : B → C)
    (empty : Jl C) (xs : List A) (init : C) :
    mapfoldl elementType f (valueReducer binary first empty) (.values xs) (.value init) =
      .ok ((xs.map f).foldl binary init) := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    change (match xs.foldl (fun (state : FoldInit C) y => match state with
      | .initial => .value (first (f y))
      | .value a => .value (binary a (f y))) (.value (binary init (f x))) with
        | .initial => _
        | .value a => (Except.ok a : Jl C)) = Except.ok (((x :: xs).map f).foldl binary init)
    rw [value_fold]
    simp only [List.map_cons, List.foldl_cons, List.foldl_map]

theorem mapfoldl_values_nonempty {A B C : Type} [EmptyMappingOps C]
    (elementType : {I : Type} → JIterator I → EltypeStatus)
    (f : A → B) (binary : C → B → C) (first : B → C)
    (empty : Jl C) (x : A) (xs : List A) :
    mapfoldl elementType f (valueReducer binary first empty) (.values (x :: xs)) .initial =
      .ok ((xs.map f).foldl binary (first (f x))) := by
  change (match xs.foldl (fun (state : FoldInit C) y => match state with
    | .initial => .value (first (f y))
    | .value a => .value (binary a (f y))) (.value (first (f x))) with
      | .initial => _
      | .value a => (Except.ok a : Jl C)) = _
  rw [value_fold]
  simp only [List.foldl_map]

theorem mapfoldl_identity_mapper {A C : Type} [EmptyMappingOps C]
    (elementType : {I : Type} → JIterator I → EltypeStatus)
    (binary : C → A → C) (first : A → C)
    (empty : Jl C) (xs : List A) (init : C) :
    mapfoldl elementType (IdentityMapper.mk (id : A → A)) (valueReducer binary first empty) (.values xs) (.value init) =
      .ok (xs.foldl binary init) := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    change (match xs.foldl (fun (state : FoldInit C) y => match state with
      | .initial => .value (first y)
      | .value a => .value (binary a y)) (.value (binary init x)) with
        | .initial => _
        | .value a => (Except.ok a : Jl C)) = Except.ok ((x :: xs).foldl binary init)
    rw [value_fold]
    rfl

theorem mapfoldl_identity_mapper_nonempty {A C : Type} [EmptyMappingOps C]
    (elementType : {I : Type} → JIterator I → EltypeStatus)
    (binary : C → A → C) (first : A → C)
    (empty : Jl C) (x : A) (xs : List A) :
    mapfoldl elementType (IdentityMapper.mk (id : A → A)) (valueReducer binary first empty) (.values (x :: xs)) .initial =
      .ok (xs.foldl binary (first x)) := by
  change (match xs.foldl (fun (state : FoldInit C) y => match state with
    | .initial => .value (first y)
    | .value a => .value (binary a y)) (.value (first x)) with
      | .initial => _
      | .value a => (Except.ok a : Jl C)) = _
  rw [value_fold]
theorem flatten_state {A : Type} [EmptyMappingOps A] (binary : A → A → A) (first : A → A)
    (empty : Jl A) (nested : List (List A)) (init : FoldInit A) :
    _foldl_impl ((_xfadjoint (bottomRFReducer (valueReducer binary first empty))
      (.generator (IdentityMapper.mk (id : A → A)) (.flatten (.values nested)))).op)
      init ((_xfadjoint (bottomRFReducer (valueReducer binary first empty))
      (.generator (IdentityMapper.mk (id : A → A)) (.flatten (.values nested)))).itr) =
    nested.flatten.foldl (valueReducer binary first empty).step init := by
  simp [_foldl_impl, _xfadjoint, _xfadjoint_unwrap_dispatch,
    _xfadjoint_unwrap_generator, _xfadjoint_unwrap_flatten, _xfadjoint_unwrap_values,
    MapCallable.isIdentity, MapCallable.apply, mappingRFReducer,
    iteratorValues, bottomRFReducer, valueReducer, List.foldl_flatten]
  cases nested <;> rfl
theorem flattenFoldl_proven : FlattenFoldl := by
  intro A elementType binary first empty nested init
  constructor
  · unfold foldl mapfoldl mapfoldl_impl foldl_impl
    dsimp only
    rw [flatten_state]
    change (match nested.flatten.foldl
      (fun (state : FoldInit A) x => match state with
        | .initial => .value (first x)
        | .value a => .value (binary a x)) (.value init) with
      | .initial => _
      | .value a => (Except.ok a : Jl A)) = _
    rw [value_fold]
  · intro x rest h
    unfold foldl mapfoldl mapfoldl_impl foldl_impl
    dsimp only
    rw [flatten_state, h]
    change (match rest.foldl
      (fun (state : FoldInit A) y => match state with
        | .initial => .value (first y)
        | .value a => .value (binary a y)) (.value (first x)) with
      | .initial => _
      | .value a => (Except.ok a : Jl A)) = _
    rw [value_fold]

theorem singleElementResults_proven : SingleElementResults := by
  intro Input Output Acc elementType f binary first empty x
  constructor <;> rfl

theorem sumProdContents_proven : SumProdContents := by
  intro Input Output Acc elementType f plus times first empty xs init
  constructor
  · exact mapfoldl_values elementType f plus first empty xs init
  · exact mapfoldl_values elementType f times first empty xs init

theorem unmappedSumProd_proven : UnmappedSumProd := by
  intro Input Acc elementType plus times first empty xs init
  exact ⟨mapfoldl_identity_mapper elementType plus first empty xs init,
    mapfoldl_identity_mapper elementType times first empty xs init⟩

theorem foldInitSpec_proven : FoldInitSpec := by
  intro A B elementType f binary first empty xs init
  constructor
  · exact mapfoldl_values elementType f binary first empty xs init
  · change mapfoldl elementType f (valueReducer (fun a b => binary b a) first empty)
      (.values xs.reverse) (.value init) = _
    rw [mapfoldl_values]
    simp only [List.map_reverse, List.foldl_reverse]

theorem extrema_fold {A : Type} (minOp maxOp : A → A → A)
    (xs : List A) (init : A × A) :
    (xs.map (fun x => (x, x))).foldl (extrema_rf minOp maxOp) init =
      (xs.foldl minOp init.1, xs.foldl maxOp init.2) := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simpa only [List.map_cons, List.foldl_cons, extrema_rf] using
      (ih (minOp init.1 x, maxOp init.2 x))

theorem extremaContents_proven : ExtremaContents := by
  intro Input Output elementType f minOp maxOp xs init
  refine ⟨?_, mapfoldl_values elementType f minOp id _empty_reduce_error xs init.1,
    mapfoldl_values elementType f maxOp id _empty_reduce_error xs init.2⟩
  unfold extrema_f mapreduce
  rw [mapfoldl_values]
  change (Except.ok ((xs.map (fun x => (f x, f x))).foldl (extrema_rf minOp maxOp) init) :
    Jl (Output × Output)) = _
  simpa only [List.map_map, Function.comp_def] using
    congrArg Except.ok (extrema_fold minOp maxOp (xs.map f) init)

theorem emptyReductions_proven : EmptyReductions := by
  intro A plus times minOp maxOp zero one init pairs less greater hp
  dsimp only
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · unfold findmax _findmax_identity findmax_f _findmax
    rw [hp]
    rfl
  · unfold findmin _findmin_identity findmin_f _findmin
    rw [hp]
    rfl

theorem flattenSumAgrees_proven : FlattenSumAgrees := by
  intro A plus first zero nested
  dsimp only
  cases h : nested.flatten with
  | nil =>
    unfold sum sum_f mapreduce mapfoldl mapfoldl_impl foldl_impl
    dsimp only
    rw [flatten_state, h]
    rfl
  | cons x xs =>
    have hl := (flattenFoldl_proven (fun _ => .hasEltype)
      (add_sum plus) (reduce_first_add_sum first) (.ok zero) nested zero).2 x xs h
    change sum (fun _ => .hasEltype) id _ (.flatten (.values nested)) .initial = _
    exact hl.trans (by
      symm
      exact mapfoldl_identity_mapper_nonempty (fun _ => .hasEltype)
        (add_sum plus) (reduce_first_add_sum first) (.ok zero) x xs)

theorem adapterSpec_proven : AdapterSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B C f binary xs init
    constructor <;>
      change xs.foldl (fun acc x => binary acc (f x)) init = _ <;>
      rw [List.foldl_map]
  · intro A C predicate binary xs init
    change xs.foldl (fun acc x => if predicate x then binary acc x else acc) init = _
    rw [List.foldl_filter]
  · intro A C binary first empty xs init
    cases xs with
    | nil => rfl
    | cons x xs =>
      change xs.foldl (fun (state : FoldInit C) y => match state with
        | .initial => .value (first y)
        | .value a => .value (binary a y)) (.value (binary init x)) =
        .value (xs.foldl binary (binary init x))
      exact value_fold binary first xs (binary init x)
  · intro A binary xs init
    change xs.reverse.foldl (fun a b => binary b a) init = _
    rw [List.foldl_reverse]

theorem genericReductionContents_proven : GenericReductionContents := by
  intro A B elementType f binary xs ys init
  refine ⟨mapfoldl_values elementType f binary id _empty_reduce_error xs init,
    mapfoldl_identity_mapper elementType binary id _empty_reduce_error ys init,
    mapfoldl_identity_mapper elementType binary id _empty_reduce_error ys init, ?_⟩
  change mapfoldl elementType (IdentityMapper.mk id) (valueReducer (fun a b => binary b a) id _empty_reduce_error)
    (.values ys.reverse) (.value init) = _
  rw [mapfoldl_identity_mapper]
  simp only [List.foldl_reverse]

theorem intBoolFold {A : Type} (predicate : A → Bool) (xs : List A) (init : JInt .i64) :
    xs.foldl
      (fun n x => add_sum_small id (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add n (predicate x))
      init =
      JInt.wrap .i64 (init.val + (xs.countP predicate : Int)) := by
  induction xs generalizing init with
  | nil =>
    simp only [List.foldl_nil, List.countP_nil, Int.natCast_zero, Int.add_zero]
    apply Subtype.ext
    exact (JuliaLean.Proofs.base.int.wrapInt_val init).symm
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    apply Subtype.ext
    change wrapInt .i64
      ((add_sum_small id (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add init (predicate x)).val +
        (xs.countP predicate : Int)) =
      wrapInt .i64 (init.val + ((x :: xs).countP predicate : Int))
    rw [add_sum_small, id_eq, JuliaLean.base.int.add, JuliaLean.Proofs.base.int.add_int_val]
    have hb : (JuliaLean.base.int.ofBool .i64 (predicate x)).val =
        (if predicate x then 1 else 0) := by cases predicate x <;> decide
    rw [hb, JuliaLean.Proofs.base.int.wrapInt_add_left, List.countP_cons]
    cases hx : predicate x <;>
      simp only [hx, Bool.false_eq_true, ↓reduceIte, Int.natCast_add, Int.natCast_one,
        Int.natCast_zero, Int.add_zero, Int.add_assoc, Int.add_comm, Int.add_left_comm]

theorem count_intPredicate {A : Type} (predicate : A → Bool) (xs : List A) (init : JInt .i64) :
    count_f (_simple_count (fun _ => .hasEltype)
      (valueReducer (add_sum_small id (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add)
        (reduce_first_add_sum (reduce_first_plus_bool (JuliaLean.base.int.ofBool .i64)))
        (reduce_empty_add_bool (fun _ => JuliaLean.base.int.lit .i64 0) (JInt .i64))))
      predicate (.values xs) (.value init) =
      .ok (JInt.wrap .i64 (init.val + (xs.countP predicate : Int))) := by
  change mapfoldl (fun _ => .hasEltype) predicate
    (valueReducer (add_sum_small id (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add)
      (reduce_first_add_sum (reduce_first_plus_bool (JuliaLean.base.int.ofBool .i64)))
      (reduce_empty_add_bool (fun _ => JuliaLean.base.int.lit .i64 0) (JInt .i64)))
    (.values xs) (.value init) = _
  rw [mapfoldl_values, List.foldl_map]
  exact congrArg Except.ok (intBoolFold predicate xs init)

def BooleanTypeSpec : Prop :=
  (∀ {A B : Type} (x y : Bool),
    and_all (A := A) (B := B) (.inl x) (.inl y) = .ok (x && y) ∧
    or_any (A := A) (B := B) (.inl x) (.inl y) = .ok (x || y)) ∧
  (∀ {A B : Type} (bad : A) (y : Bool ⊕ B),
    and_all (.inr bad) y = .error .typeError ∧
    or_any (.inr bad) y = .error .typeError) ∧
  (∀ {A B : Type} (bad : B),
    and_all (A := A) (.inl false) (.inr bad) = .ok false ∧
    or_any (A := A) (.inl true) (.inr bad) = .ok true ∧
    and_all (A := A) (.inl true) (.inr bad) = .error .typeError ∧
    or_any (A := A) (.inl false) (.inr bad) = .error .typeError) ∧
  (∀ {Input Other : Type} (f : Input → Bool ⊕ Other) (x : Input),
    (∀ b, f x = .inl b → _bool f x = .ok b) ∧
    (∀ bad, f x = .inr bad → _bool f x = .error .typeError))

theorem booleanTypeSpec_proven : BooleanTypeSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B x y
    cases x <;> cases y <;> exact ⟨rfl, rfl⟩
  · intro A B bad y
    exact ⟨rfl, rfl⟩
  · intro A B bad
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro Input Other f x
    constructor
    · intro b hb
      change assertBool (f x) = .ok b
      rw [hb]
      rfl
    · intro bad hb
      change assertBool (f x) = .error .typeError
      rw [hb]
      rfl
theorem countPredicateSpec_proven : CountPredicateSpec :=
  ⟨count_intPredicate, fun xs init => count_intPredicate id xs init⟩

theorem booleanReductionRules_proven : BooleanReductionRules := by
  intro x y
  cases x <;> cases y <;> decide

def intervalResult {Index A B : Type} [LE Index] [LT Index] [ReductionIndex Index]
    (f : A → B) (binary : B → B → B)
    (array : LinearArray A Index) (start : Index) (count : Nat) : FoldInit B :=
  ((List.range count).map
    (fun k => FoldInit.value (f (array.get (ReductionIndex.offset start k))))).foldl
    (combineFoldInit (valueReducer binary id _empty_reduce_error)) .initial

theorem combine_assoc {B : Type} (binary : B → B → B)
    (h : ∀ a b c, binary (binary a b) c = binary a (binary b c)) :
    Std.Associative (combineFoldInit (valueReducer binary id _empty_reduce_error)) := by
  constructor
  intro a b c
  cases a <;> cases b <;> cases c <;> simp [combineFoldInit, valueReducer, h]

theorem interval_split {Index A B : Type} [LE Index] [LT Index] [ReductionIndex Index]
    (f : A → B) (binary : B → B → B)
    (h : ∀ a b c, binary (binary a b) c = binary a (binary b c))
    (array : LinearArray A Index) (start : Index) (n m : Nat) :
    intervalResult f binary array start (n + m) =
      combineFoldInit (valueReducer binary id _empty_reduce_error)
        (intervalResult f binary array start n)
        (intervalResult f binary array (ReductionIndex.offset start n) m) := by
  let op := combineFoldInit (valueReducer binary id (_empty_reduce_error : Jl B))
  letI : Std.Associative op := combine_assoc binary h
  have right_id (x : FoldInit B) : op x .initial = x := by cases x <;> rfl
  unfold intervalResult
  rw [List.range_add, List.map_append, List.foldl_append]
  simp only [List.map_map, Function.comp_def, ← ReductionIndex.offset_add]
  change List.foldl op (List.foldl op .initial _) _ = op (List.foldl op .initial _) _
  simpa only [right_id] using
    (List.foldl_assoc (op := op)
      (l := (List.range m).map
        (fun k => FoldInit.value (f (array.get (ReductionIndex.offset (ReductionIndex.offset start n) k)))))
      (a₁ := ((List.range n).map
        (fun k => FoldInit.value (f (array.get (ReductionIndex.offset start k))))).foldl op .initial)
      (a₂ := FoldInit.initial))

theorem interval_nonempty {Index A B : Type} [LE Index] [LT Index] [ReductionIndex Index]
    (f : A → B) (binary : B → B → B)
    (array : LinearArray A Index) (start : Index) (count : Nat) :
    intervalResult f binary array start (count + 1) =
      .value ((List.range count).foldl
        (fun acc k => binary acc (f (array.get (ReductionIndex.offset start (k + 1)))))
        (f (array.get start))) := by
  unfold intervalResult
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.foldl_cons, List.map_map, List.foldl_map,
    Function.comp_def, ReductionIndex.offset_zero, combineFoldInit]
  have hh (xs : List Nat) (init : B) :
      xs.foldl (fun state k =>
        combineFoldInit (valueReducer binary id _empty_reduce_error)
          state (.value (f (array.get (ReductionIndex.offset start (k + 1)))))) (.value init) =
        .value (xs.foldl
          (fun acc k => binary acc (f (array.get (ReductionIndex.offset start (k + 1))))) init) := by
    induction xs generalizing init with
    | nil => rfl
    | cons x xs ih =>
      simpa only [List.foldl_cons, combineFoldInit, valueReducer] using
        (ih (binary init (f (array.get (ReductionIndex.offset start (x + 1))))))
  simpa only [Nat.add_succ, Nat.add_zero, combineFoldInit] using
    hh (List.range count) (f (array.get start))

theorem mapreduce_interval {Index A B : Type} [LE Index] [LT Index] [DecidableLE Index]
    [DecidableEq Index] [ReductionIndex Index]
    (f : A → B) (binary : B → B → B)
    (assoc : ∀ a b c, binary (binary a b) c = binary a (binary b c))
    (array : LinearArray A Index) (lo hi : Index) (block : Nat) (valid : lo ≤ hi) :
    mapreduce_impl f (valueReducer binary id _empty_reduce_error) array lo hi block valid =
      intervalResult f binary array lo (ReductionIndex.distance lo hi + 1) := by
  rw [mapreduce_impl]
  by_cases hEq : lo = hi
  · rw [dif_pos hEq]
    subst hi
    rw [ReductionIndex.distance_self]
    simp [intervalResult, mapreduce_first, reduce_first_dispatch, valueReducer, combineFoldInit,
      ReductionIndex.offset_zero]
  · rw [dif_neg hEq]
    have hd : 0 < ReductionIndex.distance lo hi := ReductionIndex.distance_pos lo hi valid hEq
    split
    · dsimp only
      have hc : (if ReductionIndex.offset lo 2 ≤ hi then
          ReductionIndex.distance (ReductionIndex.offset lo 2) hi + 1 else 0) =
          ReductionIndex.distance lo hi - 1 := by
        split
        · rename_i h2
          have h2le : 2 ≤ ReductionIndex.distance lo hi :=
            (ReductionIndex.offset_le_iff lo hi 2 valid).mp h2
          have hdist := (ReductionIndex.distance_offset_le lo hi 2 valid h2le).2
          omega
        · rename_i h2
          have hnot : ¬ (2 ≤ ReductionIndex.distance lo hi) :=
            fun hle => h2 ((ReductionIndex.offset_le_iff lo hi 2 valid).mpr hle)
          omega
      rw [hc, interval_nonempty]
      have hh : ReductionIndex.distance lo hi = (ReductionIndex.distance lo hi - 1) + 1 := by omega
      conv => rhs; rw [hh, List.range_succ_eq_map]
      simp only [List.foldl_cons, List.foldl_map, valueReducer, id_eq]
      change (List.range (ReductionIndex.distance lo hi - 1)).foldl
        (fun (state : FoldInit B) k => match state with
          | .initial => .value (f (array.get (ReductionIndex.offset (ReductionIndex.offset lo 2) k)))
          | .value a => .value (binary a (f (array.get (ReductionIndex.offset (ReductionIndex.offset lo 2) k)))))
        (.value (binary (f (array.get lo)) (f (array.get (ReductionIndex.offset lo 1))))) = _
      rw [value_fold]
      have hfn :
          (fun (a : B) (k : Nat) => binary a (f (array.get (ReductionIndex.offset (ReductionIndex.offset lo 2) k)))) =
          (fun (a : B) (k : Nat) => binary a (f (array.get (ReductionIndex.offset lo (k.succ + 1))))) := by
        funext acc k
        rw [ReductionIndex.offset_add]
        have hk : 2 + k = k.succ + 1 := by omega
        rw [hk]
      rw [hfn]
    · dsimp only
      let half := ReductionIndex.distance lo hi / 2
      let imid := ReductionIndex.offset lo half
      have hm : half < ReductionIndex.distance lo hi := Nat.div_lt_self hd (by decide)
      have hLeft : lo ≤ imid := ReductionIndex.middle_le lo hi valid hEq
      have hRight : ReductionIndex.offset imid 1 ≤ hi := ReductionIndex.next_middle_le lo hi valid hEq
      rw [mapreduce_interval f binary assoc array lo imid block hLeft,
        mapreduce_interval f binary assoc array (ReductionIndex.offset imid 1) hi block hRight]
      have hl : ReductionIndex.distance lo imid + 1 = half + 1 := by
        dsimp only [imid]
        rw [ReductionIndex.distance_to_offset]
      rw [hl]
      have hs : ReductionIndex.offset imid 1 = ReductionIndex.offset lo (half + 1) := by
        dsimp only [imid]
        exact ReductionIndex.offset_add lo half 1
      rw [hs]
      rw [← interval_split f binary assoc array lo (half + 1)
        (ReductionIndex.distance (ReductionIndex.offset lo (half + 1)) hi + 1)]
      have hr : ReductionIndex.distance (ReductionIndex.offset lo (half + 1)) hi =
          ReductionIndex.distance lo hi - (half + 1) :=
        (ReductionIndex.distance_offset_le lo hi (half + 1) valid (by omega)).2
      congr 1
      omega
termination_by ReductionIndex.distance lo hi
decreasing_by
  · exact ReductionIndex.left_decreases lo hi valid hEq
  · exact ReductionIndex.right_decreases lo hi valid hEq

theorem pairwiseFoldl_proven : PairwiseFoldl := by
  intro Index A B _ _ _ _ _ f binary array lo hi block valid assoc
  rw [mapreduce_interval f binary assoc, interval_nonempty]

theorem foldlM_ok {A B : Type} (f : B → A → B) (xs : List A) (init : B) :
    xs.foldlM (fun b a => (Except.ok (f b a) : Jl B)) init = .ok (xs.foldl f init) :=
  List.foldlM_pure

theorem foldlM_ext_on {A B : Type} (xs : List A) (f g : B → A → Jl B)
    (init : B) (h : ∀ x ∈ xs, ∀ a, f a x = g a x) :
    xs.foldlM f init = xs.foldlM g init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    change (f init x).bind (fun a => xs.foldlM f a) =
      (g init x).bind (fun a => xs.foldlM g a)
    rw [h x (by simp) init]
    apply congrArg (fun k : B → Jl B => (g init x).bind k)
    funext a
    exact ih a (fun x hx a => h x (by simp [hx]) a)

theorem intWordFold (counts : Nat → Nat) (is : List Nat) (init : JInt .i64) :
    is.foldl (fun n i => JuliaLean.base.int.add n (JuliaLean.base.int.lit .i64 (counts i))) init =
      JInt.wrap .i64 (init.val + ((is.map counts).sum : Nat)) := by
  induction is generalizing init with
  | nil =>
    simp only [List.map_nil, List.foldl_nil, List.sum_nil, Int.natCast_zero, Int.add_zero]
    apply Subtype.ext
    exact (JuliaLean.Proofs.base.int.wrapInt_val init).symm
  | cons i is ih =>
    rw [List.foldl_cons, ih]
    apply Subtype.ext
    simp only [List.map_cons, List.sum_cons, Int.natCast_add]
    rw [JuliaLean.base.int.add, JuliaLean.Proofs.base.int.add_int_val]
    change wrapInt .i64 (wrapInt .i64 (init.val + wrapInt .i64 (counts i)) + (is.map counts).sum) = _
    rw [JuliaLean.Proofs.base.int.wrapInt_add_left]
    rw [Int.add_comm init.val (wrapInt .i64 (counts i)), Int.add_assoc,
      JuliaLean.Proofs.base.int.wrapInt_add_left]
    change wrapInt .i64 ((counts i : Int) + (init.val + ((is.map counts).sum : Int))) =
      wrapInt .i64 (init.val + ((counts i : Int) + ((is.map counts).sum : Int)))
    congr 1
    omega

theorem chunkCountSum (xs : List Bool) (chunks : Nat) :
    ((List.range chunks).map (fun i => ((xs.drop (8 * i)).take 8).countP id)).sum =
      (xs.take (8 * chunks)).countP id := by
  induction chunks with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [Nat.mul_succ, List.take_add, List.countP_append]

theorem small_widen_value (t w : IntTy) (x : JInt t) (ht : t.bits < 64)
    (hw : w = .i64 ∨ (w = .u64 ∧ t.signed = false)) :
    (JuliaLean.base.int.widenTo w x).val = x.val := by
  apply wrapInt_of_inRange
  have hx := x.property
  rcases hw with rfl | ⟨rfl, hs⟩ <;> cases t <;>
    simp_all [IntTy.bits, IntTy.signed, IntTy.min, IntTy.max] <;> omega

theorem pack8_count_ones (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    JuliaLean.base.int.count_ones
      (JuliaLean.base.int.and_int
        (JuliaLean.base.int.lit .u64 (packBoolBytes [b0, b1, b2, b3, b4, b5, b6, b7]))
        (JuliaLean.base.int.remT .u64 (JInt.lit .u64 0x0101010101010101))) =
      JuliaLean.base.int.lit .i64 ([b0, b1, b2, b3, b4, b5, b6, b7].countP id) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl

theorem unsafeLoadUInt_count_ones (xs : List Bool) (i : Nat) (hi : i < xs.length / 8) :
    JuliaLean.base.int.count_ones
      (JuliaLean.base.int.and_int
        (unsafeLoadUInt (ptrUIntOfPtr (pointerBoolArray ⟨xs⟩)) (i + 1))
        (JuliaLean.base.int.remT .u64 (JInt.lit .u64 0x0101010101010101))) =
      JuliaLean.base.int.lit .i64 (((xs.drop (8 * i)).take 8).countP id) := by
  have hbound : 8 * (i + 1) ≤ xs.length := by
    have := Nat.mul_le_of_le_div 8 (i + 1) xs.length (by omega)
    omega
  have hlen : ((xs.drop (8 * i)).take 8).length = 8 := by
    rw [List.length_take, List.length_drop]
    omega
  unfold unsafeLoadUInt ptrUIntOfPtr pointerBoolArray
  simp only [Nat.zero_add, Nat.add_sub_cancel]
  generalize (xs.drop (8 * i)).take 8 = chunk at hlen ⊢
  rcases chunk with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hlen; done)
  exact pack8_count_ones b0 b1 b2 b3 b4 b5 b6 b7

theorem simpleCountChunkLoop_eq {Acc : Type}
    (addWord : Acc → JInt .i64 → Acc) (remT : Acc → Jl Acc)
    (ptr : Ptr (JInt .u64)) (mask : JInt .u64) (chunks i : Nat) (n : Acc) :
    simpleCountChunkLoop addWord remT ptr mask chunks i n =
      (List.range (chunks + 1 - i)).foldlM (fun acc k =>
        remT (addWord acc
          (JuliaLean.base.int.count_ones
            (JuliaLean.base.int.and_int (unsafeLoadUInt ptr (i + k)) mask)))) n := by
  rw [simpleCountChunkLoop]
  by_cases hi : i ≤ chunks
  · rw [dif_pos hi]
    have hn : chunks + 1 - i = (chunks + 1 - (i + 1)) + 1 := by omega
    rw [hn, List.range_succ_eq_map]
    simp only [List.foldlM_cons, List.foldlM_map, Nat.add_zero]
    change (remT (addWord n (JuliaLean.base.int.count_ones (JuliaLean.base.int.and_int (unsafeLoadUInt ptr i) mask)))).bind _ =
      (remT (addWord n (JuliaLean.base.int.count_ones (JuliaLean.base.int.and_int (unsafeLoadUInt ptr i) mask)))).bind _
    cases remT (addWord n (JuliaLean.base.int.count_ones (JuliaLean.base.int.and_int (unsafeLoadUInt ptr i) mask))) with
    | error e => rfl
    | ok n' =>
      change simpleCountChunkLoop addWord remT ptr mask chunks (i + 1) n' = _
      rw [simpleCountChunkLoop_eq addWord remT ptr mask chunks (i + 1) n']
      apply foldlM_ext_on
      intro k _ acc
      have hk : i + 1 + k = i + (k + 1) := by omega
      rw [hk]
  · rw [dif_neg hi]
    have hn : chunks + 1 - i = 0 := by omega
    rw [hn]
    rfl
termination_by chunks + 1 - i
decreasing_by omega

theorem drop_eq_getD_cons {α : Type} (xs : List α) (d : α) (j : Nat) (hj : j < xs.length) :
    xs.drop j = xs.getD j d :: xs.drop (j + 1) := by
  induction xs generalizing j with
  | nil => contradiction
  | cons x xs ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [List.length_cons] at hj
      simpa only [List.drop_succ_cons, List.getD_cons_succ] using ih j (by omega)

theorem simpleCountTailLoop_eq {Acc : Type}
    (addBool : Acc → Bool → Acc) (remT : Acc → Jl Acc)
    (xs : List Bool) (i : Nat) (hi1 : 1 ≤ i) (n : Acc) :
    simpleCountTailLoop addBool remT ⟨xs⟩ xs.length i n =
      (xs.drop (i - 1)).foldlM (fun acc b => remT (addBool acc b)) n := by
  rw [simpleCountTailLoop]
  by_cases hi : i ≤ xs.length
  · rw [dif_pos hi]
    have hdrop := drop_eq_getD_cons xs false (i - 1) (by omega)
    have hnext : i - 1 + 1 = i := by omega
    rw [hnext] at hdrop
    rw [hdrop, List.foldlM_cons]
    change (remT (addBool n (xs.getD (i - 1) false))).bind _ =
      (remT (addBool n (xs.getD (i - 1) false))).bind _
    cases remT (addBool n (xs.getD (i - 1) false)) with
    | error e => rfl
    | ok n' =>
      dsimp only [bind, Except.bind]
      simpa only [Nat.add_sub_cancel] using
        simpleCountTailLoop_eq addBool remT xs (i + 1) (by omega) n'
  · rw [dif_neg hi]
    have hdrop : xs.drop (i - 1) = [] := List.drop_eq_nil_of_le (by omega)
    rw [hdrop]
    rfl
termination_by xs.length + 1 - i
decreasing_by omega

def BoolArrayCountSpec : Prop :=
  (∀ (xs : List Bool) (init : JInt .i64),
    _simple_count_bool_array
      (add_sum_small id (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add)
      JuliaLean.base.int.add
      (add_sum_small id (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add)
      (fun n => .ok (JuliaLean.base.int.remT .i64 n))
      ⟨xs⟩ init =
      .ok (JInt.wrap .i64 (init.val + (xs.countP id : Int)))) ∧
  (∀ (t : IntTy) (xs : List Bool) (init : JInt t), t.bits < 64 →
    _simple_count_bool_array
      (add_sum_small (JuliaLean.base.int.widenTo .i64) (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add)
      JuliaLean.base.int.add
      (add_sum_small id (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add)
      (fun n => .ok (JuliaLean.base.int.remT .i64 n))
      ⟨xs⟩ init =
      .ok (JInt.wrap .i64 (init.val + (xs.countP id : Int))))

theorem boolArrayCount_int64 (xs : List Bool) (init : JInt .i64) :
    _simple_count_bool_array
      (add_sum_small id (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add)
      JuliaLean.base.int.add
      (add_sum_small id (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add)
      (fun n => .ok (JuliaLean.base.int.remT .i64 n))
      ⟨xs⟩ init =
      .ok (JInt.wrap .i64 (init.val + (xs.countP id : Int))) := by
  have hz : add_sum_small id (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add init false = init := by
    apply Subtype.ext
    change (JuliaLean.base.int.add init (JuliaLean.base.int.ofBool .i64 false)).val = init.val
    rw [JuliaLean.base.int.add, JuliaLean.Proofs.base.int.add_int_val]
    have hb : (JuliaLean.base.int.ofBool .i64 false).val = 0 := by decide
    rw [hb, Int.add_zero, JuliaLean.Proofs.base.int.wrapInt_val]
  unfold _simple_count_bool_array gcPreserve lengthBoolArray sizeofUInt
  dsimp only
  rw [hz, simpleCountChunkLoop_eq]
  have hchunk_step :
      (List.range (xs.length / 8 + 1 - 1)).foldlM
        (fun acc k =>
          (Except.ok
            (JuliaLean.base.int.remT .i64
              (JuliaLean.base.int.add acc
                (JuliaLean.base.int.count_ones
                  (JuliaLean.base.int.and_int
                    (unsafeLoadUInt (ptrUIntOfPtr (pointerBoolArray ⟨xs⟩)) (1 + k))
                    (JuliaLean.base.int.remT .u64 (JInt.lit .u64 0x0101010101010101)))))) : Jl (JInt .i64)))
        init =
      (List.range (xs.length / 8 + 1 - 1)).foldlM
        (fun acc k =>
          (Except.ok
            (JuliaLean.base.int.add acc
              (JuliaLean.base.int.lit .i64 (((xs.drop (8 * k)).take 8).countP id))) : Jl (JInt .i64)))
        init := by
    apply foldlM_ext_on
    intro k hk acc
    have h1k : 1 + k = k + 1 := by omega
    rw [h1k, unsafeLoadUInt_count_ones xs k (by simpa only [Nat.add_sub_cancel] using List.mem_range.mp hk)]
    simp only [JuliaLean.base.int.remT, JuliaLean.base.int.rem_same, dite_true]
  simp only [Nat.add_sub_cancel] at hchunk_step ⊢
  rw [hchunk_step, foldlM_ok, intWordFold, chunkCountSum]
  simp only [bind, Except.bind]
  rw [simpleCountTailLoop_eq _ _ xs (8 * (xs.length / 8) + 1) (by omega)]
  simp only [Nat.add_sub_cancel, JuliaLean.base.int.remT, JuliaLean.base.int.rem_same, dite_true]
  rw [foldlM_ok]
  have htail := intBoolFold id (xs.drop (8 * (xs.length / 8)))
    (JInt.wrap .i64 (init.val + ((xs.take (8 * (xs.length / 8))).countP id : Nat)))
  simp only [id_eq] at htail
  rw [htail]
  apply congrArg Except.ok
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 (init.val + _) + _) = _
  rw [JuliaLean.Proofs.base.int.wrapInt_add_left]
  have hsplit := congrArg (List.countP id) (List.take_append_drop (8 * (xs.length / 8)) xs)
  rw [List.countP_append] at hsplit
  rw [Int.add_assoc, ← Int.natCast_add, hsplit]
  rfl
theorem boolArrayCountSpec_proven : BoolArrayCountSpec := by
  constructor
  · exact boolArrayCount_int64
  · intro t xs init ht
    have hv0 : add_sum_small (JuliaLean.base.int.widenTo .i64) (JuliaLean.base.int.ofBool .i64)
        JuliaLean.base.int.add init false =
        add_sum_small id (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add
          (JuliaLean.base.int.widenTo .i64 init) false := rfl
    have hrun :
        _simple_count_bool_array
          (add_sum_small (JuliaLean.base.int.widenTo .i64) (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add)
          JuliaLean.base.int.add
          (add_sum_small id (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add)
          (fun n => .ok (JuliaLean.base.int.remT .i64 n))
          ⟨xs⟩ init =
        _simple_count_bool_array
          (add_sum_small id (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add)
          JuliaLean.base.int.add
          (add_sum_small id (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add)
          (fun n => .ok (JuliaLean.base.int.remT .i64 n))
          ⟨xs⟩ (JuliaLean.base.int.widenTo .i64 init) := rfl
    rw [hrun, boolArrayCount_int64]
    congr 2
    rw [small_widen_value t .i64 init ht (Or.inl rfl)]

theorem linearReduceWhile_eq_fold {Index Input Output F : Type} [MapCallable F Input Output]
    [LE Index] [LT Index] [DecidableLT Index] [ReductionIndex Index]
    (f : F) (op : Reducer Output Output) (getindex : Index → Input) (last i : Index)
    (hle : i ≤ last) (s : FoldInit Output) :
    linearReduceWhile f op getindex last i s =
      (List.range (ReductionIndex.distance i last)).foldl
        (fun state k =>
          op.step state (MapCallable.apply (Input := Input) f (getindex (ReductionIndex.offset i (k + 1))))) s := by
  rw [linearReduceWhile]
  by_cases hi : i < last
  · rw [dif_pos hi]
    have hne : i ≠ last := ((ReductionIndex.lt_iff_le_and_ne i last).mp hi).2
    have hd : 0 < ReductionIndex.distance i last := ReductionIndex.distance_pos i last hle hne
    have hstep := ReductionIndex.distance_offset_le i last 1 hle (by omega)
    rw [linearReduceWhile_eq_fold f op getindex last (ReductionIndex.offset i 1) hstep.1]
    have hn : ReductionIndex.distance i last =
        ReductionIndex.distance (ReductionIndex.offset i 1) last + 1 := by omega
    rw [hn, List.range_succ_eq_map]
    simp only [List.foldl_cons, List.foldl_map, Nat.add_zero]
    congr 1
    funext state k
    rw [ReductionIndex.offset_add]
    have hk : 1 + (k + 1) = k + 1 + 1 := by omega
    rw [hk]
  · rw [dif_neg hi]
    have heq : i = last :=
      Classical.byContradiction fun hne =>
        hi ((ReductionIndex.lt_iff_le_and_ne i last).mpr ⟨hle, hne⟩)
    subst last
    rw [ReductionIndex.distance_self]
    rfl
termination_by ReductionIndex.distance i last
decreasing_by exact ReductionIndex.next_decreases _ _ hi

def ArrayTraversalSpec : Prop :=
  ∀ {Index Array Input Output : Type}
    [LE Index] [LT Index] [DecidableLE Index] [DecidableLT Index] [DecidableEq Index] [ReductionIndex Index]
    (indices : Array → LinearArray Input Index)
    (iterateArray : Array → JIterator Input)
    (elementType : JIterator Input → EltypeStatus)
    (f : Input → Output) (binary : Output → Output → Output)
    (a : Array) (valid : ∀ a, (indices a).length > 0 → (indices a).first ≤ (indices a).last),
    (indices a).length > 0 →
    ReductionIndex.distance (indices a).first (indices a).last + 1 = (indices a).length →
    (∀ x y z, binary (binary x y) z = binary x (binary y z)) →
    _mapreduce_linear (fun a => (indices a).indices) (fun a => (indices a).get)
      iterateArray elementType f
      (valueReducer binary id _empty_reduce_error) a valid =
      .ok ((List.range (ReductionIndex.distance (indices a).first (indices a).last)).foldl
        (fun acc k => binary acc (f ((indices a).get (ReductionIndex.offset (indices a).first (k + 1)))))
        (f ((indices a).get (indices a).first)))

theorem arrayTraversalSpec_proven : ArrayTraversalSpec := by
  intro Index Array Input Output _ _ _ _ _ _ indices iterateArray elementType f binary a valid positive shape assoc
  have hn : (indices a).length ≠ 0 := by omega
  have hvalid : (indices a).first ≤ (indices a).last := valid a positive
  unfold _mapreduce_linear
  dsimp only [LinearArray.indices, MapCallable.apply]
  rw [dif_neg hn]
  by_cases hs : (indices a).length = 1
  · rw [if_pos hs]
    have hd : ReductionIndex.distance (indices a).first (indices a).last = 0 := by omega
    rw [hd]
    rfl
  · rw [if_neg hs]
    by_cases hshort : (indices a).length < 16
    · rw [if_pos hshort]
      have hd : 0 < ReductionIndex.distance (indices a).first (indices a).last := by omega
      have hstep := ReductionIndex.distance_offset_le (indices a).first (indices a).last 1 hvalid (by omega)
      rw [linearReduceWhile_eq_fold f (valueReducer binary id _empty_reduce_error)
        (indices a).get (indices a).last (ReductionIndex.offset (indices a).first 1) hstep.1]
      rw [hstep.2]
      change (match (List.range (ReductionIndex.distance (indices a).first (indices a).last - 1)).foldl
        (fun (state : FoldInit Output) k => match state with
          | .initial => .value (f ((indices a).get
              (ReductionIndex.offset (ReductionIndex.offset (indices a).first 1) (k + 1))))
          | .value acc => .value (binary acc (f ((indices a).get
              (ReductionIndex.offset (ReductionIndex.offset (indices a).first 1) (k + 1))))))
        (.value (binary (f ((indices a).get (indices a).first))
          (f ((indices a).get (ReductionIndex.offset (indices a).first 1))))) with
          | .initial => _empty_reduce_error
          | .value x => .ok x) = _
      rw [value_fold]
      have he : ReductionIndex.distance (indices a).first (indices a).last =
          (ReductionIndex.distance (indices a).first (indices a).last - 1) + 1 := by omega
      conv => rhs; rw [he, List.range_succ_eq_map]
      simp only [List.foldl_cons, List.foldl_map, Nat.add_zero]
      congr 2
      funext acc k
      rw [ReductionIndex.offset_add]
      have hk : 1 + (k + 1) = k + 1 + 1 := by omega
      rw [hk]
    · rw [if_neg hshort]
      unfold mapreduce_impl_default pairwise_blocksize
      rw [pairwiseFoldl_proven f binary (indices a) (indices a).first (indices a).last 1024
        hvalid assoc]

def ArrayEmptySpec : Prop :=
  ∀ {Index Array Input Output : Type}
    [LE Index] [LT Index] [DecidableLE Index] [DecidableLT Index] [DecidableEq Index] [ReductionIndex Index]
    (indices : Array → LinearArray Input Index)
    (iterateArray : Array → JIterator Input) (f : Input → Output)
    (op : Reducer Output Output) (a : Array)
    (valid : ∀ a, (indices a).length > 0 → (indices a).first ≤ (indices a).last),
    (indices a).length = 0 →
    _mapreduce_linear (fun a => (indices a).indices) (fun a => (indices a).get)
      iterateArray (fun _ => .hasEltype) f op a valid = _empty_reduce_error

theorem arrayEmptySpec_proven : ArrayEmptySpec := by
  intro Index Array Input Output _ _ _ _ _ _ indices iterateArray f op a valid he
  unfold _mapreduce_linear
  dsimp only [LinearArray.indices]
  rw [dif_pos he]
  rfl

def ArrayMethodsSpec : Prop := ArrayTraversalSpec ∧ ArrayEmptySpec

theorem arrayMethodsSpec_proven : ArrayMethodsSpec :=
  ⟨arrayTraversalSpec_proven, arrayEmptySpec_proven⟩

theorem flatten_singletons {A B : Type} (f : A → B) (xs : List A) :
    (xs.map (fun x => [f x])).flatten = xs.map f := by
  induction xs <;> simp_all

theorem reduceSafe_proven : ReduceSafe := by
  constructor
  · intro Index A _ _ _ _ _ array lo hi block valid hfirst hlast
    dsimp only
    constructor
    · rw [pairwiseFoldl_proven (fun p : Index × A => [p.1]) List.append _ lo hi block valid
        (fun a b c => List.append_assoc a b c)]
      congr 1
      change (List.range (ReductionIndex.distance lo hi)).foldl
        (fun acc k => acc ++ [ReductionIndex.offset lo (k + 1)]) [lo] = _
      rw [List.foldl_append_eq_append]
      rw [flatten_singletons]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, Function.comp_def, ReductionIndex.offset_zero,
        Nat.add_succ, Nat.add_zero, List.singleton_append]
    · intro idx hmem
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hmem
      have hb := List.mem_range.mp hk
      have hlo : lo ≤ ReductionIndex.offset lo k := ReductionIndex.le_offset lo k
      have hhi : ReductionIndex.offset lo k ≤ hi :=
        (ReductionIndex.distance_offset_le lo hi k valid (by omega)).1
      exact ⟨ReductionIndex.le_trans hfirst hlo, ReductionIndex.le_trans hhi hlast⟩
  · intro x i
    constructor
    · intro hi1 hichunk
      change i ≤ x.elements.length / 8 at hichunk
      have hbound : 8 * i ≤ x.elements.length := by
        have := Nat.mul_le_of_le_div 8 i x.elements.length hichunk
        omega
      have hlen : ((x.elements.drop (8 * (i - 1))).take 8).length = 8 := by
        rw [List.length_take, List.length_drop]
        omega
      have hslice :
          ((ptrUIntOfPtr (pointerBoolArray x)).bytes.drop
            ((ptrUIntOfPtr (pointerBoolArray x)).offset + 8 * (i - 1))).take 8 =
          (x.elements.drop (8 * (i - 1))).take 8 := by
        simp [ptrUIntOfPtr, pointerBoolArray]
      refine ⟨hbound, hslice, by rw [hslice]; exact hlen, ?_⟩
      cases x with
      | mk xs =>
        dsimp only at hichunk
        have hi_eq : i = (i - 1) + 1 := by omega
        rw [hi_eq]
        simpa only [Nat.add_sub_cancel] using
          unsafeLoadUInt_count_ones xs (i - 1) (by omega)
    · intro hlo hhi
      change 8 * (x.elements.length / 8) + 1 ≤ i at hlo
      change i ≤ x.elements.length at hhi
      omega
theorem extreme_extend {A K : Type} (less : A → A → Bool) (order : StrictWeakOrder less)
    (entries : List (K × A)) (best : A × K) (key : K) (x : A)
    (hbest : FirstExtreme less entries best.1 best.2) :
    FirstExtreme less (entries ++ [(key, x)])
      (rf_findmax less best (x, key)).1 (rf_findmax less best (x, key)).2 := by
  obtain ⟨before, after, heq, hmax, hfirst⟩ := hbest
  by_cases hx : less best.1 x = true
  · simp only [rf_findmax, hx, ↓reduceIte]
    refine ⟨entries, [], by simp, ?_, ?_⟩
    · intro k y hy
      rcases List.mem_append.mp hy with hy | hy
      · cases hxy : less x y with
        | false => rfl
        | true =>
          have hh := order.trans best.1 x y hx hxy
          rw [hmax k y hy] at hh
          contradiction
      · cases List.mem_singleton.mp hy
        exact order.irrefl x
    · intro k y hy
      cases hyx : less y x with
      | true => rfl
      | false =>
        have hh := order.not_trans best.1 y x (hmax k y hy) hyx
        rw [hx] at hh
        contradiction
  · have hfalse : less best.1 x = false := by
      cases h : less best.1 x <;> simp_all
    simp only [rf_findmax, hfalse, Bool.false_eq_true, ↓reduceIte]
    refine ⟨before, after ++ [(key, x)], ?_, ?_, hfirst⟩
    · rw [heq]
      simp only [List.append_assoc, List.cons_append]
    · intro k y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hmax k y hy
      · cases List.mem_singleton.mp hy
        exact hfalse

theorem extreme_fold {A K : Type} (less : A → A → Bool) (order : StrictWeakOrder less)
    (suffix processed : List (K × A)) (best : A × K)
    (hbest : FirstExtreme less processed best.1 best.2) :
    FirstExtreme less (processed ++ suffix)
      ((suffix.map (fun p => (p.2, p.1))).foldl (rf_findmax less) best).1
      ((suffix.map (fun p => (p.2, p.1))).foldl (rf_findmax less) best).2 := by
  induction suffix generalizing processed best with
  | nil => simpa using hbest
  | cons p suffix ih =>
    have hn := extreme_extend less order processed best p.1 p.2 hbest
    have hr := ih (processed ++ [p]) (rf_findmax less best (p.2, p.1)) hn
    simpa only [List.map_cons, List.foldl_cons, List.append_assoc,
      List.singleton_append] using hr

theorem findmax_nonempty {A K : Type}
    (elementType : {I : Type} → JIterator I → EltypeStatus)
    (pairs : JIterator A → JIterator (K × A)) (less : A → A → Bool)
    (domain : JIterator A) (key : K) (x : A) (entries : List (K × A))
    (hp : pairs domain = .values ((key, x) :: entries)) :
    findmax elementType pairs id less domain =
      .ok ((entries.map (fun p => (p.2, p.1))).foldl (rf_findmax less) (x, key)) := by
  unfold findmax _findmax_identity findmax_f _findmax
  rw [hp]
  change mapfoldl elementType (fun p : K × A => (p.2, p.1))
    (valueReducer (rf_findmax less) id _empty_reduce_error)
    (.values ((key, x) :: entries)) .initial = _
  rw [mapfoldl_values_nonempty]
  rfl

theorem findmax_extreme {A K : Type}
    (elementType : {I : Type} → JIterator I → EltypeStatus)
    (pairs : JIterator A → JIterator (K × A)) (less : A → A → Bool)
    (order : StrictWeakOrder less) (domain : JIterator A) (entries : List (K × A))
    (hp : pairs domain = .values entries) (nonempty : entries ≠ []) :
    ∃ v k, findmax elementType pairs id less domain = .ok (v, k) ∧
      FirstExtreme less entries v k := by
  cases entries with
  | nil => exact False.elim (nonempty rfl)
  | cons p entries =>
    let result := (entries.map (fun p => (p.2, p.1))).foldl (rf_findmax less) (p.2, p.1)
    refine ⟨result.1, result.2, findmax_nonempty elementType pairs less domain p.1 p.2 entries hp, ?_⟩
    have hfirst : FirstExtreme less [p] p.2 p.1 := by
      refine ⟨[], [], by cases p; rfl, ?_, ?_⟩
      · intro k y hy
        cases List.mem_singleton.mp hy
        exact order.irrefl _
      · simp
    simpa only [List.singleton_append] using extreme_fold less order entries [p] (p.2, p.1) hfirst

theorem findExtremaSpec_proven : FindExtremaSpec := by
  intro A K elementType pairs less greater domain entries hless hgreater hp nonempty
  constructor
  · obtain ⟨v, k, hr, he⟩ := findmax_extreme elementType pairs less hless domain entries hp nonempty
    refine ⟨v, k, hr, he, ?_⟩
    unfold argmax
    rw [hr]
    rfl
  · obtain ⟨v, k, hr, he⟩ := findmax_extreme elementType pairs greater hgreater domain entries hp nonempty
    refine ⟨v, k, hr, he, ?_⟩
    change (findmax elementType pairs id greater domain).map Prod.snd = _
    rw [hr]
    rfl

theorem firstExtreme_member {A K : Type} {less : A → A → Bool}
    {entries : List (K × A)} {v : A} {k : K} (h : FirstExtreme less entries v k) :
    (k, v) ∈ entries := by
  obtain ⟨before, after, he, _, _⟩ := h
  rw [he]
  simp

theorem mapped_findmax_extreme {A B K : Type}
    (elementType : {I : Type} → JIterator I → EltypeStatus)
    (pairs : JIterator A → JIterator (K × A)) (f : A → B) (less : B → B → Bool)
    (order : StrictWeakOrder less) (domain : JIterator A) (entries : List (K × A))
    (hp : pairs domain = .values entries) (hn : entries ≠ []) :
    ∃ v k, findmax_f elementType pairs f less domain = .ok (v, k) ∧
      FirstExtreme less (entries.map (fun p => (p.1, f p.2))) v k := by
  cases entries with
  | nil => exact False.elim (hn rfl)
  | cons p entries =>
    let result := (entries.map (fun p => (f p.2, p.1))).foldl (rf_findmax less) (f p.2, p.1)
    refine ⟨result.1, result.2, ?_, ?_⟩
    · unfold findmax_f _findmax
      rw [hp]
      change mapfoldl elementType (fun p : K × A => (f p.2, p.1))
        (valueReducer (rf_findmax less) id _empty_reduce_error)
        (.values (p :: entries)) .initial = _
      rw [mapfoldl_values_nonempty]
      rfl
    · have hfirst : FirstExtreme less [(p.1, f p.2)] (f p.2) p.1 := by
        refine ⟨[], [], rfl, ?_, ?_⟩
        · intro k y hy
          cases List.mem_singleton.mp hy
          exact order.irrefl _
        · simp
      have hf := extreme_fold less order (entries.map (fun p => (p.1, f p.2)))
        [(p.1, f p.2)] (f p.2, p.1) hfirst
      simpa only [List.map_cons, List.map_map, Function.comp_def, List.singleton_append] using hf

theorem argmax_extreme {A B : Type}
    (elementType : {I : Type} → JIterator I → EltypeStatus)
    (f : A → B) (less : B → B → Bool) (order : StrictWeakOrder less)
    (xs : List A) (hn : xs ≠ []) :
    ∃ x, argmax_f elementType f less (.values xs) = .ok x ∧
      FirstExtreme less (xs.map (fun x => (x, f x))) (f x) x := by
  cases xs with
  | nil => exact False.elim (hn rfl)
  | cons x xs =>
    let result := (xs.map (fun x => (f x, x))).foldl (rf_findmax less) (f x, x)
    have hfirst : FirstExtreme less [(x, f x)] (f x) x := by
      refine ⟨[], [], rfl, ?_, ?_⟩
      · intro k y hy
        cases List.mem_singleton.mp hy
        exact order.irrefl _
      · simp
    have hf := extreme_fold less order (xs.map (fun x => (x, f x))) [(x, f x)] (f x, x) hfirst
    have hbest : FirstExtreme less ((x :: xs).map (fun x => (x, f x))) result.1 result.2 := by
      simpa only [List.map_cons, List.map_map, Function.comp_def, List.singleton_append] using hf
    obtain ⟨y, _, hy⟩ := List.mem_map.mp (firstExtreme_member hbest)
    have hk := congrArg Prod.fst hy
    have hv := congrArg Prod.snd hy
    change y = result.2 at hk
    change f y = result.1 at hv
    rw [hk] at hv
    refine ⟨result.2, ?_, ?_⟩
    · unfold argmax_f
      change (mapfoldl elementType (fun x => (f x, x))
        (valueReducer (rf_findmax less) id _empty_reduce_error)
        (.values (x :: xs)) .initial).map Prod.snd = _
      rw [mapfoldl_values_nonempty]
      rfl
    · rw [hv]
      exact hbest

def MappedSearchSpec : Prop :=
  ∀ {A B K : Type} (elementType : {I : Type} → JIterator I → EltypeStatus)
    (pairs : JIterator A → JIterator (K × A)) (f : A → B)
    (less greater : B → B → Bool) (domain : JIterator A) (entries : List (K × A)),
    StrictWeakOrder less → StrictWeakOrder greater →
    pairs domain = .values entries → entries ≠ [] →
    (∃ v k, findmax_f elementType pairs f less domain = .ok (v, k) ∧
      FirstExtreme less (entries.map (fun p => (p.1, f p.2))) v k) ∧
    (∃ v k, findmin_f elementType pairs f greater domain = .ok (v, k) ∧
      FirstExtreme greater (entries.map (fun p => (p.1, f p.2))) v k) ∧
    (∀ xs : List A, xs ≠ [] →
      (∃ x, argmax_f elementType f less (.values xs) = .ok x ∧
        FirstExtreme less (xs.map (fun x => (x, f x))) (f x) x) ∧
      (∃ x, argmin_f elementType f greater (.values xs) = .ok x ∧
        FirstExtreme greater (xs.map (fun x => (x, f x))) (f x) x))

theorem mappedSearchSpec_proven : MappedSearchSpec := by
  intro A B K elementType pairs f less greater domain entries hless hgreater hp hn
  refine ⟨mapped_findmax_extreme elementType pairs f less hless domain entries hp hn,
    mapped_findmax_extreme elementType pairs f greater hgreater domain entries hp hn, ?_⟩
  intro xs hn
  exact ⟨argmax_extreme elementType f less hless xs hn,
    argmax_extreme elementType f greater hgreater xs hn⟩

theorem rf_fold_fst {A K : Type} (less : A → A → Bool)
    (entries : List (K × A)) (init : A × K) :
    ((entries.map (fun p => (p.2, p.1))).foldl (rf_findmax less) init).1 =
      (entries.map Prod.snd).foldl (fun a b => if less a b then b else a) init.1 := by
  induction entries generalizing init with
  | nil => rfl
  | cons p entries ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ih]
    unfold rf_findmax
    split <;> rfl

theorem findmax_agrees_one {A K : Type}
    (elementType : {I : Type} → JIterator I → EltypeStatus)
    (pairs : JIterator A → JIterator (K × A)) (less : A → A → Bool)
    (order : StrictWeakOrder less) (xs : List A) (entries : List (K × A))
    (hp : pairs (.values xs) = .values entries) (he : entries.map Prod.snd = xs)
    (hn : xs ≠ []) (v : A) (k : K)
    (hr : findmax elementType pairs id less (.values xs) = .ok (v, k)) :
    maximum elementType id
      (valueReducer (fun a b => if less a b then b else a) id _empty_reduce_error)
      (.values xs) .initial = .ok v ∧ (k, v) ∈ entries := by
  have hne : entries ≠ [] := by intro h; simp [h] at he; subst xs; exact hn rfl
  obtain ⟨v0, k0, hknown, hbest⟩ :=
    findmax_extreme elementType pairs less order (.values xs) entries hp hne
  have heq : (v0, k0) = (v, k) := Except.ok.inj (hknown.symm.trans hr)
  have hmem : (k, v) ∈ entries := by
    obtain ⟨before, after, hb, _, _⟩ := hbest
    have hv := congrArg Prod.fst heq
    have hk := congrArg Prod.snd heq
    change v0 = v at hv
    change k0 = k at hk
    rw [hv, hk] at hb
    rw [hb]
    simp
  refine ⟨?_, hmem⟩
  subst xs
  cases entries with
  | nil => exact False.elim (hne rfl)
  | cons p entries =>
    have hf := findmax_nonempty elementType pairs less
      (.values (((p :: entries).map Prod.snd))) p.1 p.2 entries hp
    have hv := congrArg Prod.fst (Except.ok.inj (hf.symm.trans hr))
    unfold maximum mapreduce
    simp only [List.map_cons]
    rw [mapfoldl_identity_mapper_nonempty]
    dsimp only [id]
    rw [← rf_fold_fst less entries (p.2, p.1)]
    exact congrArg Except.ok hv

theorem selection_fold_equiv {A : Type} (less : A → A → Bool) (op : A → A → A)
    (E : A → A → Prop) (eqLaws : Equivalence E)
    (compatible : ∀ a b c d, E a b → E c d → less a c = less b d)
    (opLaw : ∀ a b, E (op a b) (if less a b then b else a))
    (xs : List A) (left right : A) (hinit : E left right) :
    E (xs.foldl (fun a b => if less a b then b else a) left) (xs.foldl op right) := by
  induction xs generalizing left right with
  | nil => exact hinit
  | cons x xs ih =>
    apply ih
    have hc := compatible left right x x hinit (eqLaws.refl x)
    have hselected :
        E (if less left x then x else left) (if less right x then x else right) := by
      rw [hc]
      split
      · exact eqLaws.refl x
      · exact hinit
    exact eqLaws.trans hselected (eqLaws.symm (opLaw right x))

theorem maximum_equiv_selection {A : Type}
    (elementType : {I : Type} → JIterator I → EltypeStatus)
    (less : A → A → Bool) (op : A → A → A) (E : A → A → Prop)
    (eqLaws : Equivalence E)
    (compatible : ∀ a b c d, E a b → E c d → less a c = less b d)
    (opLaw : ∀ a b, E (op a b) (if less a b then b else a))
    (xs : List A) (v : A) (hn : xs ≠ [])
    (hv : maximum elementType id
      (valueReducer (fun a b => if less a b then b else a) id _empty_reduce_error)
      (.values xs) .initial = .ok v) :
    ∃ m, maximum elementType id (valueReducer op (reduce_first op) _empty_reduce_error)
      (.values xs) .initial = .ok m ∧ E v m := by
  cases xs with
  | nil => exact False.elim (hn rfl)
  | cons x xs =>
    refine ⟨xs.foldl op x, ?_, ?_⟩
    · exact mapfoldl_identity_mapper_nonempty elementType op id _empty_reduce_error x xs
    · unfold maximum mapreduce at hv
      rw [mapfoldl_identity_mapper_nonempty] at hv
      simp only [Except.ok.injEq] at hv
      rw [← hv]
      exact selection_fold_equiv less op E eqLaws compatible opLaw xs x x (eqLaws.refl x)

theorem findmaxAgree_proven : FindmaxAgree := by
  intro A K elementType pairs less greater maxOp minOp E xs entries
    hless hgreater eqLaws cless cgreater maxLaw minLaw hp he hn
  constructor
  · intro v k hr
    obtain ⟨hv, hm⟩ := findmax_agrees_one elementType pairs less hless xs entries hp he hn v k hr
    obtain ⟨m, hmax, hvmax⟩ :=
      maximum_equiv_selection elementType less maxOp E eqLaws cless maxLaw xs v hn hv
    exact ⟨m, hmax, hvmax, hm⟩
  · intro v k hr
    obtain ⟨hv, hm⟩ := findmax_agrees_one elementType pairs greater hgreater xs entries hp he hn v k hr
    obtain ⟨m, hmin, hvmin⟩ :=
      maximum_equiv_selection elementType greater minOp E eqLaws cgreater minLaw xs v hn hv
    exact ⟨m, hmin, hvmin, hm⟩

abbrev FloatValue := JuliaLean.base.float.FV .f64

def floatEquivalent (x y : FloatValue) : Prop :=
  x = y ∨ (JuliaLean.Promotion.Fl.isnan x = true ∧ JuliaLean.Promotion.Fl.isnan y = true)

abbrev floatGreater : FloatValue → FloatValue → Bool :=
  JuliaLean.base.operators.isgreater
    (JuliaLean.base.operators.isunorderedFloat JuliaLean.base.float.isnan_IEEEFloat)
    (JuliaLean.base.operators.isunorderedFloat JuliaLean.base.float.isnan_IEEEFloat)
    JuliaLean.base.float.isless_IEEEFloat JuliaLean.base.float.isless_IEEEFloat

theorem floatEquivalent_equivalence : Equivalence floatEquivalent := by
  refine ⟨fun _ => Or.inl rfl, ?_, ?_⟩
  · intro x y h
    rcases h with h | ⟨hx, hy⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hy, hx⟩
  · intro x y z hxy hyz
    rcases hxy with rfl | ⟨hx, hy⟩
    · exact hyz
    rcases hyz with rfl | ⟨_, hz⟩
    · exact Or.inr ⟨hx, hy⟩
    · exact Or.inr ⟨hx, hz⟩

theorem floatLess_order : StrictWeakOrder
    (JuliaLean.base.float.isless_IEEEFloat (T := .f64)) := by
  constructor
  · intro a
    rw [JuliaLean.Proofs.base.float.isless_IEEEFloat_eq]
    cases h : a.isnan <;> simp [JuliaLean.Promotion.Fl.isless, h]
  · exact JuliaLean.Proofs.base.float.islessTransitive_proven .f64
  · intro a b c hab hbc
    rw [JuliaLean.Proofs.base.float.isless_IEEEFloat_eq] at hab hbc ⊢
    cases ha : a.isnan <;> cases hb : b.isnan <;> cases hc : c.isnan <;>
      cases sa : a.signbit <;> cases sb : b.signbit <;> cases sc : c.signbit <;>
      simp_all [JuliaLean.Promotion.Fl.isless] <;> omega

theorem floatGreater_order : StrictWeakOrder floatGreater := by
  constructor
  · intro a
    simp only [floatGreater, JuliaLean.base.operators.isgreater,
      JuliaLean.base.operators.isunorderedFloat, JuliaLean.Proofs.base.float.isnan_IEEEFloat_eq,
      JuliaLean.Proofs.base.float.isless_IEEEFloat_eq]
    cases h : a.isnan <;> simp [JuliaLean.Promotion.Fl.isless, h]
  · intro a b c hab hbc
    simp only [floatGreater, JuliaLean.base.operators.isgreater,
      JuliaLean.base.operators.isunorderedFloat, JuliaLean.Proofs.base.float.isnan_IEEEFloat_eq,
      JuliaLean.Proofs.base.float.isless_IEEEFloat_eq] at hab hbc ⊢
    cases ha : a.isnan <;> cases hb : b.isnan <;> cases hc : c.isnan <;>
      cases sa : a.signbit <;> cases sb : b.signbit <;> cases sc : c.signbit <;>
      simp_all [JuliaLean.Promotion.Fl.isless] <;> omega
  · intro a b c hab hbc
    simp only [floatGreater, JuliaLean.base.operators.isgreater,
      JuliaLean.base.operators.isunorderedFloat, JuliaLean.Proofs.base.float.isnan_IEEEFloat_eq,
      JuliaLean.Proofs.base.float.isless_IEEEFloat_eq] at hab hbc ⊢
    cases ha : a.isnan <;> cases hb : b.isnan <;> cases hc : c.isnan <;>
      cases sa : a.signbit <;> cases sb : b.signbit <;> cases sc : c.signbit <;>
      simp_all [JuliaLean.Promotion.Fl.isless] <;> omega

theorem floatOrder_compatible (a b c d : FloatValue)
    (hab : floatEquivalent a b) (hcd : floatEquivalent c d) :
    JuliaLean.base.float.isless_IEEEFloat a c = JuliaLean.base.float.isless_IEEEFloat b d ∧
    floatGreater a c = floatGreater b d := by
  rcases hab with rfl | ⟨ha, hb⟩ <;> rcases hcd with rfl | ⟨hc, hd⟩ <;>
    simp [floatGreater, JuliaLean.base.operators.isgreater,
      JuliaLean.base.operators.isunorderedFloat, JuliaLean.Proofs.base.float.isnan_IEEEFloat_eq,
      JuliaLean.Proofs.base.float.isless_IEEEFloat_eq, JuliaLean.Promotion.Fl.isless, *]

abbrev floatMax : FloatValue → FloatValue → FloatValue :=
  JuliaLean.base.operators.max JuliaLean.base.float.isless_IEEEFloat JuliaLean.base.essentials.ifelse

abbrev floatMin : FloatValue → FloatValue → FloatValue :=
  JuliaLean.base.operators.min
    (JuliaLean.base.operators.greaterThan floatGreater)
    JuliaLean.base.essentials.ifelse


theorem floatMin_law (a b : FloatValue) :
    floatEquivalent (floatMin a b) (if floatGreater a b then b else a) := by
  exact Or.inl rfl

def FloatFindmaxAgreeSpec : Prop :=
  ∀ {K : Type} (elementType : {I : Type} → JIterator I → EltypeStatus)
    (pairs : JIterator FloatValue → JIterator (K × FloatValue))
    (xs : List FloatValue) (entries : List (K × FloatValue)),
    pairs (.values xs) = .values entries → entries.map Prod.snd = xs → xs ≠ [] →
    (∀ v k, findmax elementType pairs id JuliaLean.base.float.isless_IEEEFloat (.values xs) = .ok (v, k) →
      ∃ m, maximum elementType id (valueReducer floatMax (reduce_first floatMax) _empty_reduce_error)
        (.values xs) .initial = .ok m ∧ floatEquivalent v m ∧ (k, v) ∈ entries) ∧
    (∀ v k, findmin elementType pairs id floatGreater (.values xs) = .ok (v, k) →
      ∃ m, minimum elementType id (valueReducer floatMin (reduce_first floatMin) _empty_reduce_error)
        (.values xs) .initial = .ok m ∧ floatEquivalent v m ∧ (k, v) ∈ entries)

def FindmaxAgreementSpec : Prop := FindmaxAgree ∧ FloatFindmaxAgreeSpec

theorem source_add_widen (w : IntTy) {s t : IntTy} (x : JInt s) (y : JInt t) :
    JuliaLean.base.int.add (JuliaLean.base.int.widenTo w x) (JuliaLean.base.int.widenTo w y) =
      JInt.wrap w (x.val + y.val) := by
  apply Subtype.ext
  rw [JuliaLean.base.int.add, JuliaLean.Proofs.base.int.add_int_val]
  change wrapInt w (wrapInt w x.val + wrapInt w y.val) = wrapInt w (x.val + y.val)
  rw [JuliaLean.Proofs.base.int.wrapInt_add_left, JuliaLean.Proofs.base.int.wrapInt_add_right]

theorem source_mul_widen (w : IntTy) {s t : IntTy} (x : JInt s) (y : JInt t) :
    JuliaLean.base.int.mul (JuliaLean.base.int.widenTo w x) (JuliaLean.base.int.widenTo w y) =
      JInt.wrap w (x.val * y.val) := by
  apply Subtype.ext
  rw [JuliaLean.base.int.mul, JuliaLean.Proofs.base.int.mul_int_val]
  change wrapInt w (wrapInt w x.val * wrapInt w y.val) = wrapInt w (x.val * y.val)
  rw [JuliaLean.Proofs.base.int.wrapInt_mul_left, JuliaLean.Proofs.base.int.wrapInt_mul_right]

def smallSumWidth (s t : IntTy) : IntTy :=
  if s.signed = false ∧ t.signed = false then .u64 else .i64

theorem integerAddSum_small {s t : IntTy} (x : JInt s) (y : JInt t)
    (hs : s.bits < 64) (ht : t.bits < 64) :
    integerAddSum ⟨s, x⟩ ⟨t, y⟩ =
      ⟨smallSumWidth s t, JInt.wrap (smallSumWidth s t) (x.val + y.val)⟩ := by
  unfold integerAddSum
  rw [if_pos ⟨hs, ht⟩]
  by_cases hu : s.signed = false ∧ t.signed = false
  · rw [if_pos hu, show smallSumWidth s t = .u64 from if_pos hu]
    exact congrArg (Sigma.mk IntTy.u64) (source_add_widen .u64 x y)
  · rw [if_neg hu, show smallSumWidth s t = .i64 from if_neg hu]
    exact congrArg (Sigma.mk IntTy.i64) (source_add_widen .i64 x y)

theorem reductionOperatorSemantics_proven : ReductionOperatorSemantics := by
  constructor
  · intro s t x y hs ht
    refine ⟨integerAddSum_small x y hs ht, ?_⟩
    intro hsign
    cases hb : s.signed with
    | false =>
      have hy : t.signed = false := hsign.symm.trans hb
      simpa [integerMulProd, hs, ht, hb, hy, mul_prod_unsigned_small] using
        congrArg (Sigma.mk IntTy.u64) (source_mul_widen .u64 x y)
    | true =>
      have hy : t.signed = true := hsign.symm.trans hb
      simpa [integerMulProd, hs, ht, hb, hy, mul_prod_signed_small] using
        congrArg (Sigma.mk IntTy.i64) (source_mul_widen .i64 x y)
  · intro A B R Other plus mul x y
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr
      change assertReal (plus x y) = .ok r
      rw [hr]
      rfl
    · intro bad hbad
      change assertReal (plus x y) = .error .typeError
      rw [hbad]
      rfl
    · intro r hr
      change assertReal (mul x y) = .ok r
      rw [hr]
      rfl
    · intro bad hbad
      change assertReal (mul x y) = .error .typeError
      rw [hbad]
      rfl
def BoolSmallSumSpec : Prop :=
  (∀ (t : IntTy) (x : JInt t) (b : Bool), t.bits < 64 →
    add_sum_small (JuliaLean.base.int.ofBool .i64) (JuliaLean.base.int.widenTo .i64)
      JuliaLean.base.int.add b x =
      JInt.wrap .i64 ((if b then 1 else 0) + x.val) ∧
    add_sum_small (JuliaLean.base.int.widenTo .i64) (JuliaLean.base.int.ofBool .i64)
      JuliaLean.base.int.add x b =
      JInt.wrap .i64 (x.val + (if b then 1 else 0))) ∧
  (∀ a b : Bool,
    add_sum_small (JuliaLean.base.int.ofBool .i64) (JuliaLean.base.int.ofBool .i64)
      JuliaLean.base.int.add a b =
      JInt.wrap .i64 ((if a then 1 else 0) + (if b then 1 else 0)))

theorem boolSmallSumSpec_proven : BoolSmallSumSpec := by
  constructor
  · intro t x b _
    have hb : (JuliaLean.base.int.ofBool .i64 b).val = (if b then 1 else 0) := by
      cases b <;> decide
    constructor <;> apply Subtype.ext
    · simp only [add_sum_small, JuliaLean.base.int.add, JuliaLean.Proofs.base.int.add_int_val]
      change wrapInt .i64 ((JuliaLean.base.int.ofBool .i64 b).val + wrapInt .i64 x.val) = _
      rw [hb, JuliaLean.Proofs.base.int.wrapInt_add_right]
      rfl
    · simp only [add_sum_small, JuliaLean.base.int.add, JuliaLean.Proofs.base.int.add_int_val]
      change wrapInt .i64 (wrapInt .i64 x.val + (JuliaLean.base.int.ofBool .i64 b).val) = _
      rw [hb, JuliaLean.Proofs.base.int.wrapInt_add_left]
      rfl
  · intro a b
    cases a <;> cases b <;> decide

theorem integerAddSum_word {t w : IntTy} (x : JInt w) (y : JInt t)
    (ht : t.bits < 64) (hw : w = .i64 ∨ w = .u64) :
    integerAddSum ⟨w, x⟩ ⟨t, y⟩ = ⟨w, JInt.wrap w (x.val + y.val)⟩ := by
  rcases hw with rfl | rfl <;> cases t <;>
    simp_all [IntTy.bits, integerAddSum, add_sum, integerBinary, integerPromotion,
      JuliaLean.base.int.promote_rule, JuliaLean.base.int.promote_rule_Int64,
      JuliaLean.base.int.promote_rule_UInt64, source_add_widen]

theorem integer_fold_word {t w : IntTy} (xs : List (JInt t)) (a : JInt w)
    (ht : t.bits < 64) (hw : w = .i64 ∨ w = .u64) :
    (xs.map (fun x => (⟨t, x⟩ : IntegerAccumulator))).foldl integerAddSum ⟨w, a⟩ =
      ⟨w, JInt.wrap w (a.val + (xs.map (fun x => x.val)).sum)⟩ := by
  induction xs generalizing a with
  | nil =>
    simp only [List.map_nil, List.foldl_nil, List.sum_nil, Int.add_zero]
    congr 1
    apply Subtype.ext
    exact (JuliaLean.Proofs.base.int.wrapInt_val a).symm
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [integerAddSum_word a x ht hw, ih]
    congr 1
    apply Subtype.ext
    change wrapInt w (wrapInt w (a.val + x.val) + (xs.map (fun x => x.val)).sum) =
      wrapInt w (a.val + (x.val + (xs.map (fun x => x.val)).sum))
    rw [JuliaLean.Proofs.base.int.wrapInt_add_left, Int.add_assoc]

theorem sumInitWidened_proven : SumInitWidened := by
  intro t s xs ht hs nonempty
  cases xs with
  | nil => exact False.elim (nonempty rfl)
  | cons x xs =>
    let w := smallSumWidth s t
    have hw : w = .i64 ∨ w = .u64 := by
      unfold w smallSumWidth
      split <;> simp
    refine ⟨w, hw, ?_⟩
    rw [sum, sum_f, mapreduce, mapfoldl_identity_mapper]
    simp only [List.map_cons, List.foldl_cons]
    rw [integerAddSum_small _ _ hs ht, integer_fold_word _ _ ht hw]
    have hz : (JuliaLean.base.int.lit s 0).val = 0 := by cases s <;> decide
    congr 2
    apply Subtype.ext
    change wrapInt w (wrapInt w ((JuliaLean.base.int.lit s 0).val + x.val) +
      (xs.map (fun x => x.val)).sum) = wrapInt w (x.val + (xs.map (fun x => x.val)).sum)
    rw [hz, Int.zero_add, JuliaLean.Proofs.base.int.wrapInt_add_left]

theorem bool_ne_jint64 : Bool ≠ JInt .i64 := by
  intro h
  let g : JInt .i64 → Bool := cast h.symm
  have inj {x y : JInt .i64} (he : g x = g y) : x = y := by
    have hh := congrArg (cast h) he
    simpa [g] using hh
  let z := JuliaLean.base.int.lit .i64 0
  let o := JuliaLean.base.int.lit .i64 1
  let t := JuliaLean.base.int.lit .i64 2
  have hzo : g z ≠ g o := by
    intro hh
    have := congrArg Subtype.val (inj hh)
    exact (by decide : z.val ≠ o.val) this
  have hzt : g z ≠ g t := by
    intro hh
    have := congrArg Subtype.val (inj hh)
    exact (by decide : z.val ≠ t.val) this
  have hot : g o ≠ g t := by
    intro hh
    have := congrArg Subtype.val (inj hh)
    exact (by decide : o.val ≠ t.val) this
  cases hz : g z <;> cases ho : g o <;> cases ht : g t <;> simp_all

theorem reduceNumberFirst_refuted : ¬ ReduceNumberFirst := by
  intro h
  let op := valueReducer
    (fun a b => JuliaLean.base.int.add a (JuliaLean.base.int.ofBool .i64 b))
    (reduce_first_plus_bool (JuliaLean.base.int.ofBool .i64))
    (reduce_empty_add_bool (fun _ => JuliaLean.base.int.lit .i64 0) (JInt .i64))
  obtain ⟨same, _⟩ := h op true
  exact bool_ne_jint64 same

theorem countInitAgrees_refuted : ¬ CountInitAgrees := by
  intro h
  let zeroF := JuliaLean.base.float.zero_float .f64
  let plusF : JuliaLean.base.float.FV .f64 → Bool → JuliaLean.base.float.FV .f64 := fun x _ => x
  let wordF : JuliaLean.base.float.FV .f64 → JInt .i64 → JuliaLean.base.float.FV .f64 := fun x _ => x
  let firstF : Bool → JuliaLean.base.float.FV .f64 := fun _ => zeroF
  have hr := h.2 plusF wordF firstF zeroF [true, false]
  unfold count count_f _simple_count sum_f mapreduce at hr
  rw [mapfoldl_values] at hr
  unfold _simple_count_bool_array gcPreserve lengthBoolArray sizeofUInt at hr
  dsimp only at hr
  rw [simpleCountChunkLoop, dif_neg (by decide)] at hr
  dsimp only [bind, Except.bind] at hr
  rw [simpleCountTailLoop, dif_pos (by decide)] at hr
  dsimp only [bind, Except.bind] at hr
  cases hr

theorem prodInitWidened_refuted : ¬ ProdInitWidened := by
  intro h
  obtain ⟨w, _, hr⟩ := h .u8 .i8 (by decide) (by decide)
  have hr1 := hr [JuliaLean.base.int.lit .u8 1] (by decide)
  have hr2 := hr [JuliaLean.base.int.lit .u8 1, JuliaLean.base.int.lit .u8 1] (by decide)
  have ht1 : (Except.ok IntTy.u8 : Jl IntTy) = Except.ok w :=
    congrArg (fun r : Jl IntegerAccumulator => r.map Sigma.fst) hr1
  have ht2 : (Except.ok IntTy.u64 : Jl IntTy) = Except.ok w :=
    congrArg (fun r : Jl IntegerAccumulator => r.map Sigma.fst) hr2
  have hw1 : IntTy.u8 = w := Except.ok.inj ht1
  have hw2 : IntTy.u64 = w := Except.ok.inj ht2
  exact (by decide : IntTy.u8 ≠ IntTy.u64) (hw1.trans hw2.symm)
def EmptyDispatchSpec : Prop :=
  ∀ (t : IntTy),
    reduce_empty_add (fun _ => JuliaLean.base.int.lit t 0) (JInt t) =
      .ok (JuliaLean.base.int.lit t 0) ∧
    reduce_empty_mul (fun _ => JuliaLean.base.int.lit t 1) (JInt t) =
      .ok (JuliaLean.base.int.lit t 1) ∧
    reduce_empty_add_bool (fun _ => JuliaLean.base.int.lit .i64 0) (JInt .i64) =
      .ok (JuliaLean.base.int.lit .i64 0) ∧
    reduce_empty_add_sum_signed_small (fun _ => JuliaLean.base.int.lit .i64 0) (JInt .i64) =
      .ok (JuliaLean.base.int.lit .i64 0) ∧
    reduce_empty_add_sum_unsigned_small (fun _ => JuliaLean.base.int.lit .u64 0) (JInt .u64) =
      .ok (JuliaLean.base.int.lit .u64 0) ∧
    reduce_empty_mul_prod_signed_small (fun _ => JuliaLean.base.int.lit .i64 1) (JInt .i64) =
      .ok (JuliaLean.base.int.lit .i64 1) ∧
    reduce_empty_mul_prod_unsigned_small (fun _ => JuliaLean.base.int.lit .u64 1) (JInt .u64) =
      .ok (JuliaLean.base.int.lit .u64 1) ∧
    reduce_empty_mul_char = .ok "" ∧
    reduce_empty_and_bool = .ok true ∧ reduce_empty_or_bool = .ok false ∧
    reduce_empty_and_all = .ok true ∧ reduce_empty_or_any = .ok false ∧
    (∀ x : JInt t,
      (reduce_empty_add (fun _ => JuliaLean.base.int.lit t 0) (JInt t)).map
        (fun e => JuliaLean.base.int.add x e) = .ok x ∧
      (reduce_empty_mul (fun _ => JuliaLean.base.int.lit t 1) (JInt t)).map
        (fun e => JuliaLean.base.int.mul x e) = .ok x)

theorem emptyDispatchSpec_proven : EmptyDispatchSpec := by
  intro t
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro x
  have hz : (JuliaLean.base.int.lit t 0).val = 0 := by cases t <;> decide
  have ho : (JuliaLean.base.int.lit t 1).val = 1 := by cases t <;> decide
  constructor
  · change Except.ok (JuliaLean.base.int.add x (JuliaLean.base.int.lit t 0)) = Except.ok x
    apply congrArg Except.ok
    apply Subtype.ext
    rw [JuliaLean.base.int.add, JuliaLean.Proofs.base.int.add_int_val, hz, Int.add_zero,
      JuliaLean.Proofs.base.int.wrapInt_val]
  · change Except.ok (JuliaLean.base.int.mul x (JuliaLean.base.int.lit t 1)) = Except.ok x
    apply congrArg Except.ok
    apply Subtype.ext
    rw [JuliaLean.base.int.mul, JuliaLean.Proofs.base.int.mul_int_val, ho, Int.mul_one,
      JuliaLean.Proofs.base.int.wrapInt_val]

def FirstDispatchSpec : Prop :=
  (∀ {A : Type} (binary : A → A → A) (x : A),
    mapfoldl (fun _ => .hasEltype) (id : A → A)
      (valueReducer binary (reduce_first binary) _empty_reduce_error) (.values [x]) .initial = .ok x ∧
    mapreduce_number id (valueReducer binary (reduce_first binary) _empty_reduce_error) x = .value x) ∧
  (∀ (b : Bool), (reduce_first_plus_bool (JuliaLean.base.int.ofBool .i64) b).val =
    (if b then 1 else 0)) ∧
  (∀ (t : IntTy) (x : JInt t), t.bits < 64 →
    (t.signed = true →
      (reduce_first_add_sum_signed_small (JuliaLean.base.int.widenTo .i64) x).val = x.val ∧
      (reduce_first_mul_prod_signed_small (JuliaLean.base.int.widenTo .i64) x).val = x.val) ∧
    (t.signed = false →
      (reduce_first_add_sum_unsigned_small (JuliaLean.base.int.widenTo .u64) x).val = x.val ∧
      (reduce_first_mul_prod_unsigned_small (JuliaLean.base.int.widenTo .u64) x).val = x.val)) ∧
  (∀ c : Char, (reduce_first_times_char String.singleton c).toList = [c])


theorem firstDispatchSpec_proven : FirstDispatchSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A binary x
    exact ⟨rfl, rfl⟩
  · intro b
    cases b <;> decide
  · intro t x ht
    constructor
    · intro _
      exact ⟨small_widen_value t .i64 x ht (Or.inl rfl),
        small_widen_value t .i64 x ht (Or.inl rfl)⟩
    · intro hs
      exact ⟨small_widen_value t .u64 x ht (Or.inr ⟨rfl, hs⟩),
        small_widen_value t .u64 x ht (Or.inr ⟨rfl, hs⟩)⟩
  · intro c
    simp [reduce_first_times_char]

def IsArgumentError {A : Type} (result : Jl A) : Prop :=
  ∃ message, result = .error (.argumentError message)

def UnsupportedEmptySpec : Prop :=
  ∀ {Acc Input Output Splat : Type} (op : Reducer Acc Output) (f : Input → Output)
    (binary : Output → Output → Acc) (args : Splat),
    IsArgumentError (_empty_reduce_error : Jl Acc) ∧
    IsArgumentError (reduce_empty_fallback op Output) ∧
    IsArgumentError (mapreduce_empty f op Input) ∧
    IsArgumentError (reduce_empty_union binary args) ∧
    IsArgumentError (mapreduce_empty_union f binary args) ∧
    IsArgumentError (reduce_empty_iter_unknown (Acc := Acc) op) ∧
    IsArgumentError (reduce_empty_iter (fun _ => .unknown) op (.values ([] : List Output))) ∧
    IsArgumentError (mapreduce_empty_iter f op (.values ([] : List Input)) .unknown)

theorem unsupportedEmptySpec_proven : UnsupportedEmptySpec := by
  intro Acc Input Output Splat op f binary args
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact ⟨_, rfl⟩

def MappedEmptySpec : Prop :=
  ∀ (t : IntTy) (abs abs2 : JInt t → JInt t),
    abs (JuliaLean.base.int.lit t 0) = JuliaLean.base.int.lit t 0 →
    abs2 (JuliaLean.base.int.lit t 0) = JuliaLean.base.int.lit t 0 →
    let zero := fun _ : Type => JuliaLean.base.int.lit t 0
    let one := fun _ : Type => JuliaLean.base.int.lit t 1
    let empty := reduce_empty_add_sum (_Input := JInt t) (reduce_empty_add zero) (JInt t)
    let op := valueReducer (add_sum JuliaLean.base.int.add)
      (reduce_first_add_sum (reduce_first (JuliaLean.base.int.add (t := t)))) empty
    empty = .ok (JuliaLean.base.int.lit t 0) ∧
    reduce_empty_mul_prod (_Input := JInt t) (reduce_empty_mul one) (JInt t) =
      .ok (JuliaLean.base.int.lit t 1) ∧
    mapreduce_empty_identity op (JInt t) = .ok (JuliaLean.base.int.lit t 0) ∧
    mapreduce_empty_abs (fun x => .ok (abs x)) op (JInt t) = .ok (JuliaLean.base.int.lit t 0) ∧
    mapreduce_empty_abs2 (fun x => .ok (abs2 x)) op (JInt t) = .ok (JuliaLean.base.int.lit t 0) ∧
    mapreduce_empty_abs_max (fun T => .ok (zero T)) (fun x => .ok (abs x)) (JInt t) =
      .ok (JuliaLean.base.int.lit t 0) ∧
    mapreduce_empty_abs2_max (fun T => .ok (zero T)) (fun x => .ok (abs2 x)) (JInt t) =
      .ok (JuliaLean.base.int.lit t 0) ∧
    reduce_empty_iter_has_eltype op (.values ([] : List (JInt t))) = .ok (JuliaLean.base.int.lit t 0) ∧
    reduce_empty_iter_tuple op (some (JInt t)) = .ok (JuliaLean.base.int.lit t 0)

theorem mappedEmptySpec_proven : MappedEmptySpec := by
  intro t abs abs2 ha ha2
  dsimp only
  refine ⟨rfl, rfl, rfl, ?_, ?_, congrArg Except.ok ha, congrArg Except.ok ha2, rfl, rfl⟩
  · change Except.ok (abs (JuliaLean.base.int.lit t 0)) = Except.ok _
    rw [ha]
  · change Except.ok (abs2 (JuliaLean.base.int.lit t 0)) = Except.ok _
    rw [ha2]

def MappedEmptyCollections : Prop :=
  ∀ {Input Output Acc : Type} (f : Input → Output) (op : Reducer Acc Output),
    let eltype : {I : Type} → JIterator I → EltypeStatus := fun _ => .hasEltype
    let zero := JuliaLean.base.int.lit .i64 0
    let add := valueReducer (add_sum JuliaLean.base.int.add)
      (reduce_first_add_sum (reduce_first (JuliaLean.base.int.add (t := .i64))))
      (reduce_empty_add (fun _ => zero) (JInt .i64))
    let maxFn := JuliaLean.base.operators.max
      (JuliaLean.base.operators.islessReal (JuliaLean.base.int.lt (s := .i64) (t := .i64)))
      JuliaLean.base.essentials.ifelse
    let max := valueReducer maxFn (reduce_first maxFn) _empty_reduce_error true
    let minFn := JuliaLean.base.operators.min
      (JuliaLean.base.operators.islessReal (JuliaLean.base.int.lt (s := .i64) (t := .i64)))
      JuliaLean.base.essentials.ifelse
    mapfoldl eltype f op (.values ([] : List Input)) .initial = _empty_reduce_error ∧
    mapreduce eltype f op (.values ([] : List Input)) .initial = _empty_reduce_error ∧
    maximum_f eltype f op (.values ([] : List Input)) .initial = _empty_reduce_error ∧
    minimum_f eltype f op (.values ([] : List Input)) .initial = _empty_reduce_error ∧
    sum_f eltype AbsFn.abs add (.values ([] : List (JInt .i64))) .initial = .ok zero ∧
    sum_f eltype Abs2Fn.abs2 add (.values ([] : List (JInt .i64))) .initial = .ok zero ∧
    maximum_f eltype AbsFn.abs max (.values ([] : List (JInt .i64))) .initial = .ok zero ∧
    maximum_f eltype Abs2Fn.abs2 max (.values ([] : List (JInt .i64))) .initial = .ok zero ∧
    minimum_f eltype AbsFn.abs
      (valueReducer minFn (reduce_first minFn) _empty_reduce_error)
      (.values ([] : List (JInt .i64))) .initial = _empty_reduce_error ∧
    mapfoldl eltype AbsFn.abs add (.values ([] : List (JInt .i64))) .initial = .ok zero ∧
    mapfoldr eltype (fun itr => .values (iteratorValues itr).reverse)
      Abs2Fn.abs2 add (.values ([] : List (JInt .i64))) .initial = .ok zero

def TypeChangingEmptySum : Prop :=
  ∀ {Arg Output Result : Type} [AbsCallable Arg Output]
    (plus : Result → Output → Result)
    (first : Output → Result) (abs : Arg → Jl Result) (zeroArg : Arg) (zeroResult : Result),
    abs zeroArg = .ok zeroResult →
    let neutral : EmptyReducer Arg := ⟨reduce_empty_add (fun _ => zeroArg) Arg⟩
    let op := { valueReducer (add_sum plus) (reduce_first_add_sum first) _empty_reduce_error with
      mappingAbs := ⟨Arg, neutral, abs, .ok zeroArg⟩ }
    sum_f (fun _ => .hasEltype) AbsFn.abs op (.values ([] : List Arg)) .initial = .ok zeroResult

theorem typeChangingEmptySum_proven : TypeChangingEmptySum := by
  intro Arg Output Result _ plus first abs zeroArg zeroResult hzero
  change abs zeroArg = .ok zeroResult
  exact hzero

theorem mappedEmptyCollections_proven : MappedEmptyCollections := by
  intro Input Output Acc f op
  dsimp only
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  all_goals
    apply congrArg Except.ok
    apply Subtype.ext
    decide
def MappedEmptyDispatchSpec : Prop := MappedEmptyCollections ∧ TypeChangingEmptySum
theorem mappedEmptyDispatchSpec_proven : MappedEmptyDispatchSpec :=
  ⟨mappedEmptyCollections_proven, typeChangingEmptySum_proven⟩

def EmptyMethodSpec : Prop :=
  EmptyDispatchSpec ∧ UnsupportedEmptySpec ∧ MappedEmptySpec ∧ MappedEmptyCollections ∧ TypeChangingEmptySum

theorem emptyMethodSpec_proven : EmptyMethodSpec :=
  ⟨emptyDispatchSpec_proven, unsupportedEmptySpec_proven, mappedEmptySpec_proven,
    mappedEmptyCollections_proven, typeChangingEmptySum_proven⟩

def TupleFoldSpec : Prop :=
  ∀ {A C : Type} (binary : C → A → C) (first : A → C) (empty : Jl C)
    (xs : List A) (init : C)
    (afoldl : Reducer C A → FoldInit C → List A → FoldInit C),
    let op := valueReducer binary first empty
    (∀ state ys, afoldl op state ys = ys.foldl op.step state) →
    _foldl_impl_tuple List.length JIterator.values afoldl _foldl_impl op (.value init) xs =
      .value (xs.foldl binary init) ∧
    _foldl_impl_tuple List.length JIterator.values afoldl _foldl_impl op .initial xs =
      match xs with
      | [] => .initial
      | x :: rest => .value (rest.foldl binary (first x))

theorem tupleFoldSpec_proven : TupleFoldSpec := by
  intro A C binary first empty xs init afoldl
  dsimp only
  intro hlaw
  constructor
  · unfold _foldl_impl_tuple
    split
    · rw [hlaw]
      exact value_fold binary first xs init
    · cases xs with
      | nil => rfl
      | cons x xs =>
        exact value_fold binary first xs (binary init x)
  · unfold _foldl_impl_tuple
    split
    · rw [hlaw]
      cases xs with
      | nil => rfl
      | cons x xs => exact value_fold binary first xs (first x)
    · cases xs with
      | nil => rfl
      | cons x xs => exact value_fold binary first xs (first x)

theorem filter_value_fold {A B C : Type} (predicate : A → Bool) (f : A → B)
    (binary : C → B → C) (first : B → C) (xs : List A) (init : C) :
    xs.foldl (fun (state : FoldInit C) x =>
      if predicate x then match state with
        | .initial => .value (first (f x))
        | .value a => .value (binary a (f x))
      else state) (.value init) =
      .value (((xs.filter predicate).map f).foldl binary init) := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    cases hx : predicate x
    · simpa only [List.foldl_cons, List.filter_cons, hx, Bool.false_eq_true,
        ↓reduceIte] using ih init
    · simpa only [List.foldl_cons, List.filter_cons, hx, ↓reduceIte, List.map_cons] using
        ih (binary init (f x))

def IteratorTransformSpec : Prop :=
  (∀ {A B C : Type} (elementType : {I : Type} → JIterator I → EltypeStatus)
    (predicate : A → Bool) (f : A → B) (binary : C → B → C) (first : B → C)
    (empty : Jl C) (xs : List A) (init : C),
    mapfoldl elementType f (valueReducer binary first empty)
      (.filter predicate (.values xs)) (.value init) =
      .ok (((xs.filter predicate).map f).foldl binary init)) ∧
  (∀ {A B C D : Type} (elementType : {I : Type} → JIterator I → EltypeStatus)
    (g : A → B) (f : B → C) (binary : D → C → D) (first : C → D)
    (empty : Jl D) (xs : List A) (init : D),
    mapfoldl elementType f (valueReducer binary first empty)
      (.generator g (.values xs)) (.value init) =
      .ok ((xs.map (fun x => f (g x))).foldl binary init)) ∧
  (∀ {A B C : Type} (elementType : {I : Type} → JIterator I → EltypeStatus)
    (f : A → B) (binary : C → B → C) (first : B → C)
    (empty : Jl C) (xs : List A) (init : C),
    (_xfadjoint (valueReducer binary first empty)
      (.generator IdentityFn.identity (.values (xs.map f)))).op =
      valueReducer binary first empty ∧
    mapfoldl elementType f (valueReducer binary first empty)
      (.generator IdentityFn.identity (.values xs)) (.value init) =
      .ok ((xs.map f).foldl binary init))

theorem iteratorTransformSpec_proven : IteratorTransformSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B C elementType predicate f binary first empty xs init
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases hx : predicate x <;>
        simp [mapfoldl, mapfoldl_impl, _xfadjoint, _xfadjoint_unwrap_dispatch,
          _xfadjoint_unwrap_generator, _xfadjoint_unwrap_filter, _xfadjoint_unwrap_values,
          MapCallable.isIdentity, MapCallable.apply, mappingRFReducer,
          iteratorValues, bottomRFReducer, bottomRF_initial, bottomRF_apply,
          mappingRF_constructor, mappingRF_apply, filteringRF_apply, valueReducer,
          foldl_impl, _foldl_impl, hx, filter_value_fold, List.foldl_map]
      all_goals
        change (match xs.foldl (fun (state : FoldInit C) x =>
          if predicate x then match state with
            | .initial => .value (first (f x))
            | .value a => .value (binary a (f x))
          else state) (.value _) with
            | .initial => _
            | .value a => (Except.ok a : Jl C)) = _
        rw [filter_value_fold]
        simp only [List.foldl_map]
  · intro A B C D elementType g f binary first empty xs init
    change mapfoldl elementType (fun x => f (g x))
      (valueReducer binary first empty) (.values xs) (.value init) = _
    exact mapfoldl_values elementType (fun x => f (g x)) binary first empty xs init
  · intro A B C elementType f binary first empty xs init
    refine ⟨rfl, ?_⟩
    change mapfoldl elementType f (valueReducer binary first empty) (.values xs) (.value init) = _
    exact mapfoldl_values elementType f binary first empty xs init

def FoldMethodsSpec : Prop := FoldInitSpec ∧ AdapterSpec ∧ TupleFoldSpec ∧ IteratorTransformSpec

theorem foldMethodsSpec_proven : FoldMethodsSpec :=
  ⟨foldInitSpec_proven, adapterSpec_proven, tupleFoldSpec_proven, iteratorTransformSpec_proven⟩

def BoolSumSpec : Prop :=
  ∀ xs : List Bool,
    let op := valueReducer (add_sum_small id (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add)
      (reduce_first_add_sum (reduce_first_plus_bool (JuliaLean.base.int.ofBool .i64)))
      (reduce_empty_add_bool (fun _ => JuliaLean.base.int.lit .i64 0) (JInt .i64))
    sum_bool_array (fun _ => .hasEltype) false op (JuliaLean.base.int.lit .i64 0) (.values xs) .initial =
      .ok (JInt.wrap .i64 (xs.countP id : Int)) ∧
    ∀ init : JInt .i64,
      sum_bool_array (fun _ => .hasEltype) true op (JuliaLean.base.int.lit .i64 0) (.values xs) (.value init) =
      .ok (JInt.wrap .i64 (init.val + (xs.countP id : Int)))

theorem boolSumSpec_proven : BoolSumSpec := by
  intro xs
  dsimp only
  constructor
  · change count (count_f (_simple_count (fun _ => .hasEltype)
      (valueReducer (add_sum_small id (JuliaLean.base.int.ofBool .i64) JuliaLean.base.int.add)
        (reduce_first_add_sum (reduce_first_plus_bool (JuliaLean.base.int.ofBool .i64)))
        (reduce_empty_add_bool (fun _ => JuliaLean.base.int.lit .i64 0) (JInt .i64)))))
      id (.values xs)
      (.value (JuliaLean.base.int.lit .i64 0)) = _
    have h := countPredicateSpec_proven.2 xs (JuliaLean.base.int.lit .i64 0)
    have hz : (JuliaLean.base.int.lit .i64 0).val = 0 := by decide
    simpa only [hz, Int.zero_add] using h
  · intro init
    rw [sum_bool_array, if_pos rfl, reduce, mapreduce, mapfoldl_identity_mapper]
    exact congrArg Except.ok (intBoolFold id xs init)
def NonemptyPublicSpec : Prop :=
  ∀ {Input Output Acc : Type} (elementType : {I : Type} → JIterator I → EltypeStatus)
    (f : Input → Output) (plus times : Acc → Output → Acc)
    (firstPlus firstTimes : Output → Acc) (emptySum emptyProd : Jl Acc)
    (minOp maxOp : Output → Output → Output) (x : Input) (xs : List Input),
    let sop := valueReducer (add_sum plus) (reduce_first_add_sum firstPlus) emptySum
    let pop := valueReducer (mul_prod times) (reduce_first_mul_prod firstTimes) emptyProd
    let min := valueReducer minOp (reduce_first minOp) (_empty_reduce_error : Jl Output)
    let max := valueReducer maxOp (reduce_first maxOp) (_empty_reduce_error : Jl Output)
    let pair := valueReducer (extrema_rf minOp maxOp) (reduce_first (extrema_rf minOp maxOp))
      (_empty_reduce_error : Jl (Output × Output))
    let values := f x :: xs.map f
    sum_f elementType f sop (.values (x :: xs)) .initial =
      .ok ((xs.map f).foldl plus (firstPlus (f x))) ∧
    prod_f elementType f pop (.values (x :: xs)) .initial =
      .ok ((xs.map f).foldl times (firstTimes (f x))) ∧
    sum elementType id sop (.values values) .initial =
      .ok ((xs.map f).foldl plus (firstPlus (f x))) ∧
    prod elementType id pop (.values values) .initial =
      .ok ((xs.map f).foldl times (firstTimes (f x))) ∧
    maximum_f elementType f max (.values (x :: xs)) .initial =
      .ok ((xs.map f).foldl maxOp (f x)) ∧
    minimum_f elementType f min (.values (x :: xs)) .initial =
      .ok ((xs.map f).foldl minOp (f x)) ∧
    maximum elementType id max (.values values) .initial =
      .ok ((xs.map f).foldl maxOp (f x)) ∧
    minimum elementType id min (.values values) .initial =
      .ok ((xs.map f).foldl minOp (f x)) ∧
    extrema_f elementType f pair (.values (x :: xs)) .initial =
      .ok ((xs.map f).foldl minOp (f x), (xs.map f).foldl maxOp (f x)) ∧
    extrema elementType id pair (.values values) .initial =
      .ok ((xs.map f).foldl minOp (f x), (xs.map f).foldl maxOp (f x))

theorem nonemptyPublicSpec_proven : NonemptyPublicSpec := by
  intro Input Output Acc elementType f plus times firstPlus firstTimes emptySum emptyProd minOp maxOp x xs
  dsimp only
  refine ⟨mapfoldl_values_nonempty elementType f plus firstPlus emptySum x xs,
    mapfoldl_values_nonempty elementType f times firstTimes emptyProd x xs, ?_, ?_,
    mapfoldl_values_nonempty elementType f maxOp id _empty_reduce_error x xs,
    mapfoldl_values_nonempty elementType f minOp id _empty_reduce_error x xs, ?_, ?_, ?_, ?_⟩
  · exact mapfoldl_identity_mapper_nonempty elementType plus firstPlus emptySum (f x) (xs.map f)
  · exact mapfoldl_identity_mapper_nonempty elementType times firstTimes emptyProd (f x) (xs.map f)
  · exact mapfoldl_identity_mapper_nonempty elementType maxOp id _empty_reduce_error (f x) (xs.map f)
  · exact mapfoldl_identity_mapper_nonempty elementType minOp id _empty_reduce_error (f x) (xs.map f)
  · unfold extrema_f mapreduce
    rw [mapfoldl_values_nonempty]
    change (Except.ok ((xs.map (fun x => (f x, f x))).foldl
      (extrema_rf minOp maxOp) (f x, f x)) : Jl (Output × Output)) = _
    simpa only [List.map_map, Function.comp_def] using
      congrArg Except.ok (extrema_fold minOp maxOp (xs.map f) (f x, f x))
  · unfold extrema extrema_f mapreduce
    rw [mapfoldl_values_nonempty]
    change (Except.ok (((xs.map f).map (fun x => (x, x))).foldl
      (extrema_rf minOp maxOp) (f x, f x)) : Jl (Output × Output)) = _
    exact congrArg Except.ok (extrema_fold minOp maxOp (xs.map f) (f x, f x))

def MultiMapreduceSpec : Prop :=
  ∀ {I IS F Input Output : Type} (elementType : {T : Type} → JIterator T → EltypeStatus)
    (generator : F → I → IS → JIterator Output) (zipValues : I → IS → List Input)
    (applyTuple : F → Input → Output) (f : F) (binary : Output → Output → Output)
    (first : Output → Output) (empty : Jl Output)
    (itr : I) (itrs : IS) (init : Output),
    generator f itr itrs =
      .generator (applyTuple f) (.values (zipValues itr itrs)) →
    mapreduce_multi elementType generator f (valueReducer binary first empty)
      itr itrs (.value init) =
      .ok (((zipValues itr itrs).map (applyTuple f)).foldl binary init) ∧
    (∀ x xs, zipValues itr itrs = x :: xs →
      mapreduce_multi elementType generator f (valueReducer binary first empty)
        itr itrs .initial =
        .ok ((xs.map (applyTuple f)).foldl binary (first (applyTuple f x)))) ∧
    (zipValues itr itrs = [] → elementType (.values ([] : List Input)) = .hasEltype →
      mapreduce_multi elementType generator f (valueReducer binary first _empty_reduce_error)
        itr itrs .initial = _empty_reduce_error)

theorem multiMapreduceSpec_proven : MultiMapreduceSpec := by
  intro I IS F Input Output elementType generator zipValues applyTuple f binary first empty itr itrs init hgen
  unfold mapreduce_multi reduce mapreduce
  rw [hgen]
  refine ⟨?_, ?_, ?_⟩
  · change mapfoldl elementType (applyTuple f)
      (valueReducer binary first empty)
      (.values (zipValues itr itrs)) (.value init) = _
    exact mapfoldl_values elementType (applyTuple f) binary first
      empty (zipValues itr itrs) init
  · intro x xs hzip
    rw [hzip]
    change mapfoldl elementType (applyTuple f)
      (valueReducer binary first empty)
      (.values (x :: xs)) .initial = _
    exact mapfoldl_values_nonempty elementType (applyTuple f) binary first empty x xs
  · intro hzip heltype
    rw [hzip]
    change foldl_impl elementType
      (mappingRFReducer (mappingRF_constructor (applyTuple f)
        (bottomRFReducer (valueReducer binary first _empty_reduce_error))))
      .initial (.values ([] : List Input)) = _empty_reduce_error
    unfold foldl_impl _foldl_impl reduce_empty_iter reduce_empty_iter_eltype
    simp [iteratorValues, heltype, reduce_empty_iter_has_eltype, reduce_empty,
      EmptyDispatch.empty, mappingRFReducer, reduce_empty_mapping,
      MapreduceEmptyDispatch.dispatch, MapCallable.mappingKind, mapreduce_empty]

def NoInitFoldSpec : Prop :=
  ∀ {A B : Type} (elementType : {I : Type} → JIterator I → EltypeStatus)
    (f : A → B) (binary : B → B → B) (first : B → B) (empty : Jl B) (x : A) (xs : List A),
    let op := valueReducer binary first empty
    mapfoldl elementType f op (.values (x :: xs)) .initial =
      .ok ((xs.map f).foldl binary (first (f x))) ∧
    mapreduce elementType f op (.values (x :: xs)) .initial =
      .ok ((xs.map f).foldl binary (first (f x))) ∧
    foldl elementType id op (.values (f x :: xs.map f)) .initial =
      .ok ((xs.map f).foldl binary (first (f x))) ∧
    reduce elementType id op (.values (f x :: xs.map f)) .initial =
      .ok ((xs.map f).foldl binary (first (f x))) ∧
    mapfoldr elementType (fun itr => .values (iteratorValues itr).reverse)
      f op (.values (xs ++ [x])) .initial =
      .ok ((xs.map f).foldr binary (first (f x))) ∧
    foldr elementType (fun itr => .values (iteratorValues itr).reverse)
      id op (.values (xs.map f ++ [f x])) .initial =
      .ok ((xs.map f).foldr binary (first (f x)))

theorem noInitFoldSpec_proven : NoInitFoldSpec := by
  intro A B elementType f binary first empty x xs
  dsimp only
  refine ⟨mapfoldl_values_nonempty elementType f binary first empty x xs,
    mapfoldl_values_nonempty elementType f binary first empty x xs, ?_, ?_, ?_, ?_⟩
  · exact mapfoldl_identity_mapper_nonempty elementType binary first empty (f x) (xs.map f)
  · exact mapfoldl_identity_mapper_nonempty elementType binary first empty (f x) (xs.map f)
  · change mapfoldl elementType f (valueReducer (fun a b => binary b a) first empty)
      (.values (xs ++ [x]).reverse) .initial = _
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append]
    rw [mapfoldl_values_nonempty]
    simp only [List.map_reverse, List.foldl_reverse]
  · change mapfoldl elementType (IdentityMapper.mk id) (valueReducer (fun a b => binary b a) first empty)
      (.values (xs.map f ++ [f x]).reverse) .initial = _
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append]
    rw [mapfoldl_identity_mapper_nonempty]
    simp only [List.foldl_reverse]
def FindAllSpec : Prop := FindExtremaSpec ∧ EmptyReductions
theorem findAllSpec_proven : FindAllSpec := ⟨findExtremaSpec_proven, emptyReductions_proven⟩

def FoldAllSpec : Prop := FoldInitSpec ∧ GenericReductionContents
theorem foldAllSpec_proven : FoldAllSpec := ⟨foldInitSpec_proven, genericReductionContents_proven⟩

def EmptyAllSpec : Prop := EmptyReductions ∧ EmptyMethodSpec
theorem emptyAllSpec_proven : EmptyAllSpec := ⟨emptyReductions_proven, emptyMethodSpec_proven⟩

def FirstMethodsSpec : Prop := SingleElementResults ∧ FirstDispatchSpec
theorem firstMethodsSpec_proven : FirstMethodsSpec :=
  ⟨singleElementResults_proven, firstDispatchSpec_proven⟩

def PairwiseMethodsSpec : Prop := PairwiseFoldl ∧ ArrayMethodsSpec
theorem pairwiseMethodsSpec_proven : PairwiseMethodsSpec :=
  ⟨pairwiseFoldl_proven, arrayMethodsSpec_proven⟩

def FoldAllMethodsSpec : Prop :=
  FoldMethodsSpec ∧ GenericReductionContents ∧ MultiMapreduceSpec ∧ NoInitFoldSpec
theorem foldAllMethodsSpec_proven : FoldAllMethodsSpec :=
  ⟨foldMethodsSpec_proven, genericReductionContents_proven, multiMapreduceSpec_proven, noInitFoldSpec_proven⟩

def PublicMethodsSpec : Prop := SumProdContents ∧ NonemptyPublicSpec
theorem publicMethodsSpec_proven : PublicMethodsSpec :=
  ⟨sumProdContents_proven, nonemptyPublicSpec_proven⟩

def UnmappedMethodsSpec : Prop := UnmappedSumProd ∧ BoolSumSpec
theorem unmappedMethodsSpec_proven : UnmappedMethodsSpec :=
  ⟨unmappedSumProd_proven, boolSumSpec_proven⟩

def ExtremaMethodsSpec : Prop := ExtremaContents ∧ NonemptyPublicSpec
theorem extremaMethodsSpec_proven : ExtremaMethodsSpec :=
  ⟨extremaContents_proven, nonemptyPublicSpec_proven⟩

def SearchMethodsSpec : Prop := FindAllSpec ∧ MappedSearchSpec
theorem searchMethodsSpec_proven : SearchMethodsSpec :=
  ⟨findAllSpec_proven, mappedSearchSpec_proven⟩

/-! Nothing to promise:

* `add_sum@16`: pure forwarding to the external `+` method; behavior belongs to that callee.
* `mul_prod@27`: pure forwarding to the external `*` method; behavior belongs to that callee.
* `reduce_first@415` and `reduce_first@418`: forward to the selected `+` or `*` first-element method, whose widening behavior is specified separately.
* `reduce_first@421` and `reduce_first@422`: forward a single value to the external `vcat` or `hcat` constructor; the returned shape belongs to that constructor.
* `reduce_first@423`: unwraps `FlipArgs` and forwards to its underlying first-element method.
* `reduce_empty@358`, `reduce_empty@359`, `reduce_empty@360`, `reduce_empty@361` and `reduce_empty@362`: unwrap reducer adapters and forward to their selected empty method; identity and error behavior is specified for that method.
* `pairwise_blocksize@311` and `pairwise_blocksize@314`: internal block-size choices affect performance; the documented result permits different reduction groupings.
* `_foldl_impl@1120`: generated range specializations reuse maximum, minimum or sum and add no independent public behavior.
* `_mapreduce@437`: dispatches to the method selected by the external IndexStyle trait.
* `_mapreduce@464`: forwards Cartesian traversal to mapfoldl; its fold behavior is specified there.
-/

/-! Method -> property table (Julia source line numbers are from the pinned source):

* `add_sum@16` -> nothing to promise: pure forwarding to +.
* `add_sum@17` -> reduce-model-operators, reduce-boolean-small-widen.
* `add_sum@18` -> reduce-model-operators.
* `add_sum@19` -> reduce-model-operators, reduce-count-init-float.
* `mul_prod@27` -> nothing to promise: pure forwarding to *.
* `mul_prod@28` -> reduce-model-operators.
* `mul_prod@29` -> reduce-model-operators.
* `mul_prod@30` -> reduce-model-operators.
* `and_all@32` -> reduce-boolean-typecheck.
* `or_any@33` -> reduce-boolean-typecheck.
* `and_all@35` -> reduce-model-boolean.
* `or_any@36` -> reduce-model-boolean.
* `mapfoldl_impl@40` -> reduce-fold-init, reduce-model-folds.
* `foldl_impl@45` -> reduce-fold-init, reduce-model-folds.
* `_foldl_impl@51` -> reduce-fold-init, reduce-model-folds.
* `_foldl_impl@65` -> reduce-fold-init, reduce-model-folds.
* `(op::BottomRF)@83` -> reduce-fold-init, reduce-model-folds.
* `(op::BottomRF)@84` -> reduce-fold-init, reduce-model-folds.
* `MappingRF@94` -> reduce-fold-init, reduce-model-folds.
* `MappingRF@95` -> reduce-fold-init, reduce-model-folds.
* `(op::MappingRF)@98` -> reduce-fold-init, reduce-model-folds.
* `(op::FilteringRF)@110` -> reduce-fold-init, reduce-model-folds.
* `(op::FlatteningRF)@122` -> reduce-fold-init, reduce-model-folds.
* `_xfadjoint@146` -> reduce-fold-init, reduce-model-folds.
* `_xfadjoint_unwrap@151` -> reduce-fold-init, reduce-model-folds.
* `_xfadjoint_unwrap@152` -> reduce-fold-init, reduce-model-folds.
* `_xfadjoint_unwrap@157` -> reduce-fold-init, reduce-model-folds.
* `_xfadjoint_unwrap@161` -> reduce-fold-init, reduce-model-folds.
* `mapfoldl@173` -> reduce-fold-init, reduce-model-folds.
* `foldl@196` -> reduce-fold-init, reduce-model-folds.
* `mapfoldr_impl@200` -> reduce-fold-init, reduce-model-folds.
* `_reverse_iter@206` -> reduce-fold-init, reduce-model-folds.
* `_reverse_iter@207` -> reduce-fold-init, reduce-model-folds.
* `(f::FlipArgs)@213` -> reduce-fold-init, reduce-model-folds.
* `mapfoldr@222` -> reduce-fold-init, reduce-model-folds.
* `foldr@241` -> reduce-fold-init, reduce-model-folds.
* `mapreduce_impl@252` -> reduce-pairwise-foldl, reduce-model-pairwise.
* `mapreduce_impl@276` -> reduce-pairwise-foldl, reduce-model-pairwise.
* `mapreduce@306` -> reduce-model-folds.
* `mapreduce@307` -> reduce-model-folds.
* `pairwise_blocksize@311` -> nothing to promise: internal performance specialization.
* `pairwise_blocksize@314` -> nothing to promise: internal performance specialization.
* `_empty_reduce_error@318` -> reduce-empty, reduce-model-empty.
* `reduce_empty@319` -> reduce-empty, reduce-model-empty.
* `mapreduce_empty@320` -> reduce-empty, reduce-model-empty.
* `reduce_empty@321` -> reduce-empty, reduce-model-empty.
* `mapreduce_empty@322` -> reduce-empty, reduce-model-empty.
* `reduce_empty@342` -> reduce-empty, reduce-model-empty.
* `reduce_empty@343` -> reduce-empty, reduce-model-empty.
* `reduce_empty@344` -> reduce-empty, reduce-model-empty.
* `reduce_empty@345` -> reduce-empty, reduce-model-empty.
* `reduce_empty@346` -> reduce-empty, reduce-model-empty.
* `reduce_empty@347` -> reduce-empty, reduce-model-empty.
* `reduce_empty@348` -> reduce-empty, reduce-model-empty.
* `reduce_empty@349` -> reduce-empty, reduce-model-empty.
* `reduce_empty@351` -> reduce-empty, reduce-model-empty.
* `reduce_empty@352` -> reduce-empty, reduce-model-empty.
* `reduce_empty@353` -> reduce-empty, reduce-model-empty.
* `reduce_empty@354` -> reduce-empty, reduce-model-empty.
* `reduce_empty@355` -> reduce-empty, reduce-model-empty.
* `reduce_empty@356` -> reduce-empty, reduce-model-empty.
* `reduce_empty@358` -> nothing to promise: unwraps BottomRF.
* `reduce_empty@359` -> nothing to promise: unwraps MappingRF.
* `reduce_empty@360` -> nothing to promise: unwraps FilteringRF.
* `reduce_empty@361` -> nothing to promise: unwraps FlatteningRF.
* `reduce_empty@362` -> nothing to promise: unwraps FlipArgs.
* `mapreduce_empty@371` -> reduce-empty, reduce-model-empty.
* `mapreduce_empty@372` -> reduce-empty, reduce-model-empty.
* `mapreduce_empty@373` -> reduce-empty, reduce-model-empty.
* `mapreduce_empty@375` -> reduce-empty, reduce-model-empty.
* `mapreduce_empty@376` -> reduce-empty, reduce-model-empty.
* `mapreduce_empty_iter@379` -> reduce-model-empty, reduce-mapped-empty-dispatch.
* `reduce_empty_iter@382` -> reduce-empty, reduce-model-empty.
* `reduce_empty_iter@383` -> reduce-empty, reduce-model-empty.
* `reduce_empty_iter@384` -> reduce-empty, reduce-model-empty.
* `reduce_empty_iter@391` -> reduce-empty, reduce-model-empty.
* `reduce_empty_iter@393` -> reduce-empty, reduce-model-empty.
* `reduce_first@411` -> reduce-model-first.
* `reduce_first@412` -> reduce-model-first.
* `reduce_first@413` -> reduce-model-first.
* `reduce_first@415` -> nothing to promise: forwards to the + first-element method.
* `reduce_first@416` -> reduce-model-first.
* `reduce_first@417` -> reduce-model-first.
* `reduce_first@418` -> nothing to promise: forwards to the * first-element method.
* `reduce_first@419` -> reduce-model-first.
* `reduce_first@420` -> reduce-model-first.
* `reduce_first@421` -> nothing to promise: forwards to vcat.
* `reduce_first@422` -> nothing to promise: forwards to hcat.
* `reduce_first@423` -> nothing to promise: unwraps FlipArgs.
* `mapreduce_first@435` -> reduce-model-first, reduce-model-pairwise.
* `_mapreduce@437` -> nothing to promise: trait-based dispatch.
* `_mapreduce@439` -> reduce-model-pairwise, memsafety-reduce-linear.
* `mapreduce@462` -> reduce-model-first.
* `_mapreduce@464` -> nothing to promise: delegates to mapfoldl.
* `reduce@501` -> reduce-model-folds.
* `reduce@503` -> reducecov-reduce-number.
* `sum@546` -> reduce-model-public, reduce-sum-init-widened.
* `sum@575` -> reduce-model-unmapped-sum-prod, reduce-sum-init-widened.
* `sum@576` -> reduce-model-unmapped-sum-prod, reduce-model-count.
* `prod@602` -> reduce-model-public, reduce-prod-init-mixed-sign.
* `prod@631` -> reduce-model-unmapped-sum-prod, reduce-prod-init-mixed-sign.
* `maximum@659` -> reduce-model-extrema, reduce-empty.
* `minimum@686` -> reduce-model-extrema, reduce-empty.
* `maximum@718` -> reduce-model-extrema, reduce-empty.
* `minimum@750` -> reduce-model-extrema, reduce-empty.
* `extrema@779` -> reduce-model-extrema, reduce-empty.
* `extrema@809` -> reduce-model-extrema, reduce-empty.
* `ExtremaMap@816` -> reduce-model-extrema, reduce-empty.
* `(f::ExtremaMap)@817` -> reduce-model-extrema, reduce-empty.
* `_extrema_rf@819` -> reduce-model-extrema, reduce-empty.
* `findmax@854` -> arrayops-find-extrema, reduce-findmax-agree, reduce-model-search.
* `_findmax@855` -> arrayops-find-extrema, reduce-findmax-agree, reduce-model-search.
* `_rf_findmax@856` -> arrayops-find-extrema, reduce-findmax-agree, reduce-model-search.
* `findmax@883` -> arrayops-find-extrema, reduce-findmax-agree, reduce-model-search.
* `_findmax@884` -> arrayops-find-extrema, reduce-findmax-agree, reduce-model-search.
* `findmin@920` -> arrayops-find-extrema, reduce-findmax-agree, reduce-model-search.
* `_findmin@921` -> arrayops-find-extrema, reduce-findmax-agree, reduce-model-search.
* `_rf_findmin@922` -> arrayops-find-extrema, reduce-findmax-agree, reduce-model-search.
* `findmin@949` -> arrayops-find-extrema, reduce-findmax-agree, reduce-model-search.
* `_findmin@950` -> arrayops-find-extrema, reduce-findmax-agree, reduce-model-search.
* `argmax@976` -> arrayops-find-extrema, reduce-findmax-agree, reduce-model-search.
* `argmax@1005` -> arrayops-find-extrema, reduce-findmax-agree, reduce-model-search.
* `argmin@1034` -> arrayops-find-extrema, reduce-findmax-agree, reduce-model-search.
* `argmin@1063` -> arrayops-find-extrema, reduce-findmax-agree, reduce-model-search.
* `_bool@1067` -> reduce-boolean-typecheck, reduce-model-count.
* `count@1094` -> reduce-count-init-float, memsafety-reduce-linear, reduce-model-count.
* `count@1096` -> reduce-count-init-float, memsafety-reduce-linear, reduce-model-count.
* `_simple_count@1098` -> reduce-count-init-float, memsafety-reduce-linear, reduce-model-count.
* `_simple_count@1100` -> reduce-count-init-float, memsafety-reduce-linear, reduce-bool-array-count.
* `_foldl_impl@1120` -> nothing to promise: internal performance specialization.
-/

end JuliaLean.Proofs.base.reduce

namespace JuliaLean.ChatGPT.Batch4.Group14
open JuliaLean.Proofs.base.reduce

theorem floatEquivalent_of_no_less (a b : FloatValue)
    (hab : JuliaLean.base.float.isless_IEEEFloat a b = false)
    (hba : JuliaLean.base.float.isless_IEEEFloat b a = false) :
    floatEquivalent a b := by
  have he := (JuliaLean.Proofs.base.float.islessPartition_proven .f64 a b).2.1.mpr ⟨hab, hba⟩
  rw [JuliaLean.Proofs.base.float.isequal_IEEEFloat_eq] at he
  simp only [JuliaLean.Promotion.Fl.isequal, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq] at he
  rcases he with hn | hb
  · exact Or.inr hn
  · exact Or.inl (JuliaLean.Promotion.Fl.ext_toBits hb)

theorem floatMax_selection (a b : FloatValue) :
    floatEquivalent (floatMax a b)
      (if JuliaLean.base.float.isless_IEEEFloat a b then b else a) := by
  unfold floatMax JuliaLean.base.operators.max JuliaLean.base.essentials.ifelse
  cases hab : JuliaLean.base.float.isless_IEEEFloat a b <;>
    cases hba : JuliaLean.base.float.isless_IEEEFloat b a
  · exact floatEquivalent_of_no_less b a hba hab
  · exact Or.inl rfl
  · exact Or.inl rfl
  · have h := floatLess_order.trans a b a hab hba
    rw [floatLess_order.irrefl a] at h
    cases h

/-- reduce-findmax-agree. -/
theorem ReduceFindmaxAgree_proven : JuliaLean.Proofs.base.reduce.FindmaxAgreementSpec := by
  refine ⟨findmaxAgree_proven, ?_⟩
  intro K elementType pairs xs entries hp he hn
  exact findmaxAgree_proven elementType pairs
    JuliaLean.base.float.isless_IEEEFloat floatGreater floatMax floatMin floatEquivalent xs entries
    floatLess_order floatGreater_order floatEquivalent_equivalence
    (fun a b c d hab hcd => (floatOrder_compatible a b c d hab hcd).1)
    (fun a b c d hab hcd => (floatOrder_compatible a b c d hab hcd).2)
    floatMax_selection floatMin_law hp he hn

end JuliaLean.ChatGPT.Batch4.Group14

namespace JuliaLean.Proofs.base.reduce

open JuliaLean.Registry

def entries : List JuliaLean.Registry.Entry := [
  { id := "reduce-mapped-empty-dispatch", juliaFile := "base/reduce.jl",
    juliaFns := ["mapfoldl", "mapreduce", "sum(abs, a)", "sum(abs2, a)", "maximum", "minimum",
      "mapreduce_empty", "mapreduce_empty_iter", "reduce_empty(::MappingRF, T)"],
    statement := "Empty mapped reductions dispatch on identity, abs, abs2 or other; Int abs/abs2 sums and maxima return zero, unsupported mappings throw, and mappings may change the neutral element's type.",
    source := "base/reduce.jl:359,371-380 (mapped empty methods)", status := .proven,
    prop := ``MappedEmptyDispatchSpec, thm := some ``mappedEmptyDispatchSpec_proven },
  { id := "arrayops-find-extrema", juliaFile := "base/reduce.jl",
    juliaFns := ["findmax(itr)", "findmin(itr)", "argmax(itr)", "argmin(itr)"],
    statement := "For Float64 vectors findmax and findmin return the first maximal or minimal element with its index; argmax and argmin return that index. Empty input throws ArgumentError.",
    source := "base/reduce.jl:855-879, 921-945 (docstrings)", status := .proven,
    prop := ``FindAllSpec, thm := some ``findAllSpec_proven },
  { id := "reduce-pairwise-foldl", juliaFile := "base/reduce.jl",
    juliaFns := ["reduce(op, A)", "mapreduce(f, op, A)", "mapreduce_impl", "_mapreduce"],
    statement := "For associative operators, pairwise mapreduce equals the left fold over mapped array elements for every block size.",
    source := "base/reduce.jl:480-483 (reduce docstring: associativity is implementation dependent)", status := .proven,
    prop := ``PairwiseFoldl, thm := some ``pairwiseFoldl_proven },
  { id := "reduce-findmax-agree", juliaFile := "base/reduce.jl",
    juliaFns := ["findmax(itr)", "findmin(itr)", "argmax(itr)", "argmin(itr)", "maximum(itr)", "minimum(itr)"],
    statement := "For a nonempty Vector{Float64}, findmax and findmin return values equal to maximum and minimum, with an index holding that value.",
    source := "base/reduce.jl:855-878, 921-944 (findmax/findmin docstrings)", status := .proven,
    prop := ``FindmaxAgreementSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.ReduceFindmaxAgree_proven },
  { id := "reduce-fold-init", juliaFile := "base/reduce.jl",
    juliaFns := ["foldl(op, itr; init)", "foldr(op, itr; init)", "mapfoldl", "mapfoldr"],
    statement := "foldl and foldr with init are left and right folds starting from init, and use init exactly once.",
    source := "base/reduce.jl:166-241 (mapfoldl/foldl/mapfoldr/foldr docstrings)", status := .proven,
    prop := ``FoldAllSpec, thm := some ``foldAllSpec_proven },
  { id := "reduce-sum-init-widened", juliaFile := "base/reduce.jl",
    juliaFns := ["sum(v; init)", "add_sum"],
    statement := "sum of small signed and unsigned integers uses Int or UInt for the reduction result, including when init is provided.",
    source := "base/reduce.jl:546-557 (sum docstring: Int/UInt for small integers)", status := .proven,
    prop := ``SumInitWidened, thm := some ``sumInitWidened_proven },
  { id := "reduce-flatten-foldl", juliaFile := "base/reduce.jl",
    juliaFns := ["foldl(op, ::Iterators.Flatten)", "FlatteningRF"],
    statement := "foldl over Iterators.flatten(vs), with init, equals the left fold over the concatenated elements.",
    source := "base/reduce.jl:112-125 (FlatteningRF docstring), 175-182 (foldl)", status := .proven,
    prop := ``FlattenFoldl, thm := some ``flattenFoldl_proven },
  { id := "reduce-flatten-sum-empty", juliaFile := "base/reduce.jl",
    juliaFns := ["sum(::Iterators.Flatten)", "FlatteningRF", "reduce_empty"],
    statement := "sum(Iterators.flatten(vs)) equals sum(collect(Iterators.flatten(vs))) for vectors of Vector{Int}.",
    source := "base/reduce.jl:470-472 (reduce docstring: init is unnecessary when Julia can determine the neutral element of +)", status := .proven,
    prop := ``FlattenSumAgrees, thm := some ``flattenSumAgrees_proven },
  { id := "reduce-empty", juliaFile := "base/reduce.jl",
    juliaFns := ["maximum", "minimum", "extrema", "findmax", "findmin", "sum", "prod"],
    statement := "Empty maximum, minimum, extrema, findmax and findmin throw ArgumentError; sum and product with init return init, and integer sum/product use their neutral elements.",
    source := "base/reduce.jl:317-356, 686-747 (empty reductions and maximum/minimum docstrings)", status := .proven,
    prop := ``EmptyAllSpec, thm := some ``emptyAllSpec_proven },
  { id := "reduce-count-init-float", juliaFile := "base/reduce.jl",
    juliaFns := ["count(A::Array{Bool}; init)", "_simple_count"],
    statement := "count(A; init) for integer or Float64 init agrees with counting the same Bool values as an iterator.",
    source := "base/reduce.jl:1067-1072 (count docstring: init determines the starting value and output type)", status := .refuted,
    prop := ``CountInitAgrees, thm := some ``countInitAgrees_refuted,
    issue := "#59869 (related)", notes := "Float64 init reaches an unavailable rem(value, Type) method; reproduced on release and target nightly." },
  { id := "reduce-prod-init-mixed-sign", juliaFile := "base/reduce.jl",
    juliaFns := ["prod(A; init)", "mul_prod"],
    statement := "For small integer element and init types, prod(A; init=one(S)) has a consistent return type (Int/UInt for same signedness, or a common promoted type) and wraps the exact product in that type.",
    source := "base/reduce.jl:578-590 (prod docstring: Int/UInt for small integers, or a common promoted return type)", status := .refuted,
    prop := ``ProdInitWidened, thm := some ``prodInitWidened_refuted,
    issue := "#58374 (related)", notes := "Mixed-sign small integers return UInt8 for length 1 and UInt64 for length 2, and overflow in UInt8 before widening; reproduced on release and target nightly." },
  { id := "reducecov-reduce-number", juliaFile := "base/reduce.jl",
    juliaFns := ["reduce(::Any, ::Number)"],
    statement := "A single Number reduction equals reduce_first(op, x), as a one-element iterator reduction does.",
    source := "base/reduce.jl:503", status := .refuted,
    prop := ``ReduceNumberFirst, thm := some ``reduceNumberFirst_refuted,
    issue := "none found (queries: reduce number reduce_first; reduce(+, true); reduce Number scalar)",
    notes := "Scalar reduce preserves Bool, while the first-element plus dispatch returns Int; reproduced on release and target nightly." },
  { id := "reduce-boolean-small-widen", juliaFile := "base/reduce.jl",
    juliaFns := ["add_sum(::Union{Bool,BitIntegerSmall}, ::Union{Bool,BitIntegerSmall})"],
    statement := "Bool values and small integers use machine Int addition, preserving each Bool as zero or one before the addition.",
    source := "base/reduce.jl:17 (small-integer widening)", status := .proven,
    prop := ``BoolSmallSumSpec, thm := some ``boolSmallSumSpec_proven },
  { id := "reduce-model-operators", juliaFile := "base/reduce.jl",
    juliaFns := ["add_sum", "mul_prod"],
    statement := "Small signed sum and product operands widen to Int, small unsigned operands widen to UInt, and Real sum/product methods assert that custom Real operations return a Real.",
    source := "base/reduce.jl:16-30", status := .proven,
    prop := ``ReductionOperatorSemantics, thm := some ``reductionOperatorSemantics_proven },
  { id := "reduce-model-folds", juliaFile := "base/reduce.jl",
    juliaFns := ["foldl", "foldr", "mapfoldl", "mapfoldr", "reduce", "mapreduce", "mapfoldl_impl", "foldl_impl", "_foldl_impl", "BottomRF", "MappingRF", "FilteringRF", "FlatteningRF", "_xfadjoint", "_xfadjoint_unwrap"],
    statement := "Mapped folds use the initial value once, preserve left-to-right order, and fold nested iterators without changing their element order.",
    source := "base/reduce.jl:40-164,173-241", status := .proven,
    prop := ``FoldAllMethodsSpec, thm := some ``foldAllMethodsSpec_proven },
  { id := "reduce-model-empty", juliaFile := "base/reduce.jl",
    juliaFns := ["_empty_reduce_error", "reduce_empty", "mapreduce_empty", "mapreduce_empty_iter", "reduce_empty_iter"],
    statement := "Empty reductions return the documented identity when it is unambiguous and throw ArgumentError when it is not.",
    source := "base/reduce.jl:318-395", status := .proven,
    prop := ``EmptyAllSpec, thm := some ``emptyAllSpec_proven },
  { id := "reduce-model-first", juliaFile := "base/reduce.jl",
    juliaFns := ["reduce_first", "mapreduce_first", "mapreduce(f, op, a::Number)"],
    statement := "A one-element mapped fold returns the operator's single-element reduction result.",
    source := "base/reduce.jl:397-435", status := .proven,
    prop := ``FirstMethodsSpec, thm := some ``firstMethodsSpec_proven },
  { id := "reduce-model-public", juliaFile := "base/reduce.jl",
    juliaFns := ["sum(f, a; kw...)", "prod(f, a; kw...)", "sum", "prod", "maximum", "minimum", "extrema"],
    statement := "Mapped sum and product reduce every mapped value using the typed sum and product operators.",
    source := "base/reduce.jl:543-819 (public reduction docstrings)", status := .proven,
    prop := ``PublicMethodsSpec, thm := some ``publicMethodsSpec_proven },
  { id := "reduce-model-unmapped-sum-prod", juliaFile := "base/reduce.jl",
    juliaFns := ["sum(a; kw...)", "sum(a::AbstractArray{Bool}; kw...)", "prod(a; kw...)"],
    statement := "Unmapped sum and product reduce the original values with their corresponding reduction operator.",
    source := "base/reduce.jl:572-631", status := .proven,
    prop := ``UnmappedMethodsSpec, thm := some ``unmappedMethodsSpec_proven },
  { id := "reduce-model-extrema", juliaFile := "base/reduce.jl",
    juliaFns := ["maximum", "minimum", "extrema", "ExtremaMap", "_extrema_rf"],
    statement := "Maximum and minimum return the corresponding extrema of mapped values, and extrema returns both in one pass.",
    source := "base/reduce.jl:640-819 (maximum/minimum/extrema docstrings)", status := .proven,
    prop := ``ExtremaMethodsSpec, thm := some ``extremaMethodsSpec_proven },
  { id := "reduce-model-search", juliaFile := "base/reduce.jl",
    juliaFns := ["findmax", "_findmax", "_rf_findmax", "findmin", "_findmin", "_rf_findmin", "argmax", "argmin"],
    statement := "Extrema searches return a maximal or minimal value and the first matching key; argmax and argmin return that key.",
    source := "base/reduce.jl:820-1063 (findmax/findmin/argmax/argmin docstrings)", status := .proven,
    prop := ``SearchMethodsSpec, thm := some ``searchMethodsSpec_proven },
  { id := "reduce-model-count", juliaFile := "base/reduce.jl",
    juliaFns := ["_bool", "count(itr; init::Int)", "count(f, itr; init::Int)", "_simple_count(pred, itr, init::Int)"],
    statement := "With an Int init, predicate count returns init plus the number of true predicate values, wrapping in Int.",
    source := "base/reduce.jl:1067-1098 (count docstring and generic implementation)", status := .proven,
    prop := ``CountPredicateSpec, thm := some ``countPredicateSpec_proven }
]

end JuliaLean.Proofs.base.reduce



namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

/-! These observers are specifications, not additional Julia methods. They
instrument arbitrary dispatch leaves without constraining those leaves. The
mutable world is retained on errors. Option represents divergent callbacks;
there is no final observation for a divergent execution. Contracts state call cardinality and
result/state provenance without replaying the model as an expected result. -/

/-- A complete observation of one selected binary call, including failure and state.
Julia source: base/reduce.jl:16,27 (the forwarded call). -/
structure BinaryObservation (A B Result World Error : Type) where
  left : A
  right : B
  before : World
  result : Except Error Result
  after : World

/-- Instrument any selected operation, retaining its effects and errors.
Julia source: base/reduce.jl:16,27. -/
def observeBinary {A B Result World Error : Type}
    (binary : A → B → World → Option (Except Error Result × World)) (x : A) (y : B) :
    ExceptT Error (StateT (World × List (BinaryObservation A B Result World Error)) Option) Result :=
  ExceptT.mk fun state => do
    let answer ← binary x y state.1
    pure (answer.1, (answer.2, state.2 ++ [⟨x, y, state.1, answer.1, answer.2⟩]))

/-- The forwarding wrapper introduces no extra call, reorders no argument, and
returns precisely an observed result with its final world, even on failure.
Divergence has no terminating observation and is included without a termination premise.
Julia source: base/reduce.jl:16,27. -/
def SingleBinaryObservation {A B Result World Error : Type}
    (x : A) (y : B) (world : World)
    (observed : Option (Except Error Result ×
      (World × List (BinaryObservation A B Result World Error)))) : Prop :=
  match observed with
  | none => True
  | some observed =>
      ∃ call, observed.2.2 = [call] ∧ call.left = x ∧ call.right = y ∧
        call.before = world ∧ observed.1 = call.result ∧ observed.2.1 = call.after

/-- Full-domain observational invariant for the reused generic forwarding models.
Callbacks, effects, error type, inputs and worlds are unrestricted. This can fail
if a wrapper changes arguments, loses a result/error/world, or executes more than
one operation. Divergent leaves are included by Option; none has no terminating
observation. No arithmetic or callback law or termination premise is assumed.
Julia source: base/reduce.jl:16,27; documentation: base/reduce.jl:10-14,21-25. -/
def GenericOperatorForwarding : Prop :=
  ∀ (A B Result World Error : Type)
    (binary : A → B → World → Option (Except Error Result × World))
    (x : A) (y : B) (world : World),
    SingleBinaryObservation x y world
      ((JuliaLean.base.reduce.add_sum (observeBinary binary) x y).run (world, [])) ∧
    SingleBinaryObservation x y world
      ((JuliaLean.base.reduce.mul_prod (observeBinary binary) x y).run (world, []))

/-- Mathematical value of a Bool-or-small-bit-integer argument. This describes
input data; it does not invoke a conversion or any model under test.
Julia source: base/reduce.jl:17 and base/int.jl:22-24. -/
def smallOrBoolValue : SmallOrBool → Int
  | .inl false => 0
  | .inl true => 1
  | .inr x => x.value.val

/-- Small-operand sum is the exact mathematical sum after widening to Int.
Both signednesses, every accepted width, Bool and heterogeneous pairs are
quantified. These operands cannot overflow Int64, without value preconditions.
Julia source: base/reduce.jl:17; documentation: base/reduce.jl:10-14 and
manual/integers-and-floating-point-numbers.md:231-249. -/
def AddSumSmallExact : Prop :=
  ∀ x y : SmallOrBool,
    (addSumSmall x y).val = smallOrBoolValue x + smallOrBoolValue y

/-- Small unsigned operands widen to UInt and have their exact mathematical sum.
Every pair of UInt8/UInt16/UInt32 values and widths is included.
Julia source: base/reduce.jl:18; documentation: base/reduce.jl:10-14. -/
def AddSumUnsignedSmallExact : Prop :=
  ∀ x y : SmallUnsigned,
    (addSumUnsignedSmall x y).val = x.val.value.val + y.val.value.val

/-- Observed calls made by a Real-return method. Error includes all callback
errors; internal assertion errors occupy a separate outer exception layer only
to record their provenance.
Julia source: base/reduce.jl:19,30. -/
inductive RealObservation (A B Real Other World Error : Type) where
  | binary (left : A) (right : B) (before : World)
      (result : Except Error (Real ⊕ Other)) (after : World)
  | conversion (value : Other) (before : World)
      (result : Except Error (Real ⊕ Other)) (after : World)

/-- Observation monad preserving callback errors and the world on errors, along
with the separate return-type assertion failure. Option at the base includes
divergent dispatch leaves; no final world/trace is asserted for divergence.
Julia source: base/reduce.jl:19,30. -/
abbrev RealAuditM (A B Real Other World Error : Type) :=
  ExceptT RealTypeError
    (ExceptT Error (StateT (World × List (RealObservation A B Real Other World Error)) Option))

/-- Instrument selected arithmetic without restricting the selected callback.
Julia source: base/reduce.jl:19,30. -/
def observeRealBinary {A B Real Other World Error : Type}
    (binary : A → B → World → Option (Except Error (Real ⊕ Other) × World))
    (x : A) (y : B) : RealAuditM A B Real Other World Error (Real ⊕ Other) :=
  ExceptT.mk <| ExceptT.mk fun state => do
    let answer ← binary x y state.1
    pure (answer.1.map Except.ok,
      (answer.2, state.2 ++ [.binary x y state.1 answer.1 answer.2]))

/-- Instrument selected conversion without assuming success or a Real result.
Julia source: base/reduce.jl:19,30. -/
def observeRealConversion {A B Real Other World Error : Type}
    (convertReal : Other → World → Option (Except Error (Real ⊕ Other) × World))
    (value : Other) : RealAuditM A B Real Other World Error (Real ⊕ Other) :=
  ExceptT.mk <| ExceptT.mk fun state => do
    let answer ← convertReal value state.1
    pure (answer.1.map Except.ok,
      (answer.2, state.2 ++ [.conversion value state.1 answer.1 answer.2]))

/-- Combine independently instrumented dispatch leaves.
Julia source: base/reduce.jl:19,30. -/
def observedRealOps {A B Real Other World Error : Type}
    (binary : A → B → World → Option (Except Error (Real ⊕ Other) × World))
    (convertReal : Other → World → Option (Except Error (Real ⊕ Other) × World)) :
    RealReturnOps (RealAuditM A B Real Other World Error) A B Real Other :=
  ⟨observeRealBinary binary, observeRealConversion convertReal⟩

/-- Call-order, result-provenance and world-continuity invariant. Exactly one
arithmetic observation is present. Conversion can only follow a non-Real result
and receives it with the resulting world. Returned values/errors must originate
in the final dispatch observation, except that a non-Real conversion result is
rejected by the return assertion. An already-Real arithmetic result preserves
identity and executes no conversion. Divergence has no terminating observation.
No expected result replays the algorithm and no termination premise is imposed.
Julia source: base/reduce.jl:19,30; pinned lowering:
src/julia-syntax.scm:3870-3892,4807. -/
def RealObservationInvariant {A B Real Other World Error : Type}
    (x : A) (y : B) (world : World)
    (observed : Option (Except Error (Except RealTypeError Real) ×
      (World × List (RealObservation A B Real Other World Error)))) : Prop :=
  match observed with
  | none => True
  | some observed =>
      match observed.2.2 with
      | [.binary a b before result after] =>
          a = x ∧ b = y ∧ before = world ∧ observed.2.1 = after ∧
          ((∃ value, result = .ok (.inl value) ∧ observed.1 = .ok (.ok value)) ∨
           (∃ error, result = .error error ∧ observed.1 = .error error))
      | [.binary a b before first middle, .conversion arg next last after] =>
          a = x ∧ b = y ∧ before = world ∧ next = middle ∧ observed.2.1 = after ∧
          first = .ok (.inr arg) ∧
          ((∃ value, last = .ok (.inl value) ∧ observed.1 = .ok (.ok value)) ∨
           (∃ error, last = .error error ∧ observed.1 = .error error) ∨
           (∃ other, last = .ok (.inr other) ∧ observed.1 = .ok (.error .typeError)))
      | _ => False

/-- Real-return arithmetic obeys the observation invariant for every selected
arithmetic/conversion callback and all worlds, values and error types. Callbacks
may mutate, fail, diverge, or return a non-Real value; none is assumed correct. Returned
objects retain identity. All callbacks may include other errors such as TypeError.
Julia source: base/reduce.jl:19,30; documentation:
manual/functions.md:196-210, manual/conversion-and-promotion.md:102-109;
pinned return lowering: src/julia-syntax.scm:3870-3892,4807. -/
def RealOperatorObservation : Prop :=
  ∀ (A B Real Other World Error : Type)
    (binary : A → B → World → Option (Except Error (Real ⊕ Other) × World))
    (convertReal : Other → World → Option (Except Error (Real ⊕ Other) × World))
    (x : A) (y : B) (world : World),
    let ops := observedRealOps binary convertReal
    RealObservationInvariant x y world
      ((addSumReal ops x y).run.run (world, [])) ∧
    RealObservationInvariant x y world
      ((mulProdReal ops x y).run.run (world, []))

/-- Every two small signed operands have an exact Int product. Representation
bounds make the product fit Int64; no narrower input values are assumed.
Julia source: base/reduce.jl:28; documentation: base/reduce.jl:21-25. -/
def MulProdSignedSmallExact : Prop :=
  ∀ x y : SmallSigned,
    (mulProdSignedSmall x y).val = x.val.value.val * y.val.value.val

/-- Every two small unsigned operands have an exact UInt product, including
heterogeneous widths and the maximal UInt32 × UInt32 case.
Julia source: base/reduce.jl:29; documentation: base/reduce.jl:21-25. -/
def MulProdUnsignedSmallExact : Prop :=
  ∀ x y : SmallUnsigned,
    (mulProdUnsignedSmall x y).val = x.val.value.val * y.val.value.val

/-- Complete truth and TypeError classification for reused generic and_all.
All non-Bool Julia values inhabit unconstrained Other arms. A false first
operand suppresses the second operand's type assertion.
Julia source: base/reduce.jl:32; manual/types.md:60-83 and
manual/control-flow.md (short-circuit evaluation). -/
def AndAllTruthAndErrors : Prop :=
  ∀ (A B : Type) (x : Bool ⊕ A) (y : Bool ⊕ B),
    (and_all x y = .ok true ↔ x = .inl true ∧ y = .inl true) ∧
    (and_all x y = .ok false ↔
      x = .inl false ∨ (x = .inl true ∧ y = .inl false)) ∧
    (and_all x y = .error .typeError ↔
      (∃ a, x = .inr a) ∨ (x = .inl true ∧ ∃ b, y = .inr b))

/-- Complete truth and TypeError classification for reused generic or_any.
A true first operand suppresses the second operand's type assertion; a non-Bool
first operand always produces TypeError.
Julia source: base/reduce.jl:33; manual/types.md:60-83 and
manual/control-flow.md (short-circuit evaluation). -/
def OrAnyTruthAndErrors : Prop :=
  ∀ (A B : Type) (x : Bool ⊕ A) (y : Bool ⊕ B),
    (or_any x y = .ok true ↔
      x = .inl true ∨ (x = .inl false ∧ y = .inl true)) ∧
    (or_any x y = .ok false ↔ x = .inl false ∧ y = .inl false) ∧
    (or_any x y = .error .typeError ↔
      (∃ a, x = .inr a) ∨ (x = .inl false ∧ ∃ b, y = .inr b))

/-- Bool conjunction is true exactly when both inputs are true.
Julia source: base/reduce.jl:35 and base/bool.jl:14. -/
def AndAllBoolTruth : Prop :=
  ∀ x y : Bool, andAllBool x y = true ↔ x = true ∧ y = true

/-- Bool disjunction is true exactly when at least one input is true.
Julia source: base/reduce.jl:36 and base/bool.jl:15. -/
def OrAnyBoolTruth : Prop :=
  ∀ x y : Bool, orAnyBool x y = true ↔ x = true ∨ y = true

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

/-- A completed selected dispatch observation, with exact arguments and worlds.
These events are specification instrumentation, not additional Julia methods. -/
inductive FoldlObservation (Op I V W E : Type) where
  | fold (op : Op) (init : FoldInit V) (itr : I) (before : W)
      (result : Except E (FoldInit V)) (after : W)
  | empty (op : Op) (itr : I) (before : W)
      (result : Except E (FoldInit V)) (after : W)

abbrev FoldlAuditM (Op I V W E : Type) :=
  ExceptT E (StateT (W × List (FoldlObservation Op I V W E)) Option)

/-- Instrument arbitrary partial, stateful, throwing fold/empty dispatch.
No callee law or finite-iterator condition is imposed. -/
def observedFoldlOps {Op I V W E : Type}
    (fold : Op → FoldInit V → I → W → Option (Except E (FoldInit V) × W))
    (empty : Op → I → W → Option (Except E (FoldInit V) × W)) :
    FoldDispatchOps (FoldlAuditM Op I V W E) Op I V where
  fold := fun op init itr => ExceptT.mk fun state => do
    let (result, world) ← fold op init itr state.1
    pure (result, (world, state.2 ++ [.fold op init itr state.1 result world]))
  empty := fun op itr => ExceptT.mk fun state => do
    let (result, world) ← empty op itr state.1
    pure (result, (world, state.2 ++ [.empty op itr state.1 result world]))

/-- Independently observable dispatch invariant: there is one fold event;
the only possible second event is an empty dispatch after a sentinel result.
Its exact arguments and world continuity are preserved. Returned values and
errors come from the last event, with no fabricated default or extra check.
No terminating observation is available when an arbitrary callee diverges.
Source: base/reduce.jl:45-49, sentinel-gated empty reduction invariant. -/
def FoldlDispatchInvariant {Op I V W E : Type}
    (op : Op) (init : FoldInit V) (itr : I) (world : W)
    (observed : Option (Except E (FoldInit V) ×
      (W × List (FoldlObservation Op I V W E)))) : Prop :=
  match observed with
  | none => True
  | some (result, finalWorld, events) =>
      match events with
      | [.fold o a i before first after] =>
          o = op ∧ a = init ∧ i = itr ∧ before = world ∧ finalWorld = after ∧
          result = first ∧
          ((∃ value, first = .ok (.value value)) ∨ ∃ error, first = .error error)
      | [.fold o a i before first middle, .empty o' i' next last after] =>
          o = op ∧ a = init ∧ i = itr ∧ before = world ∧
          first = .ok .initial ∧ o' = op ∧ i' = itr ∧ next = middle ∧
          finalWorld = after ∧ result = last
      | _ => False

/-- Full-domain invariant for foldl_impl, including arbitrary user dispatch,
mutations, failures, divergent calls, and an empty reducer returning the
sentinel again. There are no assumptions on any callback's correctness.
Source: base/reduce.jl:45-49. -/
def FoldlDispatchObservation : Prop :=
  ∀ (Op I V W E : Type)
    (fold : Op → FoldInit V → I → W → Option (Except E (FoldInit V) × W))
    (empty : Op → I → W → Option (Except E (FoldInit V) × W))
    (op : Op) (init : FoldInit V) (itr : I) (world : W),
    FoldlDispatchInvariant op init itr world
      ((foldlImpl (observedFoldlOps fold empty) op init itr).run (world, []))

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce.Models2Group7

/-- An observed dispatch call. Before/after worlds and even exceptional results
are retained. The trace is specification data, not a Julia collection.
Julia source: base/reduce.jl:51-63; base/iterators.jl:696-697,732. -/
inductive FoldCall (W E I V O : Type) where
  | iterate (handle : I) (state : Option V) (before : W)
      (answer : Except (FoldError E) (Option V)) (after : W)
  | getindex (object : V) (index : JInt .i64) (before : W)
      (answer : Except (FoldError E) V) (after : W)
  | apply (op : O) (accumulator item : V) (before : W)
      (answer : Except (FoldError E) V) (after : W)
  | rest (handle : I) (state : V) (before : W)
      (answer : Except (FoldError E) (FoldIterator I V)) (after : W)
  | selectedRest (iterator : FoldIterator I V) (state : V) (before : W)
      (answer : Except (FoldError E) (FoldIterator I V)) (after : W)
  | construct (iterator : FoldIterator I V) (state : V) (before : W)
      (answer : Except (FoldError E) (FoldIterator I V)) (after : W)
  | restIterate (iterator : FoldIterator I V) (state : Option V) (before : W)
      (answer : Except (FoldError E) (Option V)) (after : W)
  | itrRead (iterator : FoldIterator I V) (before : W)
      (answer : Except (FoldError E) (FoldIterator I V)) (after : W)
  | stRead (iterator : FoldIterator I V) (before : W)
      (answer : Except (FoldError E) V) (after : W)

/-- Add one complete observation without imposing a law on the underlying call.
The callback cannot inspect or alter the instrumentation trace.
Julia source: base/reduce.jl:54-61 (open dispatch observations). -/
def observeFoldCall {W E I V O A : Type}
    (call : FoldEval W (FoldError E) A)
    (event : W → Except (FoldError E) A → W → FoldCall W E I V O) :
    FoldEval (W × List (FoldCall W E I V O)) (FoldError E) A :=
  ExceptT.mk fun state => do
    let answer ← call state.1
    pure (answer.1, (answer.2, state.2 ++ [event state.1 answer.1 answer.2]))

/-- Instrument every selected leaf while leaving the storage view unchanged.
No semantic assumption is made on iterate, getindex, op or a selected custom rest.
Julia source: base/reduce.jl:51-63; base/iterators.jl:696-697,732. -/
def observeFoldOps {W E I V O : Type} (ops : FoldProtocolOps W E I V O) :
    FoldProtocolOps (W × List (FoldCall W E I V O)) E I V O where
  iterate := fun handle state => observeFoldCall (ops.iterate handle state)
    (FoldCall.iterate handle state)
  getindex := fun object index => observeFoldCall (ops.getindex object index)
    (FoldCall.getindex object index)
  apply := fun op acc item => observeFoldCall (ops.apply op acc item)
    (FoldCall.apply op acc item)
  customRest := fun handle state => observeFoldCall (ops.customRest handle state)
    (FoldCall.rest handle state)
  fields := fun world object => ops.fields world.1 object
  selectedRest := fun iterator state => (ops.selectedRest iterator state).map fun call =>
    observeFoldCall call (FoldCall.selectedRest iterator state)
  selectedRestConstructor := fun iterator state => (ops.selectedRestConstructor iterator state).map fun call =>
    observeFoldCall call (FoldCall.construct iterator state)
  selectedRestIterate := fun iterator state => (ops.selectedRestIterate iterator state).map fun call =>
    observeFoldCall call (FoldCall.restIterate iterator state)
  selectedRestIteratorProperty := fun iterator => (ops.selectedRestIteratorProperty iterator).map fun call =>
    observeFoldCall call (FoldCall.itrRead iterator)
  selectedRestStateProperty := fun iterator => (ops.selectedRestStateProperty iterator).map fun call =>
    observeFoldCall call (FoldCall.stRead iterator)

/-- The entering world of an observation. -/
def foldCallBefore {W E I V O : Type} : FoldCall W E I V O → W
  | .iterate _ _ before _ _ => before
  | .getindex _ _ before _ _ => before
  | .apply _ _ _ before _ _ => before
  | .rest _ _ before _ _ => before
  | .selectedRest _ _ before _ _ => before
  | .construct _ _ before _ _ => before
  | .restIterate _ _ before _ _ => before
  | .itrRead _ before _ _ => before
  | .stRead _ before _ _ => before

/-- The exiting world of an observation, including an exception. -/
def foldCallAfter {W E I V O : Type} : FoldCall W E I V O → W
  | .iterate _ _ _ _ after => after
  | .getindex _ _ _ _ after => after
  | .apply _ _ _ _ _ after => after
  | .rest _ _ _ _ after => after
  | .selectedRest _ _ _ _ after => after
  | .construct _ _ _ _ after => after
  | .restIterate _ _ _ _ after => after
  | .itrRead _ _ _ after => after
  | .stRead _ _ _ after => after

/-- The exception, if any, observed from one dispatch leaf. -/
def foldCallError {W E I V O : Type} : FoldCall W E I V O → Option (FoldError E)
  | .iterate _ _ _ (.error error) _ => some error
  | .getindex _ _ _ (.error error) _ => some error
  | .apply _ _ _ _ (.error error) _ => some error
  | .rest _ _ _ (.error error) _ => some error
  | .selectedRest _ _ _ (.error error) _ => some error
  | .construct _ _ _ (.error error) _ => some error
  | .restIterate _ _ _ (.error error) _ => some error
  | .itrRead _ _ (.error error) _ => some error
  | .stRead _ _ (.error error) _ => some error
  | _ => none

/-- Adjacent call observations share a world; the returned world is the last one.
The predicate accounts for all effects without evaluating a model as its expected result. -/
def FoldWorldChain {W E I V O : Type} (world : W) :
    List (FoldCall W E I V O) → W → Prop
  | [], lastWorld => lastWorld = world
  | event :: rest, lastWorld =>
      foldCallBefore event = world ∧ FoldWorldChain (foldCallAfter event) rest lastWorld

/-- Independent left-association invariant: reducer inputs form a chain starting
at init, each successful result becomes the next accumulator, and a normal return
is the final chain value. Non-reducer calls do not change that chain. No arithmetic
or other law is imposed on the reducing function.
Julia source: base/reduce.jl:56,60,62; documentation: base/reduce.jl:175-180. -/
def FoldAccumulatorChain {W E I V O : Type} (op : O) (accumulator : V) :
    List (FoldCall W E I V O) → Except (FoldError E) V → Prop
  | [], .ok value => value = accumulator
  | [], .error _ => True
  | .apply calledOp suppliedAcc _ _ answer _ :: rest, finalAnswer =>
      calledOp = op ∧ suppliedAcc = accumulator ∧
      match answer with
      | .ok next => FoldAccumulatorChain op next rest finalAnswer
      | .error error => rest = [] ∧ finalAnswer = .error error
  | _ :: rest, finalAnswer => FoldAccumulatorChain op accumulator rest finalAnswer

/-- A recorded callback exception is terminal and is returned unchanged.
This is meaningful for arbitrary error types and mutated worlds. -/
def FoldErrorsStop {W E I V O : Type} (events : List (FoldCall W E I V O))
    (answer : Except (FoldError E) V) : Prop :=
  ∀ before event after error,
    events = before ++ event :: after → foldCallError event = some error →
    after = [] ∧ answer = .error error

/-- Every consumed item has an observed origin. The first item comes from a
successful getindex at native index 1. Tail items are the first stored field of
the latest iterate result; its second field must exist and be initialized before
that reducer can run. The expected values are storage contents, not foldFieldRead.
Julia source: base/reduce.jl:56,59-60; src/julia-syntax.scm:1888-1909,2070-2110. -/
def FoldInputProvenance {W E I V O : Type} (fields : W → V → FoldObjectView V)
    (previous : Option (FoldCall W E I V O)) : List (FoldCall W E I V O) → Prop
  | [] => True
  | event :: rest =>
      (match event with
       | .apply _ _ item _ _ _ =>
         match previous with
         | some (.getindex _ index _ (.ok value) _) => index.val = 1 ∧ item = value
         | some (.iterate _ _ _ (.ok (some object)) world)
         | some (.restIterate _ _ _ (.ok (some object)) world) =>
           match fields world object with
           | .module => False
           | .fields slots _ =>
               slots[0]? = some (some item) ∧ ∃ state, slots[1]? = some (some state)
         | _ => False
       | _ => True) ∧ FoldInputProvenance fields (some event) rest

/-- Complete finite observations of Rest iteration are specified by source
call/field dataflow. No callback is evaluated as an expected result. A selected
getter may produce any iterator/state, including a cycle; only finite terminating
observations have such a derivation. The actual model has an unrestricted fixed
point, so divergent getter/delegation cycles are retained.
Julia source: base/iterators.jl:732. -/
inductive RestIterationTrace {W E I V O : Type} (ops : FoldProtocolOps W E I V O) :
    FoldIterator I V → Option V → W → List (FoldCall W E I V O) →
    Except (FoldError E) (Option V) → W → Prop where
  | ordinary (handle : I) (state : Option V) (before : W)
      (answer : Except (FoldError E) (Option V)) (after : W) :
      RestIterationTrace ops (.ordinary handle) state before
        [.iterate handle state before answer after] answer after
  | opaqueIterator (handle : I) (state : Option V) (before : W)
      (answer : Except (FoldError E) (Option V)) (after : W) :
      RestIterationTrace ops (.customRest handle) state before
        [.iterate handle state before answer after] answer after
  | selected (inner : FoldIterator I V) (stored : V) (state : Option V)
      (before : W) (answer : Except (FoldError E) (Option V)) (after : W)
      (selected : (ops.selectedRestIterate (.knownRest inner stored) state).isSome = true) :
      RestIterationTrace ops (.knownRest inner stored) state before
        [.restIterate (.knownRest inner stored) state before answer after] answer after
  | stateError (inner : FoldIterator I V) (stored : V) (before after : W) (error : FoldError E)
      (base : (ops.selectedRestIterate (.knownRest inner stored) none).isNone = true)
      (selected : (ops.selectedRestStateProperty (.knownRest inner stored)).isSome = true) :
      RestIterationTrace ops (.knownRest inner stored) none before
        [.stRead (.knownRest inner stored) before (.error error) after] (.error error) after
  | stateStep (inner : FoldIterator I V) (stored observed : V) (before middle after : W)
      (events : List (FoldCall W E I V O)) (answer : Except (FoldError E) (Option V))
      (base : (ops.selectedRestIterate (.knownRest inner stored) none).isNone = true)
      (selected : (ops.selectedRestStateProperty (.knownRest inner stored)).isSome = true)
      (rest : RestIterationTrace ops (.knownRest inner stored) (some observed) middle events answer after) :
      RestIterationTrace ops (.knownRest inner stored) none before
        (.stRead (.knownRest inner stored) before (.ok observed) middle :: events) answer after
  | storedState (inner : FoldIterator I V) (stored : V) (before after : W)
      (events : List (FoldCall W E I V O)) (answer : Except (FoldError E) (Option V))
      (base : (ops.selectedRestIterate (.knownRest inner stored) none).isNone = true)
      (storedGetter : (ops.selectedRestStateProperty (.knownRest inner stored)).isNone = true)
      (rest : RestIterationTrace ops (.knownRest inner stored) (some stored) before events answer after) :
      RestIterationTrace ops (.knownRest inner stored) none before events answer after
  | iteratorError (inner : FoldIterator I V) (stored explicit : V) (before after : W) (error : FoldError E)
      (base : (ops.selectedRestIterate (.knownRest inner stored) (some explicit)).isNone = true)
      (selected : (ops.selectedRestIteratorProperty (.knownRest inner stored)).isSome = true) :
      RestIterationTrace ops (.knownRest inner stored) (some explicit) before
        [.itrRead (.knownRest inner stored) before (.error error) after] (.error error) after
  | iteratorStep (inner observed : FoldIterator I V) (stored explicit : V)
      (before middle after : W) (events : List (FoldCall W E I V O))
      (answer : Except (FoldError E) (Option V))
      (base : (ops.selectedRestIterate (.knownRest inner stored) (some explicit)).isNone = true)
      (selected : (ops.selectedRestIteratorProperty (.knownRest inner stored)).isSome = true)
      (rest : RestIterationTrace ops observed (some explicit) middle events answer after) :
      RestIterationTrace ops (.knownRest inner stored) (some explicit) before
        (.itrRead (.knownRest inner stored) before (.ok observed) middle :: events) answer after
  | storedIterator (inner : FoldIterator I V) (stored explicit : V) (before after : W)
      (events : List (FoldCall W E I V O)) (answer : Except (FoldError E) (Option V))
      (base : (ops.selectedRestIterate (.knownRest inner stored) (some explicit)).isNone = true)
      (storedGetter : (ops.selectedRestIteratorProperty (.knownRest inner stored)).isNone = true)
      (rest : RestIterationTrace ops inner (some explicit) before events answer after) :
      RestIterationTrace ops (.knownRest inner stored) (some explicit) before events answer after

/-- Initial iteration retains receiver/state dataflow through arbitrary Rest getters
and selected unary/binary methods. An empty result returns init immediately; a
nonempty result is first read by getindex(result,native one).
Julia source: base/reduce.jl:54-56; base/iterators.jl:732. -/
def FoldStartObservation {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (iterator : FoldIterator I V) (init : V) (world : W)
    (events : List (FoldCall W E I V O)) (answer : Except (FoldError E) V) : Prop :=
  ∃ firstEvents later firstAnswer after,
    events = firstEvents ++ later ∧
    RestIterationTrace ops iterator none world firstEvents firstAnswer after ∧
    match firstAnswer with
    | .error error => later = [] ∧ answer = .error error
    | .ok none => later = [] ∧ answer = .ok init
    | .ok (some result) =>
        ∃ readAnswer readAfter more,
          later = .getindex result (JuliaLean.base.int.lit .i64 1) after readAnswer readAfter :: more

/-- Independent trace predicates for the finite Rest construction path. -/
abbrev FoldTrace (W E I V O A : Type) :=
  W → List (FoldCall W E I V O) → Except (FoldError E) A → W → Prop

/-- A single dispatch call has exact arguments and the recorded result/world. -/
def foldLeafTrace {W E I V O A : Type}
    (event : W → Except (FoldError E) A → W → FoldCall W E I V O) : FoldTrace W E I V O A :=
  fun before events answer after => events = [event before answer after]

/-- Fixed immutable storage/construction preserves field identities and world. -/
def foldPureTrace {W E I V O A : Type} (value : A) : FoldTrace W E I V O A :=
  fun before events answer after => events = [] ∧ answer = .ok value ∧ before = after

/-- Trace composition reads prior observed results; no implementation or callback
is rerun. Errors stop at their observed world without invoking the continuation. -/
def foldThenTrace {W E I V O A B : Type} (first : FoldTrace W E I V O A)
    (next : A → FoldTrace W E I V O B) : FoldTrace W E I V O B :=
  fun before events answer after =>
    ∃ earlier later firstAnswer middle,
      events = earlier ++ later ∧ first before earlier firstAnswer middle ∧
      match firstAnswer with
      | .error error => later = [] ∧ answer = .error error ∧ after = middle
      | .ok value => next value middle later answer after

/-- Constructor result storage or one selected constructor's exact provenance. -/
def RestConstructorTrace {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (iterator : FoldIterator I V) (state : V) : FoldTrace W E I V O (FoldIterator I V) :=
  match ops.selectedRestConstructor iterator state with
  | some _ => foldLeafTrace (FoldCall.construct iterator state)
  | none => foldPureTrace (.knownRest iterator state)

/-- The fixed Base rest paths collapse exactly one stored layer, with selected
getproperty/constructor calls at their source points. A selected rest method is
separate. No old-state getter, recursive collapse, conversion, or iteration occurs. -/
def RestConstructionTrace {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (iterator : FoldIterator I V) (state : V) : FoldTrace W E I V O (FoldIterator I V) :=
  match ops.selectedRest iterator state with
  | some _ => foldLeafTrace (FoldCall.selectedRest iterator state)
  | none =>
    match iterator with
    | .customRest handle => foldLeafTrace (FoldCall.rest handle state)
    | .ordinary _ => RestConstructorTrace ops iterator state
    | .knownRest inner _stored =>
      foldThenTrace
        (match ops.selectedRestIteratorProperty iterator with
         | some _ => foldLeafTrace (FoldCall.itrRead iterator)
         | none => foldPureTrace inner)
        (fun observed => RestConstructorTrace ops observed state)

/-- Full selected/base Rest construction invariant, including arbitrary returned
iterator types, mutation, errors and divergence. Only immutable receiver/storage
invariants are used, with no callee law. Julia source: base/iterators.jl:669-673,696-697. -/
def RestConstructionObservation : Prop :=
  ∀ (W E I V O : Type) (ops : FoldProtocolOps W E I V O)
    (iterator : FoldIterator I V) (state : V) (world : W),
    match foldRest (observeFoldOps ops) iterator state (world, []) with
    | none => True
    | some (answer, (after, events)) => RestConstructionTrace ops iterator state world events answer after

/-- All finite observations of actual Rest iteration retain selected receiver,
state-getter-before-binary-redispatch ordering, observed iterator/state values,
errors and worlds. Getter cycles and other divergence have no terminating
observation; no fuel or success assumption excludes them.
Julia source: base/iterators.jl:732. -/
def RestIterationObservation : Prop :=
  ∀ (W E I V O : Type) (ops : FoldProtocolOps W E I V O)
    (iterator : FoldIterator I V) (state : Option V) (world : W),
    match foldIterate (observeFoldOps ops) iterator state (world, []) with
    | none => True
    | some (answer, (after, events)) => RestIterationTrace ops iterator state world events answer after

/-- Full-domain, unproved observation invariant for the generic internal fold.
All iterator/operator handles, universal value carriers, worlds, exceptions,
selected custom rest/constructor/iterate/property methods, storage representations and dispatch callbacks are
quantified without correctness or termination laws. Every terminating outcome,
including errors, must preserve iterator identity, left association, item origin,
world threading and immediate propagation of callback failures. Divergence has
no final observation; it is included without a termination precondition.

This is a narrow internal invariant, not a promise that arbitrary user callbacks
implement a sensible fold. It can be falsified by resetting the accumulator,
swapping reducer arguments, extracting the wrong field, skipping the field-2
check, losing a mutated world, swallowing a callback error, or changing the
original iterator handle. It does not restate the loop as an expected value.

Julia source: base/reduce.jl:51-63; base/iterators.jl:669-673,696-697,732.
Documentation: doc/src/manual/interfaces.md:8-54; base/reduce.jl:175-180. -/
def GenericFoldObservation : Prop :=
  ∀ (W E I V O : Type) (ops : FoldProtocolOps W E I V O)
    (op : O) (init : V) (iterator : FoldIterator I V) (world : W),
    match foldlGeneric (observeFoldOps ops) op init iterator (world, []) with
    | none => True
    | some (answer, (lastWorld, events)) =>
        FoldStartObservation ops iterator init world events answer ∧
        FoldAccumulatorChain op init events answer ∧
        FoldInputProvenance ops.fields none events ∧
        FoldWorldChain world events lastWorld ∧
        FoldErrorsStop events answer

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

/-- Independent concrete-Base-dispatch left-fold contract over immutable stored tuple fields, for
arbitrary stateful, throwing or divergent selected operators. List.foldlM is
used only as the mathematical sequence-fold specification; the model uses the
native cutoff, 31 explicit afoldl stages, a range tail, or the actual generic
iterator/Rest/field loop. No correctness law is assumed for any dispatch leaf.
All bounded tuple lengths and all heterogeneous values/accumulators are included.

At the maximal represented native arity, a Tuple finishes when its next native
index wraps negative. NamedTuple's iterator lacks the lower bound check and
therefore throws BoundsError after the last successful reduction. Callback
failure or divergence still takes precedence, with the resulting world retained.
This boundary is stated explicitly instead of silently replacing native addition
with an unbounded counter. No success/termination hypothesis is imposed.

Julia source: base/reduce.jl:65-68,175-180; base/operators.jl:622-663;
base/tuple.jl:69-73; base/namedtuple.jl:159-160;
doc/src/manual/interfaces.md:8-54. -/
def TupleFoldContents : Prop :=
  ∀ (W E Atom O : Type) (ops : TupleFullOps W E Atom O)
    (op : O) (init : TupleFoldValue Atom) (t : FoldTuple Atom) (world : W),
    let baseOps := { ops with
      selectedLength := fun _ => none
      selectedAfoldl := fun _ _ _ => none
      selectedInvoke := fun _ _ _ => none
      selectedIterate := fun _ _ => none
      selectedTupleIndex := fun _ _ => none
      selectedResultIndex := fun _ _ => none
      selectedRest := fun _ _ => none
      selectedRestConstructor := fun _ _ => none
      selectedRestIterate := fun _ _ => none
      selectedRestIteratorProperty := fun _ => none
      selectedRestStateProperty := fun _ => none }
    let folded := (t.values.foldlM (ops.apply op) init).run world
    let expected :=
      if t.kind = .namedTuple ∧ t.values.length = IntTy.i64.max.toNat then
        folded.map fun (result, finalWorld) =>
          (match result with
           | .error error => .error error
           | .ok _ => .error .boundsError, finalWorld)
      else folded
    (foldlTuple baseOps op init t).run world = expected


/-- Observable selected leaves. Interior tags distinguish indexing, iteration,
comparison, state arithmetic, colon and Rest routes without asserting callee laws. -/
inductive TupleDispatchAction (A O : Type) where
  | apply (op : O) (left right : TupleFoldValue A)
  | afoldl (op : O) (init : TupleFoldValue A) (args : TupleFoldArguments A)
  | invoke (op : O) (init : TupleFoldValue A) (tuple : FoldTuple A)
  | interior (tag : Nat)

structure TupleDispatchEvent (W E A O : Type) where
  action : TupleDispatchAction A O
  before : W
  after : W
  error : Option (FoldError E)
  value : Option (TupleFoldValue A)
  condition : Option (Bool ⊕ TupleFoldValue A)

/-- Instrument an arbitrary selected action; divergence produces no finite observation. -/
def observeTupleDispatch {W E A O R : Type}
    (action : TupleDispatchAction A O) (call : FoldEval W (FoldError E) R)
    (value : R → Option (TupleFoldValue A) := fun _ => none)
    (condition : R → Option (Bool ⊕ TupleFoldValue A) := fun _ => none) :
    FoldEval (W × List (TupleDispatchEvent W E A O)) (FoldError E) R :=
  ExceptT.mk fun world => do
    let (answer, after) ← call.run world.1
    let (error, result, cond) := match answer with
      | .ok r => (none, value r, condition r)
      | .error e => (some e, none, none)
    pure (answer, (after, world.2 ++ [⟨action, world.1, after, error, result, cond⟩]))

/-- Every callback is observed, including selected interior methods of concrete
Base bodies and every inherited Rest selection. Pure runtime storage metadata
is projected through the world, preserving actual aliases. -/
def observedTupleDispatchOps {W E A O : Type} (ops : TupleFullOps W E A O) :
    TupleFullOps (W × List (TupleDispatchEvent W E A O)) E A O where
  apply := fun op x y => observeTupleDispatch (.apply op x y) (ops.apply op x y) some
  atomGetindex := fun x i => observeTupleDispatch (.interior 0) (ops.atomGetindex x i) some
  nonNativeIterate := fun t state => observeTupleDispatch (.interior 1) (ops.nonNativeIterate t state)
  atomFields := fun world object => ops.atomFields world.1 object
  selectedLength := fun t => (ops.selectedLength t).map fun call => observeTupleDispatch (.interior 2) call some
  compareLength := fun value literal => observeTupleDispatch (.interior 3) (ops.compareLength value literal) (condition := some)
  selectedAfoldl := fun op init args => (ops.selectedAfoldl op init args).map fun call => observeTupleDispatch (.afoldl op init args) call some
  selectedInvoke := fun op init t => (ops.selectedInvoke op init t).map fun call => observeTupleDispatch (.invoke op init t) call some
  selectedIterate := fun t state => (ops.selectedIterate t state).map fun call => observeTupleDispatch (.interior 4) call
  selectedTupleIndex := fun t i => (ops.selectedTupleIndex t i).map fun call => observeTupleDispatch (.interior 5) call some
  selectedResultIndex := fun value i => (ops.selectedResultIndex value i).map fun call => observeTupleDispatch (.interior 6) call some
  lessEqual := fun x y => observeTupleDispatch (.interior 7) (ops.lessEqual x y) (condition := some)
  greater := fun x i => observeTupleDispatch (.interior 8) (ops.greater x i) (condition := some)
  addOne := fun x => observeTupleDispatch (.interior 9) (ops.addOne x) some
  equalLength := fun x i => observeTupleDispatch (.interior 10) (ops.equalLength x i) (condition := some)
  nonNativeTupleIndex := fun t i => observeTupleDispatch (.interior 11) (ops.nonNativeTupleIndex t i) some
  symbolView := ops.symbolView
  namedFieldNames := ops.namedFieldNames
  colon := fun first last => observeTupleDispatch (.interior 12) (ops.colon first last)
  rangeIterate := fun object state => observeTupleDispatch (.interior 13) (ops.rangeIterate object state)
  otherIterate := fun object state => observeTupleDispatch (.interior 14) (ops.otherIterate object state)
  customRest := fun object state => observeTupleDispatch (.interior 15) (ops.customRest object state)
  selectedRest := fun iterator state => (ops.selectedRest iterator state).map fun call => observeTupleDispatch (.interior 16) call
  selectedRestConstructor := fun iterator state => (ops.selectedRestConstructor iterator state).map fun call => observeTupleDispatch (.interior 17) call
  selectedRestIterate := fun iterator state => (ops.selectedRestIterate iterator state).map fun call => observeTupleDispatch (.interior 18) call
  selectedRestIteratorProperty := fun iterator => (ops.selectedRestIteratorProperty iterator).map fun call => observeTupleDispatch (.interior 19) call
  selectedRestStateProperty := fun iterator => (ops.selectedRestStateProperty iterator).map fun call => observeTupleDispatch (.interior 20) call some

/-- Consecutive selected effects expose the complete mutable world chain. -/
def TupleDispatchWorlds {W E A O : Type} (world : W) :
    List (TupleDispatchEvent W E A O) → W → Prop
  | [], after => after = world
  | event :: rest, after => event.before = world ∧ TupleDispatchWorlds event.after rest after

/-- Only the reducer or an explicitly selected afoldl/invoke produces an accumulator. -/
def tupleDispatchProduces {A O : Type} : TupleDispatchAction A O → Bool
  | .apply _ _ _ | .afoldl _ _ _ | .invoke _ _ _ => true | _ => false

/-- Actual operator identity, initial accumulator and splatted field order are unchanged. -/
def TupleDispatchArguments {A O : Type} (op : O) (init : TupleFoldValue A) (t : FoldTuple A) :
    TupleDispatchAction A O → Prop
  | .apply actual _ _ => actual = op
  | .afoldl actual original args => actual = op ∧ original = init ∧ args.values = t.values
  | .invoke actual original tuple => actual = op ∧ original = init ∧ tuple = t
  | .interior _ => True

/-- A terminating observation has no hidden mutation; exact reducer/forwarding
arguments and accumulator provenance survive arbitrary interior dispatch.
Callback errors and invalid Boolean results terminate at their actual sites.
Unobserved errors can only be the concrete Core bounds/undefined/type/field
checks. This is independent of iteration contents, termination, or callback
correctness. The concrete Base mathematical fold contract is stated separately.
Julia source: base/reduce.jl:65-68; base/operators.jl:622-663;
base/tuple.jl:69-73; base/namedtuple.jl:159-160. -/
def TupleDispatchObservation : Prop :=
  ∀ (W E A O : Type) (ops : TupleFullOps W E A O)
    (op : O) (init : TupleFoldValue A) (t : FoldTuple A) (world : W),
    match (foldlTuple (observedTupleDispatchOps ops) op init t).run (world, []) with
    | none => True
    | some (answer, after, events) =>
        TupleDispatchWorlds world events after ∧
        (∀ event ∈ events, TupleDispatchArguments op init t event.action) ∧
        (events.countP (fun e => match e.action with | .afoldl _ _ _ | .invoke _ _ _ => true | _ => false)) ≤ 1 ∧
        (∀ earlier event later error, events = earlier ++ event :: later → event.error = some error →
          later = [] ∧ answer = .error error) ∧
        (∀ earlier event later value, events = earlier ++ event :: later → event.condition = some (.inr value) →
          later = [] ∧ answer = .error .typeError) ∧
        (∀ error, answer = .error error →
          error = .boundsError ∨ error = .undefRefError ∨ error = .typeError ∨ error = .fieldError ∨
          ∃ earlier event, events = earlier ++ [event] ∧ event.error = some error) ∧
        (∀ value, answer = .ok value →
          (value = init ∧ ∀ event ∈ events, tupleDispatchProduces event.action = false) ∨
          ∃ earlier event later, events = earlier ++ event :: later ∧
            tupleDispatchProduces event.action = true ∧ event.value = some value ∧
            ∀ next ∈ later, tupleDispatchProduces next.action = false)

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

/-- Sequential mutable computations retain worlds on errors; none is divergence. -/
abbrev AdapterEval (W E A : Type) := ExceptT E (StateT W Option) A

/-- Complete call observation, with no law imposed on the callback. -/
structure AdapterCall (Args A W E : Type) where
  args : Args
  before : W
  answer : Except E A
  after : W

/-- Instrument a dispatch leaf without changing its outcome or effects. -/
def observeAdapterEffect {Args A W E Event : Type} (call : AdapterEval W E A)
    (args : Args) (tag : AdapterCall Args A W E → Event) :
    AdapterEval (W × List Event) E A :=
  ExceptT.mk fun state => do
    let answer ← call state.1
    pure (answer.1, (answer.2, state.2 ++ [tag ⟨args, state.1, answer.1, answer.2⟩]))

/-- Preserve stored selection and instrument only selected custom reads. -/
def liftPropertySelection {Object A W E Event : Type}
    (selection : PropertySelection (AdapterEval W E) Object A)
    (tag : AdapterCall Object A W E → Event) :
    PropertySelection (AdapterEval (W × List Event) E) Object A :=
  match selection with
  | .stored => .stored
  | .custom call => .custom fun object => observeAdapterEffect (call object) object tag

/-- Trace predicates describe actual observations; they never invoke a callback. -/
abbrev AdapterTrace (Event W E A : Type) := W → List Event → Except E A → W → Prop

/-- Exactly one observed call, original arguments, unchanged outcome and final world. -/
def adapterCallTrace {Args A W E Event : Type} (args : Args)
    (tag : AdapterCall Args A W E → Event) : AdapterTrace Event W E A :=
  fun before events answer after =>
    ∃ call, events = [tag call] ∧ call.args = args ∧ call.before = before ∧
      answer = call.answer ∧ after = call.after

/-- Pure return records no invocation and changes no world. -/
def adapterPureTrace {A W E Event : Type} (value : A) : AdapterTrace Event W E A :=
  fun before events answer after => events = [] ∧ answer = .ok value ∧ after = before

/-- Observed prefixes compose in order, adjacent worlds agree, and errors terminate.
No expected result is obtained by rerunning the implementation or a callback. -/
def adapterThenTrace {A B W E Event : Type} (first : AdapterTrace Event W E A)
    (next : A → AdapterTrace Event W E B) : AdapterTrace Event W E B :=
  fun before events answer after =>
    ∃ earlier later firstAnswer middle,
      events = earlier ++ later ∧ first before earlier firstAnswer middle ∧
      match firstAnswer with
      | .error error => later = [] ∧ answer = .error error ∧ after = middle
      | .ok value => next value middle later answer after

/-- Stored reads preserve the actual field; custom reads have one original-object call. -/
def propertySelectionTrace {Object A W E Event : Type}
    (selection : PropertySelection (AdapterEval W E) Object A) (field : Object → A)
    (object : Object) (tag : AdapterCall Object A W E → Event) : AdapterTrace Event W E A :=
  match selection with
  | .stored => adapterPureTrace (field object)
  | .custom _ => adapterCallTrace object tag

/-- Errors and divergence are included without a successful-run hypothesis. -/
def AdapterObserved {A W E Event : Type} (spec : AdapterTrace Event W E A) (world : W)
    (observed : Option (Except E A × (W × List Event))) : Prop :=
  match observed with
  | none => True
  | some (answer, (after, events)) => spec world events answer after

/-- Full-domain narrow invariant of readSelectedProperty: stored field/world identity,
versus one custom read with object/result/error/world provenance.
Julia source: base/Base_compiler.jl:59; base/reduce.jl:83-125. -/
def SelectedPropertyObservation : Prop :=
  ∀ (Object A W E : Type) (selection : PropertySelection (AdapterEval W E) Object A)
    (field : Object → A) (object : Object) (world : W),
    AdapterObserved (propertySelectionTrace selection field object id) world
      (readSelectedProperty (liftPropertySelection selection id) field object (world, []))

/-- Both immutable constructors retain exact field identities, for arbitrary callable
or non-callable values. Type-valued callable markers remain unchanged.
Julia source: base/reduce.jl:94-95. -/
def MappingConstructorsKeepFields : Prop :=
  ∀ (F RF : Type) (f : F) (rf : RF),
    (mappingRF_constructor f rf).f = f ∧ (mappingRF_constructor f rf).rf = rf ∧
    (mappingRF_type_constructor f rf).f = f ∧ (mappingRF_type_constructor f rf).rf = rf

/-- None/some accumulator arguments distinguish first-element and binary routes. -/
inductive BottomAdapterEvent (W E F Acc Input Result : Type) where
  | property (call : AdapterCall (BottomAdapter F) F W E)
  | invoke (call : AdapterCall (F × Option Acc × Input) Result W E)

/-- Instrument all BottomRF selections and invocation routes. -/
def observedBottomAdapterOps {W E F Acc Input Result : Type}
    (ops : BottomAdapterOps (AdapterEval W E) F Acc Input Result) :
    BottomAdapterOps (AdapterEval (W × List (BottomAdapterEvent W E F Acc Input Result)) E)
      F Acc Input Result where
  rfProperty := liftPropertySelection ops.rfProperty BottomAdapterEvent.property
  first := fun rf x => observeAdapterEffect (ops.first rf x) (rf, none, x) BottomAdapterEvent.invoke
  call := fun rf acc x => observeAdapterEffect (ops.call rf acc x) (rf, some acc, x) BottomAdapterEvent.invoke

/-- Exactly the selected getter, then exactly the requested invocation route. -/
def BottomAdapterTrace {W E F Acc Input Result : Type}
    (ops : BottomAdapterOps (AdapterEval W E) F Acc Input Result) (op : BottomAdapter F)
    (acc : Option Acc) (x : Input) : AdapterTrace (BottomAdapterEvent W E F Acc Input Result) W E Result :=
  adapterThenTrace
    (propertySelectionTrace ops.rfProperty BottomAdapter.rf op BottomAdapterEvent.property)
    (fun rf => adapterCallTrace (rf, acc, x) BottomAdapterEvent.invoke)

/-- Both BottomRF methods retain reducer identity, original operands, call cardinality,
result/error provenance and all worlds. Arbitrary getters/invocations need no laws.
Julia source: base/reduce.jl:83-84; documentation: base/reduce.jl:72-77. -/
def BottomAdapterObservation : Prop :=
  ∀ (W E F Acc Input Result : Type)
    (ops : BottomAdapterOps (AdapterEval W E) F Acc Input Result)
    (op : BottomAdapter F) (acc : Acc) (x : Input) (world : W),
    AdapterObserved (BottomAdapterTrace ops op none x) world
      (bottomInitial (observedBottomAdapterOps ops) op x (world, [])) ∧
    AdapterObserved (BottomAdapterTrace ops op (some acc) x) world
      (bottomApply (observedBottomAdapterOps ops) op acc x (world, []))

/-- Mapping observations expose both getters and both callable identities. -/
inductive MappingAdapterEvent (W E F RF Acc Input Mapped Result : Type) where
  | rfRead (call : AdapterCall (MappingRF F RF) RF W E)
  | fRead (call : AdapterCall (MappingRF F RF) F W E)
  | map (call : AdapterCall (F × Input) Mapped W E)
  | reduce (call : AdapterCall (RF × Acc × Mapped) Result W E)

/-- Instrument every mapping dispatch and both stored/custom getter selections. -/
def observedMappingAdapterOps {W E F RF Acc Input Mapped Result : Type}
    (ops : MappingAdapterOps (AdapterEval W E) F RF Acc Input Mapped Result) :
    MappingAdapterOps
      (AdapterEval (W × List (MappingAdapterEvent W E F RF Acc Input Mapped Result)) E)
      F RF Acc Input Mapped Result where
  rfProperty := liftPropertySelection ops.rfProperty MappingAdapterEvent.rfRead
  fProperty := liftPropertySelection ops.fProperty MappingAdapterEvent.fRead
  map := fun f x => observeAdapterEffect (ops.map f x) (f, x) MappingAdapterEvent.map
  call := fun rf acc value => observeAdapterEffect (ops.call rf acc value)
    (rf, acc, value) MappingAdapterEvent.reduce

/-- One mapping precedes one reduction with the original accumulator and observed
mapped result. Getter order is retained; errors truncate calls and preserve worlds. -/
def MappingAdapterTrace {W E F RF Acc Input Mapped Result : Type}
    (ops : MappingAdapterOps (AdapterEval W E) F RF Acc Input Mapped Result)
    (op : MappingRF F RF) (acc : Acc) (x : Input) :
    AdapterTrace (MappingAdapterEvent W E F RF Acc Input Mapped Result) W E Result :=
  adapterThenTrace (propertySelectionTrace ops.rfProperty MappingRF.rf op MappingAdapterEvent.rfRead) fun rf =>
  adapterThenTrace (propertySelectionTrace ops.fProperty MappingRF.f op MappingAdapterEvent.fRead) fun f =>
  adapterThenTrace (adapterCallTrace (f, x) MappingAdapterEvent.map) fun mapped =>
  adapterCallTrace (rf, acc, mapped) MappingAdapterEvent.reduce

/-- Full-domain mapping observation, with arbitrary side effects, errors, divergence
and custom property routes; no getter, mapper or reducer law is assumed.
Julia source: base/reduce.jl:98; documentation: base/reduce.jl:86-90. -/
def MappingAdapterObservation : Prop :=
  ∀ (W E F RF Acc Input Mapped Result : Type)
    (ops : MappingAdapterOps (AdapterEval W E) F RF Acc Input Mapped Result)
    (op : MappingRF F RF) (acc : Acc) (x : Input) (world : W),
    AdapterObserved (MappingAdapterTrace ops op acc x) world
      (mappingApply (observedMappingAdapterOps ops) op acc x (world, []))

/-- Filtering observations retain every predicate outcome, including non-Bools. -/
inductive FilteringAdapterEvent (W E F RF Acc Input Other : Type) where
  | fRead (call : AdapterCall (FilteringAdapter F RF) F W E)
  | rfRead (call : AdapterCall (FilteringAdapter F RF) RF W E)
  | predicate (call : AdapterCall (F × Input) (Bool ⊕ Other) W E)
  | reduce (call : AdapterCall (RF × Acc × Input) Acc W E)

/-- Separate assertion-error origin; callback errors still range over all exceptions. -/
abbrev FilteringAudit (W E F RF Acc Input Other : Type) :=
  ExceptT BoolTypeError
    (AdapterEval (W × List (FilteringAdapterEvent W E F RF Acc Input Other)) E)

/-- Observe a callback while preserving the branch-error layer. -/
def observeFilteringEffect {Args A W E F RF Acc Input Other : Type}
    (call : AdapterEval W E A) (args : Args)
    (tag : AdapterCall Args A W E → FilteringAdapterEvent W E F RF Acc Input Other) :
    FilteringAudit W E F RF Acc Input Other A :=
  ExceptT.mk do
    let answer ← observeAdapterEffect call args tag
    pure (.ok answer)

/-- Filtering retains both property-selection branches. -/
def liftFilteringProperty {Object A W E F RF Acc Input Other : Type}
    (selection : PropertySelection (AdapterEval W E) Object A)
    (tag : AdapterCall Object A W E → FilteringAdapterEvent W E F RF Acc Input Other) :
    PropertySelection (FilteringAudit W E F RF Acc Input Other) Object A :=
  match selection with
  | .stored => .stored
  | .custom call => .custom fun object => observeFilteringEffect (call object) object tag

/-- Instrument filtering without assuming Bool predicates or successful access. -/
def observedFilteringAdapterOps {W E F RF Acc Input Other : Type}
    (ops : FilteringAdapterOps (AdapterEval W E) F RF Acc Input Other) :
    FilteringAdapterOps (FilteringAudit W E F RF Acc Input Other) F RF Acc Input Other where
  fProperty := liftFilteringProperty ops.fProperty FilteringAdapterEvent.fRead
  rfProperty := liftFilteringProperty ops.rfProperty FilteringAdapterEvent.rfRead
  predicate := fun f x => observeFilteringEffect (ops.predicate f x) (f, x) FilteringAdapterEvent.predicate
  call := fun rf acc x => observeFilteringEffect (ops.call rf acc x) (rf, acc, x) FilteringAdapterEvent.reduce

/-- Embed a call outcome in an independent assertion layer without changing provenance. -/
def adapterLiftedCallTrace {Args A W E Event : Type} (args : Args)
    (tag : AdapterCall Args A W E → Event) :
    AdapterTrace Event W E (Except BoolTypeError A) :=
  fun before events answer after =>
    ∃ call, events = [tag call] ∧ call.args = args ∧ call.before = before ∧
      answer = call.answer.map Except.ok ∧ after = call.after

/-- The observed predicate decides filtering: false keeps acc with no reducer read
or call; non-Bool raises TypeError after predicate effects; true invokes the observed
reducer exactly once with original operands. Any callback error is terminal. -/
def FilteringAdapterTrace {W E F RF Acc Input Other : Type}
    (ops : FilteringAdapterOps (AdapterEval W E) F RF Acc Input Other)
    (op : FilteringAdapter F RF) (acc : Acc) (x : Input) :
    AdapterTrace (FilteringAdapterEvent W E F RF Acc Input Other) W E (Except BoolTypeError Acc) :=
  adapterThenTrace
    (propertySelectionTrace ops.fProperty FilteringAdapter.f op FilteringAdapterEvent.fRead) fun f =>
  adapterThenTrace (adapterCallTrace (f, x) FilteringAdapterEvent.predicate) fun condition =>
  match condition with
  | .inl false => adapterPureTrace (.ok acc)
  | .inl true =>
      adapterThenTrace
        (propertySelectionTrace ops.rfProperty FilteringAdapter.rf op FilteringAdapterEvent.rfRead) fun rf =>
      adapterLiftedCallTrace (rf, acc, x) FilteringAdapterEvent.reduce
  | .inr _ => adapterPureTrace (.error .typeError)

/-- All getters, predicate/reducer effects, errors and divergent callbacks are included
without correctness or termination laws. All non-Bool values range over Other.
Julia source: base/reduce.jl:110; documentation: base/reduce.jl:100-104. -/
def FilteringAdapterObservation : Prop :=
  ∀ (W E F RF Acc Input Other : Type)
    (ops : FilteringAdapterOps (AdapterEval W E) F RF Acc Input Other)
    (op : FilteringAdapter F RF) (acc : Acc) (x : Input) (world : W),
    AdapterObserved (FilteringAdapterTrace ops op acc x) world
      ((filteringApply (observedFilteringAdapterOps ops) op acc x).run.run (world, []))

/-- Flattening observations include raw transformation results and both indexed
iteration calls, so custom destructuring effects and malformed results are visible. -/
inductive FlatteningAdapterEvent (W E V : Type) where
  | rfRead (call : AdapterCall (FlatteningAdapter V) V W (FoldError E))
  | transform (call : AdapterCall (V × V) (FlattenTransformResult V) W (FoldError E))
  | indexed (call : AdapterCall (V × JInt .i64 × Option V) V W (FoldError E))
  | fold (call : AdapterCall (V × V × V) V W (FoldError E))

/-- Instrument all selected flattening calls and preserve its current storage view. -/
def observedFlatteningAdapterOps {W E V : Type} (ops : FlatteningAdapterOps W E V) :
    FlatteningAdapterOps (W × List (FlatteningAdapterEvent W E V)) E V where
  rfProperty := liftPropertySelection ops.rfProperty FlatteningAdapterEvent.rfRead
  transform := fun rf x => observeAdapterEffect (ops.transform rf x) (rf, x) FlatteningAdapterEvent.transform
  indexedIterate := fun object index state => observeAdapterEffect
    (ops.indexedIterate object index state) (object, index, state) FlatteningAdapterEvent.indexed
  fields := fun world object => ops.fields world.1 object
  fold := fun op acc itr => observeAdapterEffect (ops.fold op acc itr) (op, acc, itr) FlatteningAdapterEvent.fold

/-- Independent field-content contract in mathematical zero-based positions.
No model getter supplies the expected value: present initialized slots return their
stored value; missing/undefined slots and module integer access determine the error.
These pure reads add no dispatch event and preserve the current world. -/
def adapterFieldTrace {W E V Event : Type} (fields : W → V → FoldObjectView V)
    (object : V) (position : Nat) : AdapterTrace Event W (FoldError E) V :=
  fun before events answer after =>
    events = [] ∧ after = before ∧
    match fields before object with
    | .module => answer = .error .typeError
    | .fields slots _ =>
      match slots[position]? with
      | none => answer = .error .boundsError
      | some none => answer = .error .undefRefError
      | some (some value) => answer = .ok value

/-- Exactly one transform precedes the fold with original accumulator and observed
operator/iterator. A raw result has two indexed calls with exact indices/state;
field contents supply the operands, all access errors stop, and the last indexed
result needs only its first field. Known Base pairs require no user indexed call. -/
def FlatteningAdapterTrace {W E V : Type} (ops : FlatteningAdapterOps W E V)
    (op : FlatteningAdapter V) (acc x : V) :
    AdapterTrace (FlatteningAdapterEvent W E V) W (FoldError E) V :=
  adapterThenTrace
    (propertySelectionTrace ops.rfProperty FlatteningAdapter.rf op FlatteningAdapterEvent.rfRead) fun rf =>
  adapterThenTrace (adapterCallTrace (rf, x) FlatteningAdapterEvent.transform) fun result =>
  match result with
  | .pair operator iterator => adapterCallTrace (operator, acc, iterator) FlatteningAdapterEvent.fold
  | .custom object =>
      adapterThenTrace
        (adapterCallTrace (object, JuliaLean.base.int.lit .i64 1, none) FlatteningAdapterEvent.indexed) fun first =>
      adapterThenTrace (adapterFieldTrace ops.fields first 0) fun operator =>
      adapterThenTrace (adapterFieldTrace ops.fields first 1) fun state =>
      adapterThenTrace
        (adapterCallTrace (object, JuliaLean.base.int.lit .i64 2, some state) FlatteningAdapterEvent.indexed) fun second =>
      adapterThenTrace (adapterFieldTrace ops.fields second 0) fun iterator =>
      adapterCallTrace (operator, acc, iterator) FlatteningAdapterEvent.fold

/-- Full-domain observation invariant, including raw non-tuple transformation results,
selected custom getters/indexed_iterate, malformed fields, mutable effects, arbitrary
exceptions and divergent leaves. There are no correctness or success premises.
The expected operands come from actual call observations and stored field contents;
no expected result reruns the model or assumes a callback's correctness.
Julia source: base/reduce.jl:122-125; base/tuple.jl:161-172;
pinned src/julia-syntax.scm:1888-1909,2597-2608. -/
def FlatteningAdapterObservation : Prop :=
  ∀ (W E V : Type) (ops : FlatteningAdapterOps W E V)
    (op : FlatteningAdapter V) (acc x : V) (world : W),
    AdapterObserved (FlatteningAdapterTrace ops op acc x) world
      (flatteningApply (observedFlatteningAdapterOps ops) op acc x (world, []))

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

/-- Generic adjoint observations preserve raw return objects and both call arguments. -/
inductive AdjointEvent (W E V : Type) where
  | unwrap (call : AdapterCall V (TransformPairResult V V V) W (FoldError E))
  | indexed (call : AdapterCall (V × JInt .i64 × Option V) V W (FoldError E))
  | apply (call : AdapterCall (V × V) V W (FoldError E))

/-- Observe every open call while reading the actual current raw storage. -/
def observedAdjointOps {W E V : Type} (ops : GenericAdjointOps W E V) :
    GenericAdjointOps (W × List (AdjointEvent W E V)) E V where
  raw := {
    indexedIterate := fun object index state => observeAdapterEffect
      (ops.raw.indexedIterate object index state) (object, index, state) AdjointEvent.indexed
    fields := fun world object => ops.raw.fields world.1 object }
  unwrap := fun itr => observeAdapterEffect (ops.unwrap itr) itr AdjointEvent.unwrap
  apply := fun wrap op => observeAdapterEffect (ops.apply wrap op) (wrap, op) AdjointEvent.apply

/-- Independent content/observation specification for destructuring. Known pairs retain fields; raw results use observed indexed calls, mathematical Core field positions, and the pure carrier views. The last result needs only its first field.
Julia source: base/reduce.jl:147; src/julia-syntax.scm:2597-2608. -/
def adjointPairTrace {W E V : Type} (ops : GenericAdjointOps W E V)
    (result : TransformPairResult V V V) :
    AdapterTrace (AdjointEvent W E V) W (FoldError E) (V × V) :=
  match result with
  | .pair itr wrap => adapterPureTrace (itr, wrap)
  | .custom object firstView secondView =>
      adapterThenTrace
        (adapterCallTrace (object, JuliaLean.base.int.lit .i64 1, none) AdjointEvent.indexed) fun first =>
      adapterThenTrace (adapterFieldTrace ops.raw.fields first 0) fun itr =>
      adapterThenTrace (adapterFieldTrace ops.raw.fields first 1) fun state =>
      adapterThenTrace
        (adapterCallTrace (object, JuliaLean.base.int.lit .i64 2, some state) AdjointEvent.indexed) fun second =>
      adapterThenTrace (adapterFieldTrace ops.raw.fields second 0) fun wrap =>
      adapterPureTrace (firstView itr, secondView wrap)

/-- Full-domain generic own-body contract: one unwrap of the original iterator,
actual result destructuring, then one invocation of the observed wrapper on the
original operator. Its actual result and the observed iterator form the final
pair. Field errors and callback failures stop at their source positions and retain
all world changes; no callback is replayed or assumed correct.
Julia source: base/reduce.jl:146-149. -/
def AdjointObservation : Prop :=
  ∀ (W E V : Type) (ops : GenericAdjointOps W E V) (op itr : V) (world : W),
    AdapterObserved
      (adapterThenTrace (adapterCallTrace itr AdjointEvent.unwrap) fun unwrapped =>
      adapterThenTrace (adjointPairTrace ops unwrapped) fun pair =>
      adapterThenTrace (adapterCallTrace (pair.2, op) AdjointEvent.apply) fun value =>
      adapterPureTrace (value, pair.1)) world
      ((xfadjoint (observedAdjointOps ops) op itr).run (world, []))

/-- Every input type and value is retained exactly; the second component is the actual identity singleton token. The property compares stored fields and does not invoke a model as its expected computation.
Julia source: base/reduce.jl:151. -/
def GenericUnwrapIdentity : Prop :=
  ∀ (Object : Type) (object : Object),
    (xfadjointUnwrapFallback object).1 = object ∧
    (xfadjointUnwrapFallback object).2 = .identity

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

/-- Specification-only observation of one selected implementation call. Argument
objects are retained directly, including heterogeneous keyword values/aliases. -/
structure PublicFoldObservation (Arg Result W E : Type) where
  args : Arg
  before : W
  result : Except E Result
  after : W

/-- State and errors survive a failed call; none represents no terminating
observation because the arbitrary selected implementation diverges. -/
abbrev PublicFoldAuditM (Arg Result W E : Type) :=
  ExceptT E (StateT (W × List (PublicFoldObservation Arg Result W E)) Option)

/-- Instrument one arbitrary partial, stateful and throwing selected call.
No correctness or termination law is assumed for the callback. -/
def observePublicFold {Arg Result W E : Type}
    (call : Arg → W → Option (Except E Result × W)) (args : Arg) :
    PublicFoldAuditM Arg Result W E Result :=
  ExceptT.mk fun state => do
    let (result, world) ← call args state.1
    pure (result, (world, state.2 ++ [⟨args, state.1, result, world⟩]))

/-- An independent one-call argument/result/state provenance invariant. The
expected result is read from the observation, not computed by replaying the
wrapper body. This detects altered, missing or duplicate calls and lost errors
or world updates. No terminating trace is asserted for divergent executions. -/
def PublicFoldForwardInvariant {Arg Result W E : Type} (args : Arg) (world : W)
    (observed : Option (Except E Result ×
      (W × List (PublicFoldObservation Arg Result W E)))) : Prop :=
  match observed with
  | none => True
  | some (result, finalWorld, events) =>
      ∃ call, events = [call] ∧ call.args = args ∧ call.before = world ∧
        result = call.result ∧ finalWorld = call.after

/-- Full-domain public mapfoldl forwarding: the sole selected implementation
receives the original callable/operator/iterator, the actual default sentinel
when init is absent, and the exact supplied value otherwise. Every state, input,
callback error type and possibly divergent callback is quantified without laws.
Julia source: base/reduce.jl:166-173; doc/src/manual/functions.md:817-831. -/
def MapfoldlPublicForwarding : Prop :=
  ∀ (F Op I V Result W E : Type)
    (impl : F → Op → FoldInit V → I → W → Option (Except E Result × W))
    (f : F) (op : Op) (itr : I) (init : Option (FoldInit V)) (world : W),
    let call := fun (args : F × Op × FoldInit V × I) =>
      impl args.1 args.2.1 args.2.2.1 args.2.2.2
    let ops : PublicMapfoldOps (PublicFoldAuditM (F × Op × FoldInit V × I) Result W E)
        F Op I V Result :=
      ⟨fun f op nt itr => observePublicFold call (f, op, nt, itr)⟩
    PublicFoldForwardInvariant
      (f, op, match init with | none => .initial | some value => value, itr) world
      ((mapfoldlPublic ops f op itr init).run (world, []))

/-- Full-domain foldl forwarding retains the actual identity singleton and all
keyword objects, including those rejected by selected mapfoldl dispatch. The
arbitrary callback may mutate, throw or diverge; no law or success premise is
imposed. Opaque Kw values denote already-constructed, machine-valid Julia
keyword objects (Pairs over NamedTuples) without converting them to unrestricted Lean lists.
Julia source: base/reduce.jl:175-196; doc/src/manual/functions.md:849-860. -/
def FoldlPublicForwarding : Prop :=
  ∀ (Op I Kw Result W E : Type)
    (mapfold : IdentityFn → Op → I → Kw → W → Option (Except E Result × W))
    (op : Op) (itr : I) (kw : Kw) (world : W),
    let call := fun (args : IdentityFn × Op × I × Kw) =>
      mapfold args.1 args.2.1 args.2.2.1 args.2.2.2
    let ops : PublicFoldOps (PublicFoldAuditM (IdentityFn × Op × I × Kw) Result W E)
        Op I Kw Result :=
      ⟨fun f op itr kw => observePublicFold call (f, op, itr, kw)⟩
    PublicFoldForwardInvariant (.identity, op, itr, kw) world
      ((foldlPublic ops op itr kw).run (world, []))

end JuliaLean.Proofs.base.reduce.Models2Group7



namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

/-- Generic _reverse_iter is a one-call forwarding invariant for all iterator
and result objects, worlds, exceptions and divergent selected reverse methods.
Julia source: base/reduce.jl:206; base/iterators.jl:84-101. -/
def ReverseIterForwarding : Prop :=
  ∀ (I R W E : Type) (reverse : I → W → Option (Except E R × W))
    (itr : I) (world : W),
    let ops : ReverseIterOps (PublicFoldAuditM I R W E) I R :=
      ⟨fun x => observePublicFold reverse x⟩
    PublicFoldForwardInvariant itr world ((reverseIterDefault ops itr).run (world, []))

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

/-- Getter and invocation observations preserve all heterogeneous arguments. -/
inductive FlipAdapterEvent (W E F X Y Result : Type) where
  | property (call : AdapterCall (FlipAdapter F) F W E)
  | invoke (call : AdapterCall (F × Y × X) Result W E)

/-- Instrument selected property and callable leaves without imposing laws. -/
def observedFlipAdapterOps {W E F X Y Result : Type}
    (ops : FlipAdapterOps (AdapterEval W E) F X Y Result) :
    FlipAdapterOps (AdapterEval (W × List (FlipAdapterEvent W E F X Y Result)) E)
      F X Y Result where
  fProperty := liftPropertySelection ops.fProperty FlipAdapterEvent.property
  call := fun f y x => observeAdapterEffect (ops.call f y x) (f, y, x) FlipAdapterEvent.invoke

/-- Independent argument/result/state provenance: selected f retrieval precedes
one invocation with original operands in reversed order. Errors truncate the
observed calls and preserve the final world. Divergence is included.
Julia source: base/reduce.jl:213. -/
def FlipAdapterObservation : Prop :=
  ∀ (W E F X Y Result : Type)
    (ops : FlipAdapterOps (AdapterEval W E) F X Y Result)
    (wrapper : FlipAdapter F) (x : X) (y : Y) (world : W),
    AdapterObserved
      (adapterThenTrace
        (propertySelectionTrace ops.fProperty FlipAdapter.f wrapper FlipAdapterEvent.property)
        (fun f => adapterCallTrace (f, y, x) FlipAdapterEvent.invoke)) world
      (flipApply (observedFlipAdapterOps ops) wrapper x y (world, []))

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

/-- Full-domain public mapfoldr forwarding: the sole selected implementation
receives the original callable/operator/iterator, the actual default sentinel
when init is absent, and the exact supplied value otherwise. Every state, input,
callback error type and possibly divergent callback is quantified without laws.
Julia source: base/reduce.jl:215-222; doc/src/manual/functions.md:817-831. -/
def MapfoldrPublicForwarding : Prop :=
  ∀ (F Op I V Result W E : Type)
    (impl : F → Op → FoldInit V → I → W → Option (Except E Result × W))
    (f : F) (op : Op) (itr : I) (init : Option (FoldInit V)) (world : W),
    let call := fun (args : F × Op × FoldInit V × I) =>
      impl args.1 args.2.1 args.2.2.1 args.2.2.2
    let ops : PublicMapfoldOps (PublicFoldAuditM (F × Op × FoldInit V × I) Result W E)
        F Op I V Result :=
      ⟨fun f op nt itr => observePublicFold call (f, op, nt, itr)⟩
    PublicFoldForwardInvariant
      (f, op, match init with | none => .initial | some value => value, itr) world
      ((mapfoldrPublic ops f op itr init).run (world, []))

/-- Full-domain foldr forwarding retains the actual identity singleton and all
keyword objects, including those rejected by selected mapfoldr dispatch. The
arbitrary callback may mutate, throw or diverge; no law or success premise is
imposed. Opaque Kw values denote already-constructed, machine-valid Julia
keyword objects (Pairs over NamedTuples) without converting them to unrestricted Lean lists.
Julia source: base/reduce.jl:224-241; doc/src/manual/functions.md:849-860. -/
def FoldrPublicForwarding : Prop :=
  ∀ (Op I Kw Result W E : Type)
    (mapfold : IdentityFn → Op → I → Kw → W → Option (Except E Result × W))
    (op : Op) (itr : I) (kw : Kw) (world : W),
    let call := fun (args : IdentityFn × Op × I × Kw) =>
      mapfold args.1 args.2.1 args.2.2.1 args.2.2.2
    let ops : PublicFoldrOps (PublicFoldAuditM (IdentityFn × Op × I × Kw) Result W E)
        Op I Kw Result :=
      ⟨fun f op itr kw => observePublicFold call (f, op, itr, kw)⟩
    PublicFoldForwardInvariant (.identity, op, itr, kw) world
      ((foldrPublic ops op itr kw).run (world, []))

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce.Models2Group7

/-- Actual selected calls made by the generic pairwise body and expanded SIMD loops.
The inbounds marker records execution context, not an additional Julia argument. -/
inductive PairwiseAction (V F O A : Type) where
  | equal (left right : PairwiseValue V)
  | less (left right : PairwiseValue V)
  | subtract (left right : PairwiseValue V)
  | add (left right : PairwiseValue V)
  | addLiteral (left : PairwiseValue V) (right : JInt .i64)
  | shiftRight (left : PairwiseValue V) (right : JInt .i64)
  | zero (value : PairwiseValue V)
  | colon (first last : PairwiseValue V)
  | outerRange (range : PairwiseValue V)
  | innerLength (range outer : PairwiseValue V)
  | simdIndex (range outer index : PairwiseValue V)
  | iterate (range : PairwiseValue V) (state : Option (PairwiseValue V))
  | getindex (array : A) (index : PairwiseValue V) (inbounds : Bool)
  | map (f : F) (element : PairwiseValue V)
  | reduce (op : O) (left right : PairwiseValue V)
  | first (f : F) (op : O) (element : PairwiseValue V)
  | custom (f : F) (op : O) (array : A) (first last block : PairwiseValue V)
  | blockSize (f : F) (op : O)

/-- Tagged outcomes retain arbitrary values, non-Bool conditions and raw iteration objects. -/
inductive PairwiseReply (V : Type) where
  | value (value : PairwiseValue V)
  | condition (value : Bool ⊕ PairwiseValue V)
  | iteration (value : Option (PairwiseValue V))

/-- One completed call retains its exact entering/exiting world and outcome. -/
structure PairwiseEvent (W E V F O A : Type) where
  action : PairwiseAction V F O A
  before : W
  answer : Except (FoldError (JlError ⊕ E)) (PairwiseReply V)
  after : W

/-- Observe an arbitrary call, imposing no correctness or termination law. -/
def observePairwiseCall {W E V F O A B : Type} (call : PairwiseM W E B)
    (action : PairwiseAction V F O A) (reply : B → PairwiseReply V) :
    PairwiseM (W × List (PairwiseEvent W E V F O A)) E B :=
  ExceptT.mk fun state => do
    let answer ← call state.1
    pure (answer.1, (answer.2,
      state.2 ++ [⟨action, state.1, answer.1.map reply, answer.2⟩]))

/-- Instrument each selected dispatch. Current field storage and runtime method
selection remain representation data and are not replaced by invocation callbacks. -/
def observedPairwiseOps {W E V F O A : Type} (ops : PairwiseOps W E V F O A) :
    PairwiseOps (W × List (PairwiseEvent W E V F O A)) E V F O A where
  equal := fun x y => observePairwiseCall (ops.equal x y) (.equal x y) .condition
  less := fun x y => observePairwiseCall (ops.less x y) (.less x y) .condition
  subtract := fun x y => observePairwiseCall (ops.subtract x y) (.subtract x y) .value
  add := fun x y => observePairwiseCall (ops.add x y) (.add x y) .value
  addLiteral := fun x y => observePairwiseCall (ops.addLiteral x y) (.addLiteral x y) .value
  shiftRight := fun x y => observePairwiseCall (ops.shiftRight x y) (.shiftRight x y) .value
  zero := fun x => observePairwiseCall (ops.zero x) (.zero x) .value
  colon := fun x y => observePairwiseCall (ops.colon x y) (.colon x y) .value
  simdOuterRange := fun r => observePairwiseCall (ops.simdOuterRange r) (.outerRange r) .value
  simdInnerLength := fun r j => observePairwiseCall (ops.simdInnerLength r j) (.innerLength r j) .value
  simdIndex := fun r j i => observePairwiseCall (ops.simdIndex r j i) (.simdIndex r j i) .value
  iterate := fun r state => observePairwiseCall (ops.iterate r state) (.iterate r state) .iteration
  fields := fun world value => ops.fields world.1 value
  getindex := fun array index inbounds => observePairwiseCall
    (ops.getindex array index inbounds) (.getindex array index inbounds) .value
  map := fun f x => observePairwiseCall (ops.map f x) (.map f x) .value
  reduce := fun op x y => observePairwiseCall (ops.reduce op x y) (.reduce op x y) .value
  first := fun f op x => observePairwiseCall (ops.first f op x) (.first f op x) .value
  target := ops.target
  custom := fun f op array first last block => observePairwiseCall
    (ops.custom f op array first last block) (.custom f op array first last block) .value
  blockSize := fun f op => observePairwiseCall (ops.blockSize f op) (.blockSize f op) .value

/-- Every neighboring pair of calls shares the same world; pure method machinery
and field reads cannot discard a mutation or invent an unobserved state change. -/
def PairwiseWorlds {W E V F O A : Type} (world : W) :
    List (PairwiseEvent W E V F O A) → W → Prop
  | [], after => after = world
  | event :: rest, after => event.before = world ∧ PairwiseWorlds event.after rest after

/-- A selected callback exception terminates the outer computation unchanged. -/
def PairwiseErrorsStop {W E V F O A : Type} (events : List (PairwiseEvent W E V F O A))
    (answer : Except (FoldError (JlError ⊕ E)) (PairwiseValue V)) : Prop :=
  ∀ earlier event later error,
    events = earlier ++ event :: later → event.answer = .error error →
    later = [] ∧ answer = .error error

/-- A non-Bool comparison fails at its condition, after its observed effects. -/
def PairwiseConditionsChecked {W E V F O A : Type}
    (events : List (PairwiseEvent W E V F O A))
    (answer : Except (FoldError (JlError ⊕ E)) (PairwiseValue V)) : Prop :=
  ∀ earlier event later value,
    events = earlier ++ event :: later → event.answer = .ok (.condition (.inr value)) →
    later = [] ∧ answer = .error .typeError

/-- The original array/mapper/reducer identities and native literal arguments are
preserved throughout generic recursion. Every source array access is inbounds. -/
def PairwiseIdentity {V F O A : Type} (f : F) (op : O) (array : A) :
    PairwiseAction V F O A → Prop
  | .getindex actual _ context => actual = array ∧ context = true
  | .map actual _ => actual = f
  | .reduce actual _ _ => actual = op
  | .first actualF actualOp _ => actualF = f ∧ actualOp = op
  | .custom actualF actualOp actualA _ _ _ => actualF = f ∧ actualOp = op ∧ actualA = array
  | .blockSize actualF actualOp => actualF = f ∧ actualOp = op
  | .addLiteral _ literal => literal.val = 1 ∨ literal.val = 2
  | .shiftRight _ literal => literal.val = 1
  | _ => True

/-- A genuine value-producing reduction call, independent of arithmetic laws. -/
def PairwiseProducesReduction {V F O A : Type} : PairwiseAction V F O A → Prop
  | .reduce _ _ _ => True
  | .first _ _ _ => True
  | .custom _ _ _ _ _ _ => True
  | _ => False

/-- A mapper or earlier reduction produces values accepted by a later reducer. -/
def PairwiseProducesOperand {V F O A : Type} : PairwiseAction V F O A → Prop
  | .map _ _ => True
  | action => PairwiseProducesReduction action

/-- An earlier read returned this element; no accessor correctness is presumed. -/
def PairwiseReadOrigin {W E V F O A : Type} (events : List (PairwiseEvent W E V F O A))
    (value : PairwiseValue V) : Prop :=
  ∃ event ∈ events, (∃ array index context, event.action = .getindex array index context) ∧
    event.answer = .ok (.value value)

/-- An earlier mapping/reduction returned this operand; its value remains unrestricted. -/
def PairwiseOperandOrigin {W E V F O A : Type}
    (events : List (PairwiseEvent W E V F O A)) (value : PairwiseValue V) : Prop :=
  ∃ event ∈ events, PairwiseProducesOperand event.action ∧ event.answer = .ok (.value value)

/-- Every mapped/first-reduced element was read earlier; every reducer operand was
produced by an earlier mapping/reduction. This is independent data-flow provenance,
not an expected execution of the algorithm or an algebraic correctness law. -/
def PairwiseDataFlow {W E V F O A : Type} (events : List (PairwiseEvent W E V F O A)) : Prop :=
  ∀ earlier event later, events = earlier ++ event :: later →
    match event.action with
    | .map _ value => PairwiseReadOrigin earlier value
    | .first _ _ value => PairwiseReadOrigin earlier value
    | .reduce _ left right => PairwiseOperandOrigin earlier left ∧ PairwiseOperandOrigin earlier right
    | _ => True

/-- A normal return retains an actually observed reduction result, never a raw index,
block size, array element, or invented value. Error outcomes remain included. -/
def PairwiseResultOrigin {W E V F O A : Type}
    (events : List (PairwiseEvent W E V F O A))
    (answer : Except (FoldError (JlError ⊕ E)) (PairwiseValue V)) : Prop :=
  match answer with
  | .error _ => True
  | .ok value => ∃ event ∈ events,
      PairwiseProducesReduction event.action ∧ event.answer = .ok (.value value)

/-- Body recursion never recomputes pairwise_blocksize. -/
def PairwiseNoBlockSize {W E V F O A : Type} (events : List (PairwiseEvent W E V F O A)) : Prop :=
  ∀ event ∈ events, ∀ f op, event.action ≠ .blockSize f op

/-- Every terminating body execution starts by comparing the original interval ends. -/
def PairwiseStartsAt {W E V F O A : Type} (first last : PairwiseValue V) (world : W)
    (events : List (PairwiseEvent W E V F O A)) : Prop :=
  ∃ event rest, events = event :: rest ∧ event.action = .equal first last ∧ event.before = world

/-- Shared narrow observations: identity, inbounds context, data flow, native literal
arguments, result provenance, effect continuity and terminal condition/callback errors. -/
def PairwiseObservationInvariant {W E V F O A : Type} (f : F) (op : O) (array : A)
    (world : W) (answer : Except (FoldError (JlError ⊕ E)) (PairwiseValue V))
    (after : W) (events : List (PairwiseEvent W E V F O A)) : Prop :=
  (∀ event ∈ events, PairwiseIdentity f op array event.action) ∧
  PairwiseDataFlow events ∧ PairwiseResultOrigin events answer ∧
  PairwiseWorlds world events after ∧ PairwiseErrorsStop events answer ∧
  PairwiseConditionsChecked events answer

/-- Full-domain internal invariant for the generic pairwise implementation. All
Integer representations, arrays/broadcasted objects, selected callees, custom method
targets, worlds, effects, errors and divergence are quantified without laws. The only
subtype witnesses are the source Integer annotations. A valid nonempty interval is
the caller's source requirement; this narrower provenance invariant holds even for
other represented intervals and does not assert safety of arbitrary inbounds calls.

The property can reject changed input identities, added bounds-check context,
invented elements/results, invalid literal arguments, lost effects, swallowed errors,
or a wrong first comparison, independently of any numerical reduction semantics.
No expected output executes the model or assumes callback correctness.
Julia source: base/reduce.jl:245-274; base/simdloop.jl:67-87. -/
def PairwiseBodyObservation : Prop :=
  ∀ (W E V F O A : Type) (ops : PairwiseOps W E V F O A)
    (f : F) (op : O) (array : A) (first last : PairwiseIndex V)
    (block : JInt .i64) (world : W),
    match mapreduceImpl (observedPairwiseOps ops) f op array first last block (world, []) with
    | none => True
    | some (answer, (after, events)) =>
        PairwiseStartsAt first.val last.val world events ∧ PairwiseNoBlockSize events ∧
        PairwiseObservationInvariant f op array world answer after events

/-- The default wrapper obtains exactly one block-size value before any other
selected call, then honors its actual method dispatch. A non-native block size
is not silently narrowed to Nat or Int; it can select a custom method or fail.
The generic branch begins the real body, not a callback for that body. -/
def PairwiseDefaultDispatch {W E V F O A : Type} (ops : PairwiseOps W E V F O A)
    (f : F) (op : O) (array : A) (first last : PairwiseIndex V) (world : W)
    (events : List (PairwiseEvent W E V F O A))
    (answer : Except (FoldError (JlError ⊕ E)) (PairwiseValue V)) (after : W) : Prop :=
  ∃ blockCall rest,
    events = blockCall :: rest ∧ blockCall.action = .blockSize f op ∧ blockCall.before = world ∧
    PairwiseNoBlockSize rest ∧
    match blockCall.answer with
    | .error error => rest = [] ∧ answer = .error error ∧ after = blockCall.after
    | .ok (.value block) =>
      match ops.target f op array first.val last.val block with
      | .missing => rest = [] ∧ answer = .error (.dispatch (.inl (.methodError "mapreduce_impl"))) ∧
          after = blockCall.after
      | .custom =>
        ∃ call result,
          rest = [call] ∧ call.action = .custom f op array first.val last.val block ∧
          call.before = blockCall.after ∧ call.answer = result.map PairwiseReply.value ∧
          answer = result ∧ after = call.after
      | .generic =>
        match block with
        | .native _ => PairwiseStartsAt first.val last.val blockCall.after rest
        | _ => rest = [] ∧ answer = .error (.dispatch (.inl (.methodError "mapreduce_impl"))) ∧
            after = blockCall.after
    | .ok _ => False

/-- Every typed input and every block-size callback/result type is included. The
wrapper preserves the exact block result and original arguments through method
selection, propagates all errors/worlds, and never recomputes the block size.
Divergence is included without a termination premise. Together with the shared
observation invariant, this detects wrong call counts/order/arguments, discarded
custom method selection, an illicit block-size conversion, and lost effects.
Julia source: base/reduce.jl:276-277. -/
def PairwiseDefaultObservation : Prop :=
  ∀ (W E V F O A : Type) (ops : PairwiseOps W E V F O A)
    (f : F) (op : O) (array : A) (first last : PairwiseIndex V) (world : W),
    match mapreduceImplDefault (observedPairwiseOps ops) f op array first last (world, []) with
    | none => True
    | some (answer, (after, events)) =>
        PairwiseDefaultDispatch ops f op array first last world events answer after ∧
        PairwiseObservationInvariant f op array world answer after events

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

/-- Full-domain single-iterator mapreduce forwarding. All selected callee
effects, errors and divergence are arbitrary; opaque keyword objects preserve
their actual heterogeneous values and aliases.
Julia source: base/reduce.jl:279-306. -/
def MapreducePublicForwarding : Prop :=
  ∀ (F Op I Kw R W E : Type)
    (selected : F → Op → I → Kw → W → Option (Except E R × W))
    (f : F) (op : Op) (itr : I) (kw : Kw) (world : W),
    let call := fun (args : F × Op × I × Kw) =>
      selected args.1 args.2.1 args.2.2.1 args.2.2.2
    let ops : PublicMapreduceOps (PublicFoldAuditM (F × Op × I × Kw) R W E)
        F Op I Kw R :=
      ⟨fun f op itr kw => observePublicFold call (f, op, itr, kw)⟩
    PublicFoldForwardInvariant (f, op, itr, kw) world
      ((mapreducePublic ops f op itr kw).run (world, []))

/-- Observed dispatch events retain both heterogeneous argument packets and
their actual results. These records describe executed calls without imposing
any correctness laws on the selected dispatch targets. -/
inductive MultiMapreduceEvent (F Op I Tail Kw G R W E : Type) where
  | generator : PublicFoldObservation (F × I × Tail) G W E →
      MultiMapreduceEvent F Op I Tail Kw G R W E
  | reduce : PublicFoldObservation (Op × G × Kw) R W E →
      MultiMapreduceEvent F Op I Tail Kw G R W E

/-- Only an observation adapter: arbitrary callback outcomes and worlds are
appended to the trace, with failed-call mutations preserved. -/
def auditMultiMapreduce {F Op I Tail Kw G R W E : Type}
    (generator : F → I → Tail → W → Option (Except E G × W))
    (reduce : Op → G → Kw → W → Option (Except E R × W)) :
    PublicMultiMapreduceOps
      (ExceptT E (StateT (W × List (MultiMapreduceEvent F Op I Tail Kw G R W E)) Option))
      F Op I Tail Kw G R where
  generator := fun f itr tail => ExceptT.mk fun state => do
    let answer ← generator f itr tail state.1
    pure (answer.1, (answer.2, state.2 ++
      [.generator ⟨(f, itr, tail), state.1, answer.1, answer.2⟩]))
  reduce := fun op generated kw => ExceptT.mk fun state => do
    let answer ← reduce op generated kw state.1
    pure (answer.1, (answer.2, state.2 ++
      [.reduce ⟨(op, generated, kw), state.1, answer.1, answer.2⟩]))

/-- Independent trace provenance and failure atomicity. A terminating trace
has one constructor observation and at most one reduction observation. The
second observation must consume the first one's actual value and world. The
outcome and final world come from the last executed call, including errors.
There is no expected computation obtained by replaying the model body. -/
def MultiMapreduceInvariant {F Op I Tail Kw G R W E : Type}
    (f : F) (op : Op) (itr : I) (tail : Tail) (kw : Kw) (world : W)
    (observed : Option (Except E R ×
      (W × List (MultiMapreduceEvent F Op I Tail Kw G R W E)))) : Prop :=
  match observed with
  | none => True
  | some (result, finalWorld, events) =>
      ∃ constructed : PublicFoldObservation (F × I × Tail) G W E,
        constructed.args = (f, itr, tail) ∧ constructed.before = world ∧
        match constructed.result with
        | .error error => events = [.generator constructed] ∧
            result = .error error ∧ finalWorld = constructed.after
        | .ok generated => ∃ reduced : PublicFoldObservation (Op × G × Kw) R W E,
            events = [.generator constructed, .reduce reduced] ∧
            reduced.args = (op, generated, kw) ∧ reduced.before = constructed.after ∧
            result = reduced.result ∧ finalWorld = reduced.after

/-- All multi-iterator argument tuples, including empty tails, and complete
keyword objects are quantified. The selected constructor can return an object
of any type or mutate/throw/diverge; reduction is likewise unrestricted. The
invariant checks argument preservation, constructor-before-reduction order,
result/world provenance and error suppression, without assuming termination.
Julia source: base/reduce.jl:279-307. -/
def MapreduceMultiProvenance : Prop :=
  ∀ (F Op I Tail Kw G R W E : Type)
    (generator : F → I → Tail → W → Option (Except E G × W))
    (reduce : Op → G → Kw → W → Option (Except E R × W))
    (f : F) (op : Op) (itr : I) (tail : Tail) (kw : Kw) (world : W),
    MultiMapreduceInvariant f op itr tail kw world
      ((mapreduceMultiPublic (auditMultiMapreduce generator reduce)
        f op itr tail kw).run (world, []))

/-- Narrow internal literal-value invariant. Native Int64 return types are
part of the models; mathematical values are inspected only in this property.
Julia source: base/reduce.jl:309-314. -/
def PairwiseBlocksizeValues : Prop :=
  (∀ (F Op : Type) (f : F) (op : Op), (pairwiseBlocksize f op).val = 1024) ∧
  (∀ (f : Abs2Function) (op : PlusFunction), (pairwiseBlocksizeAbs2Plus f op).val = 4096)

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

/-- Exact exception classification and message, independently written from the
documented empty-reduction prohibition. No argument need be callable, numeric,
or inhabit an ordinary element type.
Julia source: base/reduce.jl:318-322. -/
def EmptyFallbackErrors : Prop :=
  ∀ (F Op Ty Tail R : Type) (f : F) (op : Op) (T : Ty) (tail : Tail),
    let expected : Jl R := .error (.argumentError
      "reducing over an empty collection is not allowed; consider supplying `init` to the reducer")
    JuliaLean.base.reduce._empty_reduce_error = expected ∧
    emptyFallback f T = expected ∧ mapemptyFallback f op T = expected ∧
    emptyUnion f tail = expected ∧ mapemptyUnion f op tail = expected

/-- Independent identities for constant empty methods. These methods never
inspect their type arguments, so the existing erased argument representations
cover every matching dispatch type.
Julia source: base/reduce.jl:345-349. -/
def EmptyClosedValues : Prop :=
  reduce_empty_mul_char = .ok "" ∧ reduce_empty_and_bool = .ok true ∧
  reduce_empty_or_bool = .ok false ∧ reduce_empty_and_all = .ok true ∧
  reduce_empty_or_any = .ok false

/-- Call identity is observable even if all selected calls return the same value. -/
inductive EmptyScalarAction where
  | zero
  | one
  | reduce (arithmetic : EmptyArithmetic)

/-- Instrument all open empty scalar dispatch leaves with no semantic laws. -/
def observedEmptyScalarOps {Ty R W E : Type}
    (ops : EmptyScalarOps (AdapterEval W E) Ty R) :
    EmptyScalarOps (PublicFoldAuditM (EmptyScalarAction × Ty) R W E) Ty R where
  zero := fun T => observePublicFold (fun args => ops.zero args.2) (.zero, T)
  one := fun T => observePublicFold (fun args => ops.one args.2) (.one, T)
  reduceEmpty := fun arithmetic T =>
    observePublicFold (fun args => ops.reduceEmpty arithmetic args.2) (.reduce arithmetic, T)

/-- All complete type domains, effects, errors and divergence are quantified.
The invariant detects wrong callable singleton, changed type argument, omitted
or duplicate calls and lost errors/worlds, without assuming callee correctness.
Julia source: base/reduce.jl:342,344,351,354. -/
def EmptyScalarDispatch : Prop :=
  ∀ (Ty R W E : Type) (ops : EmptyScalarOps (AdapterEval W E) Ty R)
    (T : Ty) (world : W),
    let observed := observedEmptyScalarOps ops
    PublicFoldForwardInvariant (.zero, T) world
      ((emptyPlus observed T).run (world, [])) ∧
    PublicFoldForwardInvariant (.one, T) world
      ((emptyTimes observed T).run (world, [])) ∧
    PublicFoldForwardInvariant (.reduce .plus, T) world
      ((emptyAddSum observed T).run (world, [])) ∧
    PublicFoldForwardInvariant (.reduce .times, T) world
      ((emptyMulProd observed T).run (world, []))

/-- Mathematical value and absence of errors, with machine types fixed by the
models' codomains. All source small-type widths are quantified; the necessary
concrete zero/one helpers also have their own invariant for every bit-integer
type. This states numeric identities, not an expected execution of a callee.
Julia source: base/reduce.jl:343,352-356; base/number.jl:364,405. -/
def EmptyNativeIdentities : Prop :=
  (∀ ty : IntTy,
    (emptyNativeZero ty).map (fun n => n.val) = .ok 0 ∧
    (emptyNativeOne ty).map (fun n => n.val) = .ok 1) ∧
  (emptyPlusBool.map (fun n => n.val) = .ok 0) ∧
  (∀ T : SmallSignedType,
    (emptyAddSumSigned T).map (fun n => n.val) = .ok 0 ∧
    (emptyMulProdSigned T).map (fun n => n.val) = .ok 1) ∧
  (∀ T : SmallUnsignedType,
    (emptyAddSumUnsigned T).map (fun n => n.val) = .ok 0 ∧
    (emptyMulProdUnsigned T).map (fun n => n.val) = .ok 1)

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7


/-- Observations retain actual getter objects and all selected-call arguments. -/
inductive EmptyAdapterEvent (V W E : Type) where
  | bottomProperty (call : AdapterCall (BottomAdapter V) V W E)
  | mappingFProperty (call : AdapterCall (MappingRF V V) V W E)
  | mappingRfProperty (call : AdapterCall (MappingRF V V) V W E)
  | filteringProperty (call : AdapterCall (FilteringAdapter V V) V W E)
  | flatteningProperty (call : AdapterCall (FlatteningAdapter V) V W E)
  | flipProperty (call : AdapterCall (FlipAdapter V) V W E)
  | empty (call : AdapterCall (V × V) V W E)
  | mapEmpty (call : AdapterCall (V × V × V) V W E)
  | eltype (call : AdapterCall (V) V W E)
  | absolute (call : AdapterCall (V) V W E)
  | absolute2 (call : AdapterCall (V) V W E)
  | zero (call : AdapterCall (V) V W E)

/-- Instrument every unrestricted callback with failed-call effects retained. -/
def observedEmptyAdapterOps {V W E : Type} (ops : EmptyAdapterOps (AdapterEval W E) V) :
    EmptyAdapterOps (AdapterEval (W × List (EmptyAdapterEvent V W E)) E) V where
  bottomProperty := liftPropertySelection ops.bottomProperty EmptyAdapterEvent.bottomProperty
  mappingFProperty := liftPropertySelection ops.mappingFProperty EmptyAdapterEvent.mappingFProperty
  mappingRfProperty := liftPropertySelection ops.mappingRfProperty EmptyAdapterEvent.mappingRfProperty
  filteringProperty := liftPropertySelection ops.filteringProperty EmptyAdapterEvent.filteringProperty
  flatteningProperty := liftPropertySelection ops.flatteningProperty EmptyAdapterEvent.flatteningProperty
  flipProperty := liftPropertySelection ops.flipProperty EmptyAdapterEvent.flipProperty
  empty := fun a b => observeAdapterEffect (ops.empty a b) (a, b) EmptyAdapterEvent.empty
  mapEmpty := fun f op T => observeAdapterEffect (ops.mapEmpty f op T) (f, op, T) EmptyAdapterEvent.mapEmpty
  eltype := fun T => observeAdapterEffect (ops.eltype T) T EmptyAdapterEvent.eltype
  absolute := fun x => observeAdapterEffect (ops.absolute x) x EmptyAdapterEvent.absolute
  absolute2 := fun x => observeAdapterEffect (ops.absolute2 x) x EmptyAdapterEvent.absolute2
  zero := fun T => observeAdapterEffect (ops.zero T) T EmptyAdapterEvent.zero

/-- Full-domain getter/callee observation invariants: original type and callable identities, source order, observed intermediate-value provenance and all errors/world updates. No property or callback is replayed to compute an expected result. Arbitrary divergence is included without a successful-run premise.
Julia source: base/reduce.jl:358-376. -/
def EmptyAdaptersObservation : Prop :=
  ∀ (V W E : Type) (ops : EmptyAdapterOps (AdapterEval W E) V)
    (bottom : BottomAdapter V) (mapping : MappingRF V V) (filtering : FilteringAdapter V V)
    (flattening : FlatteningAdapter V) (flipped : FlipAdapter V) (op T : V) (world : W),
    let observed := observedEmptyAdapterOps ops
    AdapterObserved (adapterThenTrace (propertySelectionTrace ops.bottomProperty BottomAdapter.rf bottom EmptyAdapterEvent.bottomProperty) fun rf =>
      adapterCallTrace (rf, T) EmptyAdapterEvent.empty) world
      (emptyBottom observed bottom T (world, [])) ∧
    AdapterObserved (adapterThenTrace (propertySelectionTrace ops.mappingFProperty MappingRF.f mapping EmptyAdapterEvent.mappingFProperty) fun f =>
      adapterThenTrace (propertySelectionTrace ops.mappingRfProperty MappingRF.rf mapping EmptyAdapterEvent.mappingRfProperty) fun rf =>
      adapterCallTrace (f, rf, T) EmptyAdapterEvent.mapEmpty) world
      (emptyMapping observed mapping T (world, [])) ∧
    AdapterObserved (adapterThenTrace (propertySelectionTrace ops.filteringProperty FilteringAdapter.rf filtering EmptyAdapterEvent.filteringProperty) fun rf =>
      adapterCallTrace (rf, T) EmptyAdapterEvent.empty) world
      (emptyFiltering observed filtering T (world, [])) ∧
    AdapterObserved (adapterThenTrace (propertySelectionTrace ops.flatteningProperty FlatteningAdapter.rf flattening EmptyAdapterEvent.flatteningProperty) fun rf =>
      adapterThenTrace (adapterCallTrace T EmptyAdapterEvent.eltype) fun elementType =>
      adapterCallTrace (rf, elementType) EmptyAdapterEvent.empty) world
      (emptyFlattening observed flattening T (world, [])) ∧
    AdapterObserved (adapterThenTrace (propertySelectionTrace ops.flipProperty FlipAdapter.f flipped EmptyAdapterEvent.flipProperty) fun f =>
      adapterCallTrace (f, T) EmptyAdapterEvent.empty) world
      (emptyFlip observed flipped T (world, [])) ∧
    AdapterObserved (adapterCallTrace (op, T) EmptyAdapterEvent.empty) world
      (mapemptyIdentity observed op T (world, [])) ∧
    AdapterObserved (adapterThenTrace (adapterCallTrace (op, T) EmptyAdapterEvent.empty) fun value =>
      adapterCallTrace value EmptyAdapterEvent.absolute) world
      (mapemptyAbsolute observed op T (world, [])) ∧
    AdapterObserved (adapterThenTrace (adapterCallTrace (op, T) EmptyAdapterEvent.empty) fun value =>
      adapterCallTrace value EmptyAdapterEvent.absolute2) world
      (mapemptyAbsolute2 observed op T (world, [])) ∧
    AdapterObserved (adapterThenTrace (adapterCallTrace T EmptyAdapterEvent.zero) fun value =>
      adapterCallTrace value EmptyAdapterEvent.absolute) world
      (mapemptyAbsoluteMax observed T (world, [])) ∧
    AdapterObserved (adapterThenTrace (adapterCallTrace T EmptyAdapterEvent.zero) fun value =>
      adapterCallTrace value EmptyAdapterEvent.absolute2) world
      (mapemptyAbsolute2Max observed T (world, []))

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7


/-- Complete original-argument and actual-outcome observations. -/
inductive EmptyIteratorEvent (V W E : Type) where
  | flatteningProperty (call : AdapterCall (FlatteningAdapter V) V W E)
  | mapping (call : AdapterCall (EmptyMapperArgument V × V) (EmptyMappingValue V) W E)
  | emptyMapping (call : AdapterCall (EmptyMappingValue V × V × V) (V) W E)
  | iteratorEltype (call : AdapterCall (V) (V) W E)
  | emptyIter (call : AdapterCall (V × V × V) (V) W E)
  | flatten (call : AdapterCall (V) (EmptyFlattenValue V) W E)
  | flattenConstructor (call : AdapterCall (V) (EmptyFlattenValue V) W E)
  | emptyFlatten (call : AdapterCall (V × EmptyFlattenValue V) (V) W E)
  | eltype (call : AdapterCall (V) (V) W E)
  | empty (call : AdapterCall (V × V) (V) W E)
  | emptyTyped (call : AdapterCall (V × EmptyTypeToken V) (V) W E)

/-- Instrument every open dispatch leaf without assuming any law. -/
def observedEmptyIteratorOps {V W E : Type}
    (ops : EmptyIteratorOps (AdapterEval W E) V) :
    EmptyIteratorOps (AdapterEval (W × List (EmptyIteratorEvent V W E)) E) V where
  selectMapping := ops.selectMapping
  selectFlatten := ops.selectFlatten
  selectFlattenConstructor := ops.selectFlattenConstructor
  flatteningProperty := liftPropertySelection ops.flatteningProperty EmptyIteratorEvent.flatteningProperty
  mapping := fun f op => observeAdapterEffect (ops.mapping f op) (f, op) EmptyIteratorEvent.mapping
  emptyMapping := fun f itr trait => observeAdapterEffect (ops.emptyMapping f itr trait) (f, itr, trait) EmptyIteratorEvent.emptyMapping
  iteratorEltype := fun itr => observeAdapterEffect (ops.iteratorEltype itr) itr EmptyIteratorEvent.iteratorEltype
  emptyIter := fun op itr trait => observeAdapterEffect (ops.emptyIter op itr trait) (op, itr, trait) EmptyIteratorEvent.emptyIter
  flatten := fun itr => observeAdapterEffect (ops.flatten itr) itr EmptyIteratorEvent.flatten
  flattenConstructor := fun itr => observeAdapterEffect (ops.flattenConstructor itr) itr EmptyIteratorEvent.flattenConstructor
  emptyFlatten := fun op itr => observeAdapterEffect (ops.emptyFlatten op itr) (op, itr) EmptyIteratorEvent.emptyFlatten
  eltype := fun itr => observeAdapterEffect (ops.eltype itr) itr EmptyIteratorEvent.eltype
  empty := fun op T => observeAdapterEffect (ops.empty op T) (op, T) EmptyIteratorEvent.empty
  emptyTyped := fun op T => observeAdapterEffect (ops.emptyTyped op T) (op, T) EmptyIteratorEvent.emptyTyped

/-- Independent stored field and parameter-shape metadata invariant. -/
def EmptyMappingFields {V : Type} (f : EmptyMapperArgument V) (op : V)
    (mapped : EmptyMappingValue V) : Prop :=
  match mapped with
  | .custom _ => False
  | .known singleton fields => fields.rf = op ∧
      match f with
      | .ordinary value => singleton = false ∧ fields.f = value
      | .typeValue value => singleton = true ∧ fields.f = value

/-- A known constructor has exact fields and no effects; a selected alternative
has exactly one call with the original mapper and operator. -/
def emptyMappingConstructionTrace {V W E : Type} (selected : Bool)
    (f : EmptyMapperArgument V) (op : V) :
    AdapterTrace (EmptyIteratorEvent V W E) W E (EmptyMappingValue V) :=
  if selected then adapterCallTrace (f, op) EmptyIteratorEvent.mapping
  else fun before events answer after => events = [] ∧ before = after ∧
    ∃ value, answer = .ok value ∧ EmptyMappingFields f op value

/-- Known flatten construction retains the original iterator identity. The two
alternative call stages remain separate so their source timing is observable. -/
def emptyFlattenConstructionTrace {V W E : Type}
    (ops : EmptyIteratorOps (AdapterEval W E) V) (itr : V) :
    AdapterTrace (EmptyIteratorEvent V W E) W E (EmptyFlattenValue V) :=
  if ops.selectFlatten itr then adapterCallTrace itr EmptyIteratorEvent.flatten
  else if ops.selectFlattenConstructor itr then adapterCallTrace itr EmptyIteratorEvent.flattenConstructor
  else adapterPureTrace (.known itr)

/-- Full-domain independent observation invariants, with no getter, constructor,
trait, eltype or reducer correctness assumptions. Errors stop subsequent calls
and preserve all worlds; divergence needs no successful-run premise. The tuple
case inspects only actual static-parameter definedness, never iterator contents.
Julia source: base/reduce.jl:379-392. -/
def EmptyIteratorObservation : Prop :=
  ∀ (V W E : Type) (ops : EmptyIteratorOps (AdapterEval W E) V)
    (f : EmptyMapperArgument V) (op itr trait : V)
    (flattening : FlatteningAdapter V) (staticType : Option (EmptyTypeToken V)) (world : W),
    let observed := observedEmptyIteratorOps ops
    AdapterObserved
      (adapterThenTrace (emptyMappingConstructionTrace (ops.selectMapping f op) f op)
        (fun mapped => adapterCallTrace (mapped, itr, trait) EmptyIteratorEvent.emptyMapping)) world
      (mapemptyIterator observed f op itr trait (world, [])) ∧
    AdapterObserved
      (adapterThenTrace (adapterCallTrace itr EmptyIteratorEvent.iteratorEltype)
        (fun result => adapterCallTrace (op, itr, result) EmptyIteratorEvent.emptyIter)) world
      (emptyIterator observed op itr (world, [])) ∧
    AdapterObserved
      (adapterThenTrace
        (propertySelectionTrace ops.flatteningProperty FlatteningAdapter.rf flattening EmptyIteratorEvent.flatteningProperty) fun rf =>
      adapterThenTrace (emptyFlattenConstructionTrace ops itr) fun flattened =>
      adapterCallTrace (rf, flattened) EmptyIteratorEvent.emptyFlatten) world
      (emptyIteratorFlattening observed flattening itr (world, [])) ∧
    AdapterObserved
      (adapterThenTrace (adapterCallTrace itr EmptyIteratorEvent.eltype)
        (fun T => adapterCallTrace (op, T) EmptyIteratorEvent.empty)) world
      (emptyIteratorHasEltype observed op itr (world, [])) ∧
    AdapterObserved
      (adapterCallTrace (op, match staticType with | none => .bottom | some T => T)
        EmptyIteratorEvent.emptyTyped) world
      (emptyIteratorTuple observed op itr staticType (world, []))

/-- The exact error text contains the source newline, with Julia's indentation
removed. It is independent of every operator/iterator/result type and value.
Julia source: base/reduce.jl:393-395. -/
def EmptyIteratorUnknownError : Prop :=
  ∀ (Op I R : Type) (op : Op) (itr : I),
    emptyIteratorUnknown (R := R) op itr = .error (.argumentError
      "reducing over an empty collection of unknown element type is not allowed.\nYou may be able to prevent this error by supplying an `init` value to the reducer.")


end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

/-- Generic first-element reduction preserves the exact input object even if
the arbitrary operator is non-callable. Julia source: base/reduce.jl:399-411. -/
def FirstIdentity : Prop :=
  ∀ (Op X : Type) (op : Op) (x : X), reduce_first op x = x

/-- Every selected one-call forwarding leaf has original-argument provenance
and retains its outcome/world. Existing polymorphic wrappers are instantiated
at effectful output types, so no purity restriction is introduced. Character
subtypes, arbitrary values, mutable worlds, exceptions and divergence are all
included, with no correctness law. Julia source: base/reduce.jl:413,415,418,421-422. -/
def FirstSelectedForwarding : Prop :=
  ∀ (X R W E : Type) (call : X → W → Option (Except E R × W))
    (x : X) (world : W),
    let observed := observePublicFold call
    PublicFoldForwardInvariant x world
      ((firstTimesChar (⟨observed⟩ : FirstCharOps (PublicFoldAuditM X R W E) X R) x).run (world, [])) ∧
    PublicFoldForwardInvariant x world
      ((reduce_first_add_sum observed x).run (world, [])) ∧
    PublicFoldForwardInvariant x world
      ((reduce_first_mul_prod observed x).run (world, [])) ∧
    PublicFoldForwardInvariant x world
      ((reduce_first_vcat observed x).run (world, [])) ∧
    PublicFoldForwardInvariant x world
      ((reduce_first_hcat observed x).run (world, []))

/-- Independent mathematical values for the installed concrete conversions,
over every accepted width and source value. Native result types are enforced
by the model codomains. Julia source: base/reduce.jl:412,416-420. -/
def FirstNativeValues : Prop :=
  (∀ x : Bool, (firstPlusBool x).val = if x then 1 else 0) ∧
  (∀ x : SmallSigned, (firstAddSumSigned x).val = x.val.value.val ∧
    (firstMulProdSigned x).val = x.val.value.val) ∧
  (∀ x : SmallUnsigned, (firstAddSumUnsigned x).val = x.val.value.val ∧
    (firstMulProdUnsigned x).val = x.val.value.val)

/-- Independent observations of getter and selected first-element dispatch. -/
inductive FirstFlipEvent (F X R W E : Type) where
  | property (call : AdapterCall (FlipAdapter F) F W E)
  | first (call : AdapterCall (F × X) R W E)

/-- Instrument selected f reads and first calls while retaining their behavior. -/
def observedFirstFlipOps {F X R W E : Type}
    (ops : FlipFirstOps (AdapterEval W E) F X R) :
    FlipFirstOps (AdapterEval (W × List (FirstFlipEvent F X R W E)) E) F X R where
  fProperty := liftPropertySelection ops.fProperty FirstFlipEvent.property
  first := fun f x => observeAdapterEffect (ops.first f x) (f, x) FirstFlipEvent.first

/-- Full-domain stored/custom getter provenance; the invocation receives the
observed callable and original input. All callback worlds and errors remain
observable and errors stop subsequent calls. Julia source: base/reduce.jl:423. -/
def FirstFlipObservation : Prop :=
  ∀ (F X R W E : Type) (ops : FlipFirstOps (AdapterEval W E) F X R)
    (op : FlipAdapter F) (x : X) (world : W),
    AdapterObserved
      (adapterThenTrace
        (propertySelectionTrace ops.fProperty FlipAdapter.f op FirstFlipEvent.property)
        (fun f => adapterCallTrace (f, x) FirstFlipEvent.first)) world
      (firstFlip (observedFirstFlipOps ops) op x (world, []))

/-- Observations preserve the potentially different mapped and final types. -/
inductive MapreduceFirstEvent (F Op X M R W E : Type) where
  | map (call : AdapterCall (F × X) M W E)
  | first (call : AdapterCall (Op × M) R W E)

/-- Both unrestricted dispatch leaves are merely instrumented. -/
def observedMapreduceFirstOps {F Op X M R W E : Type}
    (ops : MapreduceFirstOps (AdapterEval W E) F Op X M R) :
    MapreduceFirstOps
      (AdapterEval (W × List (MapreduceFirstEvent F Op X M R W E)) E) F Op X M R where
  map := fun f x => observeAdapterEffect (ops.map f x) (f, x) MapreduceFirstEvent.map
  first := fun op value => observeAdapterEffect (ops.first op value)
    (op, value) MapreduceFirstEvent.first

/-- Independent observed provenance: exactly one map precedes any first call,
which consumes its actual result and world with the original operator. Mapping
errors suppress first dispatch. No expected computation is obtained by replaying
the model, and no callback laws or successful-run premises are assumed.
Julia source: base/reduce.jl:425-435. -/
def MapreduceFirstObservation : Prop :=
  ∀ (F Op X M R W E : Type) (ops : MapreduceFirstOps (AdapterEval W E) F Op X M R)
    (f : F) (op : Op) (x : X) (world : W),
    AdapterObserved
      (adapterThenTrace (adapterCallTrace (f, x) MapreduceFirstEvent.map)
        (fun value => adapterCallTrace (op, value) MapreduceFirstEvent.first)) world
      (mapreduceFirst (observedMapreduceFirstOps ops) f op x (world, []))

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

/-- Original call arguments, including source inbounds context markers. -/
inductive LinearAction (V F O A I T : Type) where
  | indices (array : A)
  | length (indices : I)
  | equalLiteral (value : V) (literal : JInt .i64)
  | lessLiteral (value : V) (literal : JInt .i64)
  | less (left right : LinearValue V)
  | addLiteral (value : V) (literal : JInt .i64) (inbounds : Bool)
  | firstIndex (indices : I) (inbounds : Bool)
  | lastIndex (indices : I) (inbounds : Bool)
  | getindex (array : A) (index : LinearValue V) (inbounds : Bool)
  | iteratorEltype (array : A)
  | empty (f : F) (op : O) (array : A) (trait : T)
  | single (f : F) (op : O) (element : LinearValue V)
  | map (f : F) (element : LinearValue V)
  | reduce (op : O) (left right : LinearValue V)
  | impl (f : F) (op : O) (array : A) (first last : LinearValue V)

/-- Observed dynamic return objects remain distinct from condition results. -/
inductive LinearReply (V C I T : Type) where
  | value (value : LinearValue V)
  | condition (result : Bool ⊕ C)
  | indices (object : I)
  | trait (object : T)

structure LinearEvent (W E V C F O A I T : Type) where
  action : LinearAction V F O A I T
  before : W
  answer : Except (FoldError E) (LinearReply V C I T)
  after : W

/-- Observe actual selected results/worlds without any correctness law. -/
def observeLinearCall {W E V C F O A I T R : Type}
    (call : FoldEval W (FoldError E) R) (action : LinearAction V F O A I T)
    (reply : R → LinearReply V C I T) :
    FoldEval (W × List (LinearEvent W E V C F O A I T)) (FoldError E) R :=
  ExceptT.mk fun state => do
    let (answer, after) ← call.run state.1
    pure (answer, (after, state.2 ++ [⟨action, state.1, answer.map reply, after⟩]))

/-- Every open call is observed; known native arithmetic remains concrete. -/
def observedLinearOps {W E V C F O A I T : Type}
    (ops : LinearMapreduceOps W E V C F O A I T) :
    LinearMapreduceOps (W × List (LinearEvent W E V C F O A I T)) E V C F O A I T where
  indices := fun a => observeLinearCall (ops.indices a) (.indices a) .indices
  length := fun i => observeLinearCall (ops.length i) (.length i) .value
  equalLiteral := fun n k => observeLinearCall (ops.equalLiteral n k) (.equalLiteral n k) .condition
  lessLiteral := fun n k => observeLinearCall (ops.lessLiteral n k) (.lessLiteral n k) .condition
  less := fun x y => observeLinearCall (ops.less x y) (.less x y) .condition
  addLiteral := fun n k c => observeLinearCall (ops.addLiteral n k c) (.addLiteral n k c) .value
  firstIndex := fun i c => observeLinearCall (ops.firstIndex i c) (.firstIndex i c) .value
  lastIndex := fun i c => observeLinearCall (ops.lastIndex i c) (.lastIndex i c) .value
  getindex := fun a i c => observeLinearCall (ops.getindex a i c) (.getindex a i c) .value
  iteratorEltype := fun a => observeLinearCall (ops.iteratorEltype a) (.iteratorEltype a) .trait
  empty := fun f op a t => observeLinearCall (ops.empty f op a t) (.empty f op a t) .value
  single := fun f op x => observeLinearCall (ops.single f op x) (.single f op x) .value
  map := fun f x => observeLinearCall (ops.map f x) (.map f x) .value
  reduce := fun op x y => observeLinearCall (ops.reduce op x y) (.reduce op x y) .value
  impl := fun f op a first last => observeLinearCall (ops.impl f op a first last) (.impl f op a first last) .value

/-- Pure machinery cannot invent or discard a mutable-world transition. -/
def LinearWorldChain {W E V C F O A I T : Type} (start : W) :
    List (LinearEvent W E V C F O A I T) → W → Prop
  | [], after => after = start
  | event :: rest, after => event.before = start ∧ LinearWorldChain event.after rest after

/-- Lifecycle ranks do not compute a model result or replay a branch. -/
def linearActionPhase {V F O A I T : Type} : LinearAction V F O A I T → Nat
  | .indices _ => 0
  | .length _ => 1
  | .equalLiteral _ _ | .lessLiteral _ _ => 2
  | .empty _ _ _ _ | .single _ _ _ | .impl _ _ _ _ _ => 4
  | _ => 3

/-- These non-loop stages are each called at most once. -/
def linearActionTag {V F O A I T : Type} : LinearAction V F O A I T → Nat
  | .indices _ => 0 | .length _ => 1 | .firstIndex _ _ => 2
  | .iteratorEltype _ => 3 | .empty _ _ _ _ => 4 | .single _ _ _ => 5
  | .impl _ _ _ _ _ => 6 | _ => 7

/-- Original object identities, native literals and exact inbounds contexts. -/
def LinearActionIdentity {V F O A I T : Type} (f : F) (op : O) (array : A) :
    LinearAction V F O A I T → Prop
  | .indices a | .iteratorEltype a => a = array
  | .getindex a _ context => a = array ∧ context = true
  | .map actual _ => actual = f
  | .reduce actual _ _ => actual = op
  | .empty actualF actualOp a _ | .impl actualF actualOp a _ _ =>
      actualF = f ∧ actualOp = op ∧ a = array
  | .single actualF actualOp _ => actualF = f ∧ actualOp = op
  | .equalLiteral _ k => k.val = 0 ∨ k.val = 1
  | .lessLiteral _ k => k.val = 16
  | .addLiteral _ k context => k.val = 1 ∧ context = true
  | .lastIndex _ context => context = false
  | .less (.native _) (.native _) => False
  | _ => True

/-- Obtain indices first, then measure that exact object. Every later index
query keeps the same original indices object, including mutable aliases. -/
def LinearPrelude {W E V C F O A I T : Type} (array : A)
    (events : List (LinearEvent W E V C F O A I T)) : Prop :=
  ∃ first rest, events = first :: rest ∧ first.action = .indices array ∧
    match first.answer with
    | .error _ => rest = []
    | .ok (.indices indices) =>
        ∃ next later, rest = next :: later ∧ next.action = .length indices ∧
          ∀ event ∈ rest, match event.action with
            | .length actual | .firstIndex actual _ | .lastIndex actual _ => actual = indices
            | _ => True
    | _ => False

/-- Native-length branches have independent action families, selected by
mathematical integer comparisons rather than the model's native operations. -/
def LinearNativeAllowed {V F O A I T : Type} (n : JInt .i64)
    (action : LinearAction V F O A I T) : Prop :=
  if n.val = 0 then
    match action with | .iteratorEltype _ | .empty _ _ _ _ => True | _ => False
  else if n.val = 1 then
    match action with | .firstIndex _ true | .getindex _ _ true | .single _ _ _ => True | _ => False
  else if n.val < 16 then
    match action with
    | .firstIndex _ true | .getindex _ _ true | .addLiteral _ _ true
      | .lastIndex _ false | .less _ _ | .map _ _ | .reduce _ _ _ => True
    | _ => False
  else
    match action with | .firstIndex _ false | .lastIndex _ false | .impl _ _ _ _ _ => True | _ => False

/-- Successful array-read values in their observed order. -/
def linearReadValues {W E V C F O A I T : Type}
    (events : List (LinearEvent W E V C F O A I T)) : List (LinearValue V) :=
  events.filterMap fun event => match event.action, event.answer with
    | .getindex _ _ _, .ok (.value value) => some value
    | _, _ => none

/-- Mapper arguments include even the last failed invocation. -/
def linearMappedInputs {W E V C F O A I T : Type}
    (events : List (LinearEvent W E V C F O A I T)) : List (LinearValue V) :=
  events.filterMap fun event => match event.action with | .map _ value => some value | _ => none

/-- Successful mapped values, used only as observed data. -/
def linearMappedValues {W E V C F O A I T : Type}
    (events : List (LinearEvent W E V C F O A I T)) : List (LinearValue V) :=
  events.filterMap fun event => match event.action, event.answer with
    | .map _ _, .ok (.value value) => some value
    | _, _ => none

/-- Reduction operands and optional successful output. No operation is run. -/
def linearReducedValues {W E V C F O A I T : Type}
    (events : List (LinearEvent W E V C F O A I T)) :
    List (LinearValue V × LinearValue V × Option (LinearValue V)) :=
  events.filterMap fun event => match event.action with
    | .reduce _ left right => some (left, right,
        match event.answer with | .ok (.value value) => some value | _ => none)
    | _ => none

/-- Only these leaves may originate the returned value. -/
def linearValueProducer {V F O A I T : Type} : LinearAction V F O A I T → Bool
  | .empty _ _ _ _ | .single _ _ _ | .reduce _ _ _ | .impl _ _ _ _ _ => true
  | _ => false

/-- Independent dataflow: mapped arguments form a prefix of successful reads.
Each reduction uses the latest mapped value on the right and the preceding
reduction result (or first mapped value) on the left. Successful return is the
last value-producing leaf; no expected result is computed by replaying code. -/
def LinearDataflow {W E V C F O A I T : Type} (op : O)
    (events : List (LinearEvent W E V C F O A I T))
    (answer : Except (FoldError E) (LinearValue V)) : Prop :=
  (∃ suffix, linearReadValues events = linearMappedInputs events ++ suffix) ∧
  (∀ earlier event later left right, events = earlier ++ event :: later →
    event.action = .reduce op left right →
    let mapped := linearMappedValues earlier
    let reduced := linearReducedValues earlier
    mapped.length = reduced.length + 2 ∧ mapped.getLast? = some right ∧
      (match reduced.getLast? with
       | none => mapped.head? = some left
       | some previous => previous.2.2 = some left)) ∧
  (∀ value, answer = .ok value →
    ∃ earlier event later, events = earlier ++ event :: later ∧
      linearValueProducer event.action = true ∧ event.answer = .ok (.value value) ∧
      (∀ next ∈ later, linearValueProducer next.action = false) ∧
      (match event.action with
       | .reduce _ _ _ => linearMappedInputs events = linearReadValues events
       | _ => True))

/-- Full independent trace invariant for every terminating observation.
Selected errors and non-Bool conditions terminate immediately; primitive native
operations introduce no other errors. Mutations, phases, object identities,
source branch families and reduction dataflow are preserved. -/
def LinearObservationInvariant {W E V C F O A I T : Type}
    (f : F) (op : O) (array : A) (world : W)
    (observed : Option (Except (FoldError E) (LinearValue V) ×
      (W × List (LinearEvent W E V C F O A I T)))) : Prop :=
  match observed with
  | none => True
  | some (answer, after, events) =>
      LinearWorldChain world events after ∧ LinearPrelude array events ∧
      (∀ event ∈ events, LinearActionIdentity f op array event.action) ∧
      events.Pairwise (fun x y => linearActionPhase x.action ≤ linearActionPhase y.action) ∧
      (∀ tag, tag < 7 → (events.countP (fun event => linearActionTag event.action == tag)) ≤ 1) ∧
      (∀ earlier event later error, events = earlier ++ event :: later → event.answer = .error error →
        later = [] ∧ answer = .error error) ∧
      (∀ earlier event later nonBool, events = earlier ++ event :: later →
        event.answer = .ok (.condition (.inr nonBool)) → later = [] ∧ answer = .error .typeError) ∧
      (∀ error, answer = .error error →
        ∃ earlier event, events = earlier ++ [event] ∧
          (event.answer = .error error ∨
            (error = .typeError ∧ ∃ nonBool, event.answer = .ok (.condition (.inr nonBool))))) ∧
      (∀ earlier event later indices n, events = earlier ++ event :: later →
        event.action = .length indices → event.answer = .ok (.value (.native n)) →
        ∀ next ∈ later, LinearNativeAllowed n next.action) ∧
      LinearDataflow op events answer

/-- Complete IndexLinear domain: arbitrary abstract arrays, dynamic length and
index results (including negative/non-native values), stateful or malformed
comparisons, mapper/reducer changes, exceptions and divergence. No callback
correctness, arithmetic, indexing, finiteness or termination law is assumed.
Julia source: base/reduce.jl:439-460; documentation: base/reduce.jl:466-495. -/
def LinearMapreduceObservation : Prop :=
  ∀ (W E V C F O A I T : Type) (ops : LinearMapreduceOps W E V C F O A I T)
    (f : F) (op : O) (array : A) (world : W),
    LinearObservationInvariant f op array world
      ((mapreduceLinear (observedLinearOps ops) f op array).run (world, []))

/-- Trait lookup and selected method observations have separate result types. -/
inductive ArrayDispatchEvent (F O A Style Result W E : Type) where
  | trait (call : AdapterCall A Style W E)
  | reduce (call : AdapterCall (F × O × Style × A) Result W E)

/-- Full-domain trait/result provenance, including arbitrary trait objects and
all throwing, mutable or divergent selected calls. Julia source: base/reduce.jl:437. -/
def ArrayMapreduceDispatchObservation : Prop :=
  ∀ (F O A Style Result W E : Type)
    (ops : ArrayMapreduceDispatchOps (AdapterEval W E) F O A Style Result)
    (f : F) (op : O) (array : A) (world : W),
    let audited : ArrayMapreduceDispatchOps
        (AdapterEval (W × List (ArrayDispatchEvent F O A Style Result W E)) E) F O A Style Result :=
      { indexStyle := fun a => observeAdapterEffect (ops.indexStyle a) a ArrayDispatchEvent.trait
        reduce := fun f op style a => observeAdapterEffect (ops.reduce f op style a)
          (f, op, style, a) ArrayDispatchEvent.reduce }
    AdapterObserved
      (adapterThenTrace (adapterCallTrace array ArrayDispatchEvent.trait)
        (fun style => adapterCallTrace (f, op, style, array) ArrayDispatchEvent.reduce)) world
      ((mapreduceArrayDispatch audited f op array).run (world, []))

/-- Every Number subtype and arbitrary mapper/operator reaches the selected
mapreduce_first once with exact original values; effects/errors/results and
divergence are preserved. Julia source: base/reduce.jl:462. -/
def NumberMapreduceObservation : Prop :=
  ∀ (F O N Result W E : Type)
    (first : F → O → N → W → Option (Except E Result × W))
    (f : F) (op : O) (number : N) (world : W),
    let call := fun (args : F × O × N) => first args.1 args.2.1 args.2.2
    let ops : NumberMapreduceOps (PublicFoldAuditM (F × O × N) Result W E) F O N Result :=
      ⟨fun f op n => observePublicFold call (f, op, n)⟩
    PublicFoldForwardInvariant (f, op, number) world
      ((mapreduceNumber ops f op number).run (world, []))

/-- Full-domain Cartesian forwarding passes the original mapper/operator/array
once with no added init argument. Selected results, mutations, errors and
nontermination are unrestricted. Julia source: base/reduce.jl:464. -/
def CartesianMapreduceObservation : Prop :=
  ∀ (F O A Result W E : Type)
    (fold : F → O → A → W → Option (Except E Result × W))
    (f : F) (op : O) (array : A) (world : W),
    let call := fun (args : F × O × A) => fold args.1 args.2.1 args.2.2
    let ops : CartesianMapreduceOps (PublicFoldAuditM (F × O × A) Result W E) F O A Result :=
      ⟨fun f op a => observePublicFold call (f, op, a)⟩
    PublicFoldForwardInvariant (f, op, array) world
      ((mapreduceCartesian ops f op array).run (world, []))

/-- Public reduce retains actual identity and the entire keyword object (Pairs
over a NamedTuple), including unsupported keywords. Every selected callback,
world, exception and divergent case is quantified without laws.
Julia source: base/reduce.jl:501; doc/src/manual/functions.md:849-860. -/
def PublicReduceObservation : Prop :=
  ∀ (O I Kw Result W E : Type)
    (mapreduce : IdentityFn → O → I → Kw → W → Option (Except E Result × W))
    (op : O) (itr : I) (kw : Kw) (world : W),
    let call := fun (args : IdentityFn × O × I × Kw) =>
      mapreduce args.1 args.2.1 args.2.2.1 args.2.2.2
    let ops : PublicReduceOps (PublicFoldAuditM (IdentityFn × O × I × Kw) Result W E) O I Kw Result :=
      ⟨fun f op itr kw => observePublicFold call (f, op, itr, kw)⟩
    PublicFoldForwardInvariant (.identity, op, itr, kw) world
      ((reducePublic ops op itr kw).run (world, []))

/-- Numeric reduce preserves exact Number/reference identity independently of
all supplied operator objects, including non-callable values. It performs no selected
reduce_first or binary-operator call. Julia source: base/reduce.jl:503. -/
def ReduceNumberIdentity : Prop :=
  ∀ (O N : Type) (op₁ op₂ : O) (number : N),
    reduceNumber op₁ number = number ∧ reduceNumber op₂ number = number

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

/-- Call observations distinguish each public target and retain concrete
singleton identities independently of callback return values. -/
inductive ReductionPublicEvent (F I Kw R W E : Type) where
  | mapped (call : AdapterCall (F × ReductionSingleton × I × Kw) R W E)
  | identityMap (call : AdapterCall (IdentityFn × ReductionSingleton × I × Kw) R W E)
  | sum (call : AdapterCall (IdentityFn × I × Kw) R W E)
  | extrema (call : AdapterCall (IdentityFn × I × Kw) R W E)

/-- Instrument arbitrary selected callees without imposing laws. -/
def observedReductionPublicOps {F I Kw R W E : Type}
    (ops : ReductionPublicOps (AdapterEval W E) F I Kw R) :
    ReductionPublicOps
      (AdapterEval (W × List (ReductionPublicEvent F I Kw R W E)) E) F I Kw R where
  mapreduce := fun f op itr kw => observeAdapterEffect (ops.mapreduce f op itr kw)
    (f, op, itr, kw) ReductionPublicEvent.mapped
  mapreduceIdentity := fun f op itr kw => observeAdapterEffect (ops.mapreduceIdentity f op itr kw)
    (f, op, itr, kw) ReductionPublicEvent.identityMap
  sumIdentity := fun f itr kw => observeAdapterEffect (ops.sumIdentity f itr kw)
    (f, itr, kw) ReductionPublicEvent.sum
  extremaIdentity := fun f itr kw => observeAdapterEffect (ops.extremaIdentity f itr kw)
    (f, itr, kw) ReductionPublicEvent.extrema

/-- Complete source domains and keyword objects are retained: immutable Pairs
refer to their NamedTuple values and aliases without inspection or conversion.
Every wrapper makes one exact public call and preserves observed results,
exceptions and world changes. Arbitrary callbacks may diverge; no termination
or correctness law is assumed. The expected outcomes are read from call
observations, never from an expected execution of the model body.
Julia source: base/reduce.jl:546,575,602,631,659,686,718,750,779. -/
def ReductionPublicForwarding : Prop :=
  ∀ (F I Kw R W E : Type) (ops : ReductionPublicOps (AdapterEval W E) F I Kw R)
    (f : F) (itr : I) (kw : Kw) (world : W),
    let observed := observedReductionPublicOps ops
    AdapterObserved (adapterCallTrace (f, .addSum, itr, kw) ReductionPublicEvent.mapped) world
      (sumMapped observed f itr kw (world, [])) ∧
    AdapterObserved (adapterCallTrace (.identity, itr, kw) ReductionPublicEvent.sum) world
      (sumPublic observed itr kw (world, [])) ∧
    AdapterObserved (adapterCallTrace (f, .mulProd, itr, kw) ReductionPublicEvent.mapped) world
      (prodMapped observed f itr kw (world, [])) ∧
    AdapterObserved (adapterCallTrace (.identity, .mulProd, itr, kw) ReductionPublicEvent.identityMap) world
      (prodPublic observed itr kw (world, [])) ∧
    AdapterObserved (adapterCallTrace (f, .maximum, itr, kw) ReductionPublicEvent.mapped) world
      (maximumMapped observed f itr kw (world, [])) ∧
    AdapterObserved (adapterCallTrace (f, .minimum, itr, kw) ReductionPublicEvent.mapped) world
      (minimumMapped observed f itr kw (world, [])) ∧
    AdapterObserved (adapterCallTrace (.identity, .maximum, itr, kw) ReductionPublicEvent.identityMap) world
      (maximumPublic observed itr kw (world, [])) ∧
    AdapterObserved (adapterCallTrace (.identity, .minimum, itr, kw) ReductionPublicEvent.identityMap) world
      (minimumPublic observed itr kw (world, [])) ∧
    AdapterObserved (adapterCallTrace (.identity, itr, kw) ReductionPublicEvent.extrema) world
      (extremaPublic observed itr kw (world, []))

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.BootCov JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

/-- Complete selected-call observations retain arbitrary mutable worlds, errors and returned objects. -/
inductive KeywordEvent (W E Atom A R : Type) where
  | empty (call : AdapterCall (BoolKeywordPacket Atom) (JVal) W (FoldError (KeywordFailure E)))
  | donePairs (call : AdapterCall (BoolKeywordPacket Atom) (JVal) W (FoldError (KeywordFailure E)))
  | keysPairs (call : AdapterCall (BoolKeywordPacket Atom) (KeywordKeys Atom) W (FoldError (KeywordFailure E)))
  | keysNamedTuple (call : AdapterCall (BoolKeywordPacket Atom) (KeywordKeys Atom) W (FoldError (KeywordFailure E)))
  | doneKeys (call : AdapterCall (KeywordKeys Atom) (JVal) W (FoldError (KeywordFailure E)))
  | iteratePairs (call : AdapterCall (BoolKeywordPacket Atom) (Option Unit) W (FoldError (KeywordFailure E)))
  | iterateKeys (call : AdapterCall (KeywordKeys Atom) (Option (FlattenTransformResult (KeywordValue Atom))) W (FoldError (KeywordFailure E)))
  | iterateOther (call : AdapterCall (KeywordValue Atom) (Option (FlattenTransformResult (KeywordValue Atom))) W (FoldError (KeywordFailure E)))
  | keyTupleBinary (call : AdapterCall (FoldTuple (String ⊕ Atom) × JInt .i64) (Option (FlattenTransformResult (KeywordValue Atom))) W (FoldError (KeywordFailure E)))
  | keyTupleLength (call : AdapterCall (FoldTuple (String ⊕ Atom)) (KeywordValue Atom) W (FoldError (KeywordFailure E)))
  | keyTupleIndex (call : AdapterCall (FoldTuple (String ⊕ Atom) × JInt .i64) (KeywordValue Atom) W (FoldError (KeywordFailure E)))
  | keyTupleCompare (call : AdapterCall (KeywordValue Atom × KeywordValue Atom) (Bool ⊕ KeywordValue Atom) W (FoldError (KeywordFailure E)))
  | pairsElement (call : AdapterCall (BoolKeywordPacket Atom × KeywordValue Atom) Unit W (FoldError (KeywordFailure E)))
  | getindexNamedTuple (call : AdapterCall (BoolKeywordPacket Atom × KeywordValue Atom) (KeywordValue Atom) W (FoldError (KeywordFailure E)))
  | getindexOther (call : AdapterCall (BoolKeywordPacket Atom × KeywordValue Atom) (KeywordValue Atom) W (FoldError (KeywordFailure E)))
  | indexed (call : AdapterCall (KeywordValue Atom × JInt .i64 × Option (KeywordValue Atom)) (KeywordValue Atom) W (FoldError (KeywordFailure E)))
  | count (call : AdapterCall (A) (R) W (FoldError (KeywordFailure E)))
  | reduce (call : AdapterCall (ReductionSingleton × A × BoolKeywordPacket Atom) (R) W (FoldError (KeywordFailure E)))

/-- Instrument only genuinely selected custom alternatives; base selection stays base. -/
def keywordObserveSelection {Args Out W E Event : Type}
    (selection : KeywordSelection (AdapterEval W E) Args Out)
    (tag : AdapterCall Args Out W E → Event) :
    KeywordSelection (AdapterEval (W × List Event) E) Args Out :=
  match selection with
  | .base => .base
  | .custom call => .custom fun args => observeAdapterEffect (call args) args tag

/-- Lift each selected callee once while retaining every default branch. Only
indexedIterate and fields of raw are used by the computation; unused transformer,
fold and property slots are canonical inert values, not assumptions about callbacks. -/
def keywordInstrument {W E Atom A R : Type} (ops : BoolSumOps W E Atom A R) :
    BoolSumOps (W × List (KeywordEvent W E Atom A R)) E Atom A R :=
  { empty := keywordObserveSelection ops.empty .empty
    donePairs := keywordObserveSelection ops.donePairs .donePairs
    keysPairs := keywordObserveSelection ops.keysPairs .keysPairs
    keysNamedTuple := keywordObserveSelection ops.keysNamedTuple .keysNamedTuple
    doneKeys := keywordObserveSelection ops.doneKeys .doneKeys
    iteratePairs := keywordObserveSelection ops.iteratePairs .iteratePairs
    iterateKeys := keywordObserveSelection ops.iterateKeys .iterateKeys
    iterateOther := fun object => observeAdapterEffect (ops.iterateOther object) object .iterateOther
    keyTupleBinary := keywordObserveSelection ops.keyTupleBinary .keyTupleBinary
    keyTupleLength := keywordObserveSelection ops.keyTupleLength .keyTupleLength
    keyTupleIndex := keywordObserveSelection ops.keyTupleIndex .keyTupleIndex
    keyTupleCompare := fun a b => observeAdapterEffect (ops.keyTupleCompare a b) (a,b) .keyTupleCompare
    pairsElement := keywordObserveSelection ops.pairsElement .pairsElement
    getindexNamedTuple := keywordObserveSelection ops.getindexNamedTuple .getindexNamedTuple
    getindexOther := fun packet key => observeAdapterEffect (ops.getindexOther packet key) (packet, key) .getindexOther
    raw :=
      { transform := fun x y => pure (.pair x y)
        indexedIterate := fun object index state => observeAdapterEffect
          (ops.raw.indexedIterate object index state) (object, index, state) .indexed
        fields := fun state object => ops.raw.fields state.1 object
        fold := fun _ acc _ => pure acc }
    count := fun a => observeAdapterEffect (ops.count a) a .count
    reduce := fun f a packet => observeAdapterEffect (ops.reduce f a packet) (f, a, packet) .reduce }

/-- Project the observed before without invoking any callee. -/
def KeywordEvent.before {W E Atom A R : Type} : KeywordEvent W E Atom A R → W
  | .empty c => c.before
  | .donePairs c => c.before
  | .keysPairs c => c.before
  | .keysNamedTuple c => c.before
  | .doneKeys c => c.before
  | .iteratePairs c => c.before
  | .iterateKeys c => c.before
  | .iterateOther c => c.before
  | .keyTupleBinary c => c.before
  | .keyTupleLength c => c.before
  | .keyTupleIndex c => c.before
  | .keyTupleCompare c => c.before
  | .pairsElement c => c.before
  | .getindexNamedTuple c => c.before
  | .getindexOther c => c.before
  | .indexed c => c.before
  | .count c => c.before
  | .reduce c => c.before

/-- Project the observed after without invoking any callee. -/
def KeywordEvent.after {W E Atom A R : Type} : KeywordEvent W E Atom A R → W
  | .empty c => c.after
  | .donePairs c => c.after
  | .keysPairs c => c.after
  | .keysNamedTuple c => c.after
  | .doneKeys c => c.after
  | .iteratePairs c => c.after
  | .iterateKeys c => c.after
  | .iterateOther c => c.after
  | .keyTupleBinary c => c.after
  | .keyTupleLength c => c.after
  | .keyTupleIndex c => c.after
  | .keyTupleCompare c => c.after
  | .pairsElement c => c.after
  | .getindexNamedTuple c => c.after
  | .getindexOther c => c.after
  | .indexed c => c.after
  | .count c => c.after
  | .reduce c => c.after

/-- Project the observed failure without invoking any callee. -/
def KeywordEvent.failure {W E Atom A R : Type} : KeywordEvent W E Atom A R → Option (FoldError (KeywordFailure E))
  | .empty c => match c.answer with | .ok _ => none | .error e => some e
  | .donePairs c => match c.answer with | .ok _ => none | .error e => some e
  | .keysPairs c => match c.answer with | .ok _ => none | .error e => some e
  | .keysNamedTuple c => match c.answer with | .ok _ => none | .error e => some e
  | .doneKeys c => match c.answer with | .ok _ => none | .error e => some e
  | .iteratePairs c => match c.answer with | .ok _ => none | .error e => some e
  | .iterateKeys c => match c.answer with | .ok _ => none | .error e => some e
  | .iterateOther c => match c.answer with | .ok _ => none | .error e => some e
  | .keyTupleBinary c => match c.answer with | .ok _ => none | .error e => some e
  | .keyTupleLength c => match c.answer with | .ok _ => none | .error e => some e
  | .keyTupleIndex c => match c.answer with | .ok _ => none | .error e => some e
  | .keyTupleCompare c => match c.answer with | .ok _ => none | .error e => some e
  | .pairsElement c => match c.answer with | .ok _ => none | .error e => some e
  | .getindexNamedTuple c => match c.answer with | .ok _ => none | .error e => some e
  | .getindexOther c => match c.answer with | .ok _ => none | .error e => some e
  | .indexed c => match c.answer with | .ok _ => none | .error e => some e
  | .count c => match c.answer with | .ok _ => none | .error e => some e
  | .reduce c => match c.answer with | .ok _ => none | .error e => some e

/-- Every event retains original externally supplied objects at their source call sites. -/
def KeywordEvent.originalArgs {W E Atom A R : Type} (a : A) (kw : BoolKeywordPacket Atom) :
    KeywordEvent W E Atom A R → Prop
  | .empty c => c.args = kw
  | .donePairs c => c.args = kw
  | .keysPairs c => c.args = kw
  | .keysNamedTuple c => c.args = kw
  | .iteratePairs c => c.args = kw
  | .keyTupleBinary c => c.args.2 = JuliaLean.base.int.lit .i64 1
  | .keyTupleIndex c => c.args.2 = JuliaLean.base.int.lit .i64 1
  | .keyTupleCompare c => c.args.1 = .native (JuliaLean.base.int.lit .i64 1)
  | .pairsElement c => c.args.1 = kw
  | .getindexNamedTuple c => c.args.1 = kw
  | .getindexOther c => c.args.1 = kw
  | .indexed c => c.args.2.1 = JuliaLean.base.int.lit .i64 1 ∨
      c.args.2.1 = JuliaLean.base.int.lit .i64 2
  | .count c => c.args = a
  | .reduce c => c.args = (.addSum, a, kw)
  | _ => True

/-- A reduction call is terminal. Its actual result, error and mutated world survive unchanged. -/
def KeywordEvent.terminal {W E Atom A R : Type} : KeywordEvent W E Atom A R →
    Option (Except (FoldError (KeywordFailure E)) R × W)
  | .count c => some (c.answer, c.after)
  | .reduce c => some (c.answer, c.after)
  | _ => none

/-- The short-circuit condition rejects a non-Bool non-missing isdone hint;
a selected isempty result rejects missing as well. Recognition is independent
of the implementation's Bool assertion. -/
def KeywordEvent.badHint {W E Atom A R : Type} : KeywordEvent W E Atom A R → Bool
  | .empty c => match c.answer with | .ok (.bool _) => false | .ok _ => true | .error _ => false
  | .keyTupleCompare c => match c.answer with | .ok (.inr _) => true | _ => false
  | .donePairs c | .doneKeys c =>
    match c.answer with
    | .ok (.bool _) => false
    | .ok (.obj "Missing" []) => false
    | .ok _ => true
    | .error _ => false
  | _ => false

/-- Independent world continuity, exact incoming objects, immediate callback-error
propagation and terminal-reduction rules. No callback is rerun, constrained, or
assumed successful. Pure local errors may terminate between observed calls. -/
def keywordEventChain {W E Atom A R : Type} (a : A) (kw : BoolKeywordPacket Atom)
    (answer : Except (FoldError (KeywordFailure E)) R) (after : W) :
    W → List (KeywordEvent W E Atom A R) → Prop
  | world, [] => after = world ∧ (∃ error, answer = .error error)
  | world, event :: rest =>
      event.before = world ∧ event.originalArgs a kw ∧
      match event.terminal with
      | some terminal => rest = [] ∧ answer = terminal.1 ∧ after = terminal.2
      | none =>
        if event.badHint then rest = [] ∧ answer = .error .typeError ∧ after = event.after
        else match event.failure with
        | some error => rest = [] ∧ answer = .error error ∧ after = event.after
        | none => keywordEventChain a kw answer after event.after rest

/-- Select the actual concrete Base methods while leaving every unfixed array
callee arbitrary. No successful-callee law is introduced. -/
def keywordBaseSelections {W E Atom A R : Type} (ops : BoolSumOps W E Atom A R) :
    BoolSumOps W E Atom A R :=
  { ops with
    empty := .base
    donePairs := .base
    keysPairs := .base
    keysNamedTuple := .base
    doneKeys := .base
    iteratePairs := .base
    iterateKeys := .base
    pairsElement := .base
    getindexNamedTuple := .base
    keyTupleBinary := .base
    keyTupleLength := .base
    keyTupleIndex := .base }

/-- For all keyword packets, arrays, worlds and unrestricted selected methods,
every terminating run retains all supplied object identities, native destructuring
and keys-Tuple indices, interior Tuple and _pairs_elt selections, sequential
worlds, callback errors, and the actual one terminal count/reduce
result. For the concrete Base keyword methods the sole call is count exactly when
the immutable NamedTuple has no names, otherwise reduce(add_sum) with the original
keyword packet. This conjunct depends on the actual Pairs/NamedTuple/Tuple chain,
including raw Pair allocation, rather than a supplied emptiness flag. Divergence
has no terminating observation and requires no successful-run premise.
Julia source: base/reduce.jl:576-577; base/essentials.jl:1235-1239;
base/iterators.jl:298-307,316,327; base/namedtuple.jl:165-166,382; base/tuple.jl:69-73. -/
def BoolSumObservation : Prop :=
  (∀ (W E Atom A R : Type) (ops : BoolSumOps W E Atom A R)
      (a : A) (kw : BoolKeywordPacket Atom) (world : W),
    match sumBoolArray (keywordInstrument ops) a kw (world, []) with
    | none => True
    | some (answer, (after, events)) => keywordEventChain a kw answer after world events) ∧
  (∀ (W E Atom A R : Type) (ops : BoolSumOps W E Atom A R)
      (a : A) (kw : BoolKeywordPacket Atom) (world : W),
    AdapterObserved
      (if kw.entries.isEmpty then adapterCallTrace a KeywordEvent.count
       else adapterCallTrace (.addSum, a, kw) KeywordEvent.reduce)
      world (sumBoolArray (keywordInstrument (keywordBaseSelections ops)) a kw (world, [])))

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

/-- Storage and identity invariant, independent of a constructor execution. -/
def ExtremaStored {F Ty Other : Type} (argument : ExtremaArgument F Ty)
    (constructed : ExtremaConstructed F Ty Other) : Prop :=
  match constructed with
  | .custom _ => False
  | .known singleton fields => fields.f = argument ∧
      singleton = (match argument with | .value _ => false | .typeValue _ => true)

/-- The installed type constructor and both concrete construction routes retain
exact field identity and parameter-shape tags. Julia source: base/reduce.jl:812-816. -/
def ExtremaConstructorFields : Prop :=
  (∀ (F : Type) (f : F), (extremaMap_type f).f = f) ∧
  (∀ (F Ty Other : Type) (f : ExtremaArgument F Ty),
    ExtremaStored f (makeExtremaMap (Other := Other) f))

/-- Constructor and reduction observations retain heterogeneous values. -/
inductive ExtremaPublicEvent (F Ty Other I Kw R W E : Type) where
  | construct (call : AdapterCall (ExtremaArgument F Ty) (ExtremaConstructed F Ty Other) W E)
  | reduce (call : AdapterCall (ExtremaConstructed F Ty Other × ReductionSingleton × I × Kw) R W E)

/-- Every selected call is only instrumented, with failed-call mutations kept. -/
def observedExtremaPublicOps {F Ty Other I Kw R W E : Type}
    (ops : ExtremaPublicOps (AdapterEval W E) F Ty Other I Kw R) :
    ExtremaPublicOps
      (AdapterEval (W × List (ExtremaPublicEvent F Ty Other I Kw R W E)) E)
      F Ty Other I Kw R where
  customConstructor := ops.customConstructor
  construct := fun f => observeAdapterEffect (ops.construct f) f ExtremaPublicEvent.construct
  mapreduce := fun f op itr kw => observeAdapterEffect (ops.mapreduce f op itr kw)
    (f, op, itr, kw) ExtremaPublicEvent.reduce

/-- Concrete construction is described by field identity and metadata; an
alternative selected constructor has one observed invocation. -/
def extremaConstructionTrace {F Ty Other I Kw R W E : Type}
    (selected : Bool) (f : ExtremaArgument F Ty) :
    AdapterTrace (ExtremaPublicEvent F Ty Other I Kw R W E) W E (ExtremaConstructed F Ty Other) :=
  if selected then adapterCallTrace f ExtremaPublicEvent.construct
  else fun before events result after =>
    events = [] ∧ before = after ∧ ∃ value, result = .ok value ∧ ExtremaStored f value

/-- Full-domain constructor/call provenance for public extrema. Known and
selected custom constructors, arbitrary result types, mutable worlds, errors
and divergence are included with no laws on selected calls.
Julia source: base/reduce.jl:781-809. -/
def ExtremaPublicObservation : Prop :=
  ∀ (F Ty Other I Kw R W E : Type)
    (ops : ExtremaPublicOps (AdapterEval W E) F Ty Other I Kw R)
    (f : ExtremaArgument F Ty) (itr : I) (kw : Kw) (world : W),
    AdapterObserved
      (adapterThenTrace (extremaConstructionTrace (ops.customConstructor f) f)
        (fun mapped => adapterCallTrace (mapped, .extremaRF, itr, kw) ExtremaPublicEvent.reduce)) world
      (extremaMapped (observedExtremaPublicOps ops) f itr kw (world, []))

/-- Getter and map observations retain source callable and input identities. -/
inductive ExtremaMapEvent (F X Y W E : Type) where
  | property (call : AdapterCall (ExtremaMap F) F W E)
  | map (call : AdapterCall (F × X) Y W E)

/-- Instrument getter and invocation without changing their behavior. -/
def observedExtremaMapOps {F X Y W E : Type}
    (ops : ExtremaMapOps (AdapterEval W E) F X Y) :
    ExtremaMapOps (AdapterEval (W × List (ExtremaMapEvent F X Y W E)) E) F X Y where
  fProperty := liftPropertySelection ops.fProperty ExtremaMapEvent.property
  apply := fun f x => observeAdapterEffect (ops.apply f x) (f, x) ExtremaMapEvent.map

/-- Every original input and arbitrary selected getter/mapper is quantified.
The pair shares the one observed mapping result; a duplicate mapper call,
changed input, broken alias, lost error or reordered getter is detectable.
Julia source: base/reduce.jl:817. -/
def ExtremaMapAliasing : Prop :=
  ∀ (F X Y W E : Type) (ops : ExtremaMapOps (AdapterEval W E) F X Y)
    (f : ExtremaMap F) (x : X) (world : W),
    AdapterObserved
      (adapterThenTrace
        (propertySelectionTrace ops.fProperty ExtremaMap.f f ExtremaMapEvent.property) fun callable =>
      adapterThenTrace (adapterCallTrace (callable, x) ExtremaMapEvent.map) fun value =>
      adapterPureTrace (value, value)) world
      (extremaMapApply (observedExtremaMapOps ops) f x (world, []))

/-- Extrema reduction records both destructuring protocols and both comparisons. -/
inductive ExtremaReduceEvent (V W E : Type) where
  | pair (call : FlatteningAdapterEvent W E V)
  | minimum (call : AdapterCall (V × V) V W (FoldError E))
  | maximum (call : AdapterCall (V × V) V W (FoldError E))

/-- Lift the reused destructuring interface; unused fields also retain their
behavior, while the model observes only indexedIterate and current storage. -/
def observedExtremaPairOps {W E V : Type} (ops : FlatteningAdapterOps W E V) :
    FlatteningAdapterOps (W × List (ExtremaReduceEvent V W E)) E V where
  rfProperty := liftPropertySelection ops.rfProperty
    (fun call => .pair (.rfRead call))
  transform := fun rf x => observeAdapterEffect (ops.transform rf x) (rf, x)
    (fun call => .pair (.transform call))
  indexedIterate := fun object index state =>
    observeAdapterEffect (ops.indexedIterate object index state) (object, index, state)
      (fun call => .pair (.indexed call))
  fields := fun world object => ops.fields world.1 object
  fold := fun op acc itr => observeAdapterEffect (ops.fold op acc itr) (op, acc, itr)
    (fun call => .pair (.fold call))

/-- Instrument arbitrary min/max dispatch, with no ordering/algebraic laws. -/
def observedExtremaCompareOps {W E V : Type}
    (ops : ExtremaCompareOps (FoldEval W (FoldError E)) V) :
    ExtremaCompareOps
      (FoldEval (W × List (ExtremaReduceEvent V W E)) (FoldError E)) V where
  minimum := fun a b => observeAdapterEffect (ops.minimum a b) (a, b) ExtremaReduceEvent.minimum
  maximum := fun a b => observeAdapterEffect (ops.maximum a b) (a, b) ExtremaReduceEvent.maximum

/-- Independent pair-content and raw indexed-iteration trace specification.
Core field outcomes come directly from current storage and mathematical field
positions, not from the model getter. The last indexed result needs only its
first field. Known Base pairs introduce no selected call events. -/
def extremaPairTrace {W E V : Type} (ops : FlatteningAdapterOps W E V)
    (value : FlattenTransformResult V) :
    AdapterTrace (ExtremaReduceEvent V W E) W (FoldError E) (V × V) :=
  match value with
  | .pair a b => adapterPureTrace (a, b)
  | .custom object =>
      adapterThenTrace
        (adapterCallTrace (object, JuliaLean.base.int.lit .i64 1, none)
          (fun call => .pair (.indexed call))) fun first =>
      adapterThenTrace (adapterFieldTrace ops.fields first 0) fun a =>
      adapterThenTrace (adapterFieldTrace ops.fields first 1) fun state =>
      adapterThenTrace
        (adapterCallTrace (object, JuliaLean.base.int.lit .i64 2, some state)
          (fun call => .pair (.indexed call))) fun second =>
      adapterThenTrace (adapterFieldTrace ops.fields second 0) fun b =>
      adapterPureTrace (a, b)

/-- Full-domain extrema reducer invariant, including raw non-tuple objects,
custom indexed iteration, missing/undefined fields, arbitrary min/max dispatch,
state updates, errors and divergence. It detects altered operands, order or
returned tuple components without computing an expected reduction result.
Julia source: base/reduce.jl:819; pinned src/julia-syntax.scm:2597-2608. -/
def ExtremaReducerObservation : Prop :=
  ∀ (W E V : Type) (pairOps : FlatteningAdapterOps W E V)
    (ops : ExtremaCompareOps (FoldEval W (FoldError E)) V)
    (left right : FlattenTransformResult V) (world : W),
    AdapterObserved
      (adapterThenTrace (extremaPairTrace pairOps left) fun a =>
      adapterThenTrace (extremaPairTrace pairOps right) fun b =>
      adapterThenTrace (adapterCallTrace (a.1, b.1) ExtremaReduceEvent.minimum) fun lo =>
      adapterThenTrace (adapterCallTrace (a.2, b.2) ExtremaReduceEvent.maximum) fun hi =>
      adapterPureTrace (lo, hi)) world
      (extremaReduce (observedExtremaPairOps pairOps)
        (observedExtremaCompareOps ops) left right (world, []))

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

 theorem genericOperatorForwarding_proven : GenericOperatorForwarding := by
  intro A B R W E binary x y world
  have h : SingleBinaryObservation x y world ((observeBinary binary x y).run (world, [])) := by
    simp only [observeBinary, ExceptT.run_mk, StateT.run, List.nil_append]
    cases binary x y world with
    | none => trivial
    | some answer => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨h, h⟩

 theorem mappingConstructorsKeepFields_proven : MappingConstructorsKeepFields := by
  intro F RF f rf
  exact ⟨rfl, rfl, rfl, rfl⟩

 theorem genericUnwrapIdentity_proven : GenericUnwrapIdentity := by
  intro O x
  exact ⟨rfl, rfl⟩

 theorem andAllTruthAndErrors_proven : AndAllTruthAndErrors := by
  intro A B x y
  cases x with
  | inl x => cases x <;> cases y with
    | inl y => cases y <;> simp [and_all, assertBool, bind, Except.bind]
    | inr y => simp [and_all, assertBool, bind, Except.bind]
  | inr x => cases y <;> simp [and_all, assertBool, bind, Except.bind]

 theorem orAnyTruthAndErrors_proven : OrAnyTruthAndErrors := by
  intro A B x y
  cases x with
  | inl x => cases x <;> cases y with
    | inl y => cases y <;> simp [or_any, assertBool, bind, Except.bind]
    | inr y => simp [or_any, assertBool, bind, Except.bind]
  | inr x => cases y <;> simp [or_any, assertBool, bind, Except.bind]

 theorem andAllBoolTruth_proven : AndAllBoolTruth := by
  intro x y
  cases x <;> cases y <;> decide

 theorem orAnyBoolTruth_proven : OrAnyBoolTruth := by
  intro x y
  cases x <;> cases y <;> decide

 theorem observePublicFold_forward {Arg R W E : Type}
    (call : Arg → W → Option (Except E R × W)) (args : Arg) (world : W) :
    PublicFoldForwardInvariant args world ((observePublicFold call args).run (world, [])) := by
  simp only [observePublicFold, ExceptT.run_mk, StateT.run, List.nil_append]
  cases call args world with
  | none => trivial
  | some answer => exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

 theorem mapfoldlPublicForwarding_proven : MapfoldlPublicForwarding := by
  intro F Op I V R W E impl f op itr init world
  cases init <;> dsimp only [mapfoldlPublic, Option.getD] <;> apply observePublicFold_forward

 theorem foldlPublicForwarding_proven : FoldlPublicForwarding := by
  intro Op I Kw R W E impl op itr kw world
  dsimp only [foldlPublic]
  apply observePublicFold_forward

 theorem reverseIterForwarding_proven : ReverseIterForwarding := by
  intro I R W E reverse itr world
  exact observePublicFold_forward _ _ _

 theorem mapfoldrPublicForwarding_proven : MapfoldrPublicForwarding := by
  intro F Op I V R W E impl f op itr init world
  cases init <;> dsimp only [mapfoldrPublic, Option.getD] <;> apply observePublicFold_forward

 theorem foldrPublicForwarding_proven : FoldrPublicForwarding := by
  intro Op I Kw R W E impl op itr kw world
  dsimp only [foldrPublic]
  apply observePublicFold_forward

 theorem pairwiseBlocksizeValues_proven : PairwiseBlocksizeValues := by
  constructor <;> intros <;> rfl

 theorem emptyFallbackErrors_proven : EmptyFallbackErrors := by
  intro F Op Ty Tail R f op T tail
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

 theorem emptyClosedValues_proven : EmptyClosedValues := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

 theorem emptyScalarDispatch_proven : EmptyScalarDispatch := by
  intro Ty R W E ops T world
  dsimp only [emptyPlus, emptyTimes, emptyAddSum, emptyMulProd, observedEmptyScalarOps]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals apply observePublicFold_forward

 theorem emptyIteratorUnknownError_proven : EmptyIteratorUnknownError := by
  intro Op I R op itr
  rfl

 theorem firstIdentity_proven : FirstIdentity := by
  intro Op X op x
  rfl

 theorem firstSelectedForwarding_proven : FirstSelectedForwarding := by
  intro X R W E call x world
  exact ⟨observePublicFold_forward _ _ _, observePublicFold_forward _ _ _,
    observePublicFold_forward _ _ _, observePublicFold_forward _ _ _, observePublicFold_forward _ _ _⟩

 theorem reduceNumberIdentity_proven : ReduceNumberIdentity := by
  intro O N op₁ op₂ number
  exact ⟨rfl, rfl⟩

 theorem extremaConstructorFields_proven : ExtremaConstructorFields := by
  constructor
  · intros; rfl
  · intro F Ty Other f
    cases f <;> exact ⟨rfl, rfl⟩

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

/-- Every selected call records exact arguments, worlds, result and error without a law on that call. -/
inductive FindEvent (W E V : Type) where
  | internalMapped (call : AdapterCall (FindDirection × V × V × FindColon) (V) W (FoldError E))
  | internalSingle (call : AdapterCall (FindDirection × V × FindColon) (V) W (FoldError E))
  | publicIdentity (call : AdapterCall (FindDirection × IdentityFn × V) (V) W (FoldError E))
  | publicSingle (call : AdapterCall (FindDirection × V) (V) W (FoldError E))
  | pairs (call : AdapterCall (V) (V) W (FoldError E))
  | mapfoldl (call : AdapterCall (FindClosure V × FindDirection × V) (V) W (FoldError E))
  | getindex (call : AdapterCall (V × JInt .i64) (V) W (FoldError E))
  | indexed (call : AdapterCall (V × JInt .i64 × Option V) (V) W (FoldError E))
  | apply (call : AdapterCall (V × V) (V) W (FoldError E))
  | isless (call : AdapterCall (V × V) (Bool ⊕ V) W (FoldError E))
  | isgreater (call : AdapterCall (V × V) (Bool ⊕ V) W (FoldError E))

/-- Instrument unrestricted public dispatch once at each source invocation. -/
def observedFindPublicOps {W E V : Type} (ops : FindPublicOps (FoldEval W (FoldError E)) V) :
    FindPublicOps (FoldEval (W × List (FindEvent W E V)) (FoldError E)) V :=
  { internalMapped := fun direction f domain colonArg => observeAdapterEffect
      (ops.internalMapped direction f domain colonArg) (direction, f, domain, colonArg) .internalMapped
    internalSingle := fun direction itr colonArg => observeAdapterEffect
      (ops.internalSingle direction itr colonArg) (direction, itr, colonArg) .internalSingle
    publicIdentity := fun direction identityFn a => observeAdapterEffect
      (ops.publicIdentity direction identityFn a) (direction, identityFn, a) .publicIdentity
    publicSingle := fun direction itr => observeAdapterEffect
      (ops.publicSingle direction itr) (direction, itr) .publicSingle
    pairs := fun domain => observeAdapterEffect (ops.pairs domain) domain .pairs
    mapfoldl := fun closure direction itr => observeAdapterEffect
      (ops.mapfoldl closure direction itr) (closure, direction, itr) .mapfoldl
    getindex := fun object index => observeAdapterEffect
      (ops.getindex object index) (object, index) .getindex }

/-- The reused destructuring helper reads only indexedIterate and fields. These
retain their actual behavior and worlds; other, unobserved slots are inert values. -/
def observedFindPairOps {W E V : Type} (ops : FlatteningAdapterOps W E V) :
    FlatteningAdapterOps (W × List (FindEvent W E V)) E V :=
  { transform := fun a b => pure (.pair a b)
    indexedIterate := fun object index state => observeAdapterEffect
      (ops.indexedIterate object index state) (object, index, state) .indexed
    fields := fun world object => ops.fields world.1 object
    fold := fun _ acc _ => pure acc }

/-- Instrument both comparison identities, preserving arbitrary non-Bool answers. -/
def observedFindCompareOps {W E V : Type}
    (ops : FindCompareOps (FoldEval W (FoldError E)) V) :
    FindCompareOps (FoldEval (W × List (FindEvent W E V)) (FoldError E)) V :=
  { isless := fun a b => observeAdapterEffect (ops.isless a b) (a,b) .isless
    isgreater := fun a b => observeAdapterEffect (ops.isgreater a b) (a,b) .isgreater }

/-- Independent storage/trace description of two-variable ordinary destructuring.
The last indexed result needs only one initialized field; no second-field check is
invented. Core outcomes are specified directly by current storage and mathematical
positions, independent of the model getter and native loop operations. -/
def findPairTrace {W E V : Type} (ops : FlatteningAdapterOps W E V)
    (value : FlattenTransformResult V) : AdapterTrace (FindEvent W E V) W (FoldError E) (V × V) :=
  match value with
  | .pair a b => adapterPureTrace (a,b)
  | .custom object =>
    adapterThenTrace (adapterCallTrace (object, JuliaLean.base.int.lit .i64 1, none) FindEvent.indexed) fun first =>
    adapterThenTrace (adapterFieldTrace ops.fields first 0) fun a =>
    adapterThenTrace (adapterFieldTrace ops.fields first 1) fun state =>
    adapterThenTrace (adapterCallTrace (object, JuliaLean.base.int.lit .i64 2, some state) FindEvent.indexed) fun second =>
    adapterThenTrace (adapterFieldTrace ops.fields second 0) fun b =>
    adapterPureTrace (a,b)

/-- Independent conditional contract: only Bool can choose a branch; every other
returned object raises TypeError at the already observed current world. -/
def findConditionTrace {W E V : Type} : Bool ⊕ V →
    AdapterTrace (FindEvent W E V) W (FoldError E) Bool
  | .inl b => adapterPureTrace b
  | .inr _ => fun before events answer after =>
      events = [] ∧ answer = .error .typeError ∧ after = before

/-- The actual indexed lambda's capture and value/key dataflow, including arbitrary
raw input objects, errors in either indexed step/Core read, effects, and divergence.
The f invocation uses the immutable captured f without a property callback, maps
exactly the observed second component, and retains the first component's identity.
Julia source: base/reduce.jl:855,921; base/tuple.jl:161-172;
pinned src/julia-syntax.scm:2597-2608. -/
def FindIndexedClosureObservation : Prop :=
  ∀ (W E V : Type) (pairOps : FlatteningAdapterOps W E V)
    (apply : V → V → FoldEval W (FoldError E) V)
    (closure : FindIndexedClosure V) (argument : FlattenTransformResult V) (world : W),
    AdapterObserved
      (adapterThenTrace (findPairTrace pairOps argument) fun pair =>
      adapterThenTrace (adapterCallTrace (closure.f, pair.2) FindEvent.apply) fun mapped =>
      adapterPureTrace (mapped, pair.1)) world
      (findIndexedClosureApply (observedFindPairOps pairOps)
        (fun f x => observeAdapterEffect (apply f x) (f,x) FindEvent.apply)
        closure argument (world, []))

/-- The value lambda maps the original x exactly once with captured f and returns
that observed result paired with the same original x reference. Arbitrary failed,
mutating and divergent maps require no correctness or success premise.
Julia source: base/reduce.jl:976,1034. -/
def FindValueClosureObservation : Prop :=
  ∀ (W E V : Type) (apply : V → V → FoldEval W (FoldError E) V)
    (closure : FindValueClosure V) (x : V) (world : W),
    AdapterObserved
      (adapterThenTrace (adapterCallTrace (closure.f, x) FindEvent.apply) fun mapped =>
      adapterPureTrace (mapped, x)) world
      (findValueClosureApply
        (fun f x => observeAdapterEffect (apply f x) (f,x) FindEvent.apply)
        closure x (world, []))

/-- One selected internal call receives the original f/domain and exact Colon singleton; its actual outcome/world is retained.
Universal quantification includes custom dispatch, all mutable worlds, exceptions
and divergence, with no callee laws. Julia source: base/reduce.jl:854. -/
def FindMaxMappedObservation : Prop :=
  ∀ (W E V : Type) (ops : FindPublicOps (FoldEval W (FoldError E)) V)
    (f domain : V) (world : W),
    AdapterObserved
      (adapterCallTrace (.maximum, f, domain, FindColon.colon) FindEvent.internalMapped) world
      (findMaxMapped (observedFindPublicOps ops) f domain (world, []))

/-- Exactly pairs(original domain), then mapfoldl with its actual result, the correct reducer and a known indexed closure capturing the original f. The lambda body has its separately registered full-domain invariant.
Universal quantification includes custom dispatch, all mutable worlds, exceptions
and divergence, with no callee laws. Julia source: base/reduce.jl:855. -/
def FindMaxColonObservation : Prop :=
  ∀ (W E V : Type) (ops : FindPublicOps (FoldEval W (FoldError E)) V)
    (f domain : V) (colonArg : FindColon) (world : W),
    AdapterObserved
      (adapterThenTrace (adapterCallTrace domain FindEvent.pairs) fun paired =>
      adapterCallTrace (FindClosure.indexed ⟨.maximum, f⟩, .maximum, paired) FindEvent.mapfoldl) world
      (findMaxColon (observedFindPublicOps ops) f domain colonArg (world, []))

/-- Destructure left then right; compare exactly their observed first components
with the correct function identity; reject non-Bool, and return the entire right
pair for true or left pair for false. This retains the actual key/value aliases
and tie branch without imposing an ordering law. All errors, state and divergence
are quantified. Julia source: base/reduce.jl:856. -/
def FindMaxReducerObservation : Prop :=
  ∀ (W E V : Type) (pairOps : FlatteningAdapterOps W E V)
    (ops : FindCompareOps (FoldEval W (FoldError E)) V)
    (left right : FlattenTransformResult V) (world : W),
    AdapterObserved
      (adapterThenTrace (findPairTrace pairOps left) fun a =>
      adapterThenTrace (findPairTrace pairOps right) fun b =>
      adapterThenTrace (adapterCallTrace (a.1,b.1) FindEvent.isless) fun condition =>
      adapterThenTrace (findConditionTrace condition) fun better =>
      adapterPureTrace (if better then b else a)) world
      (findReduceMax (observedFindPairOps pairOps) (observedFindCompareOps ops)
        left right (world, []))

/-- One selected unary internal call receives the original iterator and Colon singleton, preserving its exact outcome/world.
Universal quantification includes custom dispatch, all mutable worlds, exceptions
and divergence, with no callee laws. Julia source: base/reduce.jl:883. -/
def FindMaxSingleObservation : Prop :=
  ∀ (W E V : Type) (ops : FindPublicOps (FoldEval W (FoldError E)) V)
    (itr : V) (world : W),
    AdapterObserved
      (adapterCallTrace (.maximum, itr, FindColon.colon) FindEvent.internalSingle) world
      (findMaxSingle (observedFindPublicOps ops) itr (world, []))

/-- One selected public call receives the exact identity function singleton and original collection, retaining every outcome/world.
Universal quantification includes custom dispatch, all mutable worlds, exceptions
and divergence, with no callee laws. Julia source: base/reduce.jl:884. -/
def FindMaxIdentityObservation : Prop :=
  ∀ (W E V : Type) (ops : FindPublicOps (FoldEval W (FoldError E)) V)
    (a : V) (colonArg : FindColon) (world : W),
    AdapterObserved
      (adapterCallTrace (.maximum, IdentityFn.identity, a) FindEvent.publicIdentity) world
      (findMaxIdentity (observedFindPublicOps ops) a colonArg (world, []))

/-- Mapfoldl receives the exact known value closure capture, reducer and domain; selected getindex receives its actual result and native Int64 two. No pair result is assumed; the actual lambda body is independently registered.
Universal quantification includes custom dispatch, all mutable worlds, exceptions
and divergence, with no callee laws. Julia source: base/reduce.jl:976. -/
def ArgMaxMappedObservation : Prop :=
  ∀ (W E V : Type) (ops : FindPublicOps (FoldEval W (FoldError E)) V)
    (f domain : V) (world : W),
    AdapterObserved
      (adapterThenTrace
        (adapterCallTrace (FindClosure.value ⟨.maximum, f⟩, .maximum, domain) FindEvent.mapfoldl) fun result =>
      adapterCallTrace (result, JuliaLean.base.int.lit .i64 2) FindEvent.getindex) world
      (argMaxMapped (observedFindPublicOps ops) f domain (world, []))

/-- Find receives the original iterator; selected getindex then receives the exact observed result and native Int64 two, with result/error/world provenance and no invented pair projection.
Universal quantification includes custom dispatch, all mutable worlds, exceptions
and divergence, with no callee laws. Julia source: base/reduce.jl:1005. -/
def ArgMaxSingleObservation : Prop :=
  ∀ (W E V : Type) (ops : FindPublicOps (FoldEval W (FoldError E)) V)
    (itr : V) (world : W),
    AdapterObserved
      (adapterThenTrace (adapterCallTrace (.maximum, itr) FindEvent.publicSingle) fun result =>
      adapterCallTrace (result, JuliaLean.base.int.lit .i64 2) FindEvent.getindex) world
      (argMaxSingle (observedFindPublicOps ops) itr (world, []))

/-- One selected internal call receives the original f/domain and exact Colon singleton; its actual outcome/world is retained.
Universal quantification includes custom dispatch, all mutable worlds, exceptions
and divergence, with no callee laws. Julia source: base/reduce.jl:920. -/
def FindMinMappedObservation : Prop :=
  ∀ (W E V : Type) (ops : FindPublicOps (FoldEval W (FoldError E)) V)
    (f domain : V) (world : W),
    AdapterObserved
      (adapterCallTrace (.minimum, f, domain, FindColon.colon) FindEvent.internalMapped) world
      (findMinMapped (observedFindPublicOps ops) f domain (world, []))

/-- Exactly pairs(original domain), then mapfoldl with its actual result, the correct reducer and a known indexed closure capturing the original f. The lambda body has its separately registered full-domain invariant.
Universal quantification includes custom dispatch, all mutable worlds, exceptions
and divergence, with no callee laws. Julia source: base/reduce.jl:921. -/
def FindMinColonObservation : Prop :=
  ∀ (W E V : Type) (ops : FindPublicOps (FoldEval W (FoldError E)) V)
    (f domain : V) (colonArg : FindColon) (world : W),
    AdapterObserved
      (adapterThenTrace (adapterCallTrace domain FindEvent.pairs) fun paired =>
      adapterCallTrace (FindClosure.indexed ⟨.minimum, f⟩, .minimum, paired) FindEvent.mapfoldl) world
      (findMinColon (observedFindPublicOps ops) f domain colonArg (world, []))

/-- Destructure left then right; compare exactly their observed first components
with the correct function identity; reject non-Bool, and return the entire right
pair for true or left pair for false. This retains the actual key/value aliases
and tie branch without imposing an ordering law. All errors, state and divergence
are quantified. Julia source: base/reduce.jl:922. -/
def FindMinReducerObservation : Prop :=
  ∀ (W E V : Type) (pairOps : FlatteningAdapterOps W E V)
    (ops : FindCompareOps (FoldEval W (FoldError E)) V)
    (left right : FlattenTransformResult V) (world : W),
    AdapterObserved
      (adapterThenTrace (findPairTrace pairOps left) fun a =>
      adapterThenTrace (findPairTrace pairOps right) fun b =>
      adapterThenTrace (adapterCallTrace (a.1,b.1) FindEvent.isgreater) fun condition =>
      adapterThenTrace (findConditionTrace condition) fun better =>
      adapterPureTrace (if better then b else a)) world
      (findReduceMin (observedFindPairOps pairOps) (observedFindCompareOps ops)
        left right (world, []))

/-- One selected unary internal call receives the original iterator and Colon singleton, preserving its exact outcome/world.
Universal quantification includes custom dispatch, all mutable worlds, exceptions
and divergence, with no callee laws. Julia source: base/reduce.jl:949. -/
def FindMinSingleObservation : Prop :=
  ∀ (W E V : Type) (ops : FindPublicOps (FoldEval W (FoldError E)) V)
    (itr : V) (world : W),
    AdapterObserved
      (adapterCallTrace (.minimum, itr, FindColon.colon) FindEvent.internalSingle) world
      (findMinSingle (observedFindPublicOps ops) itr (world, []))

/-- One selected public call receives the exact identity function singleton and original collection, retaining every outcome/world.
Universal quantification includes custom dispatch, all mutable worlds, exceptions
and divergence, with no callee laws. Julia source: base/reduce.jl:950. -/
def FindMinIdentityObservation : Prop :=
  ∀ (W E V : Type) (ops : FindPublicOps (FoldEval W (FoldError E)) V)
    (a : V) (colonArg : FindColon) (world : W),
    AdapterObserved
      (adapterCallTrace (.minimum, IdentityFn.identity, a) FindEvent.publicIdentity) world
      (findMinIdentity (observedFindPublicOps ops) a colonArg (world, []))

/-- Mapfoldl receives the exact known value closure capture, reducer and domain; selected getindex receives its actual result and native Int64 two. No pair result is assumed; the actual lambda body is independently registered.
Universal quantification includes custom dispatch, all mutable worlds, exceptions
and divergence, with no callee laws. Julia source: base/reduce.jl:1034. -/
def ArgMinMappedObservation : Prop :=
  ∀ (W E V : Type) (ops : FindPublicOps (FoldEval W (FoldError E)) V)
    (f domain : V) (world : W),
    AdapterObserved
      (adapterThenTrace
        (adapterCallTrace (FindClosure.value ⟨.minimum, f⟩, .minimum, domain) FindEvent.mapfoldl) fun result =>
      adapterCallTrace (result, JuliaLean.base.int.lit .i64 2) FindEvent.getindex) world
      (argMinMapped (observedFindPublicOps ops) f domain (world, []))

/-- Find receives the original iterator; selected getindex then receives the exact observed result and native Int64 two, with result/error/world provenance and no invented pair projection.
Universal quantification includes custom dispatch, all mutable worlds, exceptions
and divergence, with no callee laws. Julia source: base/reduce.jl:1063. -/
def ArgMinSingleObservation : Prop :=
  ∀ (W E V : Type) (ops : FindPublicOps (FoldEval W (FoldError E)) V)
    (itr : V) (world : W),
    AdapterObserved
      (adapterThenTrace (adapterCallTrace (.minimum, itr) FindEvent.publicSingle) fun result =>
      adapterCallTrace (result, JuliaLean.base.int.lit .i64 2) FindEvent.getindex) world
      (argMinSingle (observedFindPublicOps ops) itr (world, []))

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

/-- The actual init has a native numeric zero when absent and exactly the
original object when present. This does not invoke the default-selection model. -/
def CountInitialValue {V : Type} (supplied : Option (CountArgument V))
    (actual : CountArgument V) : Prop :=
  match supplied with
  | some value => actual = value
  | none => match actual with | .native n => n.val = 0 | .other _ => False

/-- Full-domain captured identity, one-call and Bool assertion invariant.
Non-Bool results cause an actual TypeError, with no conversion call; the world
after the original predicate is retained. Source: base/reduce.jl:1067. -/
def BoolClosureObservation : Prop :=
  ∀ (W E F X Other : Type)
    (invoke : F → X → FoldEval W (FoldError E) (Bool ⊕ Other))
    (f : F) (x : X) (world : W),
    (makeBoolClosure f).captured = f ∧
    AdapterObserved
      (adapterThenTrace (adapterCallTrace (f, x) id) fun result =>
        match result with
        | .inl value => adapterPureTrace value
        | .inr _ => fun before events answer after =>
            events = [] ∧ answer = .error .typeError ∧ after = before) world
      (applyBoolClosure
        (fun f x => observeAdapterEffect (invoke f x) (f, x) id)
        (makeBoolClosure f) x (world, []))

/-- All selected public count, simple_count, constructor and sum observations. -/
inductive CountGeneralEvent (F I V OtherClosure R W E : Type) where
  | count (call : AdapterCall (IdentityFn × I × CountKeyword V) R W E)
  | simple (call : AdapterCall (F × I × CountArgument V) R W E)
  | bool (call : AdapterCall F (BoolClosureResult F OtherClosure) W E)
  | sum (call : AdapterCall (BoolClosureResult F OtherClosure × I × CountKeyword V) R W E)

/-- Instrument unrestricted selected dispatch with all error worlds retained. -/
def observedCountGeneralOps {F I V OtherClosure R W E : Type}
    (ops : CountGeneralOps (AdapterEval W E) F I V OtherClosure R) :
    CountGeneralOps
      (AdapterEval (W × List (CountGeneralEvent F I V OtherClosure R W E)) E)
      F I V OtherClosure R where
  count := fun f itr kw => observeAdapterEffect (ops.count f itr kw) (f, itr, kw) CountGeneralEvent.count
  simple := fun f itr init => observeAdapterEffect (ops.simple f itr init) (f, itr, init) CountGeneralEvent.simple
  selectBool := ops.selectBool
  bool := fun f => observeAdapterEffect (ops.bool f) f CountGeneralEvent.bool
  sum := fun f itr kw => observeAdapterEffect (ops.sum f itr kw) (f, itr, kw) CountGeneralEvent.sum

/-- A default closure retains its capture with no call/effect; a selected _bool
method has precisely one observed invocation on the original predicate. -/
def countClosureTrace {F I V OtherClosure R W E : Type} (selected : Bool) (f : F) :
    AdapterTrace (CountGeneralEvent F I V OtherClosure R W E) W E (BoolClosureResult F OtherClosure) :=
  if selected then adapterCallTrace f CountGeneralEvent.bool
  else fun before events answer after => events = [] ∧ after = before ∧
    ∃ closure : BoolClosure F, answer = .ok (.known closure) ∧ closure.captured = f

/-- Independent complete-domain forwarding and default-value invariants.
All callback result types, errors, states and divergence are quantified, including
noninteger explicit init values. The source body has no Integer type assertion.
Only original arguments, call observations, captured fields and mathematical zero
supply expected values; no callback correctness or termination law is assumed.
Julia source: base/reduce.jl:1094-1098. -/
def CountForwardingObservation : Prop :=
  ∀ (F I V OtherClosure R W E : Type)
    (ops : CountGeneralOps (AdapterEval W E) F I V OtherClosure R)
    (f : F) (itr : I) (init : Option (CountArgument V)) (explicit : CountArgument V) (world : W),
    let observed := observedCountGeneralOps ops
    CountInitialValue init (countInitial init) ∧
    AdapterObserved
      (fun before events answer after =>
        ∃ kw : CountKeyword V, CountInitialValue init kw.init ∧
          adapterCallTrace (.identity, itr, kw) CountGeneralEvent.count before events answer after) world
      (countPublic observed itr init (world, [])) ∧
    AdapterObserved
      (fun before events answer after =>
        ∃ chosen : CountArgument V, CountInitialValue init chosen ∧
          adapterCallTrace (f, itr, chosen) CountGeneralEvent.simple before events answer after) world
      (countMapped observed f itr init (world, [])) ∧
    AdapterObserved
      (adapterThenTrace (countClosureTrace (ops.selectBool f) f)
        (fun mapped => adapterCallTrace (mapped, itr, (⟨explicit⟩ : CountKeyword V)) CountGeneralEvent.sum)) world
      (simpleCount observed f itr explicit (world, []))

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

 def AdapterSatisfies {A W E Event : Type} (spec : AdapterTrace Event W E A)
    (call : AdapterEval (W × List Event) E A) : Prop :=
  ∀ world priorEvents answer after events,
    call (world, priorEvents) = some (answer, after, events) →
    ∃ suffix, events = priorEvents ++ suffix ∧ spec world suffix answer after

 theorem adapterSatisfies_observed {A W E Event : Type}
    {spec : AdapterTrace Event W E A} {call : AdapterEval (W × List Event) E A}
    (h : AdapterSatisfies spec call) (world : W) :
    AdapterObserved spec world (call (world, [])) := by
  cases hc : call (world, []) with
  | none => trivial
  | some result =>
    obtain ⟨answer, after, events⟩ := result
    obtain ⟨suffix, he, hs⟩ := h world [] answer after events hc
    simpa [AdapterObserved, List.nil_append, he] using hs

 theorem adapterSatisfies_call {Args A W E Event : Type}
    (call : AdapterEval W E A) (args : Args) (tag : AdapterCall Args A W E → Event) :
    AdapterSatisfies (adapterCallTrace args tag) (observeAdapterEffect call args tag) := by
  intro world priorEvents answer after events h
  dsimp only [observeAdapterEffect, ExceptT.mk] at h
  cases hc : call world with
  | none => simp [hc] at h
  | some result =>
    obtain ⟨result, last⟩ := result
    simp [hc] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨_, rfl, _, rfl, rfl, rfl, rfl, rfl⟩

 theorem adapterSatisfies_pure {A W E Event : Type} (value : A) :
    AdapterSatisfies (adapterPureTrace (W := W) (E := E) (Event := Event) value)
      (pure value) := by
  intro world priorEvents answer after events h
  change some (.ok value, world, priorEvents) = some (answer, after, events) at h
  cases h
  exact ⟨[], by simp, rfl, rfl, rfl⟩

 theorem adapterSatisfies_bind {A B W E Event : Type}
    {first : AdapterTrace Event W E A} {next : A → AdapterTrace Event W E B}
    {call : AdapterEval (W × List Event) E A}
    {cont : A → AdapterEval (W × List Event) E B}
    (hf : AdapterSatisfies first call) (hn : ∀ a, AdapterSatisfies (next a) (cont a)) :
    AdapterSatisfies (adapterThenTrace first next) (call >>= cont) := by
  intro world priorEvents answer after events h
  dsimp only [bind, ExceptT.bind, ExceptT.mk, StateT.bind, ExceptT.bindCont, ExceptT.run] at h
  cases hc : call (world, priorEvents) with
  | none => simp [hc] at h
  | some result =>
    obtain ⟨result, middle, prior⟩ := result
    obtain ⟨earlier, hp, hs⟩ := hf world priorEvents result middle prior hc
    cases result with
    | error error =>
      simp [hc] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨earlier, hp, earlier, [], .error error, _, by simp, hs, rfl, rfl, rfl⟩
    | ok value =>
      simp [hc] at h
      obtain ⟨later, hl, ht⟩ := hn value middle prior answer after events h
      refine ⟨earlier ++ later, ?_, earlier, later, .ok value, middle, rfl, hs, ht⟩
      simp [hl, hp, List.append_assoc]

 theorem adapterSatisfies_property {Object A W E Event : Type}
    (selection : PropertySelection (AdapterEval W E) Object A) (field : Object → A)
    (object : Object) (tag : AdapterCall Object A W E → Event) :
    AdapterSatisfies (propertySelectionTrace selection field object tag)
      (readSelectedProperty (liftPropertySelection selection tag) field object) := by
  cases selection with
  | stored => exact adapterSatisfies_pure _
  | custom call => exact adapterSatisfies_call _ _ _

 theorem selectedPropertyObservation_proven : SelectedPropertyObservation := by
  intro Object A W E selection field object world
  exact adapterSatisfies_observed (adapterSatisfies_property selection field object _) world

 theorem bottomAdapterObservation_proven : BottomAdapterObservation := by
  intro W E F Acc Input Result ops op acc x world
  constructor <;> apply adapterSatisfies_observed
  all_goals apply adapterSatisfies_bind (adapterSatisfies_property _ _ _ _)
  all_goals intro rf; apply adapterSatisfies_call

 theorem mappingAdapterObservation_proven : MappingAdapterObservation := by
  intro W E F RF Acc Input Mapped Result ops op acc x world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (adapterSatisfies_property _ _ _ _)
  intro rf
  apply adapterSatisfies_bind (adapterSatisfies_property _ _ _ _)
  intro f
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro mapped
  apply adapterSatisfies_call

 theorem flipAdapterObservation_proven : FlipAdapterObservation := by
  intro W E F X Y R ops wrapper x y world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (adapterSatisfies_property _ _ _ _)
  intro f
  apply adapterSatisfies_call

 theorem firstFlipObservation_proven : FirstFlipObservation := by
  intro F X R W E ops op x world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (adapterSatisfies_property _ _ _ _)
  intro f
  apply adapterSatisfies_call

 theorem mapreduceFirstObservation_proven : MapreduceFirstObservation := by
  intro F Op X M R W E ops f op x world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro mapped
  apply adapterSatisfies_call

 theorem arrayMapreduceDispatchObservation_proven : ArrayMapreduceDispatchObservation := by
  intro F O A Style R W E ops f op array world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro style
  apply adapterSatisfies_call

 theorem reductionPublicForwarding_proven : ReductionPublicForwarding := by
  intro F I Kw R W E ops f itr kw world
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals apply adapterSatisfies_observed; apply adapterSatisfies_call

 theorem extremaMapAliasing_proven : ExtremaMapAliasing := by
  intro F X Y W E ops f x world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (adapterSatisfies_property _ _ _ _)
  intro callable
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro value
  apply adapterSatisfies_pure

 theorem findMaxMappedObservation_proven : FindMaxMappedObservation := by
  intro W E V ops f domain world
  apply adapterSatisfies_observed
  apply adapterSatisfies_call

 theorem findMaxSingleObservation_proven : FindMaxSingleObservation := by
  intro W E V ops itr world
  apply adapterSatisfies_observed
  apply adapterSatisfies_call

 theorem findMaxIdentityObservation_proven : FindMaxIdentityObservation := by
  intro W E V ops a colonArg world
  apply adapterSatisfies_observed
  apply adapterSatisfies_call

 theorem findMinMappedObservation_proven : FindMinMappedObservation := by
  intro W E V ops f domain world
  apply adapterSatisfies_observed
  apply adapterSatisfies_call

 theorem findMinSingleObservation_proven : FindMinSingleObservation := by
  intro W E V ops itr world
  apply adapterSatisfies_observed
  apply adapterSatisfies_call

 theorem findMinIdentityObservation_proven : FindMinIdentityObservation := by
  intro W E V ops a colonArg world
  apply adapterSatisfies_observed
  apply adapterSatisfies_call

 theorem argMaxMappedObservation_proven : ArgMaxMappedObservation := by
  intro W E V ops f domain world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro result
  apply adapterSatisfies_call

 theorem argMaxSingleObservation_proven : ArgMaxSingleObservation := by
  intro W E V ops itr world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro result
  apply adapterSatisfies_call

 theorem argMinMappedObservation_proven : ArgMinMappedObservation := by
  intro W E V ops f domain world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro result
  apply adapterSatisfies_call

 theorem argMinSingleObservation_proven : ArgMinSingleObservation := by
  intro W E V ops itr world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro result
  apply adapterSatisfies_call

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

 theorem firstNativeValues_proven : FirstNativeValues := by
  refine ⟨?_, ?_, ?_⟩
  · intro x; cases x <;> rfl
  · intro x
    have h := small_widen_value x.val.ty .i64 x.val.value x.val.small (Or.inl rfl)
    exact ⟨h, h⟩
  · intro x
    have h := small_widen_value x.val.ty .u64 x.val.value x.val.small
      (Or.inr ⟨rfl, x.property⟩)
    exact ⟨h, h⟩

 theorem emptyNativeIdentities_proven : EmptyNativeIdentities := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ty; cases ty <;> exact ⟨rfl, rfl⟩
  · rfl
  · intro T; exact ⟨rfl, rfl⟩
  · intro T; exact ⟨rfl, rfl⟩

 theorem smallInteger_bounds (x : SmallInteger) :
    -2147483648 ≤ x.value.val ∧ x.value.val ≤ 4294967295 := by
  rcases x with ⟨ty, value, ht⟩
  change -2147483648 ≤ value.val ∧ value.val ≤ 4294967295
  have h := value.property
  cases ty <;> simp only [IntTy.bits] at ht <;> try omega
  all_goals simp [IntTy.min, IntTy.max, IntTy.bits, IntTy.signed] at h; omega

 theorem smallOrBool_bounds (x : SmallOrBool) :
    -2147483648 ≤ smallOrBoolValue x ∧ smallOrBoolValue x ≤ 4294967295 := by
  cases x with
  | inl b => cases b <;> decide
  | inr x => exact smallInteger_bounds x

 theorem smallOrBoolInt_value (x : SmallOrBool) :
    (smallOrBoolInt x).val = smallOrBoolValue x := by
  cases x with
  | inl b => cases b <;> rfl
  | inr x => exact small_widen_value x.ty .i64 x.value x.small (Or.inl rfl)

 theorem addSumSmallExact_proven : AddSumSmallExact := by
  intro x y
  have hx := smallOrBool_bounds x
  have hy := smallOrBool_bounds y
  rw [addSumSmall, JuliaLean.base.int.add, JuliaLean.Proofs.base.int.add_int_val]
  rw [smallOrBoolInt_value, smallOrBoolInt_value]
  apply wrapInt_of_inRange
  change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
  omega

 theorem addSumUnsignedSmallExact_proven : AddSumUnsignedSmallExact := by
  intro x y
  have hx := smallInteger_bounds x.val
  have hy := smallInteger_bounds y.val
  have hxn := x.val.value.property.1
  have hyn := y.val.value.property.1
  rw [show (addSumUnsignedSmall x y).val =
    wrapInt .u64 (x.val.value.val + y.val.value.val) by
      exact congrArg Subtype.val (source_add_widen .u64 _ _)]
  apply wrapInt_of_inRange
  simp only [IntTy.min, IntTy.max, IntTy.bits, IntTy.signed]
  simp only [IntTy.min, x.property, y.property, Bool.false_eq_true, ↓reduceIte] at hxn hyn
  omega

 theorem signedSmall_bounds (x : SmallSigned) :
    -2147483648 ≤ x.val.value.val ∧ x.val.value.val ≤ 2147483647 := by
  rcases x with ⟨⟨ty, value, ht⟩, hs⟩
  change -2147483648 ≤ value.val ∧ value.val ≤ 2147483647
  change ty.signed = true at hs
  have h := value.property
  cases ty <;> simp only [IntTy.bits] at ht <;>
    simp only [IntTy.signed] at hs <;> try contradiction <;> try omega
  all_goals simp [IntTy.min, IntTy.max, IntTy.bits, IntTy.signed] at h; omega

 theorem unsignedSmall_bounds (x : SmallUnsigned) :
    0 ≤ x.val.value.val ∧ x.val.value.val ≤ 4294967295 := by
  have h := smallInteger_bounds x.val
  have hn := x.val.value.property.1
  simp only [IntTy.min, x.property, Bool.false_eq_true, ite_false] at hn
  exact ⟨hn, h.2⟩

 theorem mul_symmetric_bounds (a b C : Int) (hC : 0 ≤ C)
    (ha : -C ≤ a ∧ a ≤ C) (hb : -C ≤ b ∧ b ≤ C) :
    -(C * C) ≤ a * b ∧ a * b ≤ C * C := by
  by_cases hna : 0 ≤ a
  · by_cases hnb : 0 ≤ b
    · have hi := Int.mul_le_mul ha.2 hb.2 hnb hC
      have lo := Int.mul_nonneg hna hnb
      have hc := Int.mul_nonneg hC hC
      omega
    · have hi := Int.mul_le_mul ha.2 (show -b ≤ C by omega) (show 0 ≤ -b by omega) hC
      have lo := Int.mul_nonneg hna (show 0 ≤ -b by omega)
      have hc := Int.mul_nonneg hC hC
      simp only [Int.mul_neg] at hi lo
      omega
  · by_cases hnb : 0 ≤ b
    · have hi := Int.mul_le_mul (show -a ≤ C by omega) hb.2 hnb hC
      have lo := Int.mul_nonneg (show 0 ≤ -a by omega) hnb
      have hc := Int.mul_nonneg hC hC
      simp only [Int.neg_mul] at hi lo
      omega
    · have hi := Int.mul_le_mul (show -a ≤ C by omega) (show -b ≤ C by omega)
        (show 0 ≤ -b by omega) hC
      have lo := Int.mul_nonneg (show 0 ≤ -a by omega) (show 0 ≤ -b by omega)
      have hc := Int.mul_nonneg hC hC
      simp only [Int.neg_mul_neg] at hi lo
      omega

 theorem mulProdSignedSmallExact_proven : MulProdSignedSmallExact := by
  intro x y
  have hx := signedSmall_bounds x
  have hy := signedSmall_bounds y
  have bounds := mul_symmetric_bounds x.val.value.val y.val.value.val 2147483648
    (by decide) (by omega) (by omega)
  rw [show (mulProdSignedSmall x y).val =
    wrapInt .i64 (x.val.value.val * y.val.value.val) by
      exact congrArg Subtype.val (source_mul_widen .i64 _ _)]
  apply wrapInt_of_inRange
  change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
  omega

 theorem mulProdUnsignedSmallExact_proven : MulProdUnsignedSmallExact := by
  intro x y
  have hx := unsignedSmall_bounds x
  have hy := unsignedSmall_bounds y
  have hi := Int.mul_le_mul hx.2 hy.2 hy.1 (by decide : (0 : Int) ≤ 4294967295)
  have lo := Int.mul_nonneg hx.1 hy.1
  rw [show (mulProdUnsignedSmall x y).val =
    wrapInt .u64 (x.val.value.val * y.val.value.val) by
      exact congrArg Subtype.val (source_mul_widen .u64 _ _)]
  apply wrapInt_of_inRange
  change 0 ≤ _ ∧ _ ≤ 18446744073709551615
  omega

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

/-- Range conditions, range reductions and operator calls are separate observable events. -/
inductive RangeFoldEvent (W E Range F V Other : Type) where
  | isempty (call : AdapterCall Range (Bool ⊕ Other) W (FoldError E))
  | reduceRange (call : AdapterCall (RangeFoldKind × Range) V W (FoldError E))
  | bottom (call : BottomAdapterEvent W (FoldError E) (RangeCallable F)
      (FoldInit V) V (FoldInit V))
  | custom (call : AdapterCall
      (BottomAdapter (RangeCallable F) × FoldInit V × V) (FoldInit V) W (FoldError E))

/-- Instrument every unrestricted callback and selected getter. -/
def observedRangeFoldOps {W E Range F V Other : Type}
    (ops : RangeFoldOps W E Range F V Other) :
    RangeFoldOps (W × List (RangeFoldEvent W E Range F V Other)) E Range F V Other where
  isempty := fun range => observeAdapterEffect (ops.isempty range) range RangeFoldEvent.isempty
  reduceRange := fun kind range => observeAdapterEffect (ops.reduceRange kind range)
    (kind, range) RangeFoldEvent.reduceRange
  selectBottom := ops.selectBottom
  customBottom := fun op init x => observeAdapterEffect (ops.customBottom op init x)
    (op, init, x) RangeFoldEvent.custom
  bottom := {
    rfProperty := liftPropertySelection ops.bottom.rfProperty
      (fun call => .bottom (.property call))
    first := fun rf x => observeAdapterEffect (ops.bottom.first rf x) (rf, none, x)
      (fun call => .bottom (.invoke call))
    call := fun rf init x => observeAdapterEffect (ops.bottom.call rf init x) (rf, some init, x)
      (fun call => .bottom (.invoke call)) }

/-- Embed a previously independent trace specification without replaying its model. -/
def embedAdapterTrace {Event Event' W E A : Type} (tag : Event → Event')
    (spec : AdapterTrace Event W E A) : AdapterTrace Event' W E A :=
  fun before events answer after => ∃ inner, events = inner.map tag ∧ spec before inner answer after

/-- The independent generator inventory specifies the exact source singleton
pairs, and every conditional/operator outcome comes from actual observations.
The empty branch has no reducer/getter/operator calls; non-Bool throws at the
condition; nonempty preserves range-reduction-before-BottomRF ordering.
Julia source: base/reduce.jl:1119-1124. -/
def RangeFoldObservation : Prop :=
  ∀ (W E Range F V Other : Type) (ops : RangeFoldOps W E Range F V Other)
    (kind : RangeFoldKind) (init : FoldInit V) (range : Range) (world : W),
    let sourceReducer : ReductionSingleton :=
      match kind with | .maximum => .maximum | .minimum => .minimum | .sum => .addSum
    let sourceOp : BottomAdapter (RangeCallable F) := ⟨.standard sourceReducer⟩
    AdapterObserved
      (adapterThenTrace (adapterCallTrace range RangeFoldEvent.isempty) fun condition =>
        match condition with
        | .inr _ => fun before events answer after =>
            events = [] ∧ answer = .error .typeError ∧ after = before
        | .inl true => adapterPureTrace init
        | .inl false =>
            adapterThenTrace (adapterCallTrace (kind, range) RangeFoldEvent.reduceRange) fun value =>
            if ops.selectBottom kind init value then
              adapterCallTrace (sourceOp, init, value) RangeFoldEvent.custom
            else embedAdapterTrace RangeFoldEvent.bottom
              (BottomAdapterTrace ops.bottom sourceOp
                (match init with | .initial => none | .value _ => some init) value)) world
      (foldlRangeSpecial (observedRangeFoldOps ops) kind init range (world, []))

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

theorem mapreducePublicForwarding_proven : MapreducePublicForwarding := by
  intro F Op I Kw R W E impl f op itr kw world
  dsimp only [mapreducePublic]
  apply observePublicFold_forward

theorem numberMapreduceObservation_proven : NumberMapreduceObservation := by
  intro F O N R W E first f op number world
  dsimp only [mapreduceNumber]
  apply observePublicFold_forward

theorem cartesianMapreduceObservation_proven : CartesianMapreduceObservation := by
  intro F O A R W E fold f op array world
  dsimp only [mapreduceCartesian]
  apply observePublicFold_forward

theorem publicReduceObservation_proven : PublicReduceObservation := by
  intro O I Kw R W E reduce op itr kw world
  dsimp only [reducePublic]
  apply observePublicFold_forward

theorem adapterSatisfies_error {A W E Event : Type} (error : E) :
    AdapterSatisfies (fun before events answer after =>
      events = [] ∧ answer = .error error ∧ after = before)
      (throw error : AdapterEval (W × List Event) E A) := by
  intro world priorEvents answer after events h
  change some (.error error, world, priorEvents) = some (answer, after, events) at h
  cases h
  exact ⟨[], by simp, rfl, rfl, rfl⟩

theorem boolClosureObservation_proven : BoolClosureObservation := by
  intro W E F X Other invoke f x world
  refine ⟨rfl, ?_⟩
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro result
  cases result with
  | inl b => apply adapterSatisfies_pure
  | inr other => apply adapterSatisfies_error

theorem extremaConstruction_satisfies {F Ty Other I Kw R W E : Type}
    (ops : ExtremaPublicOps (AdapterEval W E) F Ty Other I Kw R)
    (f : ExtremaArgument F Ty) :
    AdapterSatisfies (extremaConstructionTrace (ops.customConstructor f) f)
      (if ops.customConstructor f then (observedExtremaPublicOps ops).construct f
       else pure (makeExtremaMap f)) := by
  cases h : ops.customConstructor f with
  | true =>
    simp only [Bool.true_eq, ite_true, extremaConstructionTrace]
    apply adapterSatisfies_call
  | false =>
    simp only [Bool.false_eq_true, ite_false, extremaConstructionTrace]
    intro world priorEvents answer after events hc
    change some (.ok (makeExtremaMap f), world, priorEvents) = some (answer, after, events) at hc
    cases hc
    refine ⟨[], by simp, rfl, rfl, _, rfl, ?_⟩
    cases f <;> exact ⟨rfl, rfl⟩

theorem extremaPublicObservation_proven : ExtremaPublicObservation := by
  intro F Ty Other I Kw R W E ops f itr kw world
  apply adapterSatisfies_observed
  cases h : ops.customConstructor f
  all_goals simp only [extremaMapped, observedExtremaPublicOps, h, Bool.false_eq_true, ite_false, ite_true]
  all_goals apply adapterSatisfies_bind
  all_goals first
    | simpa only [h, observedExtremaPublicOps, Bool.false_eq_true, ite_false, ite_true] using
        extremaConstruction_satisfies (I := I) (Kw := Kw) (R := R) ops f
    | (intro constructed; apply adapterSatisfies_call)

theorem findMaxColonObservation_proven : FindMaxColonObservation := by
  intro W E V ops f domain colonArg world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro paired
  apply adapterSatisfies_call

theorem findMinColonObservation_proven : FindMinColonObservation := by
  intro W E V ops f domain colonArg world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro paired
  apply adapterSatisfies_call

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

theorem fieldRead_satisfies {W E V Event : Type}
    (fields : W → V → FoldObjectView V) (object : V) (index : JInt .i64)
    (position : Nat) (hi : index.val = (position : Int) + 1) :
    AdapterSatisfies (adapterFieldTrace (Event := Event) fields object position)
      (do
        let state ← get
        match foldFieldRead (E := E) (fields state.1 object) index with
        | .ok value => pure value
        | .error error => throw error) := by
  intro world priorEvents answer after events h
  dsimp [get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, StateT.map, Functor.map, StateT.get, bind, ExceptT.bind, ExceptT.mk,
    StateT.bind, ExceptT.bindCont, ExceptT.run] at h
  have hn : ¬ index.val < 1 := by omega
  have hp : (index.val - 1).toNat = position := by omega
  cases hf : fields world object with
  | module =>
    simp only [foldFieldRead, hf] at h
    change some (.error .typeError, world, priorEvents) = some (answer, after, events) at h
    cases h
    exact ⟨[], by simp, rfl, rfl, by simp [adapterFieldTrace, hf]⟩
  | fields slots valid =>
    cases hs : slots[position]? with
    | none =>
      simp only [foldFieldRead, hf, hn, ite_false, hp, hs] at h
      change some (.error .boundsError, world, priorEvents) = some (answer, after, events) at h
      cases h
      exact ⟨[], by simp, rfl, rfl, by simp [adapterFieldTrace, hf, hs]⟩
    | some slot =>
      cases slot with
      | none =>
        simp only [foldFieldRead, hf, hn, ite_false, hp, hs] at h
        change some (.error .undefRefError, world, priorEvents) = some (answer, after, events) at h
        cases h
        exact ⟨[], by simp, rfl, rfl, by simp [adapterFieldTrace, hf, hs]⟩
      | some value =>
        simp only [foldFieldRead, hf, hn, ite_false, hp, hs] at h
        change some (.ok value, world, priorEvents) = some (answer, after, events) at h
        cases h
        exact ⟨[], by simp, rfl, rfl, by simp [adapterFieldTrace, hf, hs]⟩

theorem findPair_satisfies {W E V : Type} (ops : FlatteningAdapterOps W E V)
    (value : FlattenTransformResult V) :
    AdapterSatisfies (findPairTrace ops value)
      (flatteningDestructure (observedFindPairOps ops) value) := by
  cases value with
  | pair a b => exact adapterSatisfies_pure _
  | custom object =>
    apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
    intro first
    apply adapterSatisfies_bind (fieldRead_satisfies _ _ _ 0 rfl)
    intro a
    apply adapterSatisfies_bind (fieldRead_satisfies _ _ _ 1 rfl)
    intro state
    apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
    intro second
    apply adapterSatisfies_bind (fieldRead_satisfies _ _ _ 0 rfl)
    intro b
    apply adapterSatisfies_pure

theorem extremaPair_satisfies {W E V : Type} (ops : FlatteningAdapterOps W E V)
    (value : FlattenTransformResult V) :
    AdapterSatisfies (extremaPairTrace ops value)
      (flatteningDestructure (observedExtremaPairOps ops) value) := by
  cases value with
  | pair a b => exact adapterSatisfies_pure _
  | custom object =>
    apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
    intro first
    apply adapterSatisfies_bind (fieldRead_satisfies _ _ _ 0 rfl)
    intro a
    apply adapterSatisfies_bind (fieldRead_satisfies _ _ _ 1 rfl)
    intro state
    apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
    intro second
    apply adapterSatisfies_bind (fieldRead_satisfies _ _ _ 0 rfl)
    intro b
    apply adapterSatisfies_pure

theorem findCondition_satisfies {W E V : Type} (condition : Bool ⊕ V) :
    AdapterSatisfies (findConditionTrace (W := W) (E := E) condition) (findCondition condition) := by
  cases condition with
  | inl b => exact adapterSatisfies_pure _
  | inr value => exact adapterSatisfies_error _

theorem findMaxReducerObservation_proven : FindMaxReducerObservation := by
  intro W E V pairOps ops left right world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (findPair_satisfies _ _)
  intro a
  apply adapterSatisfies_bind (findPair_satisfies _ _)
  intro b
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro condition
  apply adapterSatisfies_bind (findCondition_satisfies _)
  intro better
  cases better <;> apply adapterSatisfies_pure

theorem findMinReducerObservation_proven : FindMinReducerObservation := by
  intro W E V pairOps ops left right world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (findPair_satisfies _ _)
  intro a
  apply adapterSatisfies_bind (findPair_satisfies _ _)
  intro b
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro condition
  apply adapterSatisfies_bind (findCondition_satisfies _)
  intro better
  cases better <;> apply adapterSatisfies_pure

theorem findIndexedClosureObservation_proven : FindIndexedClosureObservation := by
  intro W E V pairOps invoke closure argument world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (findPair_satisfies _ _)
  intro pair
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro mapped
  apply adapterSatisfies_pure

theorem findValueClosureObservation_proven : FindValueClosureObservation := by
  intro W E V invoke closure x world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro mapped
  apply adapterSatisfies_pure

theorem extremaReducerObservation_proven : ExtremaReducerObservation := by
  intro W E V pairOps ops left right world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (extremaPair_satisfies _ _)
  intro a
  apply adapterSatisfies_bind (extremaPair_satisfies _ _)
  intro b
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro lo
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro hi
  apply adapterSatisfies_pure

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

theorem emptyAdaptersObservation_proven : EmptyAdaptersObservation := by
  intro V W E ops bottom mapping filtering flattening flipped op T world
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals apply adapterSatisfies_observed
  all_goals repeat' first
    | apply adapterSatisfies_property
    | apply adapterSatisfies_call
    | apply adapterSatisfies_bind
    | intro value

theorem foldlDispatchObservation_proven : FoldlDispatchObservation := by
  intro Op I V W E fold empty op init itr world
  dsimp only [foldlImpl, observedFoldlOps, ExceptT.run, ExceptT.mk,
    bind, ExceptT.bind, ExceptT.bindCont, StateT.bind]
  cases hf : fold op init itr world with
  | none => trivial
  | some answer =>
    obtain ⟨answer, middle⟩ := answer
    cases answer with
    | error error => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inr ⟨error, rfl⟩⟩
    | ok result =>
      cases result with
      | value value => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inl ⟨value, rfl⟩⟩
      | initial =>
        dsimp only [Option.bind, pure, ExceptT.pure, StateT.pure, ExceptT.mk]
        cases he : empty op itr middle with
        | none => trivial
        | some last => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mapreduceMultiProvenance_proven : MapreduceMultiProvenance := by
  intro F Op I Tail Kw G R W E generator reduce f op itr tail kw world
  dsimp only [mapreduceMultiPublic, auditMultiMapreduce, ExceptT.run, ExceptT.mk,
    bind, ExceptT.bind, ExceptT.bindCont, StateT.bind]
  cases hg : generator f itr tail world with
  | none => trivial
  | some answer =>
    obtain ⟨answer, middle⟩ := answer
    cases answer with
    | error error =>
      exact ⟨⟨(f, itr, tail), world, .error error, middle⟩, rfl, rfl, rfl, rfl, rfl⟩
    | ok generated =>
      dsimp only [Option.bind, pure, ExceptT.pure, StateT.pure, ExceptT.mk]
      cases hr : reduce op generated kw middle with
      | none => trivial
      | some result =>
        exact ⟨⟨(f, itr, tail), world, .ok generated, middle⟩, rfl, rfl,
          ⟨(op, generated, kw), middle, result.1, result.2⟩, rfl, rfl, rfl, rfl, rfl⟩

theorem realOperatorObservation_proven : RealOperatorObservation := by
  intro A B Real Other W E binary convertReal x y world
  have h : RealObservationInvariant x y world
      ((addSumReal (observedRealOps binary convertReal) x y).run.run (world, [])) := by
    dsimp only [addSumReal, observedRealOps, observeRealBinary, observeRealConversion,
      ExceptT.run, ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont, StateT.bind]
    cases hb : binary x y world with
    | none => trivial
    | some answer =>
      obtain ⟨answer, middle⟩ := answer
      cases answer with
      | error error => exact ⟨rfl, rfl, rfl, rfl, Or.inr ⟨error, rfl, rfl⟩⟩
      | ok value =>
        cases value with
        | inl value => exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨value, rfl, rfl⟩⟩
        | inr other =>
          dsimp only [returnReal, Option.bind, pure, ExceptT.pure, StateT.pure, ExceptT.mk,
            Except.map, bind, ExceptT.bind, ExceptT.bindCont, StateT.bind, observeRealConversion]
          cases hc : convertReal other middle with
          | none => trivial
          | some answer =>
            obtain ⟨answer, after⟩ := answer
            cases answer with
            | error error => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inr (Or.inl ⟨error, rfl, rfl⟩)⟩
            | ok value =>
              cases value with
              | inl value => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inl ⟨value, rfl, rfl⟩⟩
              | inr other => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inr (Or.inr ⟨other, rfl, rfl⟩)⟩
  exact ⟨h, h⟩

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

theorem adjointPair_satisfies {W E V : Type} (ops : GenericAdjointOps W E V)
    (result : TransformPairResult V V V) :
    AdapterSatisfies (adjointPairTrace ops result)
      (destructureTransformPair (observedAdjointOps ops).raw result) := by
  cases result with
  | pair a b => exact adapterSatisfies_pure _
  | custom object firstView secondView =>
    apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
    intro first
    apply adapterSatisfies_bind (fieldRead_satisfies _ _ _ 0 rfl)
    intro a
    apply adapterSatisfies_bind (fieldRead_satisfies _ _ _ 1 rfl)
    intro state
    apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
    intro second
    apply adapterSatisfies_bind (fieldRead_satisfies _ _ _ 0 rfl)
    intro b
    apply adapterSatisfies_pure

theorem adjointObservation_proven : AdjointObservation := by
  intro W E V ops op itr world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro unwrapped
  apply adapterSatisfies_bind (adjointPair_satisfies _ _)
  intro pair
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro value
  apply adapterSatisfies_pure

theorem flatteningAdapterObservation_proven : FlatteningAdapterObservation := by
  intro W E V ops op acc x world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (adapterSatisfies_property _ _ _ _)
  intro rf
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro result
  cases result with
  | pair operator iterator =>
    change AdapterSatisfies _ (pure (operator, iterator) >>= _)
    simp only [pure_bind]
    apply adapterSatisfies_call
  | custom object =>
    simp only [flatteningDestructure, bind_assoc, pure_bind]
    apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
    intro first
    apply adapterSatisfies_bind (fieldRead_satisfies _ _ _ 0 rfl)
    intro operator
    apply adapterSatisfies_bind (fieldRead_satisfies _ _ _ 1 rfl)
    intro state
    apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
    intro second
    apply adapterSatisfies_bind (fieldRead_satisfies _ _ _ 0 rfl)
    intro iterator
    apply adapterSatisfies_call

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

theorem AdapterSatisfies.mono {A W E Event : Type}
    {first next : AdapterTrace Event W E A} {call : AdapterEval (W × List Event) E A}
    (h : AdapterSatisfies first call)
    (imp : ∀ before events answer after, first before events answer after → next before events answer after) :
    AdapterSatisfies next call := by
  intro world priorEvents answer after events hc
  obtain ⟨suffix, he, hs⟩ := h world priorEvents answer after events hc
  exact ⟨suffix, he, imp _ _ _ _ hs⟩

theorem countInitial_valid {V : Type} (init : Option (CountArgument V)) :
    CountInitialValue init (countInitial init) := by
  cases init <;> rfl

theorem countClosure_satisfies {F I V OtherClosure R W E : Type}
    (ops : CountGeneralOps (AdapterEval W E) F I V OtherClosure R) (f : F) :
    AdapterSatisfies (countClosureTrace (I := I) (V := V) (R := R) (ops.selectBool f) f)
      (if ops.selectBool f then (observedCountGeneralOps ops).bool f
       else pure (.known (makeBoolClosure f))) := by
  cases h : ops.selectBool f
  · simp only [Bool.false_eq_true, ite_false, countClosureTrace]
    apply (adapterSatisfies_pure (W := W) (E := E)
      (Event := CountGeneralEvent F I V OtherClosure R W E)
      (BoolClosureResult.known (Other := OtherClosure) (makeBoolClosure f))).mono
    intro before events answer after hs
    exact ⟨hs.1, hs.2.2, _, hs.2.1, rfl⟩
  · simp only [ite_true, countClosureTrace]
    apply adapterSatisfies_call

theorem countForwardingObservation_proven : CountForwardingObservation := by
  intro F I V OtherClosure R W E ops f itr init explicit world
  refine ⟨countInitial_valid init, ?_, ?_, ?_⟩
  · apply adapterSatisfies_observed
    apply (adapterSatisfies_call _ _ _).mono
    intro before events answer after hs
    exact ⟨⟨countInitial init⟩, countInitial_valid init, hs⟩
  · apply adapterSatisfies_observed
    apply (adapterSatisfies_call _ _ _).mono
    intro before events answer after hs
    exact ⟨countInitial init, countInitial_valid init, hs⟩
  · apply adapterSatisfies_observed
    cases h : ops.selectBool f
    all_goals simp only [simpleCount, observedCountGeneralOps, h, Bool.false_eq_true, ite_false, ite_true]
    all_goals apply adapterSatisfies_bind
    all_goals first
      | simpa only [h, observedCountGeneralOps, Bool.false_eq_true, ite_false, ite_true] using
          countClosure_satisfies ops f
      | (intro mapped; apply adapterSatisfies_call)

theorem emptyMappingConstruction_satisfies {V W E : Type}
    (ops : EmptyIteratorOps (AdapterEval W E) V) (f : EmptyMapperArgument V) (op : V) :
    AdapterSatisfies (emptyMappingConstructionTrace (ops.selectMapping f op) f op)
      (if ops.selectMapping f op then (observedEmptyIteratorOps ops).mapping f op
       else pure (emptyMappingConstructor f op)) := by
  cases h : ops.selectMapping f op
  · simp only [Bool.false_eq_true, ite_false, emptyMappingConstructionTrace]
    apply (adapterSatisfies_pure (emptyMappingConstructor f op)).mono
    intro before events answer after hs
    refine ⟨hs.1, hs.2.2.symm, _, hs.2.1, ?_⟩
    cases f <;> exact ⟨rfl, rfl, rfl⟩
  · simp only [ite_true, emptyMappingConstructionTrace]
    apply adapterSatisfies_call

theorem emptyFlattenConstruction_satisfies {V W E : Type}
    (ops : EmptyIteratorOps (AdapterEval W E) V) (itr : V) :
    AdapterSatisfies (emptyFlattenConstructionTrace ops itr)
      (emptyFlattenConstructor (observedEmptyIteratorOps ops) itr) := by
  cases h : ops.selectFlatten itr
  · cases hc : ops.selectFlattenConstructor itr
    · simpa [emptyFlattenConstructionTrace, emptyFlattenConstructor, observedEmptyIteratorOps, h, hc] using
        (adapterSatisfies_pure (W := W) (E := E) (Event := EmptyIteratorEvent V W E)
          (EmptyFlattenValue.known itr))
    · simpa [emptyFlattenConstructionTrace, emptyFlattenConstructor, observedEmptyIteratorOps, h, hc] using
        (adapterSatisfies_call (ops.flattenConstructor itr) itr EmptyIteratorEvent.flattenConstructor)
  · simpa [emptyFlattenConstructionTrace, emptyFlattenConstructor, observedEmptyIteratorOps, h] using
      (adapterSatisfies_call (ops.flatten itr) itr EmptyIteratorEvent.flatten)

theorem emptyIteratorObservation_proven : EmptyIteratorObservation := by
  intro V W E ops f op itr trait flattening staticType world
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply adapterSatisfies_observed
    cases h : ops.selectMapping f op
    all_goals simp only [mapemptyIterator, observedEmptyIteratorOps, h, Bool.false_eq_true, ite_false, ite_true]
    all_goals apply adapterSatisfies_bind
    all_goals first
      | simpa only [h, observedEmptyIteratorOps, Bool.false_eq_true, ite_false, ite_true] using
          emptyMappingConstruction_satisfies ops f op
      | (intro mapped; apply adapterSatisfies_call)
  · apply adapterSatisfies_observed
    apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
    intro result
    apply adapterSatisfies_call
  · apply adapterSatisfies_observed
    apply adapterSatisfies_bind (adapterSatisfies_property _ _ _ _)
    intro rf
    apply adapterSatisfies_bind (emptyFlattenConstruction_satisfies ops itr)
    intro flattened
    apply adapterSatisfies_call
  · apply adapterSatisfies_observed
    apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
    intro T
    apply adapterSatisfies_call
  · cases staticType <;> apply adapterSatisfies_observed <;> apply adapterSatisfies_call

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

theorem foldCall_satisfies {W E I V O A : Type} (call : FoldEval W (FoldError E) A)
    (event : W → Except (FoldError E) A → W → FoldCall W E I V O) :
    AdapterSatisfies (foldLeafTrace event) (observeFoldCall call event) := by
  intro world priorEvents answer after events h
  dsimp [observeFoldCall, ExceptT.mk] at h
  cases hc : call world with
  | none => simp [hc] at h
  | some result =>
    simp [hc] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨_, rfl, rfl⟩

theorem foldPure_satisfies {W E I V O A : Type} (value : A) :
    AdapterSatisfies (foldPureTrace (W := W) (E := E) (I := I) (V := V) (O := O) value)
      (pure value) := by
  apply (adapterSatisfies_pure value).mono
  intro before events answer after h
  exact ⟨h.1, h.2.1, h.2.2.symm⟩

theorem foldSatisfies_bind {W E I V O A B : Type}
    (first : FoldTrace W E I V O A) (next : A → FoldTrace W E I V O B)
    (call : FoldEval (W × List (FoldCall W E I V O)) (FoldError E) A)
    (cont : A → FoldEval (W × List (FoldCall W E I V O)) (FoldError E) B)
    (hf : AdapterSatisfies first call) (hn : ∀ x, AdapterSatisfies (next x) (cont x)) :
    AdapterSatisfies (foldThenTrace first next) (call >>= cont) := by
  apply (adapterSatisfies_bind hf hn).mono
  intro before events answer after h
  obtain ⟨earlier, later, firstAnswer, middle, he, hf, hn⟩ := h
  refine ⟨earlier, later, firstAnswer, middle, he, hf, ?_⟩
  cases firstAnswer <;> exact hn

theorem restConstructor_satisfies {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (iterator : FoldIterator I V) (state : V) :
    AdapterSatisfies (RestConstructorTrace ops iterator state)
      (foldRestConstruct (observeFoldOps ops) iterator state) := by
  cases h : ops.selectedRestConstructor iterator state with
  | none => simpa [RestConstructorTrace, foldRestConstruct, observeFoldOps, h] using
      (foldPure_satisfies (W := W) (E := E) (I := I) (V := V) (O := O) (FoldIterator.knownRest iterator state))
  | some call => simpa [RestConstructorTrace, foldRestConstruct, observeFoldOps, h] using
      (foldCall_satisfies call (FoldCall.construct iterator state))

theorem restConstruction_satisfies {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (iterator : FoldIterator I V) (state : V) :
    AdapterSatisfies (RestConstructionTrace ops iterator state)
      (foldRest (observeFoldOps ops) iterator state) := by
  cases h : ops.selectedRest iterator state with
  | some call => simpa [RestConstructionTrace, foldRest, observeFoldOps, h] using
      (foldCall_satisfies call (FoldCall.selectedRest iterator state))
  | none =>
    cases iterator with
    | ordinary handle => simpa [RestConstructionTrace, foldRest, observeFoldOps, h] using
        restConstructor_satisfies ops (.ordinary handle) state
    | customRest handle => simpa [RestConstructionTrace, foldRest, observeFoldOps, h] using
        (foldCall_satisfies (ops.customRest handle state) (FoldCall.rest handle state))
    | knownRest inner stored =>
      simp only [RestConstructionTrace, h, foldRest, observeFoldOps, Option.map_none]
      apply foldSatisfies_bind
      · cases hp : ops.selectedRestIteratorProperty (.knownRest inner stored) with
        | none => simpa [foldRestItr, observeFoldOps, hp] using
            (foldPure_satisfies (W := W) (E := E) (O := O) inner)
        | some call => simpa [foldRestItr, observeFoldOps, hp] using
            (foldCall_satisfies call (FoldCall.itrRead (.knownRest inner stored)))
      · intro observed
        exact restConstructor_satisfies ops observed state

theorem restConstructionObservation_proven : RestConstructionObservation := by
  intro W E I V O ops iterator state world
  cases hc : foldRest (observeFoldOps ops) iterator state (world, []) with
  | none => trivial
  | some result =>
    obtain ⟨answer, after, events⟩ := result
    obtain ⟨suffix, he, hs⟩ := restConstruction_satisfies ops iterator state world [] answer after events hc
    simp only [List.nil_append] at he
    subst events
    exact hs

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

theorem adapterSatisfies_admissible {A W E Event : Type} (spec : AdapterTrace Event W E A) :
    Lean.Order.admissible (fun call => AdapterSatisfies spec call) := by
  have heq : (fun call : AdapterEval (W × List Event) E A => AdapterSatisfies spec call) =
      (fun call => ∀ input result, call input = some result →
        ∃ suffix, result.2.2 = input.2 ++ suffix ∧ spec input.1 suffix result.1 result.2.1) := by
    funext call
    apply propext
    constructor
    · intro h input result hc
      exact h input.1 input.2 result.1 result.2.1 result.2.2 hc
    · intro h world priorEvents answer after events hc
      exact h (world, priorEvents) (answer, after, events) hc
  rw [heq]
  refine Lean.Order.admissible_pi_apply (fun (input : W × List Event) output =>
    ∀ result : Except E A × (W × List Event), output = some result →
      ∃ suffix, result.2.2 = input.2 ++ suffix ∧ spec input.1 suffix result.1 result.2.1) ?_
  intro input
  refine Lean.Order.admissible_pi (fun output (result : Except E A × (W × List Event)) =>
    output = some result → ∃ suffix, result.2.2 = input.2 ++ suffix ∧
      spec input.1 suffix result.1 result.2.1) ?_
  intro result
  exact Lean.Order.Option.admissible_eq_some _ result

theorem restIteration_satisfies {W E I V O : Type} (ops : FoldProtocolOps W E I V O) :
    ∀ iterator state, AdapterSatisfies (RestIterationTrace ops iterator state)
      (foldIterate (observeFoldOps ops) iterator state) := by
  apply foldIterate.fixpoint_induct (observeFoldOps ops)
    (fun loop => ∀ iterator state, AdapterSatisfies (RestIterationTrace ops iterator state) (loop iterator state))
  · refine Lean.Order.admissible_pi_apply (fun (iterator : FoldIterator I V)
      (output : Option V → FoldEval (W × List (FoldCall W E I V O)) (FoldError E) (Option V)) =>
      ∀ state, AdapterSatisfies (RestIterationTrace ops iterator state) (output state)) ?_
    intro iterator
    refine Lean.Order.admissible_pi_apply (fun (state : Option V)
      (output : FoldEval (W × List (FoldCall W E I V O)) (FoldError E) (Option V)) =>
      AdapterSatisfies (RestIterationTrace ops iterator state) output) ?_
    intro state
    exact adapterSatisfies_admissible _
  · intro loop ih iterator state
    cases iterator with
    | ordinary handle =>
      apply (foldCall_satisfies (ops.iterate handle state) (FoldCall.iterate handle state)).mono
      intro before events answer after h
      rw [h]
      exact .ordinary handle state before answer after
    | customRest handle =>
      apply (foldCall_satisfies (ops.iterate handle state) (FoldCall.iterate handle state)).mono
      intro before events answer after h
      rw [h]
      exact .opaqueIterator handle state before answer after
    | knownRest inner stored =>
      cases hs : ops.selectedRestIterate (.knownRest inner stored) state with
      | some call =>
        simp only [observeFoldOps, hs, Option.map_some]
        apply (foldCall_satisfies call (FoldCall.restIterate (.knownRest inner stored) state)).mono
        intro before events answer after h
        rw [h]
        exact .selected inner stored state before answer after (by simp [hs])
      | none =>
        simp only [observeFoldOps, hs, Option.map_none]
        cases state with
        | none =>
          cases hp : ops.selectedRestStateProperty (.knownRest inner stored) with
          | none =>
            simp only [foldRestState, observeFoldOps, hp, Option.map_none, pure_bind]
            apply (ih (.knownRest inner stored) (some stored)).mono
            intro before events answer after h
            exact .storedState inner stored before after events answer (by simp [hs]) (by simp [hp]) h
          | some call =>
            simp only [foldRestState, observeFoldOps, hp, Option.map_some]
            apply (adapterSatisfies_bind (foldCall_satisfies call (FoldCall.stRead (.knownRest inner stored)))
              (fun observed => ih (.knownRest inner stored) (some observed))).mono
            intro before events answer after h
            obtain ⟨earlier, later, firstAnswer, middle, he, hf, hn⟩ := h
            change earlier = [FoldCall.stRead (.knownRest inner stored) before firstAnswer middle] at hf
            subst earlier
            cases firstAnswer with
            | error error =>
              obtain ⟨rfl, rfl, rfl⟩ := hn
              simp only [List.append_nil] at he
              subst events
              exact .stateError inner stored before after error (by simp [hs]) (by simp [hp])
            | ok observed =>
              subst events
              exact .stateStep inner stored observed before middle after later answer
                (by simp [hs]) (by simp [hp]) hn
        | some explicit =>
          cases hp : ops.selectedRestIteratorProperty (.knownRest inner stored) with
          | none =>
            simp only [foldRestItr, observeFoldOps, hp, Option.map_none, pure_bind]
            apply (ih inner (some explicit)).mono
            intro before events answer after h
            exact .storedIterator inner stored explicit before after events answer (by simp [hs]) (by simp [hp]) h
          | some call =>
            simp only [foldRestItr, observeFoldOps, hp, Option.map_some]
            apply (adapterSatisfies_bind (foldCall_satisfies call (FoldCall.itrRead (.knownRest inner stored)))
              (fun observed => ih observed (some explicit))).mono
            intro before events answer after h
            obtain ⟨earlier, later, firstAnswer, middle, he, hf, hn⟩ := h
            change earlier = [FoldCall.itrRead (.knownRest inner stored) before firstAnswer middle] at hf
            subst earlier
            cases firstAnswer with
            | error error =>
              obtain ⟨rfl, rfl, rfl⟩ := hn
              simp only [List.append_nil] at he
              subst events
              exact .iteratorError inner stored explicit before after error (by simp [hs]) (by simp [hp])
            | ok observed =>
              subst events
              exact .iteratorStep inner observed stored explicit before middle after later answer
                (by simp [hs]) (by simp [hp]) hn

theorem restIterationObservation_proven : RestIterationObservation := by
  intro W E I V O ops iterator state world
  cases hc : foldIterate (observeFoldOps ops) iterator state (world, []) with
  | none => trivial
  | some result =>
    obtain ⟨answer, after, events⟩ := result
    obtain ⟨suffix, he, hs⟩ := restIteration_satisfies ops iterator state world [] answer after events hc
    simp only [List.nil_append] at he
    subst events
    exact hs

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

theorem filteringRun {W E F RF Acc Input Other : Type}
    (ops : FilteringAdapterOps (AdapterEval W E) F RF Acc Input Other)
    (op : FilteringAdapter F RF) (acc : Acc) (x : Input) :
    (filteringApply (observedFilteringAdapterOps ops) op acc x).run = (do
      let f ← readSelectedProperty (liftPropertySelection ops.fProperty FilteringAdapterEvent.fRead) FilteringAdapter.f op
      let condition ← observeAdapterEffect (ops.predicate f x) (f, x) FilteringAdapterEvent.predicate
      match condition with
      | .inl false => pure (.ok acc)
      | .inl true => do
          let rf ← readSelectedProperty (liftPropertySelection ops.rfProperty FilteringAdapterEvent.rfRead) FilteringAdapter.rf op
          let value ← observeAdapterEffect (ops.call rf acc x) (rf, acc, x) FilteringAdapterEvent.reduce
          pure (.ok value)
      | .inr _ => pure (.error .typeError)) := by
  cases hf : ops.fProperty <;> cases hr : ops.rfProperty <;>
    simp [filteringApply, observedFilteringAdapterOps, hf, hr, liftFilteringProperty,
      readSelectedProperty, liftPropertySelection, observeFilteringEffect, ExceptT.run_bind,
      ExceptT.run_mk, bind_assoc, pure_bind]
  case stored.stored | stored.custom =>
    congr 1
    funext condition
    cases condition with
    | inl b => cases b <;> simp [assertBool, liftExcept, ExceptT.run_bind, bind_assoc]
    | inr other => simp [assertBool, liftExcept, ExceptT.run_bind, bind_assoc]
  case custom.stored | custom.custom =>
    congr 1
    funext f
    congr 1
    funext condition
    cases condition with
    | inl b => cases b <;> simp [assertBool, liftExcept, ExceptT.run_bind, bind_assoc]
    | inr other => simp [assertBool, liftExcept, ExceptT.run_bind, bind_assoc]

theorem filteringLiftedCall_satisfies {Args A W E F RF Acc Input Other : Type}
    (call : AdapterEval W E A) (args : Args)
    (tag : AdapterCall Args A W E → FilteringAdapterEvent W E F RF Acc Input Other) :
    AdapterSatisfies (adapterLiftedCallTrace args tag)
      (do let value ← observeAdapterEffect call args tag; pure (.ok value : Except BoolTypeError A)) := by
  intro world priorEvents answer after events h
  dsimp [bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, StateT.bind, observeAdapterEffect] at h
  cases hc : call world with
  | none => simp [hc] at h
  | some result =>
    obtain ⟨result, last⟩ := result
    cases result with
    | error error =>
      simp [hc] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨_, rfl, ⟨args, world, .error error, _⟩, rfl, rfl, rfl, rfl, rfl⟩
    | ok value =>
      simp [hc] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨_, rfl, ⟨args, world, .ok value, _⟩, rfl, rfl, rfl, rfl, rfl⟩

theorem filteringAdapterObservation_proven : FilteringAdapterObservation := by
  intro W E F RF Acc Input Other ops op acc x world
  rw [filteringRun]
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (adapterSatisfies_property _ _ _ _)
  intro f
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro condition
  cases condition with
  | inr value => apply adapterSatisfies_pure
  | inl b =>
    cases b
    · apply adapterSatisfies_pure
    · apply adapterSatisfies_bind (adapterSatisfies_property _ _ _ _)
      intro rf
      apply filteringLiftedCall_satisfies

open JuliaLean JuliaLean.base.reduce JuliaLean.base.reduce.Models2Group7

theorem embed_call_satisfies {Args A W E Event Event' : Type}
    (call : AdapterEval W E A) (args : Args) (event : AdapterCall Args A W E → Event)
    (tag : Event → Event') :
    AdapterSatisfies (embedAdapterTrace tag (adapterCallTrace args event))
      (observeAdapterEffect call args (fun c => tag (event c))) := by
  apply (adapterSatisfies_call call args (fun c => tag (event c))).mono
  intro before events answer after h
  obtain ⟨c, he, ha, hb, hr, hw⟩ := h
  exact ⟨[event c], he, c, rfl, ha, hb, hr, hw⟩

theorem embed_pure_satisfies {A W E Event Event' : Type} (value : A) (tag : Event → Event') :
    AdapterSatisfies (embedAdapterTrace tag (adapterPureTrace (W := W) (E := E) value))
      (pure value) := by
  apply (adapterSatisfies_pure value).mono
  intro before events answer after h
  exact ⟨[], h.1, rfl, h.2⟩

theorem embed_property_satisfies {Object A W E Event Event' : Type}
    (selection : PropertySelection (AdapterEval W E) Object A) (field : Object → A)
    (object : Object) (event : AdapterCall Object A W E → Event) (tag : Event → Event') :
    AdapterSatisfies (embedAdapterTrace tag (propertySelectionTrace selection field object event))
      (readSelectedProperty (liftPropertySelection selection (fun c => tag (event c))) field object) := by
  cases selection with
  | stored => exact embed_pure_satisfies _ _
  | custom call => exact embed_call_satisfies _ _ _ _

theorem embed_bind_satisfies {A B W E Event Event' : Type}
    (tag : Event → Event') (first : AdapterTrace Event W E A) (next : A → AdapterTrace Event W E B)
    (call : AdapterEval (W × List Event') E A) (cont : A → AdapterEval (W × List Event') E B)
    (hf : AdapterSatisfies (embedAdapterTrace tag first) call)
    (hn : ∀ a, AdapterSatisfies (embedAdapterTrace tag (next a)) (cont a)) :
    AdapterSatisfies (embedAdapterTrace tag (adapterThenTrace first next)) (call >>= cont) := by
  apply (adapterSatisfies_bind hf hn).mono
  intro before events answer after h
  obtain ⟨earlier, later, firstAnswer, middle, he, hf, hn⟩ := h
  obtain ⟨inner, hei, hfi⟩ := hf
  cases firstAnswer with
  | error error =>
    obtain ⟨rfl, rfl, rfl⟩ := hn
    refine ⟨inner, ?_, inner, [], .error error, _, by simp, hfi, rfl, rfl, rfl⟩
    simpa [hei] using he
  | ok value =>
    obtain ⟨last, hel, hnl⟩ := hn
    refine ⟨inner ++ last, ?_, inner, last, .ok value, middle, rfl, hfi, hnl⟩
    simp [he, hei, hel, List.map_append]

theorem rangeBottom_satisfies {W E Range F V Other : Type}
    (ops : RangeFoldOps W E Range F V Other) (op : BottomAdapter (RangeCallable F))
    (init : FoldInit V) (value : V) :
    AdapterSatisfies (embedAdapterTrace RangeFoldEvent.bottom
      (BottomAdapterTrace ops.bottom op (match init with | .initial => none | .value _ => some init) value))
      (match init with
       | .initial => bottomInitial (observedRangeFoldOps ops).bottom op value
       | .value _ => bottomApply (observedRangeFoldOps ops).bottom op init value) := by
  cases init <;> apply embed_bind_satisfies
  all_goals first
    | apply embed_property_satisfies
    | (intro rf; apply embed_call_satisfies)

theorem rangeFoldObservation_proven : RangeFoldObservation := by
  intro W E Range F V Other ops kind init range world
  apply adapterSatisfies_observed
  apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
  intro condition
  cases condition with
  | inr other => apply adapterSatisfies_error
  | inl b =>
    cases b
    · apply adapterSatisfies_bind (adapterSatisfies_call _ _ _)
      intro value
      cases h : ops.selectBottom kind init value
      · have hb := rangeBottom_satisfies ops (rangeFoldBottom kind) init value
        cases kind <;> cases init <;> simpa [observedRangeFoldOps, h, rangeFoldBottom, rangeFoldReducer] using hb
      · have hb := adapterSatisfies_call (ops.customBottom (rangeFoldBottom kind) init value)
            (rangeFoldBottom (F := F) kind, init, value)
            (RangeFoldEvent.custom (Range := Range) (F := F) (Other := Other))
        cases kind <;> simpa [observedRangeFoldOps, h, rangeFoldBottom, rangeFoldReducer] using hb
    · apply adapterSatisfies_pure

end JuliaLean.Proofs.base.reduce.Models2Group7

namespace JuliaLean.Proofs.base.reduce.Models2Group7.GenericFoldCompletion

open JuliaLean JuliaLean.base.reduce.Models2Group7
open JuliaLean.Proofs.base.reduce.Models2Group7

def TailLayer {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (op : O) (iterator : FoldIterator I V) (value : V) (state : Option V)
    (next : V → Option V → FoldTrace W E I V O V) : FoldTrace W E I V O V :=
  foldThenTrace (RestIterationTrace ops iterator state) fun result =>
    match result with
    | none => foldPureTrace value
    | some object =>
      foldThenTrace (adapterFieldTrace (E := E) (Event := FoldCall W E I V O) ops.fields object 0) fun item =>
      foldThenTrace (adapterFieldTrace (E := E) (Event := FoldCall W E I V O) ops.fields object 1) fun nextState =>
      foldThenTrace (foldLeafTrace (FoldCall.apply op value item)) fun nextValue =>
        next nextValue (some nextState)

inductive TailTrace {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (op : O) (iterator : FoldIterator I V) :
    V → Option V → FoldTrace W E I V O V where
  | iterationError {value state before events error after}
      (iteration : RestIterationTrace ops iterator state before events (.error error) after) :
      TailTrace ops op iterator value state before events (.error error) after
  | done {value state before events after}
      (iteration : RestIterationTrace ops iterator state before events (.ok none) after) :
      TailTrace ops op iterator value state before events (.ok value) after
  | firstError {value state before events object middle error}
      (iteration : RestIterationTrace ops iterator state before events (.ok (some object)) middle)
      (field : adapterFieldTrace (E := E) (Event := FoldCall W E I V O) ops.fields object 0 middle [] (.error error) middle) :
      TailTrace ops op iterator value state before events (.error error) middle
  | secondError {value state before events object middle item error}
      (iteration : RestIterationTrace ops iterator state before events (.ok (some object)) middle)
      (first : adapterFieldTrace (E := E) (Event := FoldCall W E I V O) ops.fields object 0 middle [] (.ok item) middle)
      (second : adapterFieldTrace (E := E) (Event := FoldCall W E I V O) ops.fields object 1 middle [] (.error error) middle) :
      TailTrace ops op iterator value state before events (.error error) middle
  | applyError {value state before events object middle item nextState error after}
      (iteration : RestIterationTrace ops iterator state before events (.ok (some object)) middle)
      (first : adapterFieldTrace (E := E) (Event := FoldCall W E I V O) ops.fields object 0 middle [] (.ok item) middle)
      (second : adapterFieldTrace (E := E) (Event := FoldCall W E I V O) ops.fields object 1 middle [] (.ok nextState) middle) :
      TailTrace ops op iterator value state before
        (events ++ [.apply op value item middle (.error error) after]) (.error error) after
  | step {value state before events object middle item nextState nextValue nextWorld tail answer after}
      (iteration : RestIterationTrace ops iterator state before events (.ok (some object)) middle)
      (first : adapterFieldTrace (E := E) (Event := FoldCall W E I V O) ops.fields object 0 middle [] (.ok item) middle)
      (second : adapterFieldTrace (E := E) (Event := FoldCall W E I V O) ops.fields object 1 middle [] (.ok nextState) middle)
      (rest : TailTrace ops op iterator nextValue (some nextState) nextWorld tail answer after) :
      TailTrace ops op iterator value state before
        (events ++ .apply op value item middle (.ok nextValue) nextWorld :: tail) answer after

theorem tailTrace_of_layer {W E I V O : Type} {ops : FoldProtocolOps W E I V O}
    {op iterator value state before events answer after}
    (h : TailLayer ops op iterator value state (TailTrace ops op iterator)
      before events answer after) :
    TailTrace ops op iterator value state before events answer after := by
  obtain ⟨initial, later, firstAnswer, middle, he, hi, hn⟩ := h
  subst events
  cases firstAnswer with
  | error error =>
      obtain ⟨rfl, rfl, rfl⟩ := hn
      simpa using TailTrace.iterationError hi
  | ok result =>
      cases result with
      | none =>
          obtain ⟨rfl, rfl, rfl⟩ := hn
          simpa using TailTrace.done hi
      | some object =>
          obtain ⟨read, remaining, readAnswer, readAfter, hr, hread, hnext⟩ := hn
          have first := hread
          obtain ⟨rfl, rfl, _⟩ := hread
          simp only [List.nil_append] at hr
          subst later
          cases readAnswer with
          | error error =>
              obtain ⟨rfl, rfl, rfl⟩ := hnext
              simpa using TailTrace.firstError hi first
          | ok item =>
              obtain ⟨read, remaining2, readAnswer, readAfter, hr, hread, hnext⟩ := hnext
              have second := hread
              obtain ⟨rfl, rfl, _⟩ := hread
              simp only [List.nil_append] at hr
              subst remaining
              cases readAnswer with
              | error error =>
                  obtain ⟨rfl, rfl, rfl⟩ := hnext
                  simpa using TailTrace.secondError hi first second
              | ok nextState =>
                  obtain ⟨call, remaining3, callAnswer, callAfter, hc, hcall, hnext⟩ := hnext
                  subst call
                  subst remaining2
                  cases callAnswer with
                  | error error =>
                      obtain ⟨rfl, rfl, rfl⟩ := hnext
                      simpa using TailTrace.applyError hi first second
                  | ok nextValue =>
                      exact TailTrace.step hi first second hnext

theorem field_satisfies {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (object : V) (index : JInt .i64) (position : Nat)
    (hi : index.val = (position : Int) + 1) :
    AdapterSatisfies (adapterFieldTrace ops.fields object position)
      (foldGetfield (observeFoldOps ops) object index) := by
  intro world priorEvents answer after events h
  dsimp [foldGetfield, observeFoldOps, get, getThe, MonadStateOf.get, liftM,
    monadLift, MonadLift.monadLift, ExceptT.lift, StateT.map, Functor.map,
    StateT.get, bind, ExceptT.bind, ExceptT.mk, StateT.bind, ExceptT.bindCont, ExceptT.run] at h
  have hn : ¬ index.val < 1 := by omega
  have hp : (index.val - 1).toNat = position := by omega
  cases hf : ops.fields world object with
  | module =>
    simp only [foldFieldRead, hf] at h
    change some (.error .typeError, world, priorEvents) = some (answer, after, events) at h
    cases h
    exact ⟨[], by simp, rfl, rfl, by simp [adapterFieldTrace, hf]⟩
  | fields slots valid =>
    cases hs : slots[position]? with
    | none =>
      simp only [foldFieldRead, hf, hn, ite_false, hp, hs] at h
      change some (.error .boundsError, world, priorEvents) = some (answer, after, events) at h
      cases h
      exact ⟨[], by simp, rfl, rfl, by simp [adapterFieldTrace, hf, hs]⟩
    | some slot =>
      cases slot with
      | none =>
        simp only [foldFieldRead, hf, hn, ite_false, hp, hs] at h
        change some (.error .undefRefError, world, priorEvents) = some (answer, after, events) at h
        cases h
        exact ⟨[], by simp, rfl, rfl, by simp [adapterFieldTrace, hf, hs]⟩
      | some value =>
        simp only [foldFieldRead, hf, hn, ite_false, hp, hs] at h
        change some (.ok value, world, priorEvents) = some (answer, after, events) at h
        cases h
        exact ⟨[], by simp, rfl, rfl, by simp [adapterFieldTrace, hf, hs]⟩

theorem tail_satisfies {W E I V O : Type} (ops : FoldProtocolOps W E I V O) :
    ∀ op iterator value state,
      AdapterSatisfies (TailTrace ops op iterator value state)
        (foldTail (observeFoldOps ops) op iterator value state) := by
  intro op iterator
  apply foldTail.fixpoint_induct (observeFoldOps ops) op iterator
    (fun loop => ∀ value state,
      AdapterSatisfies (TailTrace ops op iterator value state) (loop value state))
  · refine Lean.Order.admissible_pi_apply (fun (value : V)
      (output : Option V → FoldEval (W × List (FoldCall W E I V O)) (FoldError E) V) =>
      ∀ state, AdapterSatisfies (TailTrace ops op iterator value state) (output state)) ?_
    intro value
    refine Lean.Order.admissible_pi_apply (fun (state : Option V)
      (output : FoldEval (W × List (FoldCall W E I V O)) (FoldError E) V) =>
      AdapterSatisfies (TailTrace ops op iterator value state) output) ?_
    intro state
    exact adapterSatisfies_admissible _
  · intro loop ih value state
    apply AdapterSatisfies.mono (first := TailLayer ops op iterator value state (TailTrace ops op iterator))
    · unfold TailLayer
      apply foldSatisfies_bind
      · exact restIteration_satisfies ops iterator state
      · intro result
        cases result with
        | none => exact foldPure_satisfies value
        | some object =>
          apply foldSatisfies_bind
          · exact field_satisfies ops object (JuliaLean.base.int.lit .i64 1) 0 rfl
          · intro item
            apply foldSatisfies_bind
            · exact field_satisfies ops object (JuliaLean.base.int.lit .i64 2) 1 rfl
            · intro nextState
              apply foldSatisfies_bind
              · exact foldCall_satisfies (ops.apply op value item) (FoldCall.apply op value item)
              · intro nextValue
                exact ih nextValue (some nextState)
    · intro before events answer after h
      exact tailTrace_of_layer h

def NotReducer {W E I V O : Type} : FoldCall W E I V O → Prop
  | .apply .. => False
  | _ => True

theorem rest_notReducer {W E I V O : Type} {ops : FoldProtocolOps W E I V O}
    {iterator state before events answer after}
    (h : RestIterationTrace ops iterator state before events answer after) :
    ∀ event ∈ events, NotReducer event := by
  induction h <;> simp_all [NotReducer]

theorem rest_worldChain {W E I V O : Type} {ops : FoldProtocolOps W E I V O}
    {iterator state before events answer after}
    (h : RestIterationTrace ops iterator state before events answer after) :
    FoldWorldChain before events after := by
  induction h <;> simp_all [FoldWorldChain, foldCallBefore, foldCallAfter]

theorem errorsStop_cons {W E I V O : Type} (head : FoldCall W E I V O)
    (tail : List (FoldCall W E I V O)) (answer : Except (FoldError E) V)
    (hhead : foldCallError head = none) (htail : FoldErrorsStop tail answer) :
    FoldErrorsStop (head :: tail) answer := by
  intro before event after error he herr
  cases before with
  | nil =>
      have heq : head = event := (List.cons.inj he).1
      subst event
      simp [hhead] at herr
  | cons first rest =>
      exact htail rest event after error (List.cons.inj he).2 herr

theorem worldChain_append {W E I V O : Type}
    {prior suffix : List (FoldCall W E I V O)} {before middle after : W}
    (hp : FoldWorldChain before prior middle) (hs : FoldWorldChain middle suffix after) :
    FoldWorldChain before (prior ++ suffix) after := by
  induction prior generalizing before with
  | nil =>
      have h : middle = before := hp
      subst middle
      exact hs
  | cons event rest ih =>
      exact ⟨hp.1, ih hp.2⟩

theorem accumulatorChain_prefix {W E I V O : Type} (op : O) (value : V)
    (prior suffix : List (FoldCall W E I V O)) (answer : Except (FoldError E) V)
    (hp : ∀ event ∈ prior, NotReducer event) :
    FoldAccumulatorChain op value (prior ++ suffix) answer ↔
      FoldAccumulatorChain op value suffix answer := by
  induction prior with
  | nil => rfl
  | cons event rest ih =>
      have he := hp event (by simp)
      have ht : ∀ e ∈ rest, NotReducer e := fun e h => hp e (by simp [h])
      have hrec := ih ht
      cases event <;> simp_all [NotReducer, FoldAccumulatorChain]

theorem inputProvenance_prefix {W E I V O : Type} (fields : W → V → FoldObjectView V)
    (prior : List (FoldCall W E I V O)) (leaf : FoldCall W E I V O)
    (suffix : List (FoldCall W E I V O)) (previous : Option (FoldCall W E I V O))
    (hp : ∀ event ∈ prior, NotReducer event) (hl : NotReducer leaf) :
    FoldInputProvenance fields previous (prior ++ leaf :: suffix) ↔
      FoldInputProvenance fields (some leaf) suffix := by
  induction prior generalizing previous with
  | nil =>
      cases leaf <;> simp_all [NotReducer, FoldInputProvenance]
  | cons event rest ih =>
      have he := hp event (by simp)
      have ht : ∀ e ∈ rest, NotReducer e := fun e h => hp e (by simp [h])
      have hrec := ih (some event) ht
      cases event <;> simp_all [NotReducer, FoldInputProvenance]

def GenericTrace {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (op : O) (init : V) (iterator : FoldIterator I V) : FoldTrace W E I V O V :=
  foldThenTrace (RestIterationTrace ops iterator none) fun result =>
    match result with
    | none => foldPureTrace init
    | some object =>
      foldThenTrace (foldLeafTrace (FoldCall.getindex object (JuliaLean.base.int.lit .i64 1))) fun item =>
      foldThenTrace (foldLeafTrace (FoldCall.apply op init item)) fun value =>
      foldThenTrace (foldLeafTrace (FoldCall.getindex object (JuliaLean.base.int.lit .i64 2))) fun state =>
      foldThenTrace (RestConstructionTrace ops iterator state) fun rest =>
        TailTrace ops op rest value none

theorem generic_satisfies {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (op : O) (init : V) (iterator : FoldIterator I V) :
    AdapterSatisfies (GenericTrace ops op init iterator)
      (foldlGeneric (observeFoldOps ops) op init iterator) := by
  unfold GenericTrace foldlGeneric
  apply foldSatisfies_bind
  · exact restIteration_satisfies ops iterator none
  · intro result
    cases result with
    | none => exact foldPure_satisfies init
    | some object =>
      apply foldSatisfies_bind
      · exact foldCall_satisfies (ops.getindex object (JuliaLean.base.int.lit .i64 1)) _
      · intro item
        apply foldSatisfies_bind
        · exact foldCall_satisfies (ops.apply op init item) _
        · intro value
          apply foldSatisfies_bind
          · exact foldCall_satisfies (ops.getindex object (JuliaLean.base.int.lit .i64 2)) _
          · intro state
            apply foldSatisfies_bind
            · exact restConstruction_satisfies ops iterator state
            · intro rest
              exact tail_satisfies ops op rest value none

theorem genericTrace_start {W E I V O : Type} {ops : FoldProtocolOps W E I V O}
    {op init iterator before events answer after}
    (h : GenericTrace ops op init iterator before events answer after) :
    FoldStartObservation ops iterator init before events answer := by
  obtain ⟨initial, later, firstAnswer, middle, he, hi, hn⟩ := h
  refine ⟨initial, later, firstAnswer, middle, he, hi, ?_⟩
  cases firstAnswer with
  | error error => exact ⟨hn.1, hn.2.1⟩
  | ok result =>
      cases result with
      | none => exact ⟨hn.1, hn.2.1⟩
      | some object =>
          obtain ⟨read, rest, readAnswer, readAfter, hr, hread, _⟩ := hn
          exact ⟨readAnswer, readAfter, rest, by rw [hr, hread]; rfl⟩

theorem passive_provenance {W E I V O : Type} (fields : W → V → FoldObjectView V)
    (events : List (FoldCall W E I V O)) (previous : Option (FoldCall W E I V O))
    (h : ∀ event ∈ events, NotReducer event) :
    FoldInputProvenance fields previous events := by
  induction events generalizing previous with
  | nil => trivial
  | cons event rest ih =>
      have he := h event (by simp)
      have ht : ∀ e ∈ rest, NotReducer e := fun e hm => h e (by simp [hm])
      have hp := ih (some event) ht
      cases event <;> simp_all [NotReducer, FoldInputProvenance]

theorem errorsStop_single {W E I V O : Type} (event : FoldCall W E I V O)
    (answer : Except (FoldError E) V)
    (h : ∀ error, foldCallError event = some error → answer = .error error) :
    FoldErrorsStop [event] answer := by
  intro before observed after error he herr
  cases before with
  | nil =>
      have hhead : event = observed := (List.cons.inj he).1
      have htail : [] = after := (List.cons.inj he).2
      subst observed
      exact ⟨htail.symm, h error herr⟩
  | cons head rest =>
      have htail : [] = rest ++ observed :: after := (List.cons.inj he).2
      have hlength := congrArg List.length htail
      simp at hlength

theorem rest_stops {W E I V O : Type} {ops : FoldProtocolOps W E I V O}
    {iterator state before events answer after}
    (h : RestIterationTrace ops iterator state before events answer after) (value : V) :
    FoldErrorsStop events (answer.map (fun _ => value)) := by
  induction h with
  | ordinary handle state before answer after =>
      apply errorsStop_single
      intro error he
      cases answer <;> simp_all [foldCallError, Except.map]
  | opaqueIterator handle state before answer after =>
      apply errorsStop_single
      intro error he
      cases answer <;> simp_all [foldCallError, Except.map]
  | selected inner stored state before answer after selected =>
      apply errorsStop_single
      intro error he
      cases answer <;> simp_all [foldCallError, Except.map]
  | stateError inner stored before after error base selected =>
      apply errorsStop_single
      intro failure he
      simp only [foldCallError, Option.some.injEq] at he
      subst failure
      rfl
  | stateStep inner stored observed before middle after events answer base selected rest ih =>
      exact errorsStop_cons _ _ _ rfl ih
  | storedState inner stored before after events answer base storedGetter rest ih => exact ih
  | iteratorError inner stored explicit before after error base selected =>
      apply errorsStop_single
      intro failure he
      simp only [foldCallError, Option.some.injEq] at he
      subst failure
      rfl
  | iteratorStep inner observed stored explicit before middle after events answer base selected rest ih =>
      exact errorsStop_cons _ _ _ rfl ih
  | storedIterator inner stored explicit before after events answer base storedGetter rest ih => exact ih

def IterationLeaf {W E I V O : Type} (result : Option V) (world : W) :
    FoldCall W E I V O → Prop
  | .iterate _ _ _ answer after | .restIterate _ _ _ answer after =>
      answer = .ok result ∧ after = world
  | _ => False

theorem rest_last {W E I V O : Type} {ops : FoldProtocolOps W E I V O}
    {iterator state before events answer after}
    (h : RestIterationTrace ops iterator state before events answer after) :
    ∀ result, answer = .ok result → ∃ prior leaf,
      events = prior ++ [leaf] ∧ IterationLeaf result after leaf := by
  induction h with
  | ordinary handle state before answer after =>
      intro result he
      subst answer
      exact ⟨[], _, rfl, rfl, rfl⟩
  | opaqueIterator handle state before answer after =>
      intro result he
      subst answer
      exact ⟨[], _, rfl, rfl, rfl⟩
  | selected inner stored state before answer after selected =>
      intro result he
      subst answer
      exact ⟨[], _, rfl, rfl, rfl⟩
  | stateError inner stored before after error base selected =>
      intro result he
      cases he
  | stateStep inner stored observed before middle after events answer base selected rest ih =>
      intro result he
      obtain ⟨prior, leaf, hp, hl⟩ := ih result he
      exact ⟨.stRead (.knownRest inner stored) before (.ok observed) middle :: prior,
        leaf, by simp [hp], hl⟩
  | storedState inner stored before after events answer base storedGetter rest ih => exact ih
  | iteratorError inner stored explicit before after error base selected =>
      intro result he
      cases he
  | iteratorStep inner observed stored explicit before middle after events answer base selected rest ih =>
      intro result he
      obtain ⟨prior, leaf, hp, hl⟩ := ih result he
      exact ⟨.itrRead (.knownRest inner stored) before (.ok observed) middle :: prior,
        leaf, by simp [hp], hl⟩
  | storedIterator inner stored explicit before after events answer base storedGetter rest ih => exact ih

theorem noErrors_of_success {W E I V O : Type} (events : List (FoldCall W E I V O))
    (value : V) (h : FoldErrorsStop events (.ok value)) :
    ∀ event ∈ events, foldCallError event = none := by
  induction events with
  | nil => intro event hm; cases hm
  | cons head tail ih =>
      have htail : FoldErrorsStop tail (.ok value) := by
        intro before event after error he herr
        exact h (head :: before) event after error (by simpa using congrArg (List.cons head) he) herr
      intro event hm
      rcases List.mem_cons.mp hm with heq | hmem
      · subst event
        cases he : foldCallError head with
        | none => rfl
        | some error =>
            have contradiction := (h [] head tail error rfl he).2
            cases contradiction
      · exact ih htail event hmem

theorem errorsStop_append {W E I V O : Type} (prior suffix : List (FoldCall W E I V O))
    (answer : Except (FoldError E) V)
    (hp : ∀ event ∈ prior, foldCallError event = none)
    (hs : FoldErrorsStop suffix answer) : FoldErrorsStop (prior ++ suffix) answer := by
  induction prior with
  | nil => exact hs
  | cons event rest ih =>
      apply errorsStop_cons
      · exact hp event (by simp)
      · exact ih (fun e he => hp e (by simp [he]))

theorem field_ok {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (object : V) (position : Nat) (world : W) (value : V)
    (h : adapterFieldTrace (E := E) (Event := FoldCall W E I V O)
      ops.fields object position world [] (.ok value) world) :
    match ops.fields world object with
    | .module => False
    | .fields slots _ => slots[position]? = some (some value) := by
  cases hf : ops.fields world object with
  | module => simp [adapterFieldTrace, hf] at h
  | fields slots valid =>
      cases hs : slots[position]? with
      | none => simp [adapterFieldTrace, hf, hs] at h
      | some slot =>
          cases slot with
          | none => simp [adapterFieldTrace, hf, hs] at h
          | some stored =>
              have hv : value = stored := by
                simpa [adapterFieldTrace, hf, hs] using h.2.2
              simpa [hv] using hs

theorem iteration_apply_provenance {W E I V O : Type}
    (ops : FoldProtocolOps W E I V O) (leaf : FoldCall W E I V O)
    (object item nextState : V) (world : W) (op : O) (value : V)
    (answer : Except (FoldError E) V) (after : W) (tail : List (FoldCall W E I V O))
    (hl : IterationLeaf (some object) world leaf)
    (h1 : adapterFieldTrace (E := E) (Event := FoldCall W E I V O)
      ops.fields object 0 world [] (.ok item) world)
    (h2 : adapterFieldTrace (E := E) (Event := FoldCall W E I V O)
      ops.fields object 1 world [] (.ok nextState) world)
    (ht : FoldInputProvenance ops.fields (some (.apply op value item world answer after)) tail) :
    FoldInputProvenance ops.fields (some leaf)
      (.apply op value item world answer after :: tail) := by
  have hfields : match ops.fields world object with
      | .module => False
      | .fields slots _ => slots[0]? = some (some item) ∧ ∃ state, slots[1]? = some (some state) := by
    have first := field_ok ops object 0 world item h1
    have second := field_ok ops object 1 world nextState h2
    cases hf : ops.fields world object with
    | module => simpa only [hf] using first
    | fields slots valid =>
        simp only [hf] at first second ⊢
        exact ⟨first, nextState, second⟩
  cases leaf <;> simp_all [IterationLeaf, FoldInputProvenance]

theorem rest_apply_provenance {W E I V O : Type}
    (ops : FoldProtocolOps W E I V O) (iterator : FoldIterator I V) (state : Option V)
    (before world : W) (events : List (FoldCall W E I V O)) (object item nextState : V)
    (op : O) (value : V) (answer : Except (FoldError E) V) (after : W)
    (tail : List (FoldCall W E I V O)) (previous : Option (FoldCall W E I V O))
    (hi : RestIterationTrace ops iterator state before events (.ok (some object)) world)
    (h1 : adapterFieldTrace (E := E) (Event := FoldCall W E I V O)
      ops.fields object 0 world [] (.ok item) world)
    (h2 : adapterFieldTrace (E := E) (Event := FoldCall W E I V O)
      ops.fields object 1 world [] (.ok nextState) world)
    (ht : FoldInputProvenance ops.fields (some (.apply op value item world answer after)) tail) :
    FoldInputProvenance ops.fields previous
      (events ++ .apply op value item world answer after :: tail) := by
  obtain ⟨prior, leaf, he, hl⟩ := rest_last hi (some object) rfl
  have hp := rest_notReducer hi
  have hprior : ∀ event ∈ prior, NotReducer event := by
    intro event hm
    exact hp event (by simp [he, hm])
  have hleaf : NotReducer leaf := hp leaf (by simp [he])
  rw [he, List.append_assoc]
  apply (inputProvenance_prefix ops.fields prior leaf _ previous hprior hleaf).mpr
  exact iteration_apply_provenance ops leaf object item nextState world op value answer after tail hl h1 h2 ht

def FoldFacts {W E I V O : Type} (ops : FoldProtocolOps W E I V O) (op : O)
    (value : V) (before : W) (events : List (FoldCall W E I V O))
    (answer : Except (FoldError E) V) (after : W) : Prop :=
  FoldAccumulatorChain op value events answer ∧
  (∀ previous, FoldInputProvenance ops.fields previous events) ∧
  FoldWorldChain before events after ∧ FoldErrorsStop events answer

theorem errorsStop_clean {W E I V O : Type} (events : List (FoldCall W E I V O))
    (answer : Except (FoldError E) V)
    (h : ∀ event ∈ events, foldCallError event = none) : FoldErrorsStop events answer := by
  intro before event after error he herr
  have hm : event ∈ events := by rw [he]; simp
  rw [h event hm] at herr
  cases herr

theorem rest_clean {W E I V O : Type} {ops : FoldProtocolOps W E I V O}
    {iterator state before events result after}
    (h : RestIterationTrace ops iterator state before events (.ok result) after) (value : V) :
    ∀ event ∈ events, foldCallError event = none := by
  apply noErrors_of_success events value
  simpa [Except.map] using rest_stops h value

theorem passive_facts {W E I V O : Type} {ops : FoldProtocolOps W E I V O}
    {iterator state before events first after op value answer}
    (h : RestIterationTrace ops iterator state before events first after)
    (hr : match answer with | .ok result => result = value | .error _ => True)
    (he : ∀ error, first = .error error → answer = .error error) :
    FoldFacts ops op value before events answer after := by
  have hn := rest_notReducer h
  refine ⟨?_, fun previous => passive_provenance ops.fields events previous hn,
    rest_worldChain h, ?_⟩
  · have hc : FoldAccumulatorChain op value (events ++ []) answer :=
      (accumulatorChain_prefix op value events [] answer hn).mpr (by cases answer <;> exact hr)
    simpa using hc
  · cases first with
    | error error =>
        have ha := he error rfl
        subst answer
        simpa [Except.map] using rest_stops h value
    | ok result => exact errorsStop_clean events answer (rest_clean h value)

theorem applyError_facts {W E I V O : Type} {ops : FoldProtocolOps W E I V O}
    {iterator state before events object middle item nextState op value error after}
    (hi : RestIterationTrace ops iterator state before events (.ok (some object)) middle)
    (h1 : adapterFieldTrace (E := E) (Event := FoldCall W E I V O)
      ops.fields object 0 middle [] (.ok item) middle)
    (h2 : adapterFieldTrace (E := E) (Event := FoldCall W E I V O)
      ops.fields object 1 middle [] (.ok nextState) middle) :
    FoldFacts ops op value before
      (events ++ [.apply op value item middle (.error error) after]) (.error error) after := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (accumulatorChain_prefix op value events _ _ (rest_notReducer hi)).mpr
    simp [FoldAccumulatorChain]
  · intro previous
    exact rest_apply_provenance ops iterator state before middle events object item nextState
      op value (.error error) after [] previous hi h1 h2 (by trivial)
  · exact worldChain_append (rest_worldChain hi) ⟨rfl, rfl⟩
  · apply errorsStop_append events _ _ (rest_clean hi value)
    apply errorsStop_single
    intro failure he
    simp only [foldCallError, Option.some.injEq] at he
    subst failure
    rfl

theorem applyStep_facts {W E I V O : Type} {ops : FoldProtocolOps W E I V O}
    {iterator state before events object middle item nextState op value nextValue nextWorld tail answer after}
    (hi : RestIterationTrace ops iterator state before events (.ok (some object)) middle)
    (h1 : adapterFieldTrace (E := E) (Event := FoldCall W E I V O)
      ops.fields object 0 middle [] (.ok item) middle)
    (h2 : adapterFieldTrace (E := E) (Event := FoldCall W E I V O)
      ops.fields object 1 middle [] (.ok nextState) middle)
    (ht : FoldFacts ops op nextValue nextWorld tail answer after) :
    FoldFacts ops op value before
      (events ++ .apply op value item middle (.ok nextValue) nextWorld :: tail) answer after := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (accumulatorChain_prefix op value events _ _ (rest_notReducer hi)).mpr
    exact ⟨rfl, rfl, ht.1⟩
  · intro previous
    exact rest_apply_provenance ops iterator state before middle events object item nextState
      op value (.ok nextValue) nextWorld tail previous hi h1 h2 (ht.2.1 _)
  · exact worldChain_append (rest_worldChain hi) ⟨rfl, ht.2.2.1⟩
  · exact errorsStop_append events _ _ (rest_clean hi value) (errorsStop_cons _ _ _ rfl ht.2.2.2)

theorem tail_facts {W E I V O : Type} {ops : FoldProtocolOps W E I V O}
    {op iterator value state before events answer after}
    (h : TailTrace ops op iterator value state before events answer after) :
    FoldFacts ops op value before events answer after := by
  induction h with
  | iterationError hi =>
      apply passive_facts hi
      · trivial
      · intro error he
        cases he
        rfl
  | done hi =>
      apply passive_facts hi
      · rfl
      · intro error he
        cases he
  | firstError hi first =>
      apply passive_facts hi
      · trivial
      · intro error he
        cases he
  | secondError hi first second =>
      apply passive_facts hi
      · trivial
      · intro error he
        cases he
  | applyError hi first second => exact applyError_facts hi first second
  | step hi first second rest ih => exact applyStep_facts hi first second ih

def resultError {E A : Type} : Except (FoldError E) A → Option (FoldError E)
  | .ok _ => none
  | .error error => some error

structure PassiveSummary {W E I V O A : Type} (before : W)
    (events : List (FoldCall W E I V O)) (answer : Except (FoldError E) A) (after : W) : Prop where
  nonReducer : ∀ event ∈ events, NotReducer event
  world : FoldWorldChain before events after
  stops : ∀ value : V, FoldErrorsStop events (answer.map (fun _ => value))

def PassiveTrace {W E I V O A : Type} (trace : FoldTrace W E I V O A) : Prop :=
  ∀ before events answer after, trace before events answer after → PassiveSummary before events answer after

theorem passive_pure {W E I V O A : Type} (value : A) :
    PassiveTrace (foldPureTrace (W := W) (E := E) (I := I) (V := V) (O := O) value) := by
  intro before events answer after h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨by simp, rfl, fun _ => errorsStop_clean [] _ (by simp)⟩

theorem passive_leaf {W E I V O A : Type}
    (tag : W → Except (FoldError E) A → W → FoldCall W E I V O)
    (hn : ∀ b a e, NotReducer (tag b a e))
    (hb : ∀ b a e, foldCallBefore (tag b a e) = b)
    (ha : ∀ b a e, foldCallAfter (tag b a e) = e)
    (he : ∀ b a e, foldCallError (tag b a e) = resultError a) :
    PassiveTrace (foldLeafTrace tag) := by
  intro before events answer after h
  subst events
  refine ⟨by simpa using hn before answer after, ?_, ?_⟩
  · exact ⟨hb _ _ _, by simpa [FoldWorldChain] using (ha before answer after).symm⟩
  · intro value
    apply errorsStop_single
    intro error herr
    rw [he] at herr
    cases answer <;> simp_all [resultError, Except.map]

theorem passive_then {W E I V O A B : Type}
    (first : FoldTrace W E I V O A) (next : A → FoldTrace W E I V O B)
    (hf : PassiveTrace first) (hn : ∀ x, PassiveTrace (next x)) :
    PassiveTrace (foldThenTrace first next) := by
  intro before events answer after h
  obtain ⟨initial, later, firstAnswer, middle, he, hfirst, hnext⟩ := h
  have hs := hf _ _ _ _ hfirst
  subst events
  cases firstAnswer with
  | error error =>
      obtain ⟨rfl, rfl, rfl⟩ := hnext
      simp only [List.append_nil]
      exact ⟨hs.nonReducer, hs.world, fun value => by simpa [Except.map] using hs.stops value⟩
  | ok value =>
      have ht := hn value _ _ _ _ hnext
      refine ⟨?_, worldChain_append hs.world ht.world, ?_⟩
      · intro event hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hs.nonReducer event hm
        · exact ht.nonReducer event hm
      · intro initialValue
        apply errorsStop_append initial later _ (noErrors_of_success initial initialValue (by
          simpa [Except.map] using hs.stops initialValue))
        exact ht.stops initialValue

theorem passive_restConstructor {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (iterator : FoldIterator I V) (state : V) : PassiveTrace (RestConstructorTrace ops iterator state) := by
  cases hs : ops.selectedRestConstructor iterator state with
  | none => simpa [RestConstructorTrace, hs] using
      passive_pure (W := W) (E := E) (I := I) (V := V) (O := O) (FoldIterator.knownRest iterator state)
  | some call =>
      simpa [RestConstructorTrace, hs] using
        passive_leaf (W := W) (E := E) (I := I) (V := V) (O := O)
          (FoldCall.construct iterator state) (by intros; trivial)
          (by intros; rfl) (by intros; rfl) (by intro b a e; cases a <;> rfl)

theorem passive_restConstruction {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (iterator : FoldIterator I V) (state : V) : PassiveTrace (RestConstructionTrace ops iterator state) := by
  cases hs : ops.selectedRest iterator state with
  | some call =>
      simpa [RestConstructionTrace, hs] using
        passive_leaf (W := W) (E := E) (I := I) (V := V) (O := O)
          (FoldCall.selectedRest iterator state) (by intros; trivial)
          (by intros; rfl) (by intros; rfl) (by intro b a e; cases a <;> rfl)
  | none =>
      cases iterator with
      | ordinary handle => simpa [RestConstructionTrace, hs] using passive_restConstructor ops (.ordinary handle) state
      | customRest handle =>
          simpa [RestConstructionTrace, hs] using
            passive_leaf (W := W) (E := E) (I := I) (V := V) (O := O)
              (FoldCall.rest handle state) (by intros; trivial)
              (by intros; rfl) (by intros; rfl) (by intro b a e; cases a <;> rfl)
      | knownRest inner stored =>
          simp only [RestConstructionTrace, hs]
          apply passive_then
          · cases hp : ops.selectedRestIteratorProperty (.knownRest inner stored) with
            | none => simpa [hp] using passive_pure inner
            | some call =>
                exact passive_leaf (FoldCall.itrRead (.knownRest inner stored)) (by intros; trivial)
                  (by intros; rfl) (by intros; rfl) (by intro b a e; cases a <;> rfl)
          · intro observed
            exact passive_restConstructor ops observed state

theorem passive_prepend_provenance {W E I V O : Type}
    (fields : W → V → FoldObjectView V) (prior suffix : List (FoldCall W E I V O))
    (hp : ∀ event ∈ prior, NotReducer event)
    (hs : ∀ previous, FoldInputProvenance fields previous suffix) :
    ∀ previous, FoldInputProvenance fields previous (prior ++ suffix) := by
  induction prior with
  | nil => exact hs
  | cons event rest ih =>
      have he := hp event (by simp)
      have ht : ∀ e ∈ rest, NotReducer e := fun e h => hp e (by simp [h])
      have hc := ih ht
      intro previous
      cases event <;> simp_all [NotReducer, FoldInputProvenance]

theorem passive_then_facts {W E I V O A : Type} {ops : FoldProtocolOps W E I V O}
    {op value first next before events answer after}
    (hf : PassiveTrace (A := A) (W := W) (E := E) (I := I) (V := V) (O := O) first)
    (hn : ∀ x b es a e, next x b es a e → FoldFacts ops op value b es a e)
    (h : foldThenTrace first next before events answer after) :
    FoldFacts ops op value before events answer after := by
  obtain ⟨initial, later, firstAnswer, middle, he, hfirst, hnext⟩ := h
  have hs := hf _ _ _ _ hfirst
  subst events
  cases firstAnswer with
  | error error =>
      obtain ⟨rfl, rfl, rfl⟩ := hnext
      simp only [List.append_nil]
      exact ⟨by simpa using (accumulatorChain_prefix op value initial [] (.error error) hs.nonReducer).mpr (by trivial),
        fun previous => passive_provenance ops.fields initial previous hs.nonReducer,
        hs.world, by simpa [Except.map] using hs.stops value⟩
  | ok result =>
      have ht := hn result _ _ _ _ hnext
      exact ⟨(accumulatorChain_prefix op value initial later _ hs.nonReducer).mpr ht.1,
        passive_prepend_provenance ops.fields initial later hs.nonReducer ht.2.1,
        worldChain_append hs.world ht.2.2.1,
        errorsStop_append initial later _
          (noErrors_of_success initial value (by simpa [Except.map] using hs.stops value)) ht.2.2.2⟩

theorem initial_error_facts {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (op : O) (init object : V) (before after : W) (error : FoldError E) :
    FoldFacts ops op init before
      [.getindex object (JuliaLean.base.int.lit .i64 1) before (.error error) after]
      (.error error) after := by
  refine ⟨by trivial, ?_, ⟨rfl, rfl⟩, ?_⟩
  · intro previous
    trivial
  · apply errorsStop_single
    intro failure he
    simp only [foldCallError, Option.some.injEq] at he
    subst failure
    rfl

theorem initial_apply_error_facts {W E I V O : Type} (ops : FoldProtocolOps W E I V O)
    (op : O) (init object item : V) (before middle after : W) (error : FoldError E) :
    FoldFacts ops op init before
      [.getindex object (JuliaLean.base.int.lit .i64 1) before (.ok item) middle,
       .apply op init item middle (.error error) after] (.error error) after := by
  refine ⟨by simp [FoldAccumulatorChain], ?_, ⟨rfl, rfl, rfl⟩, ?_⟩
  · intro previous
    exact ⟨trivial, ⟨⟨rfl, rfl⟩, trivial⟩⟩
  · apply errorsStop_cons _ _ _ rfl
    apply errorsStop_single
    intro failure he
    simp only [foldCallError, Option.some.injEq] at he
    subst failure
    rfl

theorem initial_apply_step_facts {W E I V O : Type} {ops : FoldProtocolOps W E I V O}
    {op init object item nextValue before middle nextWorld events answer after}
    (h : FoldFacts ops op nextValue nextWorld events answer after) :
    FoldFacts ops op init before
      (.getindex object (JuliaLean.base.int.lit .i64 1) before (.ok item) middle ::
       .apply op init item middle (.ok nextValue) nextWorld :: events) answer after := by
  refine ⟨⟨rfl, rfl, h.1⟩, ?_, ⟨rfl, rfl, h.2.2.1⟩, ?_⟩
  · intro previous
    exact ⟨trivial, ⟨⟨rfl, rfl⟩, h.2.1 _⟩⟩
  · exact errorsStop_cons _ _ _ rfl (errorsStop_cons _ _ _ rfl h.2.2.2)

theorem genericTrace_facts {W E I V O : Type} {ops : FoldProtocolOps W E I V O}
    {op init iterator before events answer after}
    (h : GenericTrace ops op init iterator before events answer after) :
    FoldFacts ops op init before events answer after := by
  apply passive_then_facts (h := h)
  · intro b es a e hi
    exact ⟨rest_notReducer hi, rest_worldChain hi, rest_stops hi⟩
  · intro result before events answer after h
    cases result with
    | none =>
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, by intros; trivial, rfl, errorsStop_clean [] _ (by simp)⟩
    | some object =>
        obtain ⟨first, rest, readAnswer, readWorld, he, hread, hn⟩ := h
        change first = [.getindex object (JuliaLean.base.int.lit .i64 1) before readAnswer readWorld] at hread
        subst first
        subst events
        cases readAnswer with
        | error error =>
            obtain ⟨rfl, rfl, rfl⟩ := hn
            simpa using initial_error_facts ops op init object before after error
        | ok item =>
            obtain ⟨second, rest2, opAnswer, opWorld, he, hcall, hn⟩ := hn
            change second = [.apply op init item readWorld opAnswer opWorld] at hcall
            subst second
            subst rest
            cases opAnswer with
            | error error =>
                obtain ⟨rfl, rfl, rfl⟩ := hn
                simpa using initial_apply_error_facts ops op init object item before readWorld after error
            | ok nextValue =>
                apply initial_apply_step_facts
                apply passive_then_facts (h := hn)
                · exact passive_leaf (FoldCall.getindex object (JuliaLean.base.int.lit .i64 2))
                    (by intros; trivial) (by intros; rfl) (by intros; rfl) (by intro b a e; cases a <;> rfl)
                · intro state b es a e hrest
                  apply passive_then_facts (h := hrest)
                  · exact passive_restConstruction ops iterator state
                  · intro rest b es a e htail
                    exact tail_facts htail

theorem genericFoldObservation_proven : GenericFoldObservation := by
  intro W E I V O ops op init iterator world
  cases hc : foldlGeneric (observeFoldOps ops) op init iterator (world, []) with
  | none => trivial
  | some result =>
      obtain ⟨answer, after, events⟩ := result
      obtain ⟨suffix, he, hs⟩ := generic_satisfies ops op init iterator world [] answer after events hc
      simp only [List.nil_append] at he
      subst events
      have hf := genericTrace_facts hs
      exact ⟨genericTrace_start hs, hf.1, hf.2.1 none, hf.2.2.1, hf.2.2.2⟩

end JuliaLean.Proofs.base.reduce.Models2Group7.GenericFoldCompletion

namespace JuliaLean.Proofs.base.reduce

open JuliaLean.Registry

def entriesModels2Group7 : List Entry := [
  { id := "reduce-generic-operator-forwarding",
    juliaFile := "base/reduce.jl",
    juliaFns := ["add_sum(x, y)", "mul_prod(x, y)"],
    statement := "For arbitrary stateful, exception-raising or divergent selected binary operations, every terminating observation of each generic wrapper records exactly one call with the original arguments and preserves its observed result, error and final world.",
    source := "base/reduce.jl:16,27 (single-call forwarding invariant)",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.GenericOperatorForwarding,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.genericOperatorForwarding_proven,
    notes := "Reuses existing add_sum and mul_prod at an effectful result type. The observed callbacks have no correctness laws or termination premises; Option represents divergence, which has no terminating observation." },
  { id := "reduce-add-sum-small-exact",
    juliaFile := "base/reduce.jl",
    juliaFns := ["add_sum(x::Union{Bool,BitIntegerSmall}, y::Union{Bool,BitIntegerSmall})"],
    statement := "For every accepted heterogeneous Bool/small-bit-integer pair on the installed 64-bit runtime, add_sum returns the exact mathematical sum as Int64.",
    source := "base/reduce.jl:10-17; base/int.jl:22-24 (small integer widening)",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.AddSumSmallExact,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.addSumSmallExact_proven,
    notes := "Covers the concrete Int conversion helper smallOrBoolInt and addSumSmall. All values are constructible JInt values; representation width bound is the Julia Small union." },
  { id := "reduce-add-sum-unsigned-small-exact",
    juliaFile := "base/reduce.jl",
    juliaFns := ["add_sum(x::BitUnsignedSmall, y::BitUnsignedSmall)"],
    statement := "For all UInt8/UInt16/UInt32 operand pairs and heterogeneous widths, add_sum returns the exact mathematical sum as UInt64.",
    source := "base/reduce.jl:10-18; base/int.jl:22-24 (small unsigned widening)",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.AddSumUnsignedSmallExact,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.addSumUnsignedSmallExact_proven },
  { id := "reduce-real-operator-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["add_sum(x::Real, y::Real)::Real", "mul_prod(x::Real, y::Real)::Real"],
    statement := "Each terminating Real-return arithmetic observation records exactly one selected operation, preserves already-Real values without conversion, and otherwise records one conversion with the observed result and world. Returned values/errors have observed provenance, state is preserved on failure, and a non-Real converted result raises TypeError. Divergent dispatch is included without a termination premise.",
    source := "base/reduce.jl:19,30; doc/src/manual/functions.md:196-210; src/julia-syntax.scm:3870-3892,4807 (return annotation)",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.RealOperatorObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.realOperatorObservation_proven,
    notes := "Covers addSumReal, mulProdReal and returnReal. All callbacks, worlds and callback error types are quantified without laws. Option represents divergence and no terminating observation. Nested exception layers distinguish callback error origin from the return assertion; callbacks may themselves raise TypeError. Exact pinned lowering verifies the isa fast path." },
  { id := "reduce-mul-prod-signed-small-exact",
    juliaFile := "base/reduce.jl",
    juliaFns := ["mul_prod(x::BitSignedSmall, y::BitSignedSmall)"],
    statement := "For all Int8/Int16/Int32 operand pairs and heterogeneous widths, mul_prod returns the exact mathematical product as Int64.",
    source := "base/reduce.jl:21-28; base/int.jl:22-24 (small signed widening)",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.MulProdSignedSmallExact,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.mulProdSignedSmallExact_proven },
  { id := "reduce-mul-prod-unsigned-small-exact",
    juliaFile := "base/reduce.jl",
    juliaFns := ["mul_prod(x::BitUnsignedSmall, y::BitUnsignedSmall)"],
    statement := "For all UInt8/UInt16/UInt32 operand pairs and heterogeneous widths, mul_prod returns the exact mathematical product as UInt64.",
    source := "base/reduce.jl:21-29; base/int.jl:22-24 (small unsigned widening)",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.MulProdUnsignedSmallExact,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.mulProdUnsignedSmallExact_proven },
  { id := "reduce-and-all-truth-errors",
    juliaFile := "base/reduce.jl",
    juliaFns := ["and_all(x, y)"],
    statement := "Generic and_all returns true exactly for two true Bools, false exactly for a false first Bool or true/false pair, and TypeError exactly for a non-Bool first argument or a true first Bool followed by a non-Bool.",
    source := "base/reduce.jl:32; doc/src/manual/types.md:60-83; doc/src/manual/control-flow.md (short-circuit evaluation)",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.AndAllTruthAndErrors,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.andAllTruthAndErrors_proven,
    notes := "Reuses existing full-domain and_all and assertBool. The arbitrary non-Bool value arms include custom values and missing." },
  { id := "reduce-or-any-truth-errors",
    juliaFile := "base/reduce.jl",
    juliaFns := ["or_any(x, y)"],
    statement := "Generic or_any returns true exactly for a true first Bool or false/true pair, false exactly for two false Bools, and TypeError exactly for a non-Bool first argument or a false first Bool followed by a non-Bool.",
    source := "base/reduce.jl:33; doc/src/manual/types.md:60-83; doc/src/manual/control-flow.md (short-circuit evaluation)",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.OrAnyTruthAndErrors,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.orAnyTruthAndErrors_proven,
    notes := "Reuses existing full-domain or_any and assertBool. The arbitrary non-Bool value arms include custom values and missing." },
  { id := "reduce-and-all-bool-truth",
    juliaFile := "base/reduce.jl",
    juliaFns := ["and_all(x::Bool, y::Bool)"],
    statement := "The Bool specialization of and_all is true exactly when both inputs are true.",
    source := "base/reduce.jl:35; base/bool.jl:14",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.AndAllBoolTruth,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.andAllBoolTruth_proven,
    notes := "Calls installed JuliaLean.base.bool.andBool rather than an arbitrary bitwise-operation callback." },
  { id := "reduce-or-any-bool-truth",
    juliaFile := "base/reduce.jl",
    juliaFns := ["or_any(x::Bool, y::Bool)"],
    statement := "The Bool specialization of or_any is true exactly when at least one input is true.",
    source := "base/reduce.jl:36; base/bool.jl:15",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.OrAnyBoolTruth,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.orAnyBoolTruth_proven,
    notes := "Calls installed JuliaLean.base.bool.orBool rather than an arbitrary bitwise-operation callback." },
  { id := "reduce-foldl-dispatch-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["foldl_impl(op::OP, nt, itr) where {OP}"],
    statement := "For arbitrary stateful, throwing or divergent selected calls, foldl_impl performs one fold with its original arguments, invokes the empty reduction exactly after an _InitialValue result, and preserves the last observed result, error and world, including an empty result that is itself _InitialValue.",
    source := "base/reduce.jl:45-49 (sentinel-gated empty dispatch invariant)",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FoldlDispatchObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.foldlDispatchObservation_proven,
    notes := "Both dispatched callees are selected on op and itr types the method does not fix. No correctness law is assumed; the source body and sentinel branch are explicit." },
  { id := "reduce-generic-fold-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_foldl_impl(op::OP, init, itr) where {OP}"],
    statement := "For arbitrary stateful, throwing or divergent iterator/getindex/reducer dispatch and genuine Rest rest/constructor/iterate/getproperty selections, every terminating generic fold retains original receiver/state dataflow through the complete initial iteration, chains reducer accumulators from init, consumes observed first-index/first-field values after both tail fields exist, threads all worlds, and propagates callback errors. Empty initial iteration returns init immediately.",
    source := "base/reduce.jl:51-63; base/iterators.jl:669-673,696-697,732; doc/src/manual/interfaces.md:8-54; src/julia-syntax.scm:1888-1909,2070-2110",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.GenericFoldObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.GenericFoldCompletion.genericFoldObservation_proven,
    notes := "Narrow independent invariant over all selected leaves without correctness or success premises. Covers foldlGeneric, actual foldTail, and concrete field reads. Initial Rest iteration uses the separately registered full finite-observation relation, including cycles/divergence; constructor/property/iterate helpers also have registered invariants. All machine indices are JInt64; no iterator list materialization." },
  { id := "reduce-rest-construction-observation",
    juliaFile := "base/iterators.jl",
    juliaFns := ["rest(itr,state)", "rest(itr::Rest,state)", "Rest(itr,state)"],
    statement := "Base rest constructs the actual immutable Rest or collapses exactly one observed itr property before constructing with the new state. Genuine selected rest/getproperty/constructor methods retain original arguments, arbitrary iterator results, worlds, errors and divergence. No old-state getter, recursive collapse or iteration is inserted.",
    source := "base/iterators.jl:669-673,696-697",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.RestConstructionObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.restConstructionObservation_proven,
    notes := "Necessary dependency of queued reduce51. Covers foldRest, foldRestConstruct and foldRestItr, with fixed initialized storage default and explicit selected alternatives." },
  { id := "reduce-rest-iteration-observation",
    juliaFile := "base/iterators.jl",
    juliaFns := ["iterate(i::Rest, st=i.st)"],
    statement := "A selected unary Rest iterate may run directly; otherwise its actual st getter precedes binary redispatch on the same Rest. The concrete binary body reads actual itr and recursively iterates that observed object with the exact explicit state. Selected iterate/getproperty methods preserve result/error/world provenance, and arbitrary getter/delegation cycles remain possible.",
    source := "base/iterators.jl:732",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.RestIterationObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.restIterationObservation_proven,
    notes := "Necessary dependency of reduce51. Covers actual fixed-point foldIterate and foldRestState/foldRestItr. Independent finite observation derivations constrain stored-field and call dataflow; none includes nontermination without fuel or a success premise." },
  { id := "reduce-tuple-fold-contents",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_foldl_impl(op, init, itr::Union{Tuple,NamedTuple})"],
    statement := "Under the explicit concrete Base length/index/iteration/Rest/afoldl/invoke selections, Tuple/NamedTuple folding equals an independent mathematical left fold over every stored field for all native-bounded arities and arbitrary stateful, throwing or divergent operators. At maximal native arity, NamedTuple iteration raises BoundsError after the last successful reduction because the next native index wraps.",
    source := "base/reduce.jl:65-68,175-180; base/operators.jl:622-663; base/tuple.jl:69-73; base/namedtuple.jl:159-160",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.TupleFoldContents,
    thm := none,
    notes := "This property explicitly selects the concrete Base routes. The separate universal TupleDispatchObservation covers every alternative dispatch route without callee laws. The model implements actual unrolling and generic/Rest loops. The native range constructor, initial iterator and next iterator reuse installed range models closed over native primitives." },
  { id := "reduce-tuple-fold-dispatch",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_foldl_impl(op, init, itr::Union{Tuple,NamedTuple})"],
    statement := "For arbitrary selected length/comparison, afoldl, invoke, tuple/pair indexing, unary/binary iteration, nonnative states, dynamic colon/range iteration and Rest routes, every terminating tuple-fold observation preserves the mutable world chain, original reducer identity and forwarded/splatted arguments. Selected errors and non-Bool conditions terminate immediately; a successful result is the last produced accumulator or the unchanged initial value when no producer ran. Concrete Core errors retain their bounds/undefined/type/field class.",
    source := "base/reduce.jl:65-68; base/operators.jl:622-663; base/tuple.jl:28,33,69-73; base/namedtuple.jl:159-160; base/iterators.jl:669-673,696-697,732; src/builtins.c:939-951",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.TupleDispatchObservation,
    thm := none,
    notes := "Universal over full TupleFullOps without callback correctness or termination assumptions; divergence has no terminating observation. Actual Base afoldl interior dispatch and dynamic for-loop remain explicit. Core._apply_iterate has a fixed field-copy fastpath for both actual Tuple and NamedTuple, so this splat does not use an arbitrary-iterator approximation. Pure symbol/name/storage views are runtime representation metadata." },
  { id := "reduce-selected-property-observation",
    juliaFile := "base/Base_compiler.jl",
    juliaFns := ["getproperty(op, :rf)", "getproperty(op, :f)"],
    statement := "A stored field read returns the original field without effects; an actually selected custom getter is invoked exactly once with the original object and preserves its observed value, exception and final world. Divergence has no terminating observation.",
    source := "base/Base_compiler.jl:59; base/reduce.jl:83-125",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.SelectedPropertyObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.selectedPropertyObservation_proven,
    notes := "Narrow helper invariant covering readSelectedProperty for arbitrary stored/custom selections and all effects/errors; no callee laws. This records the necessary fixed-field access helper used by reduce adapters; it does not claim a translation of every generic getproperty case." },
  { id := "reduce-bottom-rf-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["(op::BottomRF)(::_InitialValue, x)", "(op::BottomRF)(acc, x)"],
    statement := "After the selected rf property read, BottomRF invokes exactly reduce_first for the sentinel method or exactly the binary reducer for the ordinary method, using original operands and observed reducer identity. Every result/error/world has observed provenance; failures prevent later calls.",
    source := "base/reduce.jl:72-84",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.BottomAdapterObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.bottomAdapterObservation_proven,
    notes := "All property and invocation dispatch, worlds and exceptions are unrestricted; no successful-run or termination premise." },
  { id := "reduce-mapping-constructors-fields",
    juliaFile := "base/reduce.jl",
    juliaFns := ["MappingRF(f::F, rf::T) where {F,T}", "MappingRF(::Type{f}, rf::T) where {f,T}"],
    statement := "Both MappingRF constructors retain the exact f and rf field identities without invoking the stored values.",
    source := "base/reduce.jl:91-95",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.MappingConstructorsKeepFields,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.mappingConstructorsKeepFields_proven,
    notes := "Reuses the canonical mappingRF_constructor and mappingRF_type_constructor." },
  { id := "reduce-mapping-rf-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["(op::MappingRF)(acc, x)"],
    statement := "MappingRF reads rf before f, calls the observed mapping once on the original element, then calls the observed reducer once with the original accumulator and mapped result. Arbitrary getter/callback errors stop the trace and retain the final world.",
    source := "base/reduce.jl:86-98",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.MappingAdapterObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.mappingAdapterObservation_proven,
    notes := "Stored and selected custom property routes, arbitrary mutable effects, errors and divergence are all quantified without laws." },
  { id := "reduce-filtering-rf-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["(op::FilteringRF)(acc, x)"],
    statement := "FilteringRF evaluates the observed predicate once. False returns the original accumulator without reading or invoking rf; true reads and invokes rf once with original operands; every non-Bool predicate result raises TypeError after predicate effects. Callback errors and worlds are retained.",
    source := "base/reduce.jl:100-110",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FilteringAdapterObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.filteringAdapterObservation_proven,
    notes := "Nested exception layers distinguish the branch TypeError origin from arbitrary callback errors, which may themselves be TypeErrors. No callback correctness or termination law." },
  { id := "reduce-flattening-rf-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["(op::FlatteningRF)(acc, x)"],
    statement := "FlatteningRF transforms the observed rf and original input before folding with the original accumulator and observed operator/iterator. Raw transform results are destructured by indexed_iterate at native indices 1 and 2 with the observed state and checked Core fields; the final indexed result needs only its first field. Errors retain worlds and prevent later calls.",
    source := "base/reduce.jl:118-125; base/tuple.jl:161-172; src/julia-syntax.scm:1888-1909,2597-2608",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FlatteningAdapterObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.flatteningAdapterObservation_proven,
    notes := "Includes arbitrary non-tuple/raw results, malformed or undefined fields, selected custom getters/indexed_iterate/fold, effects, errors and divergence. Known pair Tuple behavior is concrete. Covers flatteningApply, flatteningDestructure, flatteningGetfield and flattenPairIndexed." },
  { id := "reduce-adjoint-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_xfadjoint(op, itr)"],
    statement := "The generic own body calls selected unwrap on the original iterator, destructures its actual result using indexed iteration and concrete Core fields, invokes the observed wrapper on the original operator, and returns that actual result with the observed iterator. All errors, mutation and divergence are unrestricted.",
    source := "base/reduce.jl:146-149; src/julia-syntax.scm:2597-2608",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.AdjointObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.adjointObservation_proven,
    notes := "Covers GenericAdjointOps, xfadjoint, destructureTransformPair, transformGetfield, transformPairFirst/Second, and their raw storage interface. The method fixes neither selected callee type; no correctness law is assumed. This generic body does not claim a complete known ComposedFunction instantiation for blocked row40." },
  { id := "reduce-unwrap-fallback-identity",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_xfadjoint_unwrap(itr)"],
    statement := "The generic fallback returns exactly its original input and the identity singleton for every object type, without inspecting the object or invoking a callable.",
    source := "base/reduce.jl:151",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.GenericUnwrapIdentity,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.genericUnwrapIdentity_proven },
  { id := "reduce-mapfoldl-public-forwarding",
    juliaFile := "base/reduce.jl",
    juliaFns := ["mapfoldl(f, op, itr; init=_InitialValue())"],
    statement := "For arbitrary selected implementations, every terminating public mapfoldl observation records exactly one call with the original f, op and iterator, using the sentinel only when init is omitted and preserving any supplied init. Result, errors and final state are preserved; divergent implementations are included.",
    source := "base/reduce.jl:166-173; doc/src/manual/functions.md:817-831 (keyword defaults)",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.MapfoldlPublicForwarding,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.mapfoldlPublicForwarding_proven,
    notes := "No correctness laws or termination premises. The actual default sentinel and a supplied sentinel are both represented. The called mapfoldl_impl is selected on unfixed argument types." },
  { id := "reduce-foldl-public-forwarding",
    juliaFile := "base/reduce.jl",
    juliaFns := ["foldl(op, itr; kw...)"],
    statement := "For arbitrary selected mapfoldl methods and keyword objects (Pairs over NamedTuples), every terminating foldl observation records one call with the actual identity singleton, original operator and iterator, and the exact keyword object. Returned results, errors and final state are preserved; divergence is included.",
    source := "base/reduce.jl:175-196; doc/src/manual/functions.md:849-860 (keyword forwarding)",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FoldlPublicForwarding,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.foldlPublicForwarding_proven,
    notes := "Keyword objects are opaque already-constructed Julia values, including empty NamedTuple. No callback correctness law is assumed, and unsupported keyword errors remain in selected dispatch." },
  { id := "reduce-reverse-iter-forwarding",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_reverse_iter(itr)"],
    statement := "Generic _reverse_iter forwards its original iterator exactly once and preserves the selected reverse result, exceptions, all worlds and divergence.",
    source := "base/reduce.jl:206-206",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.ReverseIterForwarding,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.reverseIterForwarding_proven,
    notes := "Complete additive model and universal independent observation; no callback correctness laws or termination premises." },
  { id := "reduce-flip-adapter-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["(f::FlipArgs)(x, y)"],
    statement := "The selected f property is read once before invoking that exact callable with y then x. Arbitrary heterogeneous arguments, getter/callee mutation, errors, results and divergence are retained without laws.",
    source := "base/reduce.jl:213-213",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FlipAdapterObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.flipAdapterObservation_proven,
    notes := "Complete additive model and universal independent observation; no callback correctness laws or termination premises." },
  { id := "reduce-mapfoldr-public-forwarding",
    juliaFile := "base/reduce.jl",
    juliaFns := ["mapfoldr(f::F, op::F2, itr; init=_InitialValue()) where {F,F2}"],
    statement := "Public mapfoldr forwards f/op/iterator once, selects the actual sentinel only on omitted init, and preserves supplied init, all results/errors/worlds and divergence of unrestricted selected implementations.",
    source := "base/reduce.jl:222-222",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.MapfoldrPublicForwarding,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.mapfoldrPublicForwarding_proven,
    notes := "Complete additive model and universal independent observation; no callback correctness laws or termination premises." },
  { id := "reduce-foldr-public-forwarding",
    juliaFile := "base/reduce.jl",
    juliaFns := ["foldr(op::F, itr; kw...) where {F}"],
    statement := "Public foldr forwards actual identity, original operator/iterator and complete keyword object (Pairs over a NamedTuple), preserving unrestricted selected results/errors/worlds and divergence.",
    source := "base/reduce.jl:241-241",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FoldrPublicForwarding,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.foldrPublicForwarding_proven,
    notes := "Complete additive model and universal independent observation; no callback correctness laws or termination premises." },
  { id := "reduce-pairwise-body-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["mapreduce_impl(f, op, A::AbstractArrayOrBroadcasted, ifirst::Integer, ilast::Integer, blksize::Int)"],
    statement := "For every represented Integer interval, native block size and arbitrary effectful selected dispatch, every terminating generic pairwise computation compares the original ends first, preserves array/mapper/reducer identities and inbounds context, uses exact native literals, derives mapped elements and reducer operands from observed earlier reads/results, retains a real reduction result, threads worlds, and immediately propagates callback or non-Bool-condition errors. It never recomputes pairwise_blocksize.",
    source := "base/reduce.jl:245-274; base/simdloop.jl:67-87; doc/src/manual/mathematical-operations.md:481-484",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.PairwiseBodyObservation,
    thm := none,
    notes := "Narrow independent internal invariant, not an algebraic reduction claim or memory-safety theorem. Full generic recursion and expanded SIMD loops are real fixed points. All selected leaves have no correctness/termination laws. Covers mapreduceImpl, pairwiseGo, pairwiseSimd, pairwiseSimdOuter, pairwiseSimdInner, pairwiseReadField and pairwiseAssertBool." },
  { id := "reduce-pairwise-default-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["mapreduce_impl(f, op, A::AbstractArrayOrBroadcasted, ifirst::Integer, ilast::Integer)"],
    statement := "The default wrapper calls pairwise_blocksize exactly once with original function/operator before other calls and passes its exact result to six-argument dispatch. A selected custom method receives all original arguments and that result, a selected generic native-block method starts the actual body, and missing or incompatible generic dispatch raises MethodError. Observed results, errors and mutated worlds are preserved, with divergence included.",
    source := "base/reduce.jl:276-277",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.PairwiseDefaultObservation,
    thm := none,
    notes := "No assumption that custom pairwise_blocksize returns Int, no callee correctness law, and no callback replaces the generic six-argument body." },
  { id := "reduce-mapreduce-public-forwarding",
    juliaFile := "base/reduce.jl",
    juliaFns := ["mapreduce(f, op, itr; kw...)"],
    statement := "For every argument, complete keyword object, world and arbitrary stateful/throwing/divergent selected mapfoldl, the public wrapper retains exactly one call with the original arguments and returns its observed outcome and final world.",
    source := "base/reduce.jl:279-306",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.MapreducePublicForwarding,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.mapreducePublicForwarding_proven },
  { id := "reduce-mapreduce-multi-provenance",
    juliaFile := "base/reduce.jl",
    juliaFns := ["mapreduce(f, op, itr, itrs...; kw...)"],
    statement := "For arbitrary selected Generator/reduce dispatch, every terminating multi-iterator wrapper has at most two observed calls: the original constructor arguments occur first; any reduction consumes that exact constructor result with the original operator and keywords; callback errors and worlds are retained and a constructor error suppresses reduction.",
    source := "base/reduce.jl:279-307",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.MapreduceMultiProvenance,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.mapreduceMultiProvenance_proven },
  { id := "reduce-pairwise-blocksize-values",
    juliaFile := "base/reduce.jl",
    juliaFns := ["pairwise_blocksize(f, op)", "pairwise_blocksize(::typeof(abs2), ::typeof(+))"],
    statement := "Default and abs2/plus block-size methods return native signed Int64 values whose mathematical values are 1024 and 4096, independently of all unused argument values.",
    source := "base/reduce.jl:309-314",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.PairwiseBlocksizeValues,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.pairwiseBlocksizeValues_proven },
  { id := "reduce-empty-errors",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_empty_reduce_error", "reduce_empty", "mapreduce_empty"],
    statement := "Every generic/Union{} fallback returns the exact ArgumentError class and message for every operator, mapping, type object and extra-argument tuple, without evaluating them.",
    source := "base/reduce.jl:318-322",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.EmptyFallbackErrors,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.emptyFallbackErrors_proven },
  { id := "reduce-empty-closed-values",
    juliaFile := "base/reduce.jl",
    juliaFns := ["reduce_empty"],
    statement := "The AbstractChar multiplication empty value is the empty string; Bool bit-and/bit-or and and_all/or_any return their exact truth identities, independent of the unused element type.",
    source := "base/reduce.jl:345-349",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.EmptyClosedValues,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.emptyClosedValues_proven },
  { id := "reduce-empty-scalar-dispatch",
    juliaFile := "base/reduce.jl",
    juliaFns := ["reduce_empty"],
    statement := "For every type object and arbitrary stateful/throwing/divergent zero, one or reduce_empty selection, scalar empty forwarding methods make exactly the intended call with the original type and exact arithmetic singleton and retain the observed outcome/world.",
    source := "base/reduce.jl:342,344,351,354",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.EmptyScalarDispatch,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.emptyScalarDispatch_proven },
  { id := "reduce-empty-native-identities",
    juliaFile := "base/reduce.jl",
    juliaFns := ["reduce_empty"],
    statement := "Every small signed/unsigned type and the Bool plus specialization return their native Int64/UInt64 zero or one identities with no error. Shared native zero/one helpers preserve numeric zero/one for every concrete bit-integer type.",
    source := "base/reduce.jl:343,352-356; base/number.jl:364,405; base/int.jl:22-24",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.EmptyNativeIdentities,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.emptyNativeIdentities_proven },
  { id := "reduce-empty-adapters-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["reduce_empty", "mapreduce_empty"],
    statement := "For all dynamic values, stored/custom getter selections and arbitrary empty/eltype/zero/abs/abs2 dispatch, empty adapter methods retain source call order, callable/type identities, observed intermediate result provenance, and all errors/world changes.",
    source := "base/reduce.jl:358-376",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.EmptyAdaptersObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.emptyAdaptersObservation_proven },
  { id := "reduce-empty-iterator-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["mapreduce_empty_iter", "reduce_empty_iter"],
    statement := "For arbitrary getters, constructors, traits, type objects and selected empty dispatch, empty-iterator methods preserve original arguments, concrete constructor field identity, actual trait/eltype result provenance, bound-versus-unbound static type selection, call order, errors and all worlds.",
    source := "base/reduce.jl:379-392; base/iterators.jl:1261-1263,1291",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.EmptyIteratorObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.emptyIteratorObservation_proven },
  { id := "reduce-empty-iterator-error",
    juliaFile := "base/reduce.jl",
    juliaFns := ["reduce_empty_iter"],
    statement := "For every operator, iterator and result type, EltypeUnknown empty reduction returns the exact ArgumentError message including the source newline between sentences.",
    source := "base/reduce.jl:393-395",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.EmptyIteratorUnknownError,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.emptyIteratorUnknownError_proven },
  { id := "reduce-first-identity",
    juliaFile := "base/reduce.jl",
    juliaFns := ["reduce_first"],
    statement := "For every operator and input type/value, generic reduce_first returns the original input identity, including non-callable operators and mutable references.",
    source := "base/reduce.jl:399-411",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FirstIdentity,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.firstIdentity_proven },
  { id := "reduce-first-selected-forwarding",
    juliaFile := "base/reduce.jl",
    juliaFns := ["reduce_first"],
    statement := "Character string conversion and generic add_sum/mul_prod/vcat/hcat first-element forwarding preserve one original-input call and its observed result/error/world, for arbitrary effects or divergence.",
    source := "base/reduce.jl:413,415,418,421-422",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FirstSelectedForwarding,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.firstSelectedForwarding_proven },
  { id := "reduce-first-native-values",
    juliaFile := "base/reduce.jl",
    juliaFns := ["reduce_first"],
    statement := "Bool first value is native Int64 zero or one; every small signed/unsigned add_sum/mul_prod first value preserves its mathematical value in native Int64/UInt64, over all source widths and values.",
    source := "base/reduce.jl:412,416-420",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FirstNativeValues,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.firstNativeValues_proven },
  { id := "reduce-first-flip-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["reduce_first"],
    statement := "For arbitrary stored/custom f getters and selected reduce_first dispatch, the FlipArgs method forwards original input and observed callable, preserving getter-before-call order and all errors/world updates.",
    source := "base/reduce.jl:423",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FirstFlipObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.firstFlipObservation_proven },
  { id := "reduce-mapreduce-first-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["mapreduce_first"],
    statement := "For arbitrary mapping and reduce_first dispatch, first-element map-reduction maps once then passes the actual mapped result and original operator to one selected first call, preserving call/result/world provenance and stopping on mapping error.",
    source := "base/reduce.jl:425-435",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.MapreduceFirstObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.mapreduceFirstObservation_proven },
  { id := "reduce-array-mapreduce-dispatch",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_mapreduce(f, op, A::AbstractArrayOrBroadcasted)"],
    statement := "IndexStyle is evaluated first; the selected _mapreduce receives its exact result and original mapper/operator/array. All selected result, error, state and divergent behavior is retained.",
    source := "base/reduce.jl:437-437",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.ArrayMapreduceDispatchObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.arrayMapreduceDispatchObservation_proven,
    notes := "All selected calls are unrestricted; no callee correctness or termination law is assumed." },
  { id := "reduce-linear-mapreduce-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_mapreduce(f, op, ::IndexLinear, A::AbstractArrayOrBroadcasted)"],
    statement := "All IndexLinear executions preserve native/custom branch behavior, source call order, original object identities, exact inbounds contexts, error/world provenance, ordered reads/maps and left-reduction dataflow. last is freshly called at each actual while guard. Arbitrary lengths, indices, mutations, non-Bool results, errors and divergence are included without laws.",
    source := "base/reduce.jl:439-460",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.LinearMapreduceObservation,
    thm := none,
    notes := "Full own algorithm with partial_fixpoint while; no positive-length, finite-loop, integer-index or interval assumption. Native Int64 equality/less/add reuse installed integer models. Other arithmetic can change type. Initial reads precede both mappings and large-branch first precedes last." },
  { id := "reduce-number-mapreduce-forwarding",
    juliaFile := "base/reduce.jl",
    juliaFns := ["mapreduce(f, op, a::Number)"],
    statement := "Every numeric input and arbitrary mapper/operator is forwarded once to selected mapreduce_first with exact result, error and state provenance, including divergent callbacks.",
    source := "base/reduce.jl:462-462",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.NumberMapreduceObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.numberMapreduceObservation_proven,
    notes := "All selected calls are unrestricted; no callee correctness or termination law is assumed." },
  { id := "reduce-cartesian-mapreduce-forwarding",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_mapreduce(f, op, ::IndexCartesian, A::AbstractArrayOrBroadcasted)"],
    statement := "The Cartesian own body forwards original mapper/operator/array once to selected mapfoldl with no added init argument, preserving arbitrary results, errors, mutations and divergence.",
    source := "base/reduce.jl:464-464",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.CartesianMapreduceObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.cartesianMapreduceObservation_proven,
    notes := "All selected calls are unrestricted; no callee correctness or termination law is assumed." },
  { id := "reduce-public-forwarding",
    juliaFile := "base/reduce.jl",
    juliaFns := ["reduce(op, itr; kw...)"],
    statement := "Public reduce forwards actual identity, operator, iterator and complete keyword object (Pairs over a NamedTuple) unchanged, retaining all selected outcomes, state changes, exceptions and divergence.",
    source := "base/reduce.jl:501-501",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.PublicReduceObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.publicReduceObservation_proven,
    notes := "All selected calls are unrestricted; no callee correctness or termination law is assumed." },
  { id := "reduce-number-identity",
    juliaFile := "base/reduce.jl",
    juliaFns := ["reduce(op, a::Number)"],
    statement := "Numeric reduce returns the exact original Number independently of every supplied operator object, including non-callable values, without selected reducer calls.",
    source := "base/reduce.jl:503-503",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.ReduceNumberIdentity,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.reduceNumberIdentity_proven,
    notes := "Baseline reduce_number restricts its ignored operator to Reducer. The additive full-domain wrapper reuses baseline reduce_first identity body, with arbitrary ignored operator type. Existing frozen contradictory reduce-first property remains unchanged." },
  { id := "reduce-reduction-public-forwarding",
    juliaFile := "base/reduce.jl",
    juliaFns := ["sum", "prod", "maximum", "minimum", "extrema"],
    statement := "Mapped and identity reduction forwarding methods make exactly their selected public call with the source singleton, original iterator and complete keywords, preserving observed result/error/world for arbitrary callbacks including divergence.",
    source := "base/reduce.jl:546,575,602,631,659,686,718,750,779",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.ReductionPublicForwarding,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.reductionPublicForwarding_proven },
  { id := "reduce-bool-sum-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["sum(a::AbstractArray{Bool}; kw...)"],
    statement := "For arbitrary arrays, machine-valid unique keyword packets and unrestricted selected methods, every terminating call preserves original objects, native destructuring and keys-Tuple indices, sequential worlds, callback errors, non-Bool conditional TypeError, and the exact terminal count/reduce outcome. This includes unary-to-binary Tuple iteration selection, selected length/index/upper comparison and _pairs_elt. With concrete Base keyword methods, the sole selected call is count exactly for an empty keyword NamedTuple; otherwise it is reduce(add_sum,array,original keywords). Divergence is included without a successful-run premise.",
    source := "base/reduce.jl:576-577; base/essentials.jl:1235-1239,1601; base/iterators.jl:298-307,316,327; base/namedtuple.jl:165-166,382; base/tuple.jl:69-73",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.BoolSumObservation,
    thm := none,
    notes := "Narrow independent trace plus concrete Base branch invariant. Covers sumBoolArray and all boolKeyword* helpers, KeywordSelection, checked keyword Tuple storage/type representation, installed isemptyAtBoundary/isdoneDefault, shared tupleFullTupleIterate/iterateFoldTuple and flatteningDestructure. The keyword Tuple adapter supplies concrete defaults and arbitrary genuinely selected routes at every reachable call; its unrelated required TupleFullOps fields are unreachable. All selected keyword routes, including interior Tuple and _pairs_elt, are reset for the concrete-default conjunct. No callee correctness laws; no free hasKeywords flag." },
  { id := "reduce-extrema-public-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["extrema"],
    statement := "Every extrema mapping wrapper constructs its concrete mapper or genuinely selected alternative before one public mapreduce call with exact _extrema_rf, iterator and keywords, preserving observed outcomes/worlds.",
    source := "base/reduce.jl:809",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.ExtremaPublicObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.extremaPublicObservation_proven },
  { id := "reduce-extrema-constructor-fields",
    juliaFile := "base/reduce.jl",
    juliaFns := ["ExtremaMap"],
    statement := "Both concrete ExtremaMap constructor forms retain exact mapper identity and type-singleton storage metadata; the installed Type{T} constructor preserves its field.",
    source := "base/reduce.jl:812-816",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.ExtremaConstructorFields,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.extremaConstructorFields_proven },
  { id := "reduce-extrema-map-aliasing",
    juliaFile := "base/reduce.jl",
    juliaFns := ["ExtremaMap"],
    statement := "For arbitrary stored/custom f getter and mapping dispatch, ExtremaMap maps exactly once and returns two references to the same observed result, retaining all getter/call effects/errors.",
    source := "base/reduce.jl:817",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.ExtremaMapAliasing,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.extremaMapAliasing_proven },
  { id := "reduce-extrema-reducer-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_extrema_rf"],
    statement := "For every known pair or raw destructurable input, extrema reduction preserves left-before-right destructuring, exact observed operands, min-before-max call order, field/error provenance, final tuple and all worlds without callback laws.",
    source := "base/reduce.jl:819",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.ExtremaReducerObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.extremaReducerObservation_proven },
  { id := "reduce-find-max-mapped-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["findmax(f, domain)"],
    statement := "One selected internal call receives the original f/domain and exact Colon singleton; its actual outcome/world is retained. Every selected callee is unrestricted, including state, exceptions, nontermination and arbitrary output types.",
    source := "base/reduce.jl:854",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FindMaxMappedObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.findMaxMappedObservation_proven,
    notes := "Independent invocation/result/alias/world trace; no callee correctness, algebraic or successful-run laws. " },
  { id := "reduce-find-max-colon-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_findmax(f, domain, ::Colon)"],
    statement := "Exactly pairs(original domain), then mapfoldl with its actual result, the correct reducer and a known indexed closure capturing the original f. The lambda body has its separately registered full-domain invariant. Every selected callee is unrestricted, including state, exceptions, nontermination and arbitrary output types.",
    source := "base/reduce.jl:855",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FindMaxColonObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.findMaxColonObservation_proven,
    notes := "Independent invocation/result/alias/world trace; no callee correctness, algebraic or successful-run laws. Includes concrete closure-body dependency." },
  { id := "reduce-find-max-reducer-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_rf_findmax((fm, im), (fx, ix))"],
    statement := "Full raw destructuring order, exact comparator operands/identity, Bool assertion, whole-pair provenance, left-tie branch, mutable worlds and immediate errors; no ordering laws. Every selected callee is unrestricted, including state, exceptions, nontermination and arbitrary output types.",
    source := "base/reduce.jl:856",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FindMaxReducerObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.findMaxReducerObservation_proven,
    notes := "Independent invocation/result/alias/world trace; no callee correctness, algebraic or successful-run laws. " },
  { id := "reduce-find-max-single-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["findmax(itr)"],
    statement := "One selected unary internal call receives the original iterator and Colon singleton, preserving its exact outcome/world. Every selected callee is unrestricted, including state, exceptions, nontermination and arbitrary output types.",
    source := "base/reduce.jl:883",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FindMaxSingleObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.findMaxSingleObservation_proven,
    notes := "Independent invocation/result/alias/world trace; no callee correctness, algebraic or successful-run laws. " },
  { id := "reduce-find-max-identity-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_findmax(a, ::Colon)"],
    statement := "One selected public call receives the exact identity function singleton and original collection, retaining every outcome/world. Every selected callee is unrestricted, including state, exceptions, nontermination and arbitrary output types.",
    source := "base/reduce.jl:884",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FindMaxIdentityObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.findMaxIdentityObservation_proven,
    notes := "Independent invocation/result/alias/world trace; no callee correctness, algebraic or successful-run laws. " },
  { id := "reduce-find-min-mapped-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["findmin(f, domain)"],
    statement := "One selected internal call receives the original f/domain and exact Colon singleton; its actual outcome/world is retained. Every selected callee is unrestricted, including state, exceptions, nontermination and arbitrary output types.",
    source := "base/reduce.jl:920",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FindMinMappedObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.findMinMappedObservation_proven,
    notes := "Independent invocation/result/alias/world trace; no callee correctness, algebraic or successful-run laws. " },
  { id := "reduce-find-min-colon-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_findmin(f, domain, ::Colon)"],
    statement := "Exactly pairs(original domain), then mapfoldl with its actual result, the correct reducer and a known indexed closure capturing the original f. The lambda body has its separately registered full-domain invariant. Every selected callee is unrestricted, including state, exceptions, nontermination and arbitrary output types.",
    source := "base/reduce.jl:921",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FindMinColonObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.findMinColonObservation_proven,
    notes := "Independent invocation/result/alias/world trace; no callee correctness, algebraic or successful-run laws. Includes concrete closure-body dependency." },
  { id := "reduce-find-min-reducer-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_rf_findmin((fm, im), (fx, ix))"],
    statement := "Full raw destructuring order, exact comparator operands/identity, Bool assertion, whole-pair provenance, left-tie branch, mutable worlds and immediate errors; no ordering laws. Every selected callee is unrestricted, including state, exceptions, nontermination and arbitrary output types.",
    source := "base/reduce.jl:922",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FindMinReducerObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.findMinReducerObservation_proven,
    notes := "Independent invocation/result/alias/world trace; no callee correctness, algebraic or successful-run laws. " },
  { id := "reduce-find-min-single-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["findmin(itr)"],
    statement := "One selected unary internal call receives the original iterator and Colon singleton, preserving its exact outcome/world. Every selected callee is unrestricted, including state, exceptions, nontermination and arbitrary output types.",
    source := "base/reduce.jl:949",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FindMinSingleObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.findMinSingleObservation_proven,
    notes := "Independent invocation/result/alias/world trace; no callee correctness, algebraic or successful-run laws. " },
  { id := "reduce-find-min-identity-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_findmin(a, ::Colon)"],
    statement := "One selected public call receives the exact identity function singleton and original collection, retaining every outcome/world. Every selected callee is unrestricted, including state, exceptions, nontermination and arbitrary output types.",
    source := "base/reduce.jl:950",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FindMinIdentityObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.findMinIdentityObservation_proven,
    notes := "Independent invocation/result/alias/world trace; no callee correctness, algebraic or successful-run laws. " },
  { id := "reduce-arg-max-mapped-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["argmax(f, domain)"],
    statement := "Mapfoldl receives the exact known value closure capture, reducer and domain; selected getindex receives its actual result and native Int64 two. No pair result is assumed; the actual lambda body is independently registered. Every selected callee is unrestricted, including state, exceptions, nontermination and arbitrary output types.",
    source := "base/reduce.jl:976",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.ArgMaxMappedObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.argMaxMappedObservation_proven,
    notes := "Independent invocation/result/alias/world trace; no callee correctness, algebraic or successful-run laws. Includes concrete closure-body dependency." },
  { id := "reduce-arg-max-single-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["argmax(itr)"],
    statement := "Find receives the original iterator; selected getindex then receives the exact observed result and native Int64 two, with result/error/world provenance and no invented pair projection. Every selected callee is unrestricted, including state, exceptions, nontermination and arbitrary output types.",
    source := "base/reduce.jl:1005",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.ArgMaxSingleObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.argMaxSingleObservation_proven,
    notes := "Independent invocation/result/alias/world trace; no callee correctness, algebraic or successful-run laws. " },
  { id := "reduce-arg-min-mapped-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["argmin(f, domain)"],
    statement := "Mapfoldl receives the exact known value closure capture, reducer and domain; selected getindex receives its actual result and native Int64 two. No pair result is assumed; the actual lambda body is independently registered. Every selected callee is unrestricted, including state, exceptions, nontermination and arbitrary output types.",
    source := "base/reduce.jl:1034",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.ArgMinMappedObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.argMinMappedObservation_proven,
    notes := "Independent invocation/result/alias/world trace; no callee correctness, algebraic or successful-run laws. Includes concrete closure-body dependency." },
  { id := "reduce-arg-min-single-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["argmin(itr)"],
    statement := "Find receives the original iterator; selected getindex then receives the exact observed result and native Int64 two, with result/error/world provenance and no invented pair projection. Every selected callee is unrestricted, including state, exceptions, nontermination and arbitrary output types.",
    source := "base/reduce.jl:1063",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.ArgMinSingleObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.argMinSingleObservation_proven,
    notes := "Independent invocation/result/alias/world trace; no callee correctness, algebraic or successful-run laws. " },
  { id := "reduce-find-indexed-closure-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_findmax(f, domain, ::Colon)", "_findmin(f, domain, ::Colon)"],
    statement := "The actual indexed closure fully destructures any argument, reads original captured f by fixed Core storage, maps the observed value exactly once, and returns that result paired with the original observed key. Raw result shapes, Core errors, state and divergence are retained.",
    source := "base/reduce.jl:855,921; base/tuple.jl:161-172; src/julia-syntax.scm:2597-2608",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FindIndexedClosureObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.findIndexedClosureObservation_proven,
    notes := "Registered necessary lambda body, not an opaque closure callback. Covers findIndexedClosureApply, FindIndexedClosure and flatteningDestructure." },
  { id := "reduce-find-value-closure-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["argmax(f, domain)", "argmin(f, domain)"],
    statement := "The actual value closure reads captured f by fixed Core storage, maps the exact original input once, and returns its actual result paired with that original input, including error/world/divergence behavior.",
    source := "base/reduce.jl:976,1034",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.FindValueClosureObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.findValueClosureObservation_proven,
    notes := "Registered necessary lambda body, no property override or algebraic/success premise. Covers findValueClosureApply and FindValueClosure." },
  { id := "reduce-bool-closure-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_bool"],
    statement := "The Bool closure retains the exact captured mapper, invokes it once with the original argument, returns an observed Bool unchanged or throws TypeError for every non-Bool result without conversion, preserving arbitrary mapper effects/errors.",
    source := "base/reduce.jl:1067",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.BoolClosureObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.boolClosureObservation_proven },
  { id := "reduce-count-forwarding-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["count", "_simple_count"],
    statement := "Count wrappers retain exact callable/iterator arguments, native Int64 zero when init is omitted and every explicit init value otherwise; generic simple_count constructs or selects its assertion closure before one sum call with the sole init keyword, preserving all outcomes/worlds.",
    source := "base/reduce.jl:1094-1098",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.CountForwardingObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.countForwardingObservation_proven },
  { id := "reduce-range-fold-observation",
    juliaFile := "base/reduce.jl",
    juliaFns := ["_foldl_impl"],
    statement := "Across all three generated range specializations and arbitrary selected range/BottomRF behavior, empty preserves init without further calls; nonempty evaluates the exact range reduction before the corresponding BottomRF first/binary or selected custom call; non-Bool emptiness raises TypeError, and every observation preserves original operands, outcomes and worlds.",
    source := "base/reduce.jl:1119-1124",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.reduce.Models2Group7.RangeFoldObservation,
    thm := ``JuliaLean.Proofs.base.reduce.Models2Group7.rangeFoldObservation_proven }
]

end JuliaLean.Proofs.base.reduce
