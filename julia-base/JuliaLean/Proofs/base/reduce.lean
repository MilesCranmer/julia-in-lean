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

theorem floatMax_law (a b : FloatValue) :
    floatEquivalent (floatMax a b)
      (if JuliaLean.base.float.isless_IEEEFloat a b then b else a) := by
  simp only [floatMax, JuliaLean.base.operators.max, JuliaLean.base.essentials.ifelse]
  cases hab : JuliaLean.base.float.isless_IEEEFloat a b
  · cases hba : JuliaLean.base.float.isless_IEEEFloat b a
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hpart := (JuliaLean.Proofs.base.float.islessPartition_proven .f64 b a).2.mpr ⟨hba, hab⟩
      rw [JuliaLean.Proofs.base.float.isequal_IEEEFloat_eq] at hpart
      simp only [JuliaLean.Promotion.Fl.isequal, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq] at hpart
      rcases hpart with ⟨hb, ha⟩ | hbits
      · exact Or.inr ⟨hb, ha⟩
      · left
        cases a; cases b
        congr
        exact Fin.ext hbits
    · simp only [↓reduceIte, Bool.false_eq_true]
      exact Or.inl rfl
  · have hba : JuliaLean.base.float.isless_IEEEFloat b a = false := by
      cases h : JuliaLean.base.float.isless_IEEEFloat b a
      · rfl
      · have haa := floatLess_order.trans a b a hab h
        rw [floatLess_order.irrefl a] at haa
        contradiction
    simp only [hba, Bool.false_eq_true, ↓reduceIte]
    exact Or.inl rfl

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

theorem floatFindmaxAgreeSpec_proven : FloatFindmaxAgreeSpec := by
  intro K elementType pairs xs entries hp he hn
  exact findmaxAgree_proven elementType pairs JuliaLean.base.float.isless_IEEEFloat
    floatGreater floatMax floatMin floatEquivalent xs entries floatLess_order floatGreater_order
    floatEquivalent_equivalence (fun a b c d hab hcd => (floatOrder_compatible a b c d hab hcd).1)
    (fun a b c d hab hcd => (floatOrder_compatible a b c d hab hcd).2) floatMax_law floatMin_law hp he hn
def FindmaxAgreementSpec : Prop := FindmaxAgree ∧ FloatFindmaxAgreeSpec
theorem findmaxAgreementSpec_proven : FindmaxAgreementSpec :=
  ⟨findmaxAgree_proven, floatFindmaxAgreeSpec_proven⟩

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

def entries : List JuliaLean.Registry.Entry := [
  { id := "reduce-mapped-empty-dispatch", juliaFile := "base/reduce.jl",
    juliaFns := ["mapfoldl", "mapreduce", "sum(abs, a)", "sum(abs2, a)", "maximum", "minimum",
      "mapreduce_empty", "mapreduce_empty_iter", "reduce_empty(::MappingRF, T)"],
    statement := "Empty mapped reductions dispatch on identity, abs, abs2 or other; Int abs/abs2 sums and maxima return zero, unsupported mappings throw, and mappings may change the neutral element's type.",
    source := "base/reduce.jl:359,371-380 (mapped empty methods)", status := .proven,
    prop := ``MappedEmptyDispatchSpec, thm := some ``mappedEmptyDispatchSpec_proven },
  { id := "reduce-bool-array-count", juliaFile := "base/reduce.jl",
    juliaFns := ["_simple_count(::typeof(identity), ::Array{Bool}, ::Int)"],
    statement := "For byte-addressed Bool storage, optimized array count returns Int init plus the number of true bytes, including all complete UInt chunks and the scalar tail.",
    source := "base/reduce.jl:1100-1116; Bool byte-storage and unsafe-load word interface", status := .proven,
    prop := ``BoolArrayCountSpec, thm := some ``boolArrayCountSpec_proven },
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
    prop := ``FindmaxAgreementSpec, thm := some ``findmaxAgreementSpec_proven },
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
  { id := "memsafety-reduce-linear", juliaFile := "base/reduce.jl",
    juliaFns := ["_mapreduce(::IndexLinear, ...)", "_simple_count(::Array{Bool})"],
    statement := "Linear mapreduce reads stay inside the selected linear-index interval, and Bool word reads cover only complete UInt-sized chunks.",
    source := "base/reduce.jl:436-455,1097-1112; IndexLinear axis invariant", status := .proven,
    prop := ``ReduceSafe, thm := some ``reduceSafe_proven },
  { id := "reducecov-reduce-number", juliaFile := "base/reduce.jl",
    juliaFns := ["reduce(::Any, ::Number)"],
    statement := "A single Number reduction equals reduce_first(op, x), as a one-element iterator reduction does.",
    source := "base/reduce.jl:503", status := .refuted,
    prop := ``ReduceNumberFirst, thm := some ``reduceNumberFirst_refuted,
    issue := "none found (queries: reduce number reduce_first; reduce(+, true); reduce Number scalar)",
    notes := "Scalar reduce preserves Bool, while the first-element plus dispatch returns Int; reproduced on release and target nightly." },
  { id := "reduce-boolean-typecheck", juliaFile := "base/reduce.jl",
    juliaFns := ["and_all", "or_any", "_bool"],
    statement := "Generic Boolean reductions reject non-Bool conditions and results, except for a short-circuited operand; predicate results are asserted to be Bool.",
    source := "base/reduce.jl:32-36,1067 (Bool assertions)", status := .proven,
    prop := ``BooleanTypeSpec, thm := some ``booleanTypeSpec_proven },
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
  { id := "reduce-model-boolean", juliaFile := "base/reduce.jl",
    juliaFns := ["and_all", "or_any"],
    statement := "Bool conjunction and disjunction use their corresponding Boolean operations.",
    source := "base/reduce.jl:32-36", status := .proven,
    prop := ``BooleanReductionRules, thm := some ``booleanReductionRules_proven },
  { id := "reduce-model-folds", juliaFile := "base/reduce.jl",
    juliaFns := ["foldl", "foldr", "mapfoldl", "mapfoldr", "reduce", "mapreduce", "mapfoldl_impl", "foldl_impl", "_foldl_impl", "BottomRF", "MappingRF", "FilteringRF", "FlatteningRF", "_xfadjoint", "_xfadjoint_unwrap"],
    statement := "Mapped folds use the initial value once, preserve left-to-right order, and fold nested iterators without changing their element order.",
    source := "base/reduce.jl:40-164,173-241", status := .proven,
    prop := ``FoldAllMethodsSpec, thm := some ``foldAllMethodsSpec_proven },
  { id := "reduce-model-pairwise", juliaFile := "base/reduce.jl",
    juliaFns := ["mapreduce_impl", "_mapreduce(::IndexLinear, A)", "mapreduce_first"],
    statement := "Associative pairwise reductions and the short and long linear-array paths traverse the complete mapped interval; empty linear arrays use the empty dispatch result.",
    source := "base/reduce.jl:252-314,435-460", status := .proven,
    prop := ``PairwiseMethodsSpec, thm := some ``pairwiseMethodsSpec_proven },
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
