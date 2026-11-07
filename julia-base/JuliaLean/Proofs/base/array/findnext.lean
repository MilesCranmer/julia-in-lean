import JuliaLean.base.array
import JuliaLean.src.genericmemory_c
import JuliaLean.Proofs.base.dict
import JuliaLean.base.operators
import JuliaLean.base.int
import JuliaLean.base.number
import JuliaLean.base.abstractarray
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.range
import JuliaLean.Proofs.base.int
import JuliaLean.base.float
import JuliaLean.base.cmem
import JuliaLean.Proofs.base.cmem
import JuliaLean.base.pointer
import JuliaLean.base.set
import JuliaLean.Proofs.base.set
import JuliaLean.base.multidimensional
import JuliaLean.base.indices
import JuliaLean.base.essentials
import JuliaLean.Proofs.base.array.common.convert
import JuliaLean.Proofs.base.array.common.copy
import JuliaLean.Proofs.base.array.common.grow

attribute [local instance] JuliaLean.Proofs.base.array.layoutAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.nativeAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.layoutFunctionAllocationProjection
attribute [local instance] JuliaLean.Proofs.base.array.nativeFunctionAllocationProjection
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array JuliaLean.src.genericmemory_c

theorem validArraySlots_set {α : Type} (layout : DictLayout) (slots : List (Option α))
    (h : ValidArraySlots layout slots) (index : Nat) (value : α) :
    ValidArraySlots layout (slots.set index (some value)) := by
  intro hc j hj
  simp only [List.length_set] at hj
  by_cases hji : j = index
  · subst j
    rw [List.getElem?_set_self hj]
    rfl
  · rw [List.getElem?_set_ne (Ne.symm hji)]
    exact h hc j hj

theorem validArraySlots_unset {α : Type} (layout : DictLayout) (slots : List (Option α))
    (h : ValidArraySlots layout slots) (index : Nat) (hi : index < slots.length) :
    ValidArraySlots layout (slots.set index (expectedUnset layout (slots[index]?).join)) := by
  intro hc j hj
  simp only [List.length_set] at hj
  by_cases hji : j = index
  · subst j
    rw [List.getElem?_set_self hi]
    simpa only [Option.join_some, expectedUnset, hc, Bool.false_eq_true, ite_false] using h hc index hi
  · rw [List.getElem?_set_ne (Ne.symm hji)]
    exact h hc j hj
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000


/-- A search returns a matching key, with no earlier matching element. -/
def firstMatch (test : α → Bool) (pairs : List (K × α)) (key : K) : Prop :=
  ∃ before value after, pairs = before ++ (key, value) :: after ∧
    test value = true ∧ ∀ p ∈ before, test p.2 = false

/-- A backward search returns a matching key, with no later matching element. -/
def lastMatch (test : α → Bool) (pairs : List (K × α)) (key : K) : Prop :=
  ∃ before value after, pairs = before ++ (key, value) :: after ∧
    test value = true ∧ ∀ p ∈ after, test p.2 = false

theorem findfirst_nil (test : α → Bool) :
    findfirst (m := Id) test ([] : List (K × α)) = none := by
  simp [findfirst, Bind.bind, Pure.pure]

theorem findfirst_cons (test : α → Bool) (k : K) (a : α) (pairs : List (K × α)) :
    findfirst (m := Id) test ((k, a) :: pairs) =
      (if test a then some k else findfirst (m := Id) test pairs) := by
  cases ht : test a <;> simp [findfirst, ht, Bind.bind, Pure.pure]

theorem findfirst_firstMatch (test : α → Bool) (pairs : List (K × α)) (key : K)
    (h : findfirst (m := Id) test pairs = some key) : firstMatch test pairs key := by
  induction pairs with
  | nil =>
    rw [findfirst_nil] at h
    cases h
  | cons p pairs ih =>
    obtain ⟨k, a⟩ := p
    rw [findfirst_cons] at h
    cases ht : test a with
    | true =>
      simp [ht] at h
      have hk := Option.some.inj h
      subst k
      exact ⟨[], a, pairs, rfl, ht, by simp⟩
    | false =>
      simp [ht] at h
      obtain ⟨before, value, after, he, hv, hb⟩ := ih h
      refine ⟨(k, a) :: before, value, after, ?_, hv, ?_⟩
      · simp [he]
      · intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ht
        · exact hb p hp

theorem findfirst_none_iff (test : α → Bool) (pairs : List (K × α)) :
    findfirst (m := Id) test pairs = none ↔ ∀ p ∈ pairs, test p.2 = false := by
  induction pairs with
  | nil => simp [findfirst_nil]
  | cons p pairs ih =>
    obtain ⟨k, a⟩ := p
    rw [findfirst_cons]
    cases ht : test a <;> simp [ht, ih]

theorem findfirst_sound (test : α → Bool) (pairs : List (K × α)) (key : K)
    (h : findfirst (m := Id) test pairs = some key) :
    ∃ value, (key, value) ∈ pairs ∧ test value = true := by
  obtain ⟨before, value, after, he, hv, _⟩ := findfirst_firstMatch test pairs key h
  exact ⟨value, by simp [he], hv⟩

theorem findlast_lastMatch (test : α → Bool) (pairs : List (K × α)) (key : K)
    (h : findlast (m := Id) List.reverse test pairs = some key) : lastMatch test pairs key := by
  obtain ⟨before, value, after, he, hv, hb⟩ :=
    findfirst_firstMatch test pairs.reverse key h
  refine ⟨after.reverse, value, before.reverse, ?_, hv, ?_⟩
  · have := congrArg List.reverse he
    simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using this
  · intro p hp
    exact hb p (by simpa using hp)

theorem findlast_sound (test : α → Bool) (pairs : List (K × α)) (key : K)
    (h : findlast (m := Id) List.reverse test pairs = some key) :
    ∃ value, (key, value) ∈ pairs ∧ test value = true := by
  obtain ⟨before, value, after, he, hv, _⟩ := findlast_lastMatch test pairs key h
  exact ⟨value, by simp [he], hv⟩

def FirstSearchSound : Prop := ∀ (α K : Type) (test : α → Bool) (pairs : List (K × α)) (key : K),
  findfirst (m := Id) test pairs = some key → ∃ value, (key, value) ∈ pairs ∧ test value = true

def FirstSearchComplete : Prop := ∀ (α K : Type) (test : α → Bool) (pairs : List (K × α)),
  findfirst (m := Id) test pairs = none ↔ ∀ p ∈ pairs, test p.2 = false

def FirstSearchEarliest : Prop := ∀ (α K : Type) (test : α → Bool) (pairs : List (K × α)) (key : K),
  findfirst (m := Id) test pairs = some key → firstMatch test pairs key

def LastSearchSound : Prop := ∀ (α K : Type) (test : α → Bool) (pairs : List (K × α)) (key : K),
  findlast (m := Id) List.reverse test pairs = some key → ∃ value, (key, value) ∈ pairs ∧ test value = true

def LastSearchLatest : Prop := ∀ (α K : Type) (test : α → Bool) (pairs : List (K × α)) (key : K),
  findlast (m := Id) List.reverse test pairs = some key → lastMatch test pairs key

theorem firstSearchSound : FirstSearchSound := fun _ _ => findfirst_sound
theorem firstSearchComplete : FirstSearchComplete := fun _ _ => findfirst_none_iff
theorem firstSearchEarliest : FirstSearchEarliest := fun _ _ => findfirst_firstMatch
theorem lastSearchSound : LastSearchSound := fun _ _ => findlast_sound
theorem lastSearchLatest : LastSearchLatest := fun _ _ => findlast_lastMatch

/-- Independent specification: the first matching one-based index at least `start`. -/
def firstAtLeast (test : α → Bool) (xs : List α) (start : Int) : Option Int :=
  ((xs.zipIdx 1).find? (fun p => test p.1 && decide (start ≤ (p.2 : Int)))).map
    (fun p => (p.2 : Int))

/-- Independent specification: the last matching one-based index at most `start`. -/
def lastUpTo (test : α → Bool) (xs : List α) (start : Int) : Option Int :=
  ((xs.zipIdx 1).reverse.find? (fun p => test p.1 && decide ((p.2 : Int) ≤ start))).map
    (fun p => (p.2 : Int))

/-- The original full all-starts promise, including starts beyond either array boundary. -/
def FindAllStarts : Prop :=
  ∀ (α : Type) (t : IntTy) (test : α → Bool) (xs : List α) (i : JInt t)
    (hn : xs.length < 2 ^ 62), IntTy.i64.min ≤ i.val → i.val ≤ IntTy.i64.max →
    (findnext (fun _ => one) (fun _ => JInt.wrap .i64 xs.length)
      (fun _ j => indexConvert j) (fun j k => decide (j.val > k.val))
      vectorGet (fun a => .ok (test a)) (forwardRank xs.length)
      (nextVectorIndex xs.length hn) xs i).map (Option.map Subtype.val) = .ok (firstAtLeast test xs i.val) ∧
    (findprev (fun _ => one) (fun _ j => indexConvert j) (fun j k => decide (j.val < k.val))
      vectorGet (fun a => .ok (test a)) backwardRank prevVectorIndex xs i).map (Option.map Subtype.val) = .ok (lastUpTo test xs i.val)

def RangeFindfirstPositive : Prop :=
  (∀ (V X Diff : Type) (value : V → Int) (xValue : X → Int)
    (subtract : X → V → Diff) (convertDifference : Diff → Except Error I)
    (lo hi : V) (x : X),
    value lo ≤ xValue x → xValue x ≤ value hi →
    ∃ k : I,
      findfirstUnitRange (m := Except Error)
        (fun r : V × V => r.1) Prod.snd value xValue
        (fun _ => .ok one) subtract (fun _ => convertDifference) (· + ·)
        x (lo, hi) = .ok (some k) ∧ 1 ≤ k.val) ∧
  (∀ (V X Step Diff Rem Quot : Type)
    (value : V → Int) (xValue : X → Int) (stepValue : Step → Int)
    (subtract : X → V → Diff) (remainder : Diff → Step → Except Error Rem)
    (iszero : Rem → Bool) (divide : Diff → Step → Except Error Quot)
    (plusOne : Quot → Quot) (convertKey : Quot → Except Error I)
    (lo hi : V) (step : Step) (x : X),
    stepValue step ≠ 0 →
    min (value lo) (value hi) ≤ xValue x →
    xValue x ≤ max (value lo) (value hi) →
    (∃ n : Nat, xValue x = value lo + n * stepValue step) →
    ∃ k : I,
      findfirstStepRange (m := Except Error)
        (fun r : V × Step × V =>
          if 0 < stepValue r.2.1 then decide (value r.2.2 < value r.1)
          else decide (value r.1 < value r.2.2))
        (fun r => if value r.1 ≤ value r.2.2 then r.1 else r.2.2)
        (fun r => if value r.1 ≤ value r.2.2 then r.2.2 else r.1)
        (fun r => r.1) (fun r => r.2.1)
        (fun a b => decide (value a ≤ xValue b))
        (fun a b => decide (xValue a ≤ value b))
        subtract remainder iszero divide plusOne convertKey x (lo, step, hi) =
          .ok (some k) ∧ 1 ≤ k.val)

theorem rangeFindfirstPositive_refuted : ¬ RangeFindfirstPositive := by
  intro h
  obtain ⟨k, hk, hp⟩ := h.2 (JInt .i8) (JInt .i8) (JInt .i8)
    (JInt .i8) (JInt .i8) (JInt .i8)
    Subtype.val Subtype.val Subtype.val (· - ·)
    (fun a b => .ok (JInt.wrap .i8 (a.val.tmod b.val)))
    (fun a => a.val == 0)
    (fun a b => .ok (JInt.wrap .i8 (a.val.tdiv b.val)))
    (fun a => a + JInt.wrap .i8 1) indexConvert
    (JInt.wrap .i8 (-100)) (JInt.wrap .i8 120) (JInt.wrap .i8 2) (JInt.wrap .i8 100)
    (by decide) (by decide) (by decide) ⟨100, by decide⟩
  have actual :
      findfirstStepRange (m := Except Error)
        (fun r : JInt .i8 × JInt .i8 × JInt .i8 =>
          if 0 < r.2.1.val then decide (r.2.2.val < r.1.val)
          else decide (r.1.val < r.2.2.val))
        (fun r => if r.1.val ≤ r.2.2.val then r.1 else r.2.2)
        (fun r => if r.1.val ≤ r.2.2.val then r.2.2 else r.1)
        (fun r => r.1) (fun r => r.2.1)
        (fun a b => decide (a.val ≤ b.val)) (fun a b => decide (a.val ≤ b.val)) (· - ·)
        (fun a b => .ok (JInt.wrap .i8 (a.val.tmod b.val)))
        (fun a => a.val == 0)
        (fun a b => .ok (JInt.wrap .i8 (a.val.tdiv b.val)))
        (fun a => a + JInt.wrap .i8 1) indexConvert (JInt.wrap .i8 100)
        (JInt.wrap .i8 (-100), JInt.wrap .i8 2, JInt.wrap .i8 120) =
          .ok (some (JInt.wrap .i64 (-27))) := by rfl
  rw [actual] at hk
  cases hk
  exact (by decide : ¬ (1 ≤ (JInt.wrap .i64 (-27)).val)) hp

def listLookupCollectOps {m : Type → Type} [Monad m] {E K T B : Type}
    (defaultB : m B) (collectList : List (Option K) → m B) :
    TypedCollectOps m (LookupGenerator m (List E) E K) (Option K) T Unit Unit B where
  size _ := ()
  sized _ := true
  unknown _ := false
  shape _ _ := pure ()
  arrayForInner _ _ _ := defaultB
  copyto _ g := do collectList (← g.iter.mapM g.f)
  emptyVector _ := defaultB
  push _ _ := pure ()

/-- The specialised membership search must use the same equality as membership
in the original collection, including IEEE signed zeros and NaNs. -/
def TupleMembershipAgreement : Prop :=
  ∀ (xs ys : List (JuliaLean.Promotion.Fl JuliaLean.Promotion.double)) (initial : MutableMemory I),
    let operation := findallIn2962 (m := MutationM I)
      (fun _ => false) id (fun values => pure values)
      (mutableAllocate (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout) 0 zero)
      (fun values => (values.zipIdx 1).map (fun p => (JInt.wrap .i64 (p.2 : Int), p.1)))
      (fun x values => pure (values.any (JuliaLean.C.jlFpiseq x)))
      (mutablePush (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout)) ys xs
    let result := operation.run initial
    result.1.map (fun handle => result.2.contents handle) =
      .ok (((xs.zipIdx 1).filter (fun p => ys.any (JuliaLean.C.jlEqFloat p.1))).map
        (fun p => some (JInt.wrap .i64 (p.2 : Int))))

def IndexinMembershipAgreement : Prop :=
  ∀ (xs ys : List (JuliaLean.Promotion.Fl JuliaLean.Promotion.double)) (initial : MutableMemory (Option I)),
    let operation := indexin
      (m := StateT (List (JuliaLean.Promotion.Fl JuliaLean.Promotion.double × I))
        (MutationM (Option I)))
      (fun values => pure ((List.range values.length).map (fun (i : Nat) => JInt.wrap .i64 ((i : Int) + 1))))
      (pure ()) List.zip
      (fun _ value key => dictInsertFirst JuliaLean.C.jlFpiseq value key)
      (fun _ value default => dictGet JuliaLean.C.jlFpiseq value default)
      (fun _ => ())
      (listLookupCollectOps (pure 0) (typedLiteral (fun n => liftM (mutableAllocate (α := Option I) (some ⟨8, false, true⟩) 0 n))
        (fun a value i => liftM (mutableTypedSet (α := Option I) a value i)) true)) xs ys
    let result := (operation.run []).run initial
    result.1.map (fun (handle, _) => result.2.contents handle) =
      .ok (xs.map (fun x => some (((ys.zipIdx 1).find? (fun p => JuliaLean.C.jlEqFloat x p.1)).map
        (fun p => JInt.wrap .i64 (p.2 : Int)))))

def FindfirstCartesian : Prop :=
  ∀ (dims : List Nat) (values : List I → Bool),
    (∀ n ∈ dims, n < 2 ^ 20) →
    findfirstArray (m := Except Error)
      (fun shape => .ok (shape.map (fun _ => one)))
      (fun shape => shape.map (fun _ => one))
      (fun shape => shape.map (fun (n : Nat) => JInt.wrap .i64 (n : Int)))
      (fun _ i => .ok i) cartesianGreater
      (fun shape key => if key ∈ cartesianKeys shape then .ok (values key) else .error .bounds)
      (cartesianRank dims) (cartesianNext dims)
      (fun value => .ok value) dims =
        .ok ((cartesianKeys dims).find? values)

/-- The number of reads and writes in an expression is unchanged by safe indexing. -/
def indexOperations : Expr Atom → Nat
  | .atom _ => 0
  | .node _ args => (args.map indexOperations).sum
  | .ref xs args => indexOperations xs + 1 + (args.map indexOperations).sum
  | .assign lhs rhs => indexOperations lhs + indexOperations rhs
  | .safeGet xs args => indexOperations xs + 1 + (args.map indexOperations).sum
  | .safeSet xs rhs args =>
      indexOperations xs + 1 + indexOperations rhs + (args.map indexOperations).sum
  | .escape body => indexOperations body
termination_by e => sizeOf e

def SafeindexSpec : Prop := ∀ (Atom : Type) (e : Expr Atom),
  indexOperations (safeindex e) = indexOperations e ∧
  indexOperations (safeindexMacro safeindex e) = indexOperations e

theorem safeindex_operations (e : Expr Atom) :
    indexOperations (safeindex e) = indexOperations e := by
  induction e using safeindex.induct with
  | case1 => simp [safeindex, indexOperations]
  | case2 xs args rhs hr ha =>
    have hm : (args.map (fun x => indexOperations (safeindex x))).sum =
        (args.map indexOperations).sum := by
      congr 1
      exact List.map_congr_left ha
    simp only [safeindex, indexOperations, List.map_map, Function.comp_def]
    rw [hr, hm]
    omega
  | case3 => simp [safeindex, indexOperations]
  | case4 lhs rhs hl hr =>
    cases lhs <;> simp_all [safeindex, indexOperations]
  | case5 h args ha =>
    simp only [safeindex, indexOperations, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro x hx
    exact ha x hx
  | case6 xs args hx ha =>
    simp only [safeindex, indexOperations, List.map_map]
    rw [hx]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro x h
    exact ha x h
  | case7 xs x args hx hv ha =>
    simp only [safeindex, indexOperations, List.map_map]
    rw [hx, hv]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro a h
    exact ha a h
  | case8 x hx => simpa only [safeindex, indexOperations] using hx

theorem safeindexSpec : SafeindexSpec := by
  intro Atom e
  exact ⟨safeindex_operations e, by
    simpa only [safeindexMacro, indexOperations] using safeindex_operations e⟩

/-- Safe-call constructors are introduced by the rewrite, not by the input AST. -/
def ordinaryExpression : Expr Atom → Prop
  | .atom _ => True
  | .node _ args => ∀ x ∈ args, ordinaryExpression x
  | .ref xs args => ordinaryExpression xs ∧ ∀ x ∈ args, ordinaryExpression x
  | .assign lhs rhs => ordinaryExpression lhs ∧ ordinaryExpression rhs
  | .escape x => ordinaryExpression x
  | .safeGet _ _ | .safeSet _ _ _ => False
termination_by e => sizeOf e

def restoreIndexing : Expr Atom → Expr Atom
  | .atom x => .atom x
  | .node h args => .node h (args.map restoreIndexing)
  | .ref xs args => .ref (restoreIndexing xs) (args.map restoreIndexing)
  | .assign lhs rhs => .assign (restoreIndexing lhs) (restoreIndexing rhs)
  | .safeGet xs args => .ref (restoreIndexing xs) (args.map restoreIndexing)
  | .safeSet xs x args =>
      .assign (.ref (restoreIndexing xs) (args.map restoreIndexing)) (restoreIndexing x)
  | .escape x => .escape (restoreIndexing x)
termination_by e => sizeOf e

theorem restoreIndexing_ordinary (e : Expr Atom) (he : ordinaryExpression e) :
    restoreIndexing e = e := by
  cases e with
  | atom x => simp [restoreIndexing]
  | node h args =>
    simp only [restoreIndexing]
    simp only [ordinaryExpression] at he
    have hm : args.map restoreIndexing = args := by
      calc
        args.map restoreIndexing = args.map id :=
          List.map_congr_left (fun x hx => restoreIndexing_ordinary x (he x hx))
        _ = args := List.map_id args
    rw [hm]
  | ref xs args =>
    simp only [ordinaryExpression] at he
    have hm : args.map restoreIndexing = args := by
      calc
        args.map restoreIndexing = args.map id :=
          List.map_congr_left (fun x hx => restoreIndexing_ordinary x (he.2 x hx))
        _ = args := List.map_id args
    simp only [restoreIndexing]
    rw [restoreIndexing_ordinary xs he.1, hm]
  | assign lhs rhs =>
    simp only [ordinaryExpression] at he
    simp only [restoreIndexing]
    rw [restoreIndexing_ordinary lhs he.1, restoreIndexing_ordinary rhs he.2]
  | escape x =>
    simp only [ordinaryExpression] at he
    simp only [restoreIndexing]
    rw [restoreIndexing_ordinary x he]
  | safeGet xs args => simp only [ordinaryExpression] at he
  | safeSet xs x args => simp only [ordinaryExpression] at he
termination_by sizeOf e

theorem safeindex_restore (e : Expr Atom) (he : ordinaryExpression e) :
    restoreIndexing (safeindex e) = e := by
  revert he
  induction e using safeindex.induct with
  | case1 => intro he; simp [safeindex, restoreIndexing]
  | case2 xs args rhs hr ha =>
    intro he
    simp only [ordinaryExpression] at he
    have hm : (args.map safeindex).map restoreIndexing = args := by
      rw [List.map_map]
      calc
        args.map (restoreIndexing ∘ safeindex) = args.map id :=
          List.map_congr_left (fun x hx => ha x hx (he.1.2 x hx))
        _ = args := List.map_id args
    simp only [safeindex, restoreIndexing]
    rw [restoreIndexing_ordinary xs he.1.1, hr he.2, hm]
  | case3 xs args =>
    intro he
    simpa only [safeindex, restoreIndexing] using restoreIndexing_ordinary (.ref xs args) he
  | case4 lhs rhs hl hr =>
    intro he
    cases lhs <;> simp_all [ordinaryExpression, safeindex, restoreIndexing]
  | case5 h args ha =>
    intro he
    simp only [ordinaryExpression] at he
    have hm : (args.map safeindex).map restoreIndexing = args := by
      rw [List.map_map]
      calc
        args.map (restoreIndexing ∘ safeindex) = args.map id :=
          List.map_congr_left (fun x hx => ha x hx (he x hx))
        _ = args := List.map_id args
    simp only [safeindex, restoreIndexing]
    rw [hm]
  | case6 => intro he; simp only [ordinaryExpression] at he
  | case7 => intro he; simp only [ordinaryExpression] at he
  | case8 x hx =>
    intro he
    simp only [ordinaryExpression] at he
    simp only [safeindex, restoreIndexing]
    rw [hx he]

def SafeindexComplete : Prop := SafeindexSpec ∧ ∀ (Atom : Type) (e : Expr Atom),
  ordinaryExpression e →
    restoreIndexing (safeindex e) = e ∧
    restoreIndexing (safeindexMacro safeindex e) = .escape e

theorem safeindexComplete : SafeindexComplete := by
  refine ⟨safeindexSpec, ?_⟩
  intro Atom e he
  exact ⟨safeindex_restore e he, by
    simp only [safeindexMacro, restoreIndexing]
    rw [safeindex_restore e he]⟩

theorem collectReadSlot_map (xs : List α) :
    (xs.map some).mapM collectReadSlot = .ok (xs.map some) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, collectReadSlot, ih, Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem collectReadSlot_undefined (xs : List (Option α)) (h : none ∈ xs) :
    xs.mapM collectReadSlot = .error .undefinedReference := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    cases x with
    | none => rfl
    | some x =>
      have ht : none ∈ xs := by simpa using h
      simp [List.mapM_cons, collectReadSlot, ih ht, Bind.bind, Except.bind]

theorem collectHeapEmpty_run {Tag α : Type} (heap : VectorHeap α) (src : HeapArray Tag)
    (xs : List (Option α)) (hs : heap[src.handle]? = some xs) :
    (collectHeapEmpty src).run heap = .ok (xs.isEmpty, heap) := by
  simp only [collectHeapEmpty, vector_bind_run, heapSlots_run, hs, vector_pure_run]

@[simp] theorem keepatPure_run (x : β) (old : MutableMemory α) :
    ((pure x : KeepatM α β).run).run old = (.ok (.ok x), old) := rfl

def ScalarFindallSpec : Prop :=
  (∀ (x : Bool), (findallBool x).Nodup ∧
    ∀ k, k ∈ findallBool x ↔ x = true ∧ k = one) ∧
  (∀ (α : Type) (test : α → Bool) (x : α), (findallNumber test x).Nodup ∧
    ∀ k, k ∈ findallNumber test x ↔ test x = true ∧ k = one) ∧
  (∀ (α Collection : Type) (contains : α → Collection → Bool)
    (collection : Collection) (x : α), (findallInNumber contains collection x).Nodup ∧
    ∀ k, k ∈ findallInNumber contains collection x ↔
      contains x collection = true ∧ k = one)

theorem scalarFindallSpec : ScalarFindallSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    cases x <;> simp [findallBool]
  · intro α test x
    cases h : test x <;> simp [findallNumber, h]
  · intro α Collection contains collection x
    cases h : contains x collection <;> simp [findallInNumber, h]

/-- Searches in a one-based integer interval return precisely its matching first key. -/
def OneToFirstSearchSpec : Prop :=
  (∀ (x stop k : Int),
    findfirstOneTo (m := Except Error) id id (fun x => pure x) x stop = .ok (some k) ↔
      k = x ∧ 1 ≤ k ∧ k ≤ stop) ∧
  (∀ (x stop : Int),
    findfirstOneTo (m := Except Error) id id (fun x => pure x) x stop = .ok none ↔
      x < 1 ∨ stop < x) ∧
  (∀ (stop : Int), findfirstZeroOneTo (K := Int) stop = none) ∧
  (∀ (stop k : Int),
    findfirstOneOneTo (m := Except Error) (fun n : Int => decide (n < 1))
      (fun _ => pure (1 : Int)) stop = .ok (some k) ↔ k = 1 ∧ 1 ≤ stop)

def NextMatch (test : α → Bool) (xs : List α) (start : Int) : Option Int → Prop
  | some k => start ≤ k ∧ 1 ≤ k ∧ (∃ x, xs[(k - 1).toNat]? = some x ∧ test x = true) ∧
      ∀ j x, start ≤ j → 1 ≤ j → j < k → xs[(j - 1).toNat]? = some x → test x = false
  | none => ∀ j x, start ≤ j → 1 ≤ j → xs[(j - 1).toNat]? = some x → test x = false

/-- Independent specification of a backward search from `start` in a one-based vector:
`some k` is the greatest position at or before `start` whose element passes `test`, and
`none` means that no element at or before `start` passes. -/
def PrevMatch (test : α → Bool) (xs : List α) (start : Int) : Option Int → Prop
  | some k => k ≤ start ∧ 1 ≤ k ∧ (∃ x, xs[(k - 1).toNat]? = some x ∧ test x = true) ∧
      ∀ j x, k < j → j ≤ start → xs[(j - 1).toNat]? = some x → test x = false
  | none => ∀ j x, 1 ≤ j → j ≤ start → xs[(j - 1).toNat]? = some x → test x = false

theorem searchOne : (one : I).val = 1 := rfl

theorem searchOneMax : (1 : Int) ≤ IntTy.i64.max := by
  simp [IntTy.max, IntTy.signed, IntTy.bits]

theorem searchSucc (i : I) (h : i.val < 9223372036854775807) : (i + one).val = i.val + 1 := by
  have hi : -9223372036854775808 ≤ i.val ∧ i.val ≤ 9223372036854775807 := i.property
  change wrapInt .i64 (i.val + one.val) = i.val + 1
  rw [show one.val = 1 from rfl]
  apply wrapInt_of_inRange
  change -9223372036854775808 ≤ i.val + 1 ∧ i.val + 1 ≤ 9223372036854775807
  omega

theorem searchPred (i : I) (h : -9223372036854775808 < i.val) : (i - one).val = i.val - 1 := by
  have hi : -9223372036854775808 ≤ i.val ∧ i.val ≤ 9223372036854775807 := i.property
  change wrapInt .i64 (i.val - one.val) = i.val - 1
  rw [show one.val = 1 from rfl]
  apply wrapInt_of_inRange
  change -9223372036854775808 ≤ i.val - 1 ∧ i.val - 1 ≤ 9223372036854775807
  omega

theorem searchIndexConvert {t : IntTy} (i : JInt t)
    (h : IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max) :
    indexConvert i = .ok ⟨i.val, h⟩ := by
  simp [indexConvert, JInt.convert, h, Except.mapError]

theorem searchGet (xs : List α) (i : I) (h1 : 1 ≤ i.val) (hlen : i.val ≤ xs.length) :
    ∃ x, xs[(i.val - 1).toNat]? = some x ∧ vectorGet xs i = .ok x := by
  have hlt : (i.val - 1).toNat < xs.length := by omega
  refine ⟨_, List.getElem?_eq_getElem hlt, ?_⟩
  unfold vectorGet
  rw [if_pos ⟨h1, hlen⟩, List.getElem?_eq_getElem hlt]

/-- Past the last position there is no element. -/
theorem searchBeyond (xs : List α) (j : Int) (hj : (xs.length : Int) < j) (x : α) :
    xs[(j - 1).toNat]? ≠ some x := by
  rw [List.getElem?_eq_none (by omega)]
  simp

theorem findnextLoop_spec (test : α → Bool) (xs : List α) (hn : xs.length < 2 ^ 62) :
    ∀ (k : Nat) (i : I), forwardRank xs.length i = k → 1 ≤ i.val → i.val ≤ xs.length →
      ∃ r, findnext.loop vectorGet (fun a => Except.ok (test a)) (forwardRank xs.length)
        (nextVectorIndex xs.length hn) xs (JInt.wrap .i64 xs.length) i = .ok r ∧
        NextMatch test xs i.val (r.map Subtype.val) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro i hk h1 hlen
    have hL : (JInt.wrap .i64 (xs.length : Int)).val = xs.length :=
      collectorLengthFits xs.length (by omega)
    obtain ⟨x, hx, hget⟩ := searchGet xs i h1 hlen
    rw [findnext.loop]
    cases htx : test x
    · by_cases hil : i = JInt.wrap .i64 xs.length
      · have hiv : i.val = xs.length := by rw [hil, hL]
        refine ⟨none, ?_, ?_⟩
        · rw [hget]
          simp [htx, hil, Bind.bind, Except.bind, Pure.pure, Except.pure]
        · intro j y hj hj1 hy
          by_cases hje : j = i.val
          · rw [hje, hx] at hy
            cases hy
            exact htx
          · exact absurd hy (searchBeyond xs j (by omega) y)
      · have hiv : i.val ≠ xs.length := fun e => hil (Subtype.ext (by rw [e, hL]))
        have hpos : 0 < forwardRank xs.length i := by simp only [forwardRank]; omega
        have hsucc := searchSucc i (by omega)
        obtain ⟨r, hr, hm⟩ := ih (forwardRank xs.length (i + one))
          (by simp only [forwardRank, hsucc] at hk ⊢; omega) (i + one) rfl
          (by rw [hsucc]; omega) (by rw [hsucc]; omega)
        refine ⟨r, ?_, ?_⟩
        · simp [hget, htx, hil, nextVectorIndex, hpos, Bind.bind, Except.bind]
          exact hr
        · rw [hsucc] at hm
          cases r with
          | none =>
            intro j y hj hj1 hy
            by_cases hje : j = i.val
            · rw [hje, hx] at hy
              cases hy
              exact htx
            · exact hm j y (by omega) hj1 hy
          | some key =>
            obtain ⟨hk1, hk2, hk3, hk4⟩ := hm
            refine ⟨by omega, hk2, hk3, ?_⟩
            intro j y hj hj1 hjk hy
            by_cases hje : j = i.val
            · rw [hje, hx] at hy
              cases hy
              exact htx
            · exact hk4 j y (by omega) hj1 hjk hy
    · refine ⟨some i, ?_, ?_⟩
      · simp [hget, htx, Bind.bind, Except.bind, Pure.pure, Except.pure]
      · refine ⟨Int.le_refl _, h1, ⟨x, hx, htx⟩, ?_⟩
        intro j y hj _ hjk _
        omega

theorem findprevLoop_spec (test : α → Bool) (xs : List α) :
    ∀ (k : Nat) (i : I), backwardRank i = k → 1 ≤ i.val → i.val ≤ xs.length →
      ∃ r, findprev.loop vectorGet (fun a => Except.ok (test a)) backwardRank
        prevVectorIndex xs one i = .ok r ∧
        PrevMatch test xs i.val (r.map Subtype.val) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro i hk h1 hlen
    obtain ⟨x, hx, hget⟩ := searchGet xs i h1 hlen
    rw [findprev.loop]
    cases htx : test x
    · by_cases hif : i = one
      · have hiv : i.val = 1 := by rw [hif]; rfl
        refine ⟨none, ?_, ?_⟩
        · rw [hget]
          simp [htx, hif, Bind.bind, Except.bind, Pure.pure, Except.pure]
        · intro j y hj1 hj hy
          have hje : j = i.val := by omega
          rw [hje, hx] at hy
          cases hy
          exact htx
      · have hiv : i.val ≠ 1 := fun e => hif (Subtype.ext (by rw [e]; rfl))
        have hpos : 0 < backwardRank i := by simp only [backwardRank]; omega
        have hpred := searchPred i (by have := i.property; omega)
        obtain ⟨r, hr, hm⟩ := ih (backwardRank (i - one))
          (by simp only [backwardRank, hpred] at hk ⊢; omega) (i - one) rfl
          (by rw [hpred]; omega) (by rw [hpred]; omega)
        refine ⟨r, ?_, ?_⟩
        · simp [hget, htx, hif, prevVectorIndex, hpos, Bind.bind, Except.bind]
          exact hr
        · rw [hpred] at hm
          cases r with
          | none =>
            intro j y hj1 hj hy
            by_cases hje : j = i.val
            · rw [hje, hx] at hy
              cases hy
              exact htx
            · exact hm j y hj1 (by omega) hy
          | some key =>
            obtain ⟨hk1, hk2, hk3, hk4⟩ := hm
            refine ⟨by omega, hk2, hk3, ?_⟩
            intro j y hkj hj hy
            by_cases hje : j = i.val
            · rw [hje, hx] at hy
              cases hy
              exact htx
            · exact hk4 j y hkj (by omega) hy
    · refine ⟨some i, ?_, ?_⟩
      · simp [hget, htx, Bind.bind, Except.bind, Pure.pure, Except.pure]
      · refine ⟨Int.le_refl _, h1, ⟨x, hx, htx⟩, ?_⟩
        intro j y hkj hj _
        omega

/-- The concrete `findnext(testf, A, start)` on a fully assigned `Vector`. -/
abbrev vectorFindnext (xs : List α) (hn : xs.length < 2 ^ 62) (test : α → Except Error Bool)
    {t : IntTy} (start : JInt t) : Except Error (Option I) :=
  findnext (fun _ => one) (fun _ => JInt.wrap .i64 xs.length) (fun _ j => indexConvert j)
    (fun j k => decide (j.val > k.val)) vectorGet test (forwardRank xs.length)
    (nextVectorIndex xs.length hn) xs start

/-- The concrete `findprev(testf, A, start)` on a fully assigned `Vector`. -/
abbrev vectorFindprev (xs : List α) (test : α → Except Error Bool) {t : IntTy}
    (start : JInt t) : Except Error (Option I) :=
  findprev (fun _ => one) (fun _ j => indexConvert j) (fun j k => decide (j.val < k.val))
    vectorGet test backwardRank prevVectorIndex xs start

theorem vectorFindnext_spec (test : α → Bool) (xs : List α) (hn : xs.length < 2 ^ 62)
    {t : IntTy} (i : JInt t) (h1 : 1 ≤ i.val) (hmax : i.val ≤ IntTy.i64.max) :
    ∃ r, vectorFindnext xs hn (fun a => .ok (test a)) i = .ok r ∧
      NextMatch test xs i.val (r.map Subtype.val) := by
  have hb : IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max :=
    ⟨by simp only [IntTy.min, IntTy.signed, IntTy.bits] at *; omega, hmax⟩
  have hL : (JInt.wrap .i64 (xs.length : Int)).val = xs.length :=
    collectorLengthFits xs.length (by omega)
  by_cases hg : (xs.length : Int) < i.val
  · refine ⟨none, ?_, ?_⟩
    · simp [findnext, searchIndexConvert i hb, hL, hg, Bind.bind, Except.bind, Pure.pure,
        Except.pure]
    · intro j y hj _ hy
      exact absurd hy (searchBeyond xs j (by omega) y)
  · obtain ⟨r, hr, hm⟩ := findnextLoop_spec test xs hn _ ⟨i.val, hb⟩ rfl h1
      (by show i.val ≤ _; omega)
    refine ⟨r, ?_, hm⟩
    simp [findnext, searchIndexConvert i hb, hL, hg, Bind.bind, Except.bind]
    exact hr

theorem vectorFindprev_spec (test : α → Bool) (xs : List α) (hn : xs.length < 2 ^ 62)
    {t : IntTy} (i : JInt t) (hlen : i.val ≤ xs.length) (hmin : IntTy.i64.min ≤ i.val) :
    ∃ r, vectorFindprev xs (fun a => .ok (test a)) i = .ok r ∧
      PrevMatch test xs i.val (r.map Subtype.val) := by
  have hb : IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max :=
    ⟨hmin, by simp only [IntTy.max, IntTy.signed, IntTy.bits]; omega⟩
  by_cases hg : i.val < 1
  · refine ⟨none, ?_, ?_⟩
    · simp [findprev, searchIndexConvert i hb, show one.val = 1 from rfl, hg, Bind.bind,
        Except.bind, Pure.pure, Except.pure]
    · intro j y hj1 hj _
      omega
  · obtain ⟨r, hr, hm⟩ := findprevLoop_spec test xs _ ⟨i.val, hb⟩ rfl
      (by show 1 ≤ i.val; omega) hlen
    refine ⟨r, ?_, hm⟩
    simp [findprev, searchIndexConvert i hb, show one.val = 1 from rfl, hg, Bind.bind,
      Except.bind]
    exact hr

theorem findfirstArray_pure [DecidableEq K] (k : K) (firstKey lastKey : A → K)
    (oftype : K → K → Except Error K) (greater : K → K → Bool) (get : A → K → Except Error α)
    (rank : K → Nat) (nextind : (i : K) → Except Error { j : K // rank j < rank i })
    (test : α → Except Error Bool) (a : A) :
    findfirstArray (fun _ => pure k) firstKey lastKey oftype greater get rank nextind test a =
      findnext firstKey lastKey oftype greater get test rank nextind a k := rfl

theorem findlastArray_pure [DecidableEq K] (last : A → K) (firstKey : A → K)
    (oftype : K → K → Except Error K) (less : K → K → Bool) (get : A → K → Except Error α)
    (rank : K → Nat) (prevind : (i : K) → Except Error { j : K // rank j < rank i })
    (test : α → Except Error Bool) (a : A) :
    findlastArray (fun a => pure (last a)) firstKey oftype less get rank prevind test a =
      findprev firstKey oftype less get test rank prevind a (last a) := rfl

theorem findfirstArrayBool_pure [DecidableEq K] (k : K) (firstKey lastKey : A → K)
    (oftype : K → K → Except Error K) (greater : K → K → Bool) (get : A → K → Except Error Bool)
    (rank : K → Nat) (nextind : (i : K) → Except Error { j : K // rank j < rank i }) (a : A) :
    findfirstArrayBool (fun _ => pure k) firstKey lastKey oftype greater get rank nextind a =
      findnext firstKey lastKey oftype greater get (fun x => pure (id x)) rank nextind a k := rfl

theorem findlastArrayBool_pure [DecidableEq K] (last : A → K) (firstKey : A → K)
    (oftype : K → K → Except Error K) (less : K → K → Bool) (get : A → K → Except Error Bool)
    (rank : K → Nat) (prevind : (i : K) → Except Error { j : K // rank j < rank i }) (a : A) :
    findlastArrayBool (fun a => pure (last a)) firstKey oftype less get rank prevind a =
      findprev firstKey oftype less get (fun x => pure (id x)) rank prevind a (last a) := rfl

/-- `findnext(f, A, i)`, `findprev(f, A, i)` and the `findfirst(f, A)`/`findlast(f, A)` methods
that search from the first/last key (array.jl:2470, 2526, 2666, 2719; docstrings at 2441-2469,
2483-2517, 2629-2665, 2679-2710): on a fully assigned vector, a forward search from any start
`≥ 1` returns the least matching position at or after it, a backward search from any start
`≤ length(A)` returns the greatest matching position at or before it, and both return `nothing`
exactly when there is none. Starts outside these ranges are `arrayops-findnext-start-below`. -/
def VectorStartSearchSpec : Prop :=
  ∀ (α : Type) (test : α → Bool) (xs : List α) (hn : xs.length < 2 ^ 62),
    (∀ (t : IntTy) (i : JInt t), 1 ≤ i.val → i.val ≤ IntTy.i64.max →
      ∃ r, vectorFindnext xs hn (fun a => .ok (test a)) i = .ok r ∧
        NextMatch test xs i.val (r.map Subtype.val)) ∧
    (∀ (t : IntTy) (i : JInt t), i.val ≤ xs.length → IntTy.i64.min ≤ i.val →
      ∃ r, vectorFindprev xs (fun a => .ok (test a)) i = .ok r ∧
        PrevMatch test xs i.val (r.map Subtype.val)) ∧
    (∃ r, findfirstArray (fun _ => pure one) (fun _ => one) (fun _ => JInt.wrap .i64 xs.length)
        (fun _ j => indexConvert j) (fun j k => decide (j.val > k.val)) vectorGet
        (forwardRank xs.length) (nextVectorIndex xs.length hn) (fun a => .ok (test a)) xs = .ok r ∧
      NextMatch test xs 1 (r.map Subtype.val)) ∧
    (∃ r, findlastArray (fun a => pure (JInt.wrap .i64 a.length)) (fun _ => one)
        (fun _ j => indexConvert j) (fun j k => decide (j.val < k.val)) vectorGet backwardRank
        prevVectorIndex (fun a => .ok (test a)) xs = .ok r ∧
      PrevMatch test xs xs.length (r.map Subtype.val))

/-- `findnext(A, i)`, `findprev(A, i)`, `findfirst(A::AbstractArray)` and
`findlast(A::AbstractArray)` (array.jl:2399, 2439, 2586, 2627; docstrings at 2367-2398,
2401-2435, 2552-2585, 2588-2623): on a fully assigned `Bool` vector the same searches find
`true` elements. -/
def BoolVectorStartSearchSpec : Prop :=
  ∀ (xs : List Bool) (hn : xs.length < 2 ^ 62),
    let next := findnextBool (m := Except Error) (fun _ => one) (fun _ => JInt.wrap .i64 xs.length)
      (fun _ (j : I) => indexConvert j) (fun j k => decide (j.val > k.val)) vectorGet
      (forwardRank xs.length) (nextVectorIndex xs.length hn)
    let prev := findprevBool (m := Except Error) (fun _ => one) (fun _ (j : I) => indexConvert j)
      (fun j k => decide (j.val < k.val)) vectorGet backwardRank prevVectorIndex
    (∀ i : I, 1 ≤ i.val → ∃ r, next xs i = .ok r ∧
      NextMatch id xs i.val (r.map Subtype.val)) ∧
    (∀ i : I, i.val ≤ xs.length → ∃ r, prev xs i = .ok r ∧
      PrevMatch id xs i.val (r.map Subtype.val)) ∧
    (∃ r, findfirstArrayBool (fun _ => pure one) (fun _ => one)
        (fun _ => JInt.wrap .i64 xs.length) (fun _ j => indexConvert j)
        (fun j k => decide (j.val > k.val)) vectorGet (forwardRank xs.length)
        (nextVectorIndex xs.length hn) xs = .ok r ∧
      NextMatch id xs 1 (r.map Subtype.val)) ∧
    (∃ r, findlastArrayBool (fun a => pure (JInt.wrap .i64 a.length)) (fun _ => one)
        (fun _ j => indexConvert j) (fun j k => decide (j.val < k.val)) vectorGet backwardRank
        prevVectorIndex xs = .ok r ∧
      PrevMatch id xs xs.length (r.map Subtype.val))

/-! ## Searches for a target value in integer ranges -/

/-- `findfirst(==(x), r)` on an integer unit range `r = lo:hi` (array.jl:2535): the
source `findfirstUnitRange` with `Int` keys starting at one, endpoints and target
of one BitInteger type `t`, and Julia's wrapping subtraction and exact `Int`
conversion. -/
def unitRangeFind (t : IntTy) (x : JInt t) (r : JInt t × JInt t) : Except Error (Option I) :=
  findfirstUnitRange (m := Except Error) Prod.fst Prod.snd Subtype.val Subtype.val
    (fun _ => .ok one) (· - ·) (fun _ d => indexConvert d) (· + ·) x r

/-- `findfirst(==(x), r)` on an integer `StepRange` `r = (start, step, stop)` with a
positive step and normalized stop (array.jl:2541): the source `findfirstStepRange`
with Julia's wrapping subtraction, truncated `%` and `÷`, and exact `Int` keys. -/
def stepRangeFind (t : IntTy) (x : JInt t) (r : JInt t × JInt t × JInt t) :
    Except Error (Option I) :=
  findfirstStepRange (m := Except Error)
    (fun r => if 0 < r.2.1.val then decide (r.2.2.val < r.1.val)
      else decide (r.1.val < r.2.2.val))
    (fun r => if r.1.val ≤ r.2.2.val then r.1 else r.2.2)
    (fun r => if r.1.val ≤ r.2.2.val then r.2.2 else r.1)
    (fun r => r.1) (fun r => r.2.1)
    (fun a b => decide (a.val ≤ b.val)) (fun a b => decide (a.val ≤ b.val)) (· - ·)
    (fun a b => .ok (JInt.wrap t (a.val.tmod b.val)))
    (fun a => a.val == 0)
    (fun a b => .ok (JInt.wrap t (a.val.tdiv b.val)))
    (fun a => a + JInt.wrap t 1) indexConvert x r

/-- `findfirst(iszero, r)` (array.jl:2549) on a unit range `lo:hi` that contains zero
returns a valid key `k ≥ 1` whose element `lo + (k - 1)` is zero. -/
def RangeZeroSearch : Prop :=
  ∀ (t : IntTy) (lo hi : JInt t), lo.val ≤ 0 → 0 ≤ hi.val →
    ∃ k : I, findfirstZeroRange (m := Except Error) Prod.fst (fun _ => JInt.wrap t 0)
        (unitRangeFind t) (lo, hi) = .ok (some k) ∧
      1 ≤ k.val ∧ lo.val + (k.val - 1) = 0

/-- `findfirst(isone, r)` (array.jl:2550) on a unit range `lo:hi` that contains one
returns a valid key `k ≥ 1` whose element `lo + (k - 1)` is one. -/
def RangeOneSearch : Prop :=
  ∀ (t : IntTy) (lo hi : JInt t), lo.val ≤ 1 → 1 ≤ hi.val →
    ∃ k : I, findfirstOneRange (m := Except Error) Prod.fst (fun _ => JInt.wrap t 1)
        (unitRangeFind t) (lo, hi) = .ok (some k) ∧
      1 ≤ k.val ∧ lo.val + (k.val - 1) = 1

/-- `findlast(==(x), r)` (array.jl:2723) on a unit range `lo:hi` containing `x`
returns a valid key `k ≥ 1` whose element `lo + (k - 1)` is `x`. -/
def RangeLastUnitSearch : Prop :=
  ∀ (t : IntTy) (lo hi x : JInt t), lo.val ≤ x.val → x.val ≤ hi.val →
    ∃ k : I, findlastRange2723 (m := Except Error) (unitRangeFind t) x (lo, hi) = .ok (some k) ∧
      1 ≤ k.val ∧ lo.val + (k.val - 1) = x.val

/-- `findlast(==(x), r)` (array.jl:2728) on a positive-step range `lo:step:hi` with
normalized stop that contains `x = lo + n*step` returns a valid key `k ≥ 1` whose
element `lo + (k - 1)*step` is `x`. -/
def RangeLastStepSearch : Prop :=
  ∀ (t : IntTy) (lo step hi x : JInt t) (n : Nat), 0 < step.val → lo.val ≤ hi.val →
    (hi.val - lo.val) % step.val = 0 → x.val = lo.val + n * step.val → x.val ≤ hi.val →
    ∃ k : I, findlastRange2728 (m := Except Error) (stepRangeFind t) x (lo, step, hi) =
        .ok (some k) ∧
      1 ≤ k.val ∧ lo.val + (k.val - 1) * step.val = x.val

/-- The documented search contract (array.jl:2483-2517 and 2679-2710 docstrings) for
the zero, one and `findlast` range methods: a target inside an integer range is
found at a valid key holding it. -/
def RangeTargetSearchSpec : Prop :=
  RangeZeroSearch ∧ RangeOneSearch ∧ RangeLastUnitSearch ∧ RangeLastStepSearch

theorem rangeZeroSearch_refuted : ¬ RangeZeroSearch := by
  intro h
  obtain ⟨k, hk, hp, _⟩ := h .i8 (JInt.wrap .i8 (-128)) (JInt.wrap .i8 127) (by decide)
    (by decide)
  have actual : findfirstZeroRange (m := Except Error) Prod.fst (fun _ => JInt.wrap .i8 0)
      (unitRangeFind .i8) (JInt.wrap .i8 (-128), JInt.wrap .i8 127) =
        .ok (some (JInt.wrap .i64 (-127))) := by rfl
  rw [actual] at hk
  cases hk
  exact (by decide : ¬ (1 ≤ (JInt.wrap .i64 (-127)).val)) hp

theorem rangeOneSearch_refuted : ¬ RangeOneSearch := by
  intro h
  obtain ⟨k, hk, hp, _⟩ := h .i8 (JInt.wrap .i8 (-128)) (JInt.wrap .i8 127) (by decide)
    (by decide)
  have actual : findfirstOneRange (m := Except Error) Prod.fst (fun _ => JInt.wrap .i8 1)
      (unitRangeFind .i8) (JInt.wrap .i8 (-128), JInt.wrap .i8 127) =
        .ok (some (JInt.wrap .i64 (-126))) := by rfl
  rw [actual] at hk
  cases hk
  exact (by decide : ¬ (1 ≤ (JInt.wrap .i64 (-126)).val)) hp

theorem rangeLastUnitSearch_refuted : ¬ RangeLastUnitSearch := by
  intro h
  obtain ⟨k, hk, hp, _⟩ := h .i8 (JInt.wrap .i8 (-128)) (JInt.wrap .i8 127) (JInt.wrap .i8 0)
    (by decide) (by decide)
  have actual : findlastRange2723 (m := Except Error) (unitRangeFind .i8) (JInt.wrap .i8 0)
      (JInt.wrap .i8 (-128), JInt.wrap .i8 127) = .ok (some (JInt.wrap .i64 (-127))) := by rfl
  rw [actual] at hk
  cases hk
  exact (by decide : ¬ (1 ≤ (JInt.wrap .i64 (-127)).val)) hp

theorem rangeLastStepSearch_refuted : ¬ RangeLastStepSearch := by
  intro h
  obtain ⟨k, hk, hp, _⟩ := h .i8 (JInt.wrap .i8 (-100)) (JInt.wrap .i8 2) (JInt.wrap .i8 120)
    (JInt.wrap .i8 100) 100 (by decide) (by decide) (by decide) (by decide) (by decide)
  have actual : findlastRange2728 (m := Except Error) (stepRangeFind .i8) (JInt.wrap .i8 100)
      (JInt.wrap .i8 (-100), JInt.wrap .i8 2, JInt.wrap .i8 120) =
        .ok (some (JInt.wrap .i64 (-27))) := by rfl
  rw [actual] at hk
  cases hk
  exact (by decide : ¬ (1 ≤ (JInt.wrap .i64 (-27)).val)) hp

/-- Every part of the range target-search contract fails. -/
theorem rangeTargetSearch_each_refuted :
    ¬ RangeZeroSearch ∧ ¬ RangeOneSearch ∧ ¬ RangeLastUnitSearch ∧ ¬ RangeLastStepSearch :=
  ⟨rangeZeroSearch_refuted, rangeOneSearch_refuted, rangeLastUnitSearch_refuted,
    rangeLastStepSearch_refuted⟩

def ArrayMembershipAgreement : Prop :=
  ∀ (xs ys : List (JuliaLean.Promotion.Fl JuliaLean.Promotion.double)) (initial : MutableMemory I),
    let operation := findallIn2961 (m := MutationM I)
      (fun _ => false) id (fun values => pure values)
      (mutableAllocate (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout) 0 zero)
      (fun values => (values.zipIdx 1).map (fun p => (JInt.wrap .i64 (p.2 : Int), p.1)))
      (fun x values => pure (values.any (JuliaLean.C.jlFpiseq x)))
      (mutablePush (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout)) ys xs
    let result := operation.run initial
    result.1.map (fun handle => result.2.contents handle) =
      .ok (((xs.zipIdx 1).filter (fun p => ys.any (JuliaLean.C.jlEqFloat p.1))).map
        (fun p => some (JInt.wrap .i64 (p.2 : Int))))

def forwardSortedFloat (xs : List (JuliaLean.Promotion.Fl JuliaLean.Promotion.double)) : Bool :=
  (xs.zip xs.tail).all (fun p =>
    !JuliaLean.base.float.isless_IEEEFloat (T := JuliaLean.base.float.FTy.f64) p.2 p.1)

/-- Keys `1:length(v)` of a vector. -/
def vectorKeys (xs : List α) : List I :=
  (List.range xs.length).map (fun (i : Nat) => JInt.wrap .i64 ((i : Int) + 1))

/-- `isless` on `Float64` (float.jl:629-635) as a pure comparison callee. -/
def floatLess (a b : JuliaLean.Promotion.Fl JuliaLean.Promotion.double) : MutationM I Bool :=
  pure (JuliaLean.base.float.isless_IEEEFloat (T := JuliaLean.base.float.FTy.f64) a b)

/-- The sorted merge `_sortedfindin` (array.jl:2910) over `Float64` vectors, with
vector keys and checked element reads. -/
def sortedFindinFloat (v w : List (JuliaLean.Promotion.Fl JuliaLean.Promotion.double)) :
    MutationM I Nat :=
  sortedfindin vectorKeys vectorKeys (mutableAllocate (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout) 0 zero)
    (fun v k => liftM (vectorGet v k)) (fun w k => liftM (vectorGet w k))
    floatLess floatLess (mutablePush (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout)) v w

/-- `_findin(x, Set(b))` (array.jl:2905, 2898) over `Float64` vectors, with set
membership by `isequal` (set.jl). -/
def setFindinFloat (xs ys : List (JuliaLean.Promotion.Fl JuliaLean.Promotion.double)) :
    MutationM I Nat :=
  findin (fun values => pure values)
    (findinSet (mutableAllocate (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout) 0 zero)
      (fun values => (values.zipIdx 1).map (fun p => (JInt.wrap .i64 (p.2 : Int), p.1)))
      (fun x values => pure (values.any (JuliaLean.C.jlFpiseq x)))
      (mutablePush (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout))) xs ys

/-- `findall(in(b), x)` for `Float64` arrays `x` and `b` (array.jl:2952), through
the sorted merge `_sortedfindin` (array.jl:2910) when both are sorted and `_findin`
otherwise, returns the indices of the elements of `x` that are members of `b` under
`==` (findall docstring, array.jl:2733-2783), including signed zeros and NaNs. -/
def SortedMembershipAgreement : Prop :=
  ∀ (xs ys : List (JuliaLean.Promotion.Fl JuliaLean.Promotion.double)) (initial : MutableMemory I),
    let operation := findallInSorted (m := MutationM I) forwardSortedFloat forwardSortedFloat
      sortedFindinFloat setFindinFloat ys xs
    let result := operation.run initial
    result.1.map (fun handle => result.2.contents handle) =
      .ok (((xs.zipIdx 1).filter (fun p => ys.any (JuliaLean.C.jlEqFloat p.1))).map
        (fun p => some (JInt.wrap .i64 (p.2 : Int))))

/-- The unsorted branch: `-0.0` is not found in the unsorted `[NaN, 0.0]`. -/
theorem sortedFindinFloat_signedZero :
    sortedFindinFloat [JuliaLean.Promotion.Fl.zero true] [JuliaLean.Promotion.Fl.zero false] =
      (mutableAllocate (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout) 0 zero >>= fun out => pure out) := by
  have hless : floatLess (JuliaLean.Promotion.Fl.zero true)
      (JuliaLean.Promotion.Fl.zero false) = pure true := rfl
  have hkeys : ∀ x : JuliaLean.Promotion.Fl JuliaLean.Promotion.double,
      vectorKeys [x] = [one] := fun _ => rfl
  have hget : ∀ x : JuliaLean.Promotion.Fl JuliaLean.Promotion.double,
      (liftM (vectorGet [x] one) : MutationM I _) = pure x := fun _ => rfl
  unfold sortedFindinFloat sortedfindin
  simp only [hkeys, hget, pure_bind]
  simp (config := { singlePass := true }) only [sortedfindin.loop.eq_1]
  simp only [hless, pure_bind, ite_true]

/-- The sorted branch also refutes the contract: `findall(in([0.0]), [-0.0])` is empty. -/
theorem sortedMembershipAgreement_sorted_refuted : ¬ SortedMembershipAgreement := by
  intro h
  have bad := h [JuliaLean.Promotion.Fl.zero true] [JuliaLean.Promotion.Fl.zero false] ⟨[], []⟩
  have hsorted : findallInSorted (m := MutationM I) forwardSortedFloat forwardSortedFloat
      sortedFindinFloat setFindinFloat [JuliaLean.Promotion.Fl.zero false]
      [JuliaLean.Promotion.Fl.zero true] = (mutableAllocate (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout) 0 zero >>= fun out => pure out) := by
    simp only [findallInSorted]
    have hc : (forwardSortedFloat [JuliaLean.Promotion.Fl.zero true] &&
        forwardSortedFloat [JuliaLean.Promotion.Fl.zero false]) = true := rfl
    rw [if_pos hc]
    exact sortedFindinFloat_signedZero
  dsimp only at bad
  rw [hsorted] at bad
  change (Except.ok [] : Except Error (List (Option I))) = .ok [some one] at bad
  cases bad

theorem findlast_none_iff (test : α → Bool) (pairs : List (K × α)) :
    findlast (m := Id) List.reverse test pairs = none ↔ ∀ p ∈ pairs, test p.2 = false := by
  change findfirst (m := Id) test pairs.reverse = none ↔ _
  have h := findfirst_none_iff test pairs.reverse
  simpa only [List.mem_reverse] using h

/-- Boolean searches return a true element at the first or last matching position,
    and return nothing exactly when every element is false. -/
def BooleanSearchPositionsSpec : Prop :=
  ∀ (K : Type) [DecidableEq K] (firstKey' lastKey' : List (K × Bool) → Id K)
    (firstKey lastKey : List (K × Bool) → K) (oftype : K → K → Id K)
    (greater less : K → K → Bool) (get : List (K × Bool) → K → Id Bool)
    (rank : K → Nat) (next prev : (i : K) → Id { j : K // rank j < rank i })
    (pairs : List (K × Bool)),
    let ff := findfirstBool (m := Id) (fun _ => false) id firstKey' firstKey lastKey oftype
      greater get rank next
    let fl := findlastBool (m := Id) (fun _ => false) id List.reverse lastKey' firstKey oftype
      less get rank prev
    (ff pairs = none ↔ ∀ p ∈ pairs, p.2 = false) ∧
    (∀ key, ff pairs = some key → firstMatch id pairs key) ∧
    (fl pairs = none ↔ ∀ p ∈ pairs, p.2 = false) ∧
    (∀ key, fl pairs = some key → lastMatch id pairs key)

theorem booleanSearchPositionsSpec : BooleanSearchPositionsSpec := by
  intro K _ firstKey' lastKey' firstKey lastKey oftype greater less get rank next prev pairs
  exact ⟨findfirst_none_iff id pairs, findfirst_firstMatch id pairs,
    findlast_none_iff id pairs, findlast_lastMatch id pairs⟩

def LastSearchComplete : Prop :=
  ∀ (α K : Type) (test : α → Bool) (pairs : List (K × α)),
    findlast (m := Id) List.reverse test pairs = none ↔ ∀ p ∈ pairs, test p.2 = false

theorem lastSearchComplete : LastSearchComplete := fun _ _ => findlast_none_iff
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section FindallFamily


/-- `findall(f, A)` (array.jl:2784-2787; docstring at array.jl:2733-2783) over the ordered
`pairs(A)`: it collects the generator `(first(p) for p in pairs(A) if f(last(p)))`, so the result
is exactly the keys whose values pass `f`, in iteration order, whichever of the two `collect`
calls the element-type test selects. `collect` is required to return the values of the
generator it is given. -/
def FindallPredicateSpec : Prop :=
  ∀ (K α T : Type) (ps : List (K × α)) (test : α → Bool) (bottom : List K → Bool)
    (keyType : List (K × α) → T) (collectTyped : T → List K → Except Error (List K))
    (collect : List K → Except Error (List K)),
    (∀ t g, collectTyped t g = .ok g) → (∀ g, collect g = .ok g) →
    findallPredicate (m := Except Error) id (fun keep key ps => (ps.filter keep).map key)
      Prod.snd Prod.fst test bottom keyType collectTyped collect ps =
      .ok ((ps.filter (fun p => test p.2)).map Prod.fst)

theorem findallPredicateSpec : FindallPredicateSpec := by
  intro K α T ps test bottom keyType collectTyped collect hct hc
  by_cases hb : bottom ((ps.filter (fun p => test p.2)).map Prod.fst) = true <;>
    simp [findallPredicate, hb, hct, hc]

/-- `findall(A)` (array.jl:2833-2835; docstring at array.jl:2795-2832): the keys of `pairs(A)`
whose value is `true`, in iteration order. -/
def FindallGenericSpec : Prop :=
  ∀ (K : Type) (ps : List (K × Bool)) (collect : List K → Except Error (List K)),
    (∀ g, collect g = .ok g) →
    findallGeneric (m := Except Error) id (fun keep key ps => (ps.filter keep).map key)
      Prod.snd Prod.fst collect ps = .ok ((ps.filter (fun p => p.2)).map Prod.fst)

theorem findallGenericSpec : FindallGenericSpec := by
  intro K ps collect hc
  simp only [findallGeneric, hc, id]

/-- The counting write loop of `findall(A::AbstractArray{Bool})`: after the pairs `ps`, the slots
of `b` hold the keys already written followed by the keys of the `true` entries of `ps`. -/
theorem boolKeysLoop_run {K : Type} (b : Nat) (f : K × Bool → I → VectorM K (ForInStep I))
    (hf : ∀ (k : K) (v : Bool) (r : I) (heap : VectorHeap K) (slots : List (Option K)),
      heap[b]? = some slots → 1 ≤ r.val → (v = true → r.val ≤ (slots.length : Int)) →
      (f (k, v) r).run heap = if v = true
        then .ok (.yield (r + one), heap.set b (slots.set (r.val - 1).toNat (some k)))
        else .ok (.yield r, heap)) :
    ∀ (ps : List (K × Bool)) (pre : List K) (r : I) (heap : VectorHeap K),
      heap[b]? = some (pre.map some ++ List.replicate (ps.filter (fun p => p.2)).length none) →
      r.val = pre.length + 1 → (pre.length : Int) + ps.length < 2 ^ 62 →
      ∃ r' heap', (forIn ps r f).run heap = .ok (r', heap') ∧
        heap'[b]? = some ((pre ++ (ps.filter (fun p => p.2)).map Prod.fst).map some) ∧
        heap'.length = heap.length ∧ ∀ j, j ≠ b → heap'[j]? = heap[j]? := by
  intro ps
  induction ps with
  | nil =>
    intro pre r heap hb _ _
    exact ⟨r, heap, rfl, by simpa using hb, rfl, fun _ _ => rfl⟩
  | cons x ps ih =>
    intro pre r heap hb hr hlen
    obtain ⟨k, v⟩ := x
    have hrb := ival_bounds r
    simp only [List.length_cons] at hlen
    cases v
    · have hstep := hf k false r heap _ hb (by omega) (by simp)
      simp only [Bool.false_eq_true, ite_false] at hstep
      have hb' : heap[b]? = some (pre.map some ++
          List.replicate (ps.filter (fun p => p.2)).length none) := by
        simpa using hb
      obtain ⟨r', heap', hrun, hb2, hl2, ho2⟩ := ih pre r heap hb' hr (by omega)
      refine ⟨r', heap', ?_, by simpa using hb2, hl2, ho2⟩
      simp only [List.forIn_cons, vector_bind_run, hstep]
      exact hrun
    · have hcount : ((k, true) :: ps).filter (fun p => p.2) = (k, true) ::
          ps.filter (fun p => p.2) := by simp
      rw [hcount, List.length_cons] at hb
      have hbl : b < heap.length := (List.getElem?_eq_some_iff.mp hb).choose
      have hslen : (r.val : Int) ≤ ((pre.map some ++ List.replicate
          ((ps.filter (fun p => p.2)).length + 1) none : List (Option K)).length : Int) := by
        simp; omega
      have hstep := hf k true r heap _ hb (by omega) (fun _ => hslen)
      simp only [ite_true] at hstep
      have hidx : (r.val - 1).toNat = pre.length := by omega
      rw [hidx, set_prefix_slot pre k _ (by omega), Nat.add_sub_cancel] at hstep
      have hr1 : (r + one).val = (pre ++ [k]).length + 1 := by
        rw [ival_add_one _ (by omega), hr]; simp
      obtain ⟨r', heap', hrun, hb2, hl2, ho2⟩ := ih (pre ++ [k]) (r + one)
        (heap.set b ((pre ++ [k]).map some ++
          List.replicate (ps.filter (fun p => p.2)).length none))
        (by simp [List.getElem?_set_self hbl]) hr1 (by simp; omega)
      refine ⟨r', heap', ?_, by rw [hb2, hcount]; simp, by rw [hl2, List.length_set],
        fun j hj => by rw [ho2 j hj, List.getElem?_set_ne (Ne.symm hj)]⟩
      simp only [List.forIn_cons, vector_bind_run, hstep]
      exact hrun

/-- `findall(A::AbstractArray{Bool})` (array.jl:2838-2849; docstring at array.jl:2795-2832) on
the shared heap: a fresh vector, allocated with the `count(A)` slots it needs, receives exactly
the keys of the `true` entries of `pairs(A)` in iteration order; every existing array is untouched.
`count` is required to return the number of `true` values. -/
def FindallBoolSpec : Prop :=
  ∀ (K A : Type) (a : A) (ps : List (K × Bool)) (count : A → VectorM K I)
    (pairs : A → VectorM K (List (K × Bool))) (heap : VectorHeap K),
    (∀ h, (count a).run h = .ok (JInt.wrap .i64 ((ps.filter (fun p => p.2)).length : Int), h)) →
    (∀ h, (pairs a).run h = .ok (ps, h)) → (ps.length : Int) < 2 ^ 62 →
    ∃ heap', (findallBoolArray count (fun n => heapAllocate n.val.toNat) pairs
        (fun b k i => heapSet b k i) a).run heap = .ok (heap.length, heap') ∧
      heap'[heap.length]? = some ((ps.filter (fun p => p.2)).map (fun p => some p.1)) ∧
      ∀ j, j < heap.length → heap'[j]? = heap[j]?

theorem findallBoolSpec : FindallBoolSpec := by
  intro K A a ps count pairs heap hcount hpairs hsmall
  have hcl : (ps.filter (fun p => p.2)).length ≤ ps.length := List.length_filter_le _ _
  have hcv : (JInt.wrap .i64 ((ps.filter (fun p => p.2)).length : Int)).val.toNat =
      (ps.filter (fun p => p.2)).length := by
    rw [ival_wrap _ (by omega)]; omega
  have hb : (heap ++ [List.replicate (ps.filter (fun p => p.2)).length none])[heap.length]? =
      some (([] : List K).map some ++ List.replicate (ps.filter (fun p => p.2)).length none) := by
    simp
  simp only [findallBoolArray, vector_bind_run, hcount, heapAllocate_run, hpairs, hcv]
  obtain ⟨r', heap', hrun, hb2, _, ho2⟩ := boolKeysLoop_run heap.length
    (fun (x : K × Bool) (r : I) => if x.2 = true then (do
        heapSet heap.length x.1 r
        pure (ForInStep.yield (r + one))) else pure (ForInStep.yield r))
    (fun k v r h slots hs h1 h2 => by
      cases v
      · rfl
      · simp only [ite_true, vector_bind_run, heapSet_run h heap.length slots hs r h1 (h2 rfl) k,
          vector_pure_run])
    ps [] one _ hb (by simp [ival_one]) (by simp; omega)
  refine ⟨heap', ?_, by rw [hb2, List.nil_append, List.map_map]; rfl, fun j hj => ?_⟩
  · simp only [hrun, vector_pure_run]
  · rw [ho2 j (Nat.ne_of_lt hj), List.getElem?_append_left hj]

def emptyBitFindallOps {m : Type → Type} [Monad m] {Mask B : Type} (defaultB : m B) :
    @BitFindallOps m m (fun _ => Unit) Unit Mask B where
  asArray _ := none
  findAll _ _ _ _ _ _ := defaultB
  count _ _ := pure zero
  allocate _ := defaultB
  set _ _ _ := pure ()
  allindices _ b _ := pure b
  trailingZeros _ := zero
  lift x := x

def dummyKeyCollectOps {m : Type → Type} [Monad m] {Pairs Pair K B : Type} (defaultB : m B) :
    GeneratorCollectOps m (KeyGenerator m Pairs Pair K) K Unit Unit Unit Unit B where
  size _ := ()
  defaultEltype _ := ()
  unknown _ := true
  emptyVector _ := defaultB
  grow b _ := pure b
  shape _ _ := pure ()
  iterate _ := pure none
  typeof _ := ()
  arrayForInner _ _ _ := defaultB
  isTypeSubtype _ := false
  typeType := ()
  anyType := ()
  isAbstractArray _ := true
  isConcrete _ := true
  ndims _ := one
  abstractArrayType _ _ _ := ()
  collectWithFirst b _ _ _ := pure b
  typeassert b _ := pure b

def FindallArrayPredicateSpec : Prop :=
  ∀ (K α A Mask : Type) (a : A) (ps : List (K × α)) (test : α → Bool)
    (broadcast : (α → Bool) → A → VectorM K Mask) (mask : Mask) (count : Mask → VectorM K I)
    (pairs : Mask → VectorM K (List (K × Bool))) (heap : VectorHeap K),
    (∀ h, (broadcast test a).run h = .ok (mask, h)) →
    (∀ h, (pairs mask).run h = .ok (ps.map (fun p => (p.1, test p.2)), h)) →
    (∀ h, (count mask).run h =
      .ok (JInt.wrap .i64 ((ps.filter (fun p => test p.2)).length : Int), h)) →
    (ps.length : Int) < 2 ^ 62 →
    ∃ heap', (findallArrayPredicate (m := VectorM K)
        (fun (_ : α → VectorM K Bool) a => broadcast test a)
        (fun _ => none) (fun n => heapAllocate n.val.toNat) (fun b _ _ => pure b)
        (emptyBitFindallOps (pure 0))
        (fun _ => true) count (fun n => heapAllocate n.val.toNat) pairs
        (fun b k i => heapSet b k i)
        pairs (fun p : K × Bool => pure p.2) Prod.fst (dummyKeyCollectOps (pure 0))
        (fun x => pure (test x)) a).run heap =
        .ok (heap.length, heap') ∧
      heap'[heap.length]? = some ((ps.filter (fun p => test p.2)).map (fun p => some p.1)) ∧
      ∀ j, j < heap.length → heap'[j]? = heap[j]?

theorem findallArrayPredicateSpec : FindallArrayPredicateSpec := by
  intro K α A Mask a ps test broadcast mask count pairs heap hbc hpairs hcount hsmall
  have hmap : (ps.map (fun p => (p.1, test p.2))).filter (fun p => p.2) =
      (ps.filter (fun p => test p.2)).map (fun p => (p.1, test p.2)) := by
    rw [List.filter_map]; rfl
  obtain ⟨heap', hrun, hslots, hold⟩ := findallBoolSpec K Mask mask
    (ps.map (fun p => (p.1, test p.2))) count pairs heap
    (fun h => by rw [hcount, hmap, List.length_map]) hpairs (by simpa using hsmall)
  refine ⟨heap', ?_, by rw [hslots, hmap, List.map_map]; rfl, hold⟩
  unfold findallArrayPredicate
  rw [vector_bind_run, hbc]
  unfold findallBoolArray at hrun
  simpa only [findallDispatch, emptyBitFindallOps, findallBoolArrayDispatch,
    instForInVectorMBoolPairs, ForIn.forIn, bind_assoc, ↓reduceIte] using hrun
end FindallFamily
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section VectorSets

variable {α : Type} [DecidableEq α]

theorem setM_id_pure {β : Type} (x : β) : (pure x : Id β) = x := rfl
end VectorSets
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! ## Combined search contracts -/

/-- On a vector, `findfirst(q, v)` / `findlast(q, v)` / `findnext(q, v, s)` / `findprev(q, v, s)`
are the first / last / first-at-or-after / last-at-or-before matching key, and `findall(q, v)`
lists every matching key in order (array.jl:2399-2470, 2526-2723, 2784-2791). -/
def FindPureSpec : Prop := VectorStartSearchSpec ∧ FindallPredicateSpec ∧ FindallArrayPredicateSpec

def FindBoolSpec : Prop := BoolVectorStartSearchSpec ∧ FindallGenericSpec ∧ FindallBoolSpec
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round4
open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- A search returns a matching key, with no earlier matching element. -/
def firstMatch (test : α → Bool) (pairs : List (K × α)) (key : K) : Prop :=
  ∃ before value after, pairs = before ++ (key, value) :: after ∧
    test value = true ∧ ∀ p ∈ before, test p.2 = false

/-- A backward search returns a matching key, with no later matching element. -/
def lastMatch (test : α → Bool) (pairs : List (K × α)) (key : K) : Prop :=
  ∃ before value after, pairs = before ++ (key, value) :: after ∧
    test value = true ∧ ∀ p ∈ after, test p.2 = false

/-- Independent specification: the first matching one-based index at least `start`. -/
def firstAtLeast (test : α → Bool) (xs : List α) (start : Int) : Option Int :=
  ((xs.zipIdx 1).find? (fun p => test p.1 && decide (start ≤ (p.2 : Int)))).map
    (fun p => (p.2 : Int))

/-- Independent specification: the last matching one-based index at most `start`. -/
def lastUpTo (test : α → Bool) (xs : List α) (start : Int) : Option Int :=
  ((xs.zipIdx 1).reverse.find? (fun p => test p.1 && decide ((p.2 : Int) ≤ start))).map
    (fun p => (p.2 : Int))

def FreshArray {B α : Type} (shape : B → List I) (slots : B → List (Option α))
    (dims : List I) (a : B) : Prop :=
  shape a = dims ∧ slots a = List.replicate ((dims.map (fun d : I => d.val)).prod.toNat) none

def filledShape (old : I → Option α) (dims : List Nat) (x : α) : I → Option α :=
  fun j => if 1 ≤ j.val ∧ j.val ≤ (dims.prod : Int) then some x else old j

def constantArrayResult (value : Z → Int) (t : T) (dims : List Z)
    (allocation : Except Error (T × List Nat) × (I → Option α))
    (element : Except Error α) : Except Error (T × List Nat) × (I → Option α) :=
  match allocation with
  | (.error e, fresh) => (.error e, fresh)
  | (.ok _, fresh) =>
    match element with
    | .error e => (.error e, fresh)
    | .ok x =>
      let shape := dims.map (fun d => (value d).toNat)
      (.ok (t, shape), filledShape fresh shape x)

/-- Independent specification of a forward search from `start` in a one-based vector:
`some k` is the least position at or after `start` whose element passes `test`, and `none`
means that no element at or after `start` passes. -/
def NextMatch (test : α → Bool) (xs : List α) (start : Int) : Option Int → Prop
  | some k => start ≤ k ∧ 1 ≤ k ∧ (∃ x, xs[(k - 1).toNat]? = some x ∧ test x = true) ∧
      ∀ j x, start ≤ j → 1 ≤ j → j < k → xs[(j - 1).toNat]? = some x → test x = false
  | none => ∀ j x, start ≤ j → 1 ≤ j → xs[(j - 1).toNat]? = some x → test x = false

/-- Independent specification of a backward search from `start` in a one-based vector:
`some k` is the greatest position at or before `start` whose element passes `test`, and
`none` means that no element at or before `start` passes. -/
def PrevMatch (test : α → Bool) (xs : List α) (start : Int) : Option Int → Prop
  | some k => k ≤ start ∧ 1 ≤ k ∧ (∃ x, xs[(k - 1).toNat]? = some x ∧ test x = true) ∧
      ∀ j x, k < j → j ≤ start → xs[(j - 1).toNat]? = some x → test x = false
  | none => ∀ j x, 1 ≤ j → j ≤ start → xs[(j - 1).toNat]? = some x → test x = false

/-- The concrete `findnext(testf, A, start)` on a fully assigned `Vector`. -/
abbrev vectorFindnext (xs : List α) (hn : xs.length < 2 ^ 62) (test : α → Except Error Bool)
    {t : IntTy} (start : JInt t) : Except Error (Option I) :=
  findnext (fun _ => one) (fun _ => JInt.wrap .i64 xs.length) (fun _ j => indexConvert j)
    (fun j k => decide (j.val > k.val)) vectorGet test (forwardRank xs.length)
    (nextVectorIndex xs.length hn) xs start

/-- `findfirst(==(x), r)` on an integer unit range `r = lo:hi` (array.jl:2535): the
source `findfirstUnitRange` with `Int` keys starting at one, endpoints and target
of one BitInteger type `t`, and Julia's wrapping subtraction and exact `Int`
conversion. -/
def unitRangeFind (t : IntTy) (x : JInt t) (r : JInt t × JInt t) : Except Error (Option I) :=
  findfirstUnitRange (m := Except Error) Prod.fst Prod.snd Subtype.val Subtype.val
    (fun _ => .ok one) (· - ·) (fun _ d => indexConvert d) (· + ·) x r

/-- `findfirst(==(x), r)` on an integer `StepRange` `r = (start, step, stop)` with a
positive step and normalized stop (array.jl:2541): the source `findfirstStepRange`
with Julia's wrapping subtraction, truncated `%` and `÷`, and exact `Int` keys. -/
def stepRangeFind (t : IntTy) (x : JInt t) (r : JInt t × JInt t × JInt t) :
    Except Error (Option I) :=
  findfirstStepRange (m := Except Error)
    (fun r => if 0 < r.2.1.val then decide (r.2.2.val < r.1.val)
      else decide (r.1.val < r.2.2.val))
    (fun r => if r.1.val ≤ r.2.2.val then r.1 else r.2.2)
    (fun r => if r.1.val ≤ r.2.2.val then r.2.2 else r.1)
    (fun r => r.1) (fun r => r.2.1)
    (fun a b => decide (a.val ≤ b.val)) (fun a b => decide (a.val ≤ b.val)) (· - ·)
    (fun a b => .ok (JInt.wrap t (a.val.tmod b.val)))
    (fun a => a.val == 0)
    (fun a b => .ok (JInt.wrap t (a.val.tdiv b.val)))
    (fun a => a + JInt.wrap t 1) indexConvert x r

/-- `issorted(v, Sort.Forward)` for a `Float64` vector: no element is `isless` than
its predecessor. -/
def forwardSortedFloat (xs : List (JuliaLean.Promotion.Fl JuliaLean.Promotion.double)) : Bool :=
  (xs.zip xs.tail).all (fun p =>
    !JuliaLean.base.float.isless_IEEEFloat (T := JuliaLean.base.float.FTy.f64) p.2 p.1)

/-- Keys `1:length(v)` of a vector. -/
def vectorKeys (xs : List α) : List I :=
  (List.range xs.length).map (fun (i : Nat) => JInt.wrap .i64 ((i : Int) + 1))

/-- `isless` on `Float64` (float.jl:629-635) as a pure comparison callee. -/
def floatLess (a b : JuliaLean.Promotion.Fl JuliaLean.Promotion.double) : MutationM I Bool :=
  pure (JuliaLean.base.float.isless_IEEEFloat (T := JuliaLean.base.float.FTy.f64) a b)

/-- The sorted merge `_sortedfindin` (array.jl:2910) over `Float64` vectors, with
vector keys and checked element reads. -/
def sortedFindinFloat (v w : List (JuliaLean.Promotion.Fl JuliaLean.Promotion.double)) :
    MutationM I Nat :=
  sortedfindin vectorKeys vectorKeys (mutableAllocate (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout) 0 zero)
    (fun v k => liftM (vectorGet v k)) (fun w k => liftM (vectorGet w k))
    floatLess floatLess (mutablePush (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout)) v w
end round4
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round4
open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section VectorSets

variable {α : Type} [DecidableEq α]

/-- The first occurrence in `xs` of each value of `keep`, in order. -/
def firstIn (keep : List α) : List α → List α
  | [] => []
  | x :: xs => if x ∈ keep then x :: firstIn (keep.erase x) xs else firstIn keep xs

/-- What remains of `keep` after `firstIn keep xs` has taken its values. -/
def firstInRest (keep : List α) : List α → List α
  | [] => keep
  | x :: xs => if x ∈ keep then firstInRest (keep.erase x) xs else firstInRest keep xs
end VectorSets
end round4
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round4
open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section NewStatements

/-- The value of the last pair stored at one-based position `p + 1`, if any. -/
def lastStored (pairs : List (I × α)) (p : Nat) : Option α :=
  (pairs.reverse.find? (fun q => decide (q.1.val = (p : Int) + 1))).map Prod.snd
end NewStatements
end round4
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round4
open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def IntegerValue.subBit (ops : BigIntegerOps) {t : IntTy} (x : IntegerValue) (v : JInt t) :
    IntegerValue :=
  match x with
  | .bit _ y => .bit _ (JuliaLean.base.int.binop JuliaLean.base.int.sub y v)
  | .bool b => .bit t (JuliaLean.base.int.sub (JInt.wrap t (if b then 1 else 0)) v)
  | .big w => .big (ops.sub w v.val)

/-- `findfirst(==(x), r::AbstractUnitRange{<:Integer})` (array.jl:2535) for a target of any
`Integer` type on a unit range `lo:hi` of BitInteger width `t`: `first(keys(r)) = 1`, the promoted
`p.x - first(r)`, `oftype(i1, ·)` (`Int(·)`) and `Int` `+`. -/
def unitRangeFindAny (ops : BigIntegerOps) (t : IntTy) (x : IntegerValue) (r : JInt t × JInt t) :
    Except Error (Option I) :=
  findfirstUnitRange (m := Except Error) Prod.fst Prod.snd Subtype.val IntegerValue.val
    (fun _ => .ok one) (fun x v => x.subBit ops v) (fun _ d => d.toInt ops) (· + ·) x r

/-- The elements of the step range `start:step:stop` with nonzero `step`, in order. -/
def stepRangeElements (start step stop : Int) : List Int :=
  if step > 0 then
    if stop < start then [] else steppedRangeValues start step ((stop - start) / step + 1).toNat
  else
    if start < stop then [] else steppedRangeValues start step ((start - stop) / (-step) + 1).toNat

/-- The documented search contract of `findfirst(iszero, r)`, `findfirst(isone, r)` (array.jl:2549,
2550, through `findfirst(==(zero(first(r))), r)`), `findlast(==(x), r)` (array.jl:2723, 2728,
through `findfirst`) and the unit- and step-range `findfirst(==(x), r)` methods (array.jl:2535,
2541) they reach (`findfirst`/`findlast` docstrings at array.jl:2483-2517, 2679-2710: the first or
last key of a matching element, or `nothing`): on a unit range `lo:hi` of any BitInteger element
type, a target of any `Integer` type inside the range is found at the key `k` with
`lo + (k - 1) = x`, and a target outside it gives `nothing`; on a step range of any BitInteger type
with a nonzero step of either sign and a normalized stop, a value of the range (zero, one, or any
`x`) is found at the key `k` whose element `start + (k - 1)*step` is that value, and a value not in
the range gives `nothing`. -/
def RangeTargetSearchSpec : Prop :=
  (∀ (ops : BigIntegerOps), ops.Lawful → ∀ (t : IntTy) (lo hi : JInt t) (x : IntegerValue),
    lo.val ≤ hi.val + 1 →
    let found := findlastRange2723 (m := Except Error) (unitRangeFindAny ops t) x (lo, hi)
    (lo.val ≤ x.val → x.val ≤ hi.val →
      ∃ k : I, found = .ok (some k) ∧ lo.val + (k.val - 1) = x.val) ∧
    (¬ (lo.val ≤ x.val ∧ x.val ≤ hi.val) → found = .ok none)) ∧
  (∀ (t : IntTy) (lo hi : JInt t), lo.val ≤ hi.val + 1 →
    let zeroFound := findfirstZeroRange (m := Except Error) Prod.fst (fun _ => JInt.wrap t 0)
      (unitRangeFind t) (lo, hi)
    let oneFound := findfirstOneRange (m := Except Error) Prod.fst (fun _ => JInt.wrap t 1)
      (unitRangeFind t) (lo, hi)
    ((lo.val ≤ 0 ∧ 0 ≤ hi.val) → ∃ k : I, zeroFound = .ok (some k) ∧ lo.val + (k.val - 1) = 0) ∧
    (¬ (lo.val ≤ 0 ∧ 0 ≤ hi.val) → zeroFound = .ok none) ∧
    ((lo.val ≤ 1 ∧ 1 ≤ hi.val) → ∃ k : I, oneFound = .ok (some k) ∧ lo.val + (k.val - 1) = 1) ∧
    (¬ (lo.val ≤ 1 ∧ 1 ≤ hi.val) → oneFound = .ok none)) ∧
  (∀ (t : IntTy) (start step stop x : JInt t), step.val ≠ 0 →
    (stop.val - start.val) % step.val = 0 →
    let values := stepRangeElements start.val step.val stop.val
    let r := (start, step, stop)
    let lastFound := findlastRange2728 (m := Except Error) (stepRangeFind t) x r
    let zeroFound := findfirstZeroRange (m := Except Error) (fun r => r.1) (fun _ => JInt.wrap t 0)
      (stepRangeFind t) r
    let oneFound := findfirstOneRange (m := Except Error) (fun r => r.1) (fun _ => JInt.wrap t 1)
      (stepRangeFind t) r
    (x.val ∈ values → ∃ k : I, lastFound = .ok (some k) ∧
      start.val + (k.val - 1) * step.val = x.val) ∧
    (x.val ∉ values → lastFound = .ok none) ∧
    ((0 : Int) ∈ values → ∃ k : I, zeroFound = .ok (some k) ∧
      start.val + (k.val - 1) * step.val = 0) ∧
    ((0 : Int) ∉ values → zeroFound = .ok none) ∧
    ((1 : Int) ∈ values → ∃ k : I, oneFound = .ok (some k) ∧
      start.val + (k.val - 1) * step.val = 1) ∧
    ((1 : Int) ∉ values → oneFound = .ok none))

def slotVectorGet {α : Type} (xs : List (Option α)) (i : I) : Except Error α :=
  match vectorGet xs i with
  | .ok (some x) => .ok x
  | .ok none => .error .undefinedReference
  | .error e => .error e

/-- `findnext(testf, A, start)` (array.jl:2470) on a `Vector` with slots `xs` for a start of any
`Integer` type: `keys(A) = 1:length(A)`, `oftype(first(keys(A)), start)` (`Int(start)`) and
`nextind(A, i) = i + 1`. -/
abbrev integerFindnext {α : Type} (ops : BigIntegerOps) (xs : List (Option α))
    (hn : xs.length < 2 ^ 62) (test : α → Except Error Bool) (start : IntegerValue) :
    Except Error (Option I) :=
  findnext (fun _ => one) (fun _ => JInt.wrap .i64 xs.length) (fun _ j => j.toInt ops)
    (fun j k => decide (j.val > k.val)) slotVectorGet test (forwardRank xs.length)
    (nextVectorIndex xs.length hn) xs start

/-- `findprev(testf, A, start)` (array.jl:2666) on a `Vector` with slots `xs`. -/
abbrev integerFindprev {α : Type} (ops : BigIntegerOps) (xs : List (Option α))
    (test : α → Except Error Bool) (start : IntegerValue) : Except Error (Option I) :=
  findprev (fun _ => one) (fun _ j => j.toInt ops) (fun j k => decide (j.val < k.val))
    slotVectorGet test backwardRank prevVectorIndex xs start

/-- The documented forward search over the slots `xs` from `start`: the first position at or
after `start` whose element passes `test`, or `nothing`; a search that reaches an unassigned slot
first raises `UndefRefError` (reading `A[i]`). -/
def slotSearchNext {α : Type} (test : α → Bool) (xs : List (Option α)) (start : Int) :
    Except Error (Option Int) :=
  match ((xs.zipIdx 1).filter (fun p => decide (start ≤ (p.2 : Int)))).find?
      (fun p => match p.1 with
        | none => true
        | some x => test x) with
  | none => .ok none
  | some (none, _) => .error .undefinedReference
  | some (some _, k) => .ok (some (k : Int))

/-- The documented backward search over the slots `xs` from `start`. -/
def slotSearchPrev {α : Type} (test : α → Bool) (xs : List (Option α)) (start : Int) :
    Except Error (Option Int) :=
  match ((xs.zipIdx 1).filter (fun p => decide ((p.2 : Int) ≤ start))).reverse.find?
      (fun p => match p.1 with
        | none => true
        | some x => test x) with
  | none => .ok none
  | some (none, _) => .error .undefinedReference
  | some (some _, k) => .ok (some (k : Int))

/-- `findnext(f, A, i)` and `findprev(f, A, i)` (array.jl:2470, 2666; docstrings at
array.jl:2441-2469 and 2629-2665: "Find the next index after or including `i` of an element of
`A` for which `predicate` returns `true`, or `nothing` if not found"; "Find the previous index
before or including `i` ...") on a vector whose slots may be unassigned, for a start of every
`Integer` type and every value: a start with no equal `Int` (the key type) raises `InexactError`;
otherwise the forward search returns the least matching position at or after `i` and the backward
search the greatest one at or before `i` (for every `i`, including starts before the first index
and after the last), `nothing` when there is none, and `UndefRefError` when an unassigned slot is
read before a match. -/
def FindAllStarts : Prop :=
  ∀ (α : Type) (ops : BigIntegerOps), ops.Lawful →
  ∀ (test : α → Bool) (xs : List (Option α)) (hn : xs.length < 2 ^ 62) (i : IntegerValue),
    let f := fun a => (Except.ok (test a) : Except Error Bool)
    (¬ i.fits → integerFindnext ops xs hn f i = .error .inexact ∧
      integerFindprev ops xs f i = .error .inexact) ∧
    (i.fits → (integerFindnext ops xs hn f i).map (Option.map Subtype.val) =
      slotSearchNext test xs i.val) ∧
    (i.fits → (integerFindprev ops xs f i).map (Option.map Subtype.val) =
      slotSearchPrev test xs i.val)

def FindfirstCartesian : Prop :=
  ∀ (dims : List Nat) (values : List I → Bool),
    (∀ n ∈ dims, n < 2 ^ 63) →
    findfirstArray (m := Except Error)
      (fun shape => .ok (shape.map (fun _ => one)))
      (fun shape => shape.map (fun _ => one))
      (fun shape => shape.map (fun (n : Nat) => JInt.wrap .i64 (n : Int)))
      (fun _ i => .ok i) cartesianGreater
      (fun shape key => if key ∈ cartesianKeys shape then .ok (values key) else .error .bounds)
      (cartesianRank dims) (cartesianNext dims)
      (fun value => .ok value) dims =
        .ok ((cartesianKeys dims).find? values)

/-- The one-based positions, as `Int` keys, of the elements of `xs` that are `==` to an element
of `ys`. -/
def eqPositions {K : Type} (eq : K → K → Bool) (xs ys : List K) : List (Option I) :=
  ((xs.zipIdx 1).filter (fun p => ys.any (eq p.1))).map (fun p => some (JInt.wrap .i64 (p.2 : Int)))

/-- `issorted(v, Sort.Forward)` for a vector: no element is `isless` than its predecessor. -/
def forwardSortedBy {K : Type} (less : K → K → Bool) (xs : List K) : Bool :=
  (xs.zip xs.tail).all (fun p => !less p.2 p.1)

/-- The sorted merge `_sortedfindin` (array.jl:2910) over vectors, with the element type's
`isless`, vector keys and checked element reads. -/
def sortedFindinBy {K : Type} (less : K → K → Bool) (v w : List K) : MutationM I Nat :=
  sortedfindin vectorKeys vectorKeys (mutableAllocate (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout) 0 zero)
    (fun v k => liftM (vectorGet v k)) (fun w k => liftM (vectorGet w k))
    (fun a b => pure (less a b)) (fun a b => pure (less a b)) (mutablePush (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout)) v w

/-- `findall(in(b), x::Tuple)` (array.jl:2962) and `findall(in(b), x::AbstractArray)`
(array.jl:2961), through `_findin` with set.jl's `Set` (docstrings of `findall(f, A)` at
array.jl:2733-2783 and of `in`): for every element type, the result holds the positions of the
elements of `x` that are `==` to an element of `b`, in order. -/
def TupleMembershipAgreement : Prop :=
  ∀ (K : Type) (eq : K → K → Bool) (ops : JuliaLean.base.set.DictRuntime K),
    JuliaLean.Proofs.base.set.DictRuntimeLawful ops →
  ∀ (xs ys : List K) (initial : MutableMemory I),
    let emptySet := JuliaLean.base.set.setConstructorEmpty (K := K) 0
    let pairs := fun (values : List K) =>
      (values.zipIdx 1).map (fun p => (JInt.wrap .i64 (p.2 : Int), p.1))
    let contains := fun (x : K) s => setResultLift (JuliaLean.base.set.setIn ops x s)
    let tuple := (findallIn2962 (m := MutationM I) (fun _ => false) (fun _ => emptySet)
      (setOfValues ops) (mutableAllocate (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout) 0 zero) pairs contains (mutablePush (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout)) ys xs).run initial
    let array := (findallIn2961 (m := MutationM I) (fun _ => false) (fun _ => emptySet)
      (setOfValues ops) (mutableAllocate (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout) 0 zero) pairs contains (mutablePush (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout)) ys xs).run initial
    tuple.1.map (fun handle => tuple.2.contents handle) = .ok (eqPositions eq xs ys) ∧
    array.1.map (fun handle => array.2.contents handle) = .ok (eqPositions eq xs ys)

def ArrayMembershipAgreement : Prop :=
  ∀ (K : Type) (eq : K → K → Bool) (ops : JuliaLean.base.set.DictRuntime K),
    JuliaLean.Proofs.base.set.DictRuntimeLawful ops →
  ∀ (xs ys : List K) (initial : MutableMemory I),
    let emptySet := JuliaLean.base.set.setConstructorEmpty (K := K) 0
    let pairs := fun (values : List K) =>
      (values.zipIdx 1).map (fun p => (JInt.wrap .i64 (p.2 : Int), p.1))
    let contains := fun (x : K) s => setResultLift (JuliaLean.base.set.setIn ops x s)
    let result := (findallIn2961 (m := MutationM I) (fun _ => false) (fun _ => emptySet)
      (setOfValues ops) (mutableAllocate (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout) 0 zero) pairs contains (mutablePush (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout)) ys xs).run initial
    result.1.map (fun handle => result.2.contents handle) = .ok (eqPositions eq xs ys)

def SortedMembershipAgreement : Prop :=
  ∀ (K : Type) (eq less : K → K → Bool) (ops : JuliaLean.base.set.DictRuntime K),
    JuliaLean.Proofs.base.set.DictRuntimeLawful ops →
  ∀ (xs ys : List K) (initial : MutableMemory I),
    let result := (findallInSorted (m := MutationM I) (forwardSortedBy less) (forwardSortedBy less)
      (sortedFindinBy less) (setFindin ops) ys xs).run initial
    result.1.map (fun handle => result.2.contents handle) = .ok (eqPositions eq xs ys)

def dictGetOrInsert {K : Type} (ops : JuliaLean.base.set.DictRuntime K) (value : K) (index : I) :
    StateT (JuliaLean.base.dict.DictState K I) (MutationM (Option I)) Unit := do
  let (_, d) ← StateT.lift (setResultLift (JuliaLean.base.dict.getBang ops.hash ops.equal
    ops.tablesz ⟨some, fun v => .ok v⟩ (← get) value (fun h => .ok (index, h))))
  set d

/-- dict.jl's `get(d, key, nothing)` on the `Dict` of the state. -/
def dictLookup {K : Type} (ops : JuliaLean.base.set.DictRuntime K) (value : K) (default : Option I) :
    StateT (JuliaLean.base.dict.DictState K I) (MutationM (Option I)) (Option I) := do
  match ← StateT.lift (setResultLift (JuliaLean.base.dict.get ops.hash ops.equal (← get) value
      default)) with
  | .inl v => pure (some v)
  | .inr d => pure d

/-- `indexin(a, b::AbstractArray)` (array.jl:2887; docstring at array.jl:2856-2886: "Return an
array containing the first index in `b` for each value in `a` that is a member of `b`. The output
array contains `nothing` wherever `a` is not a member of `b`."), with dict.jl's `Dict` (`get!`
keeping the first index, `get` with default `nothing`) for every element type: the result holds,
for each value of `a`, the first index of `b` whose element is `==` to it (`in`'s membership), or
`nothing`. -/
def IndexinMembershipAgreement : Prop :=
  ∀ (K : Type) (eq : K → K → Bool) (ops : JuliaLean.base.set.DictRuntime K),
    JuliaLean.Proofs.base.set.DictRuntimeLawful ops →
  ∀ (xs ys : List K) (initial : MutableMemory (Option I)),
    let operation := indexin
      (m := StateT (JuliaLean.base.dict.DictState K I) (MutationM (Option I)))
      (fun values => pure ((List.range values.length).map (fun (i : Nat) => JInt.wrap .i64 ((i : Int) + 1))))
      (pure ()) List.zip
      (fun _ value key => dictGetOrInsert ops value key)
      (fun _ value default => dictLookup ops value default)
      (fun _ => ())
      (listLookupCollectOps (pure 0) (typedLiteral (fun n => liftM (mutableAllocate (α := Option I) (some ⟨8, false, true⟩) 0 n))
        (fun a value i => liftM (mutableTypedSet (α := Option I) a value i)) true)) xs ys
    let result := (operation.run (JuliaLean.base.dict.dictEmpty K I)).run initial
    result.1.map (fun (handle, _) => result.2.contents handle) =
      .ok (xs.map (fun x => some (((ys.zipIdx 1).find? (fun p => eq x p.1)).map
        (fun p => JInt.wrap .i64 (p.2 : Int)))))

def VectorStartSearchSpec : Prop :=
  ∀ (α : Type) (ops : BigIntegerOps), ops.Lawful →
  ∀ (test : α → Bool) (xs : List (Option α)) (hn : xs.length < 2 ^ 62),
    let f := fun a => (Except.ok (test a) : Except Error Bool)
    (∀ i : IntegerValue, 1 ≤ i.val → i.val ≤ xs.length →
      (integerFindnext ops xs hn f i).map (Option.map Subtype.val) = slotSearchNext test xs i.val ∧
      (integerFindprev ops xs f i).map (Option.map Subtype.val) = slotSearchPrev test xs i.val) ∧
    (findfirstArray (fun _ => pure one) (fun _ => one) (fun _ => JInt.wrap .i64 xs.length)
      (fun _ j => (IntegerValue.ofInt j).toInt ops) (fun j k => decide (j.val > k.val))
      slotVectorGet (forwardRank xs.length) (nextVectorIndex xs.length hn) f xs).map
      (Option.map Subtype.val) = slotSearchNext test xs 1 ∧
    (findlastArray (fun a => pure (JInt.wrap .i64 a.length)) (fun _ => one)
      (fun _ j => (IntegerValue.ofInt j).toInt ops) (fun j k => decide (j.val < k.val))
      slotVectorGet backwardRank prevVectorIndex f xs).map
      (Option.map Subtype.val) = slotSearchPrev test xs xs.length ∧
    (∀ (dims : List Nat) (values : List I → Bool), (∀ n ∈ dims, 0 < n ∧ n < 2 ^ 63) →
      findfirstArray (m := Except Error)
        (fun shape => .ok (shape.map (fun _ => one)))
        (fun shape => shape.map (fun _ => one))
        (fun shape => shape.map (fun (n : Nat) => JInt.wrap .i64 (n : Int)))
        (fun _ i => .ok i) cartesianGreater
        (fun shape key => if key ∈ cartesianKeys shape then .ok (values key) else .error .bounds)
        (cartesianRank dims) (cartesianNext dims)
        (fun value => .ok value) dims =
          .ok ((cartesianKeys dims).find? values))

def BoolVectorStartSearchSpec : Prop :=
  ∀ (ops : BigIntegerOps), ops.Lawful →
  ∀ (xs : List Bool) (hs : (xs.map some).length < 2 ^ 62),
    let slots := xs.map some
    let next := findnextBool (m := Except Error) (fun _ => one)
      (fun _ => JInt.wrap .i64 slots.length) (fun _ (j : I) => (IntegerValue.ofInt j).toInt ops)
      (fun j k => decide (j.val > k.val)) slotVectorGet (forwardRank slots.length)
      (nextVectorIndex slots.length hs)
    let prev := findprevBool (m := Except Error) (fun _ => one)
      (fun _ (j : I) => (IntegerValue.ofInt j).toInt ops) (fun j k => decide (j.val < k.val))
      slotVectorGet backwardRank prevVectorIndex
    (∀ i : IntegerValue, i.fits →
      (integerFindnext ops slots hs (fun b => .ok (id b)) i).map (Option.map Subtype.val) =
        slotSearchNext id slots i.val ∧
      (integerFindprev ops slots (fun b => .ok (id b)) i).map (Option.map Subtype.val) =
        slotSearchPrev id slots i.val) ∧
    (∀ i : I, 1 ≤ i.val →
      (next slots i).map (Option.map Subtype.val) = slotSearchNext id slots i.val) ∧
    (∀ i : I, i.val ≤ xs.length →
      (prev slots i).map (Option.map Subtype.val) = slotSearchPrev id slots i.val) ∧
    (findfirstArrayBool (fun _ => pure one) (fun _ => one) (fun _ => JInt.wrap .i64 slots.length)
      (fun _ j => (IntegerValue.ofInt j).toInt ops) (fun j k => decide (j.val > k.val))
      slotVectorGet (forwardRank slots.length) (nextVectorIndex slots.length hs) slots).map
      (Option.map Subtype.val) = slotSearchNext id slots 1 ∧
    (findlastArrayBool (fun a => pure (JInt.wrap .i64 a.length)) (fun _ => one)
      (fun _ j => (IntegerValue.ofInt j).toInt ops) (fun j k => decide (j.val < k.val))
      slotVectorGet backwardRank prevVectorIndex slots).map
      (Option.map Subtype.val) = slotSearchPrev id slots xs.length ∧
    (∀ (dims : List Nat) (values : List I → Bool), (∀ n ∈ dims, 0 < n ∧ n < 2 ^ 63) →
      findfirstArrayBool (m := Except Error)
        (fun shape => .ok (shape.map (fun _ => one)))
        (fun shape => shape.map (fun _ => one))
        (fun shape => shape.map (fun (n : Nat) => JInt.wrap .i64 (n : Int)))
        (fun _ i => .ok i) cartesianGreater
        (fun shape key => if key ∈ cartesianKeys shape then .ok (values key) else .error .bounds)
        (cartesianRank dims) (cartesianNext dims)
        dims = .ok ((cartesianKeys dims).find? values))

def OneToFirstSearchSpec : Prop :=
  (∀ (ops : BigIntegerOps), ops.Lawful → ∀ (s : IntTy) (x : IntegerValue) (stop : JInt s),
    0 ≤ stop.val →
    findfirstOneTo (m := Except Error) IntegerValue.val Subtype.val
      (fun x => x.convertTo ops s) x stop =
      .ok (if 1 ≤ x.val ∧ x.val ≤ stop.val then some (JInt.wrap s x.val) else none)) ∧
  (∀ (s : IntTy) (r : JuliaLean.base.range.OneTo (JInt s)),
    findfirstZeroOneTo (K := JInt s) r = none) ∧
  (∀ (s : IntTy) (r : JuliaLean.base.range.OneTo (JInt s)), 0 ≤ r.stop.val →
    findfirstOneOneTo (m := Except Error) (fun r : JuliaLean.base.range.OneTo (JInt s) =>
        decide (r.stop.val = 0))
      (fun _ => pure (JInt.wrap s 1)) r =
      .ok (if 1 ≤ r.stop.val then some (JInt.wrap s 1) else none))

def matchingPairKeys {K α : Type} (test : α → Bool) (ps : List (K × α)) : List K :=
  (ps.filter (fun p => test p.2)).map Prod.fst

/-- `findall(f, A)` (array.jl:2784; docstring at array.jl:2733-2783: "Return a vector `I` of the
indices or keys of `A` where `f(A[I])` returns `true`. If there are no such elements of `A`,
return an empty array. Indices or keys are of the same type as those returned by `keys(A)` and
`pairs(A)`.") and `findall(A)` (array.jl:2833; docstring at array.jl:2793-2832: "Return a vector
`I` of the `true` indices or keys of `A`") for a collection with pairs of any key type:
whichever `collect` method the generator's inferred element type selects (`collect(T, gen)`,
array.jl:684 to the unknown-size `_collect` of array.jl:688, or `collect(gen)`, array.jl:771 to
the widening `_collect` of array.jl:855, with the Julia type lattice `L` and inferred type `et`),
the result is a fresh valid vector holding the matching keys in the order of `pairs(A)`. -/
def FindallPredicateSpec : Prop :=
  ∀ (Tag K α : Type) (layout : Tag → MemoryLayoutMetadata) (L : TypeLattice Tag K) (et keyType : Tag) (bottom : Bool) (test : α → Bool)
    (ps : List (K × α)) (bools : List (K × Bool)) (s : MutableMemory K),
    let viaTyped := fun (t : Tag) (gen : List K) => do
      let h ← collectTyped (m := MutationM K) (fun _ => ())
        (fun _ itr _ => collectUnknown (mutableAllocate (layout t) 0 zero) (mutablePush (layout t)) itr) t gen
      pure (t, h)
    let viaUnknown := fun (gen : List K) => typedCollectUnknown layout L et gen
    (∃ r next, (findallPredicate (m := MutationM K) (fun _ => ps)
        (fun keep key ps => (ps.filter keep).map key) Prod.snd Prod.fst test
        (fun _ => bottom) (fun _ => keyType) viaTyped viaUnknown ()).run s = (.ok r, next) ∧
      next.validVector r.2 ∧ next.contents r.2 = (matchingPairKeys test ps).map some) ∧
    (∃ r next, (findallGeneric (m := MutationM K) (fun _ => bools)
        (fun keep key ps => (ps.filter keep).map key) Prod.snd Prod.fst viaUnknown ()).run s =
        (.ok r, next) ∧
      next.validVector r.2 ∧ next.contents r.2 = (matchingPairKeys id bools).map some)

def FindallBoolSpec : Prop :=
  ∀ (K α : Type) (layout : Option MemoryLayout) (test : α → Bool) (bools : List (K × Bool)) (ps : List (K × α))
    (s : MutableMemory K),
    let findallMask := fun (mask : List (K × Bool)) => findallBoolArray (m := MutationM K)
      (fun mask : List (K × Bool) => pure (JInt.wrap .i64 (mask.filter Prod.snd).length))
      (mutableAllocate layout 0) (fun mask => pure mask) (fun h i k => mutableSet h i k) mask
    (∃ r next, (findallMask bools).run s = (.ok r, next) ∧ next.validVector r ∧
      next.contents r = (matchingPairKeys id bools).map some) ∧
    (∃ r next, (findallArrayPredicate (m := MutationM K)
        (fun (_ : α → MutationM K Bool) (ps : List (K × α)) =>
          pure (ps.map (fun p => (p.1, test p.2))))
        (fun _ => none) (mutableAllocate layout 0)
        (fun b _ _ => pure b)
        (emptyBitFindallOps (pure 0))
        (fun _ => true)
        (fun mask : List (K × Bool) => pure (JInt.wrap .i64 (mask.filter Prod.snd).length))
        (mutableAllocate layout 0) id (fun h i k => mutableSet h i k)
        pure (fun p : K × Bool => pure p.2) Prod.fst (dummyKeyCollectOps (pure 0))
        (fun x => pure (test x)) ps).run s =
        (.ok r, next) ∧ next.validVector r ∧
      next.contents r = (matchingPairKeys test ps).map some)
def FindPureSpec : Prop := FindAllStarts ∧ VectorStartSearchSpec ∧ FindallPredicateSpec ∧
  FindallBoolSpec

def FindBoolSpec : Prop := BoolVectorStartSearchSpec ∧ FindallPredicateSpec ∧ FindallBoolSpec

/-- `findnext(iseven, [1, 2], 0)` reads `A[0]` and raises `BoundsError` instead of returning `2`. -/
theorem findAllStarts_refuted : ¬ FindAllStarts := by
  intro h
  have hn : ([some 1, some 2] : List (Option Int)).length < 2 ^ 62 := by decide
  have bad := (h Int exactIntegerOps exactIntegerOps_lawful (fun x => x % 2 == 0) [some 1, some 2] hn
    (.bit .i64 zero)).2.1 (by unfold IntegerValue.fits; decide)
  have actual : integerFindnext exactIntegerOps [some (1 : Int), some 2] hn
      (fun a => Except.ok (a % 2 == 0)) (.bit .i64 zero) = .error .bounds := by
    have htoInt : IntegerValue.toInt exactIntegerOps (.bit .i64 zero) = .ok zero := by decide
    simp only [integerFindnext, findnext, htoInt, bind, Except.bind]
    rw [findnext.loop.eq_1]
    rfl
  have expected : slotSearchNext (fun x : Int => x % 2 == 0) [some 1, some 2]
      (IntegerValue.bit .i64 zero).val = .ok (some 2) := by decide
  rw [actual, expected] at bad
  cases bad
end round4
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace JuliaLean.Proofs.base.array.round6dcollect2

open JuliaLean JuliaLean.base.array
open JuliaLean.base.range (OneTo UnitRange)
open JuliaLean.base.generator (IteratorSize IteratorEltype)
open JuliaLean.Proofs.base.array.round4 (IntegerValue BigIntegerOps)
section lifts
variable {E U α β : Type}

def liftArray (x : JuliaLean.base.abstractarray.Result β) : M E U α β :=
  match x with
  | .ok b => pure b
  | .error e => fail (.array e)
end lifts
end JuliaLean.Proofs.base.array.round6dcollect2
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace ChatGPTBatch1.ArrayRange
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.array.round4

attribute [local irreducible] JInt.wrap wrapInt

/-- Bounds checking a generic one-based integer interval. -/
theorem batch1_checkOneTo (ops : BigIntegerOps) (ho : ops.Lawful)
    (n : I) (i : IntegerValue) (hi : 1 ≤ i.val ∧ i.val ≤ n.val) :
    JuliaLean.base.abstractarray.checkindexReal
      (fun r => .ok (JuliaLean.base.range.first_OneTo r))
      (fun r => match JuliaLean.base.range.last_OrdinalRange (T := I) (A := I) r with
        | .ok v => .ok v
        | .error _ => .error (.julia .boundsError))
      (fun l i => .ok (IntegerValue.intLe ops l i))
      (fun i l => .ok (IntegerValue.leInt ops i l))
      (⟨n⟩ : JuliaLean.base.range.OneTo I) i = .ok true := by
  have hlast : JuliaLean.base.range.last_OrdinalRange (T := I) (A := I)
      (⟨n⟩ : JuliaLean.base.range.OneTo I) = .ok n :=
    JuliaLean.Proofs.base.range.last_oneTo _
  have hone : (JuliaLean.base.range.JOneunit.oneunit : I).val = 1 := by
    change (JInt.wrap .i64 1).val = 1
    exact ival_wrap _ (by omega)
  have hlo : IntegerValue.intLe ops (JuliaLean.base.range.JOneunit.oneunit : I) i = true := by
    rw [batch1_integer_intLe ops ho]
    exact decide_eq_true (by rw [hone]; exact hi.1)
  have hhi : IntegerValue.leInt ops i n = true := by
    rw [batch1_integer_leInt ops ho]
    exact decide_eq_true hi.2
  simp only [JuliaLean.base.abstractarray.checkindexReal,
    JuliaLean.base.range.first_OneTo, hlast, Bind.bind, Pure.pure, Except.bind,
    Except.pure, hlo, hhi, Bool.true_and]
end ChatGPTBatch1.ArrayRange
end
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2

open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

/-- Ordinary membership identifies the two Float64 zeros; Set membership does not. -/
theorem TuplesFindallInIsequal_refuted :
    ¬ JuliaLean.Proofs.base.array.TupleMembershipAgreement := by
  intro h
  have bad := h [JuliaLean.Promotion.Fl.zero true]
    [JuliaLean.Promotion.Fl.zero false] ⟨[], []⟩
  change (Except.ok [] : Except Error (List (Option I))) = .ok [some one] at bad
  cases bad

/-- The dictionary-backed lookup misses a value which is a member under ==. -/
theorem ArraycovIndexinIsequal_refuted :
    ¬ JuliaLean.Proofs.base.array.IndexinMembershipAgreement := by
  intro h
  have bad := h [JuliaLean.Promotion.Fl.zero true]
    [JuliaLean.Promotion.Fl.zero false] ⟨[], []⟩
  change (Except.ok [some none] : Except Error (List (Option (Option I)))) =
    .ok [some (some one)] at bad
  cases bad
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- An empty first dimension does not make the first Cartesian key exceed the last. -/
theorem MultidimFindfirstEmptyMatrix_refuted :
    ¬ JuliaLean.Proofs.base.array.FindfirstCartesian := by
  intro h
  have bad := h [0, 2] (fun _ => false) (by decide)
  have hkeys : cartesianKeys [0, 2] = [] := rfl
  have hcompare : cartesianGreater [one, one]
      [JInt.wrap .i64 0, JInt.wrap .i64 2] = false := by decide
  simp only [findfirstArray, findnext, List.map_cons, List.map_nil,
    hcompare, Bool.false_eq_true, ite_false, Bind.bind, Except.bind] at bad
  rw [findnext.loop] at bad
  simp only [hkeys, List.not_mem_nil, ite_false, Bind.bind, Except.bind,
    List.find?_nil] at bad
  cases bad
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- One-based range searches follow their explicit membership branches. -/
theorem ArraySearchOnetoFirst_proven :
    JuliaLean.Proofs.base.array.OneToFirstSearchSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x stop k
    change (if 1 ≤ x ∧ x ≤ stop then Except.ok (some x) else Except.ok none) =
      (Except.ok (some k) : Except Error (Option Int)) ↔ k = x ∧ 1 ≤ k ∧ k ≤ stop
    by_cases h : 1 ≤ x ∧ x ≤ stop
    · rw [if_pos h]
      constructor
      · intro he
        have hk := Option.some.inj (Except.ok.inj he)
        subst k
        exact ⟨rfl, h⟩
      · rintro ⟨rfl, _, _⟩
        rfl
    · rw [if_neg h]
      constructor
      · intro he
        cases he
      · rintro ⟨rfl, h1, h2⟩
        exact (h ⟨h1, h2⟩).elim
  · intro x stop
    change (if 1 ≤ x ∧ x ≤ stop then Except.ok (some x) else Except.ok none) =
      (Except.ok none : Except Error (Option Int)) ↔ x < 1 ∨ stop < x
    by_cases h : 1 ≤ x ∧ x ≤ stop
    · rw [if_pos h]
      constructor
      · intro he
        cases he
      · intro he
        omega
    · rw [if_neg h]
      constructor
      · intro _
        omega
      · intro _
        rfl
  · intro stop
    rfl
  · intro stop k
    by_cases h : stop < 1
    · simp only [findfirstOneOneTo, h, decide_true, ite_true]
      constructor
      · intro he
        cases he
      · intro he
        omega
    · simp only [findfirstOneOneTo, h, decide_false, Bool.false_eq_true, ite_false,
        pure_bind]
      constructor
      · intro he
        have hk := Option.some.inj (Except.ok.inj he)
        exact ⟨hk.symm, by omega⟩
      · rintro ⟨rfl, _⟩
        rfl

/-- The loop invariants already proved in the destination file cover each vector entry point. -/
theorem ArrayopsFindInrange_proven :
    JuliaLean.Proofs.base.array.VectorStartSearchSpec := by
  intro α test xs hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t i h1 hmax
    exact vectorFindnext_spec test xs hn i h1 hmax
  · intro t i hlen hmin
    exact vectorFindprev_spec test xs hn i hlen hmin
  · obtain ⟨r, hr, hm⟩ := vectorFindnext_spec test xs hn one (by decide) searchOneMax
    refine ⟨r, ?_, ?_⟩
    · rw [findfirstArray_pure]
      exact hr
    · simpa only [searchOne] using hm
  · have hL : (JInt.wrap .i64 (xs.length : Int)).val = xs.length :=
      collectorLengthFits xs.length (by omega)
    have hmin : IntTy.i64.min ≤ (JInt.wrap .i64 (xs.length : Int)).val :=
      (JInt.wrap .i64 (xs.length : Int)).property.1
    obtain ⟨r, hr, hm⟩ := vectorFindprev_spec test xs hn (JInt.wrap .i64 (xs.length : Int))
      (by rw [hL]; exact Int.le_refl _) hmin
    refine ⟨r, ?_, ?_⟩
    · rw [findlastArray_pure]
      exact hr
    · simpa only [hL] using hm

/-- Boolean vector searches specialize the same predicate-search invariants to identity. -/
theorem ArraySearchBoolStart_proven :
    JuliaLean.Proofs.base.array.BoolVectorStartSearchSpec := by
  intro xs hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i h1
    exact vectorFindnext_spec id xs hn i h1 i.property.2
  · intro i hlen
    exact vectorFindprev_spec id xs hn i hlen i.property.1
  · obtain ⟨r, hr, hm⟩ := vectorFindnext_spec id xs hn one (by decide) searchOneMax
    refine ⟨r, ?_, ?_⟩
    · rw [findfirstArrayBool_pure]
      simpa only [vectorFindnext, Pure.pure, Except.pure] using hr
    · simpa only [searchOne] using hm
  · have hL : (JInt.wrap .i64 (xs.length : Int)).val = xs.length :=
      collectorLengthFits xs.length (by omega)
    have hmin : IntTy.i64.min ≤ (JInt.wrap .i64 (xs.length : Int)).val :=
      (JInt.wrap .i64 (xs.length : Int)).property.1
    obtain ⟨r, hr, hm⟩ := vectorFindprev_spec id xs hn (JInt.wrap .i64 (xs.length : Int))
      (by rw [hL]; exact Int.le_refl _) hmin
    refine ⟨r, ?_, ?_⟩
    · rw [findlastArrayBool_pure]
      simpa only [vectorFindprev, Pure.pure, Except.pure] using hr
    · simpa only [hL] using hm

/-- A 256-element Int8 range has a wrapped negative key for zero. -/
theorem ArrayRangeTargetSearchOverflow_refuted :
    ¬ JuliaLean.Proofs.base.array.RangeTargetSearchSpec := by
  intro h
  exact rangeZeroSearch_refuted h.1

/-- The generic array membership specialization distinguishes the two floating-point zeros. -/
theorem ArrayFindallInArrayIsequal_refuted :
    ¬ JuliaLean.Proofs.base.array.ArrayMembershipAgreement := by
  intro h
  have bad := h [JuliaLean.Promotion.Fl.zero true]
    [JuliaLean.Promotion.Fl.zero false] ⟨[], []⟩
  change (Except.ok [] : Except Error (List (Option I))) = .ok [some one] at bad
  cases bad

/-- The destination already proves the sorted-merge signed-zero counterexample. -/
theorem ArrayFindallInSortedIsless_refuted :
    ¬ JuliaLean.Proofs.base.array.SortedMembershipAgreement :=
  sortedMembershipAgreement_sorted_refuted

/-- The combined predicate-search contract includes the established enumeration contracts. -/
theorem MultidimcovArrayV2FindPure_proven :
    JuliaLean.Proofs.base.array.FindPureSpec :=
  ⟨ArrayopsFindInrange_proven, findallPredicateSpec, findallArrayPredicateSpec⟩

/-- The combined Boolean-search contract includes the established Boolean enumerations. -/
theorem MultidimcovArrayV2FindBool_proven :
    JuliaLean.Proofs.base.array.FindBoolSpec :=
  ⟨ArraySearchBoolStart_proven, findallGenericSpec, findallBoolSpec⟩
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section

/- Integer unsetting partials -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace JuliaLean.ChatGPT.Batch5.Group3
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array
open JuliaLean.src.genericmemory_c

/-- Boolean indices fail before the vector is accessed. -/
theorem unsetIntegerBool {α : Type} (runtime : DictLayout)
    (ops : round4.BigIntegerOps) (s : MutableMemory α) (a : Nat) (b : Bool) :
    ∃ message,
      (unsetindexInteger (fun i => round4.stateExceptLift (round4.arrayToIndex ops i))
        (fun a i => do mutableUnset runtime a i; pure a) a (.bool b)).run s =
        (.error (.argument message), s) := by
  refine ⟨"invalid index: " ++ toString b ++ " of type Bool",
    unsetIntegerConversionError runtime ops s a (.bool b) _ ?_⟩
  rfl
end JuliaLean.ChatGPT.Batch5.Group3
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section

/- Integer unsetting partials -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096


/- Allocation and collection partials -/

set_option maxHeartbeats 200000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch5.Group3
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

/-- Same-element-type conversion bypasses every allocation, axis, and conversion operation. -/
theorem allocationConvertIdentity {Tag α : Type} [DecidableEq Tag]
    (layout : Tag → Option MemoryLayout) (target : Tag)
    (check : List (Int × Nat) → List (Int × Nat) → VectorM α Bool)
    (convert : Option α → Except Error (Option α))
    (heap : VectorHeap α) (src : HeapArray Tag) (h : src.elementType = target) :
    (convertArray (fun a => a.elementType == target) id
      (heapArrayConstructor layout target check convert) pure src).run heap = .ok (src, heap) := by
  simp only [convertArray, h, beq_self_eq_true, ite_true, vector_pure_run, id_eq]

/-- The complete array-collection copy contract, conditional on its actual fresh allocation. -/
theorem allocationArrayCollectionAfterAllocation {Tag α Style Indices : Type}
    (layout : Tag → Option MemoryLayout)
    (destStyle srcStyle : HeapArray Tag → Style)
    (unaliased : Style → HeapArray Tag → Style → HeapArray Tag →
      VectorM α (HeapArray Tag))
    (cartesian : List (Int × Nat) → Indices)
    (indexed : HeapArray Tag → Indices → HeapArray Tag → Indices →
      VectorM α (HeapArray Tag))
    (hunalias : CollectUnaliasedLaw destStyle srcStyle unaliased)
    (hcart : CollectCartesianLaw cartesian indexed)
    (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α))
    (hs : heap[src.handle]? = some xs) (hdims : src.dimensions = src.axes.map Prod.snd)
    (hlen : src.dimensions.prod = xs.length) (hn : xs.length < 2 ^ 63)
    (hfit : heapDimensionsFit src.dimensions = true)
    (ha : (heapAllocateArray layout src.elementType src.dimensions).run heap =
      .ok (⟨heap.length, src.elementType, src.dimensions,
        src.dimensions.map (fun n => (1,n))⟩,
        heap ++ [List.replicate src.dimensions.prod none])) :
    (collectArray HeapArray.axes
      (collectHeapIndices layout destStyle srcStyle unaliased cartesian indexed) src).run heap =
        (xs.mapM collectReadSlot).map (fun values =>
          (HeapArray.mk heap.length src.elementType src.dimensions
            (src.dimensions.map (fun n => (1,n))), heap ++ [values])) := by
  let dest : HeapArray Tag :=
    ⟨heap.length, src.elementType, src.dimensions, src.dimensions.map (fun n => (1,n))⟩
  let next := heap ++ [List.replicate src.dimensions.prod none]
  have hsl : src.handle < heap.length := (List.getElem?_eq_some_iff.mp hs).choose
  have hsrc : next[src.handle]? = some xs := by
    simpa only [next, List.getElem?_append_left hsl] using hs
  have hdest : next[dest.handle]? = some (List.replicate src.dimensions.prod none) := by
    simp only [next, dest, List.getElem?_append, Nat.lt_irrefl, ite_false,
      Nat.sub_self, List.getElem?_cons_zero]
  have hset (values : List (Option α)) : next.set dest.handle values = heap ++ [values] := by
    simp only [next, dest, List.set_append, Nat.lt_irrefl, ite_false, Nat.sub_self,
      List.set_cons_zero]
  have hu : (unaliased (destStyle dest) dest (srcStyle src) src).run next =
      (xs.mapM collectReadSlot).map (fun values => (dest, heap ++ [values])) := by
    rw [hunalias next dest src xs (List.replicate src.dimensions.prod none)
      hsrc hdest rfl hlen (by rw [List.length_replicate, hlen]) hn]
    simp only [hset]
  have hc : (indexed dest (cartesian dest.axes) src (cartesian src.axes)).run next =
      (xs.mapM collectReadSlot).map (fun values => (dest, heap ++ [values])) := by
    rw [hcart next dest src xs (List.replicate src.dimensions.prod none)
      hsrc hdest rfl hlen (by rw [List.length_replicate, hlen]) hn]
    simp only [hset]
  have haInt :
      (heapAllocateIntDims layout src.elementType
        (src.axes.map (fun ax => JInt.wrap .i64 (ax.2 : Int)))).run heap = .ok (dest, next) := by
    have ha' := ha
    simp only [heapAllocateArray, hfit, Bool.not_true, Bool.false_eq_true, ite_false,
      Int.ofNat_eq_natCast] at ha'
    simpa only [heapAllocateIntDims, hdims, List.map_map, Function.comp_def, dest, next] using ha'
  have hempty := collectHeapEmpty_run next src xs hsrc
  have hfinish :
      (if xs.isEmpty then (pure dest : VectorM α (HeapArray Tag))
        else unaliased (destStyle dest) dest (srcStyle src) src).run next =
      (xs.mapM collectReadSlot).map (fun values => (dest, heap ++ [values])) := by
    cases xs with
    | nil =>
      have hp : src.dimensions.prod = 0 := hlen
      simp only [List.isEmpty_nil, ite_true, next, hp,
        List.replicate_zero, List.mapM_nil, Pure.pure, Except.pure, Except.map]
      rfl
    | cons x rest =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]
      exact hu
  by_cases hzero : src.axes = []
  · have hd : src.dimensions = [] := by simpa only [hzero, List.map_nil] using hdims
    have haZero : (heapAllocateArray layout src.elementType []).run heap = .ok (dest, next) := by
      simpa only [hd, dest, next] using ha
    simp only [collectArray, collectHeapIndices, hzero, ite_true, collectIndicesZero,
      vector_bind_run, haZero, hempty]
    exact hfinish
  · by_cases hone : src.axes.all (fun ax => decide (ax.1 = 1)) = true
    · simp only [collectArray, collectHeapIndices, hzero, ite_false, hone, ite_true,
        collectIndicesOneTo, vector_bind_run, haInt, hempty]
      exact hfinish
    · simp only [collectArray, collectHeapIndices, hzero, ite_false, hone, Bool.false_eq_true,
        collectIndicesGeneric, vector_bind_run, haInt]
      exact hc

/-- Every array-collection success/error conjunct follows on the checked allocation domain. -/
theorem allocationArrayCollectionOnDomain {Tag α Style Indices : Type}
    (layout : Tag → Option MemoryLayout) (el : MemoryLayout)
    (destStyle srcStyle : HeapArray Tag → Style)
    (unaliased : Style → HeapArray Tag → Style → HeapArray Tag →
      VectorM α (HeapArray Tag))
    (cartesian : List (Int × Nat) → Indices)
    (indexed : HeapArray Tag → Indices → HeapArray Tag → Indices →
      VectorM α (HeapArray Tag))
    (hunalias : CollectUnaliasedLaw destStyle srcStyle unaliased)
    (hcart : CollectCartesianLaw cartesian indexed)
    (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α))
    (hs : heap[src.handle]? = some xs) (hdims : src.dimensions = src.axes.map Prod.snd)
    (hlen : src.dimensions.prod = xs.length) (hn : xs.length < 2 ^ 63)
    (hfit : heapDimensionsFit src.dimensions = true)
    (hel : layout src.elementType = some el)
    (ha : arrayAllocError el (src.dimensions.map (fun n : Nat => (n : Int))) = none) :
    let operation := collectArray HeapArray.axes
      (collectHeapIndices layout destStyle srcStyle unaliased cartesian indexed) src
    (operation.run heap =
      (xs.mapM collectReadSlot).map (fun values =>
        (HeapArray.mk heap.length src.elementType src.dimensions
          (src.dimensions.map (fun n => (1,n))), heap ++ [values]))) ∧
    (∀ values : List α, xs = values.map some → operation.run heap =
      .ok (HeapArray.mk heap.length src.elementType src.dimensions
        (src.dimensions.map (fun n => (1,n))), heap ++ [xs])) ∧
    (none ∈ xs → operation.run heap = .error .undefinedReference) := by
  have hrun := allocationArrayCollectionAfterAllocation layout destStyle srcStyle unaliased
    cartesian indexed hunalias hcart heap src xs hs hdims hlen hn hfit
    (allocationNaturalDimensionsSuccess layout src.elementType el src.dimensions heap hel hfit ha)
  refine ⟨hrun, ?_, ?_⟩
  · intro values hv
    rw [hrun, hv, collectReadSlot_map]
    rfl
  · intro hnone
    rw [hrun, collectReadSlot_undefined xs hnone]
    rfl
end JuliaLean.ChatGPT.Batch5.Group3
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section

/- Integer unsetting partials -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096


/- Allocation and collection partials -/

set_option maxHeartbeats 200000
set_option maxRecDepth 8192




/- Complete sorted deletion and splice proof -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192


/- Filtering partials -/

set_option maxHeartbeats 200000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch5.Group3
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.array.round4

attribute [local irreducible] JInt.wrap wrapInt

/-- The first predicate failure propagates after its mandatory write, independently of finalization. -/
theorem filterVectorFirstPredicateError {σ K : Type} (v : VectorOf σ K)
    (f : K → Except Error (Option Bool)) (first last : I) (rest : List I)
    (s afterRead afterWrite : σ) (x : K) (e : Error)
    (hfirst : v.ops.firstindex.run s = (.ok first, s))
    (hlast : v.ops.lastindex.run s = (.ok last, s))
    (hrange : intRange first last = first :: rest)
    (hread : (v.ops.getAt first).run s = (.ok x, afterRead))
    (hwrite : (v.ops.setAt x first).run afterRead = (.ok (), afterWrite))
    (hpred : round4.boolResult f x = .error e) :
    setVecRunG (vecFilterBangG (fun x => liftV (baseLift (round4.boolResult f x))) v) s =
      (.error e, afterWrite) := by
  unfold setVecRunG
  rw [filterVectorExpand]
  simp only [filterBindRun, filterLiftRun, hfirst, hlast, Except.map, hrange,
    filterIndexLoopPredicateError v f first first rest _ s afterRead afterWrite x e hread hwrite hpred]
end JuliaLean.ChatGPT.Batch5.Group3
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion
open JuliaLean JuliaLean.base.array
open JuliaLean.Registry

/-- The identity-search overload forwards the identity predicate once to
the method selected by the original collection type. -/
def FindnextIdentityProtocol : Prop :=
  ∀ (E A Start : Type) (witness : E) (a : A) (start : Start) (initial : List Nat),
    (JuliaLean.base.array.Completion.findnextIdentity (fun f (_ : A) (_ : Start) => call 0 (.ok (f witness))) a start).run initial =
      (.ok witness, initial ++ [0])

/-- The identity-search overload forwards the identity predicate once to
the method selected by the original collection type. -/
def FindfirstIdentityProtocol : Prop :=
  ∀ (E A : Type) (witness : E) (a : A) (initial : List Nat),
    (JuliaLean.base.array.Completion.findfirstIdentity (fun f (_ : A) => call 0 (.ok (f witness))) a).run initial =
      (.ok witness, initial ++ [0])

/-- Key discovery and its endpoint precede search, with failures preserving
all preceding effects and suppressing later calls. Keys may be arbitrary. -/
def FindfirstArrayIdentityProtocol : Prop :=
  ∀ (W A Keys K R : Type) 
    (keys : A → ExceptT Error (StateM W) Keys)
    (endpoint : Keys → ExceptT Error (StateM W) K)
    (search : A → K → ExceptT Error (StateM W) R) (a : A) (before after : W),
    (∀ error, (keys a).run before = (.error error, after) →
      (JuliaLean.base.array.Completion.findfirstArrayIdentity keys endpoint search a).run before = (.error error, after)) ∧
    (∀ ks middle error, (keys a).run before = (.ok ks, middle) →
      (endpoint ks).run middle = (.error error, after) →
      (JuliaLean.base.array.Completion.findfirstArrayIdentity keys endpoint search a).run before = (.error error, after))

/-- Key discovery and its endpoint precede search, with failures preserving
all preceding effects and suppressing later calls. Keys may be arbitrary. -/
def FindfirstArrayPredicateProtocol : Prop :=
  ∀ (W A Keys K R : Type) (E : Type) (test : E → ExceptT Error (StateM W) Bool) 
    (keys : A → ExceptT Error (StateM W) Keys)
    (endpoint : Keys → ExceptT Error (StateM W) K)
    (search : (E → ExceptT Error (StateM W) Bool) → A → K → ExceptT Error (StateM W) R) (a : A) (before after : W),
    (∀ error, (keys a).run before = (.error error, after) →
      (JuliaLean.base.array.Completion.findfirstArrayPredicate keys endpoint search test a).run before = (.error error, after)) ∧
    (∀ ks middle error, (keys a).run before = (.ok ks, middle) →
      (endpoint ks).run middle = (.error error, after) →
      (JuliaLean.base.array.Completion.findfirstArrayPredicate keys endpoint search test a).run before = (.error error, after))

/-- The identity-search overload forwards the identity predicate once to
the method selected by the original collection type. -/
def FindprevIdentityProtocol : Prop :=
  ∀ (E A Start : Type) (witness : E) (a : A) (start : Start) (initial : List Nat),
    (JuliaLean.base.array.Completion.findprevIdentity (fun f (_ : A) (_ : Start) => call 0 (.ok (f witness))) a start).run initial =
      (.ok witness, initial ++ [0])

/-- The identity-search overload forwards the identity predicate once to
the method selected by the original collection type. -/
def FindlastIdentityProtocol : Prop :=
  ∀ (E A : Type) (witness : E) (a : A) (initial : List Nat),
    (JuliaLean.base.array.Completion.findlastIdentity (fun f (_ : A) => call 0 (.ok (f witness))) a).run initial =
      (.ok witness, initial ++ [0])

/-- Key discovery and its endpoint precede search, with failures preserving
all preceding effects and suppressing later calls. Keys may be arbitrary. -/
def FindlastArrayIdentityProtocol : Prop :=
  ∀ (W A Keys K R : Type) 
    (keys : A → ExceptT Error (StateM W) Keys)
    (endpoint : Keys → ExceptT Error (StateM W) K)
    (search : A → K → ExceptT Error (StateM W) R) (a : A) (before after : W),
    (∀ error, (keys a).run before = (.error error, after) →
      (JuliaLean.base.array.Completion.findlastArrayIdentity keys endpoint search a).run before = (.error error, after)) ∧
    (∀ ks middle error, (keys a).run before = (.ok ks, middle) →
      (endpoint ks).run middle = (.error error, after) →
      (JuliaLean.base.array.Completion.findlastArrayIdentity keys endpoint search a).run before = (.error error, after))

/-- Key discovery and its endpoint precede search, with failures preserving
all preceding effects and suppressing later calls. Keys may be arbitrary. -/
def FindlastArrayPredicateProtocol : Prop :=
  ∀ (W A Keys K R : Type) (E : Type) (test : E → ExceptT Error (StateM W) Bool) 
    (keys : A → ExceptT Error (StateM W) Keys)
    (endpoint : Keys → ExceptT Error (StateM W) K)
    (search : (E → ExceptT Error (StateM W) Bool) → A → K → ExceptT Error (StateM W) R) (a : A) (before after : W),
    (∀ error, (keys a).run before = (.error error, after) →
      (JuliaLean.base.array.Completion.findlastArrayPredicate keys endpoint search test a).run before = (.error error, after)) ∧
    (∀ ks middle error, (keys a).run before = (.ok ks, middle) →
      (endpoint ks).run middle = (.error error, after) →
      (JuliaLean.base.array.Completion.findlastArrayPredicate keys endpoint search test a).run before = (.error error, after))
end JuliaLean.Proofs.base.array.Completion


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion3
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
open JuliaLean.base.array.Completion3

/-- Key discovery errors and divergence precede key conversion, element access and predicate evaluation. The iterator needs no finite rank or evaluation limit. -/
def FindnextKeyFailures : Prop :=
  ∀ (W A Keys K Start E : Type) (keys : A → Exec W Keys) (first last : Keys → Exec W K)
    (oftype : K → Start → Exec W K) (outside : K → K → Exec W (Option Bool))
    (get : A → K → Exec W E) (test : E → Exec W (Option Bool))
    (equal : K → K → Exec W (Option Bool)) (step : A → K → Exec W K)
    (a : A) (start : Start) (before after : W) (error : Error),
    (keys a before = some (.error error, after) →
      JuliaLean.base.array.Completion3.findnext keys first last oftype outside get test equal step a start before =
        some (.error error, after)) ∧
    (keys a before = none →
      JuliaLean.base.array.Completion3.findnext keys first last oftype outside get test equal step a start before = none)

/-- Key discovery errors and divergence precede key conversion, element access and predicate evaluation. The iterator needs no finite rank or evaluation limit. -/
def FindprevKeyFailures : Prop :=
  ∀ (W A Keys K Start E : Type) (keys : A → Exec W Keys) (first : Keys → Exec W K)
    (oftype : K → Start → Exec W K) (outside : K → K → Exec W (Option Bool))
    (get : A → K → Exec W E) (test : E → Exec W (Option Bool))
    (equal : K → K → Exec W (Option Bool)) (step : A → K → Exec W K)
    (a : A) (start : Start) (before after : W) (error : Error),
    (keys a before = some (.error error, after) →
      JuliaLean.base.array.Completion3.findprev keys first oftype outside get test equal step a start before =
        some (.error error, after)) ∧
    (keys a before = none →
      JuliaLean.base.array.Completion3.findprev keys first oftype outside get test equal step a start before = none)

theorem FindnextKeyFailures_proven : FindnextKeyFailures := by
  unfold FindnextKeyFailures
  intros
  constructor <;> intros <;>
    simp_all [JuliaLean.base.array.Completion3.findnext, JuliaLean.base.iterators.bind, bind]

theorem FindprevKeyFailures_proven : FindprevKeyFailures := by
  unfold FindprevKeyFailures
  intros
  constructor <;> intros <;>
    simp_all [JuliaLean.base.array.Completion3.findprev, JuliaLean.base.iterators.bind, bind]

end JuliaLean.Proofs.base.array.Completion3


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group14

open JuliaLean JuliaLean.base.array
open JuliaLean.base.array.Models1Group14
open JuliaLean.Registry

/-- A failing prerequisite determines the whole call's observable failure:
divergence remains divergence, and an exception preserves its exact channel,
payload and state. Successful prerequisites impose no callee correctness law. -/
def FindallFailureObservation {UserError World X Y : Type}
    (prerequisite : Option (Except (FindallError UserError) X × World))
    (actual : Option (Except (FindallError UserError) Y × World)) : Prop :=
  match prerequisite with
  | none => actual = none
  | some (.error error, after) => actual = some (.error error, after)
  | some (.ok _, _) => True

/-- Generic findall observes pair construction, type discovery, and the chosen
result allocation before running its deferred predicate or reading any key.
Every failure at these prerequisite stages is returned with its exact state;
divergence remains divergence. Allocation failures therefore cannot run an
element callback, even if that callback would mutate the collection or throw.

All collections, arbitrary/nonstandard keys, raw iteration results, runtime
states, user exception types and interface operations are quantified. The
implications classify actual interface observations and do not assume a callee
correctness law. No finiteness or success precondition restricts the domain.
The expected observations are errors/states, not a copy of a collection body.

Julia source: base/array.jl:2784-2787,684-694,821-853.
Documentation: base/array.jl:2733-2783; doc/src/manual/arrays.md:353-467
(generator expressions/comprehensions); doc/src/manual/interfaces.md:8-54
(iteration).
Pin: f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def FindallDeferredConstructionInvariant : Prop :=
  ∀ (UserError World A Pairs Pair Value Key State Raw Keys Tag B Mem Ref Shape Size : Type)
    (ops : FindallInterfaces (FindallM UserError World)
      A Pairs Pair Value Key State Raw Keys Tag)
    (vectors : FindallVectorRuntime (FindallM UserError World) Key Tag B Mem Ref)
    (dormant : GeneratorCollectOps (FindallM UserError World)
      (FindallGenerator (FindallM UserError World) Pairs Pair Key)
      Key Tag Size Shape State B)
    (a : A) (initial : World),
    let run := JuliaLean.base.array.Models1Group14.findallPredicate
      ops vectors dormant a initial
    FindallFailureObservation (ops.pairs a initial) run ∧
    (∀ ps afterPairs,
      ops.pairs a initial = some (.ok ps, afterPairs) →
      let gen : FindallGenerator (FindallM UserError World) Pairs Pair Key :=
        ⟨ops.pairKey, JuliaLean.base.iterators.sourceMethod576
          (fun p => do ops.test (← ops.pairValue p)) ps⟩
      FindallFailureObservation (findallDefaultGeneratorType ops gen afterPairs) run ∧
      (∀ tag afterType,
        findallDefaultGeneratorType ops gen afterPairs = some (.ok tag, afterType) →
        (ops.isBottom tag = true →
          let keyType := findallDefaultEltypeExpression (ops.keys a)
            ops.keysIsGenerator ops.functionField ops.isType ops.inferKeys ops.promoteUnion
          FindallFailureObservation (keyType afterType) run ∧
          (∀ keyTag afterKeyType,
            keyType afterType = some (.ok keyTag, afterKeyType) →
            FindallFailureObservation
              (findallAllocate vectors keyTag zero afterKeyType) run)) ∧
        (ops.isBottom tag = false →
          FindallFailureObservation (findallDefaultGeneratorType ops gen afterType) run ∧
          (∀ inferred afterInference,
            findallDefaultGeneratorType ops gen afterType = some (.ok inferred, afterInference) →
            FindallFailureObservation
              (findallAllocate vectors inferred zero afterInference) run))))

/-- The bottom-inferred branch of public generic findall retains the macro's
observable repeated keys(A) calls. After a successful first call, an exception
or divergence from its next call remains observable. When the first returned
key iterator is a Generator, a successful second call and `.f` read are followed
by a third call, whose failure also remains observable. In particular, sharing
one keys(A) value for the macro expansion can falsify this statement.

This invariant includes every typed input and every effectful/error-producing
runtime interface. It does not claim that repeated keys calls agree, that a
returned key iterator has a specific concrete type, or that a field read succeeds.
Julia source: base/array.jl:2784-2787,821-831.
Pin: f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def FindallRepeatedKeysInvariant : Prop :=
  ∀ (UserError World A Pairs Pair Value Key State Raw Keys Tag B Mem Ref Shape Size : Type)
    (ops : FindallInterfaces (FindallM UserError World)
      A Pairs Pair Value Key State Raw Keys Tag)
    (vectors : FindallVectorRuntime (FindallM UserError World) Key Tag B Mem Ref)
    (dormant : GeneratorCollectOps (FindallM UserError World)
      (FindallGenerator (FindallM UserError World) Pairs Pair Key)
      Key Tag Size Shape State B)
    (a : A) (initial : World),
    let run := JuliaLean.base.array.Models1Group14.findallPredicate
      ops vectors dormant a initial
    ∀ ps afterPairs,
      ops.pairs a initial = some (.ok ps, afterPairs) →
      let gen : FindallGenerator (FindallM UserError World) Pairs Pair Key :=
        ⟨ops.pairKey, JuliaLean.base.iterators.sourceMethod576
          (fun p => do ops.test (← ops.pairValue p)) ps⟩
      ∀ tag afterType,
        findallDefaultGeneratorType ops gen afterPairs = some (.ok tag, afterType) →
        ops.isBottom tag = true →
        FindallFailureObservation (ops.keys a afterType) run ∧
        (∀ firstKeys afterFirst,
          ops.keys a afterType = some (.ok firstKeys, afterFirst) →
          FindallFailureObservation (ops.keys a afterFirst) run ∧
          (ops.keysIsGenerator firstKeys = true →
            ∀ secondKeys afterSecond,
              ops.keys a afterFirst = some (.ok secondKeys, afterSecond) →
              FindallFailureObservation (ops.functionField secondKeys afterSecond) run ∧
              (∀ functionValue afterField,
                ops.functionField secondKeys afterSecond = some (.ok functionValue, afterField) →
                FindallFailureObservation (ops.keys a afterField) run)))
end JuliaLean.Proofs.base.array.Models1Group14


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group14

open JuliaLean JuliaLean.base.array

/-- Independent condition-error observation over every runtime state type. The
operation's own errors propagate; a successfully returned non-Bool causes a
TypeError before allocation. Successful Bool cases impose no unsupported law
on the allocator or setter. Julia source: base/array.jl:2852-2853;
doc/src/manual/control-flow.md:180-207. -/
def ScalarConditionFailureObservation {World A : Type}
    (condition : Except Error (Option Bool) × World)
    (actual : Except Error A × World) : Prop :=
  match condition.1 with
  | .error error => actual = (.error error, condition.2)
  | .ok none => ∃ context, actual = (.error (.typeError context), condition.2)
  | .ok (some _) => True

/-- Both scalar public methods retain predicate/membership effects and errors,
including non-Bool condition errors, before any allocator or store operation.
All state types, runtime operations and values are quantified; no correctness
law is supplied for a predicate, membership, allocation, or assignment.
The concrete allocation properties below supplement this full typed-boundary
error invariant with independent result/identity/frame observations.
Julia source: base/array.jl:2852-2853. -/
def ScalarFindallBoundaryErrors : Prop :=
  ∀ (World Number Collection A : Type)
    (test : Number → ExceptT Error (StateM World) (Option Bool))
    (contains : Number → Collection → ExceptT Error (StateM World) (Option Bool))
    (allocate : I → ExceptT Error (StateM World) A)
    (set : A → I → I → ExceptT Error (StateM World) A)
    (collection : Collection) (x : Number) (initial : World),
    ScalarConditionFailureObservation ((test x).run initial)
      ((JuliaLean.base.array.Models1Group14.findallNumber test allocate set x).run initial) ∧
    ScalarConditionFailureObservation ((contains x collection).run initial)
      ((JuliaLean.base.array.Models1Group14.findallInNumber contains allocate set collection x).run initial)

private theorem scalarConditionFailure_preserved {World A : Type}
    (condition : ExceptT Error (StateM World) (Option Bool))
    (continuation : Bool → ExceptT Error (StateM World) A) (initial : World) :
    ScalarConditionFailureObservation (condition.run initial)
      ((do
        let value ← condition
        let keep ← JuliaLean.base.array.Models1Group14.requireBool value
        continuation keep).run initial) := by
  cases observed : condition.run initial with
  | mk answer final =>
    cases answer with
    | error error =>
      change condition initial = (.error error, final) at observed
      simp [ScalarConditionFailureObservation, Bind.bind, Pure.pure, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        StateT.run, StateT.bind, StateT.pure, observed]
    | ok value =>
      change condition initial = (.ok value, final) at observed
      cases value <;>
        simp [ScalarConditionFailureObservation, JuliaLean.base.array.Models1Group14.requireBool,
          throw, throwThe, MonadExceptOf.throw, Bind.bind, Pure.pure,
          ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
          StateT.run, StateT.bind, StateT.pure, observed]

theorem scalarFindallBoundaryErrors_proven : ScalarFindallBoundaryErrors := by
  intro World Number Collection A test contains allocate set collection x initial
  exact ⟨scalarConditionFailure_preserved (test x)
      (JuliaLean.base.array.findallBoolDispatch allocate set) initial,
    scalarConditionFailure_preserved (contains x collection)
      (JuliaLean.base.array.findallBoolDispatch allocate set) initial⟩

/-- Independent scalar-search result relation. The reference observation is one
evaluation of the user's predicate/membership operation, not a correctness law
about that operation. Failure and non-Bool results retain exactly its resulting
store and do not allocate. A Bool result creates a fresh, valid Int vector whose
keys are precisely the scalar key 1 when selected, preserving existing array
headers and memory records after predicate effects.
No arithmetic-size premise is needed: the only new lengths are 0 and 1.
Julia source: base/array.jl:2852-2853; documentation:
base/array.jl:2733-2783,2795-2832; base/number.jl:93,99;
doc/src/manual/control-flow.md:180-207. -/
def ScalarFindallObservation
    (condition : Except Error (Option Bool) × MutableMemory I)
    (actual : Except Error Nat × MutableMemory I) : Prop :=
  match condition.1 with
  | .error e => actual.1 = .error e ∧ actual.2 = condition.2
  | .ok none =>
    (∃ context, actual.1 = .error (.typeError context)) ∧ actual.2 = condition.2
  | .ok (some keep) =>
    ∃ handle, actual.1 = .ok handle ∧
      condition.2.arrays.length ≤ handle ∧
      actual.2.validVector handle ∧
      actual.2.contents handle = (if keep then [some one] else []) ∧
      actual.2.arrays.take condition.2.arrays.length = condition.2.arrays ∧
      actual.2.memories.take condition.2.memories.length = condition.2.memories

/-- Every scalar and every effectful predicate observation is included: thrown
errors, non-Bool returns, false, and true. Predicate effects may alter any existing
memory; the frame condition starts after those effects. A double evaluation, wrong
index, reused result vector, lost mutation, or premature allocation can falsify it.
Julia source: base/array.jl:2852. -/
def FindallNumberEffectsAndAllocation : Prop :=
  ∀ (Number : Type) (test : Number → MutationM I (Option Bool))
    (x : Number) (initial : MutableMemory I),
    ScalarFindallObservation ((test x).run initial)
      ((JuliaLean.base.array.Models1Group14.findallNumberHeap test x).run initial)

/-- The membership overload observes `in(x, collection)` once and returns a fresh
Int vector with the scalar's selected keys, with the same full failure domain as
the predicate overload. No membership correctness premise is supplied.
Julia source: base/array.jl:2853. -/
def FindallInNumberEffectsAndAllocation : Prop :=
  ∀ (Number Collection : Type)
    (contains : Number → Collection → MutationM I (Option Bool))
    (collection : Collection) (x : Number) (initial : MutableMemory I),
    ScalarFindallObservation ((contains x collection).run initial)
      ((JuliaLean.base.array.Models1Group14.findallInNumberHeap contains collection x).run initial)
end JuliaLean.Proofs.base.array.Models1Group14


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group14

open JuliaLean JuliaLean.base.array

/-- Full mutable-world observations at the existing Bool-array findall boundary.
ExceptT retains every effect before an exception. -/
abbrev BoolFindallM (World : Type) := ExceptT Error (StateM World)

/-- An independent phase/error and returned-allocation invariant for the public
Bool-array findall method. Count, keys, key-type discovery, native allocation,
and pair construction occur in that order. An error from any of those phases
is returned with precisely its resulting mutable world and no later effects;
every successful result is the vector allocated with the observed key type and
count. The key representation is unrestricted, including native and Cartesian
indices; this property does not assert the later loop's element-selection result.

Every runtime implementation, original array representation, pair iterator,
native count and shared world is included. The count/pairs consistency that a
pure unchanged input would have is not assumed: custom effects and aliases may
change the live values between or during passes. Outcomes in the implications
are observations of actual operations, not supplied callee-correctness laws.
This invariant omits the selection-loop result rather than restating its body.

Julia source: base/array.jl:2838-2849. Documentation: base/array.jl:2793-2803;
doc/src/manual/interfaces.md:9-54 (live iteration protocol).
Pin: f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def BoolArrayFindallBoundaryInvariant : Prop :=
  ∀ (World A Keys Tag Pairs K B Mem Ref : Type)
    (iteration : ForIn (BoolFindallM World) Pairs (K × Bool))
    (count : A → BoolFindallM World I)
    (keys : A → BoolFindallM World Keys)
    (keyType : Keys → BoolFindallM World Tag)
    (pairs : A → BoolFindallM World Pairs)
    (vectors : JuliaLean.base.array.Models1Group14.IndcopyVectorRuntime
      (BoolFindallM World) K Tag B Mem Ref)
    (a : A) (initial : World),
    letI := iteration
    let run := (JuliaLean.base.array.Models1Group14.findallBoolArray
      count keys keyType pairs vectors a).run initial
    (∀ error afterCount,
      (count a).run initial = (.error error, afterCount) →
      run = (.error error, afterCount)) ∧
    (∀ n afterCount error afterKeys,
      (count a).run initial = (.ok n, afterCount) →
      (keys a).run afterCount = (.error error, afterKeys) →
      run = (.error error, afterKeys)) ∧
    (∀ n afterCount ks afterKeys error afterType,
      (count a).run initial = (.ok n, afterCount) →
      (keys a).run afterCount = (.ok ks, afterKeys) →
      (keyType ks).run afterKeys = (.error error, afterType) →
      run = (.error error, afterType)) ∧
    (∀ n afterCount ks afterKeys t afterType error afterAllocation,
      (count a).run initial = (.ok n, afterCount) →
      (keys a).run afterCount = (.ok ks, afterKeys) →
      (keyType ks).run afterKeys = (.ok t, afterType) →
      (JuliaLean.base.array.Models1Group14.boolFindallAllocate vectors t n).run
        afterType = (.error error, afterAllocation) →
      run = (.error error, afterAllocation)) ∧
    (∀ n afterCount ks afterKeys t afterType allocated afterAllocation,
      (count a).run initial = (.ok n, afterCount) →
      (keys a).run afterCount = (.ok ks, afterKeys) →
      (keyType ks).run afterKeys = (.ok t, afterType) →
      (JuliaLean.base.array.Models1Group14.boolFindallAllocate vectors t n).run
        afterType = (.ok allocated, afterAllocation) →
      (∀ error afterPairs,
        (pairs a).run afterAllocation = (.error error, afterPairs) →
        run = (.error error, afterPairs)) ∧
      (∀ returned final, run = (.ok returned, final) → returned = allocated))
end JuliaLean.Proofs.base.array.Models1Group14


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group14

open JuliaLean JuliaLean.base.array
open JuliaLean.Registry

abbrev PairSearchM (World : Type) := ExceptT Error (StateM World)

/-- Every pair-construction error precedes the predicate and is returned with
its effects intact. Last-search also propagates reverse-construction errors
after the pair-construction effects and before testing any element.
The conditional observations are evaluations of actual operations, not supplied
correctness laws. All typed collections, iterator instances, predicates, errors,
and runtime states are quantified. Julia source: base/array.jl:2518-2523,2711-2716;
documentation:2483-2517,2679-2710; doc/src/manual/interfaces.md:9-54. -/
def PairSearchConstructionInvariant : Prop :=
  ∀ (World A K E Pairs Reversed : Type)
    [ForIn (PairSearchM World) Pairs (K × E)]
    [ForIn (PairSearchM World) Reversed (K × E)]
    (pairs : A → PairSearchM World Pairs)
    (reversePairs : Pairs → PairSearchM World Reversed)
    (test : E → PairSearchM World Bool) (a : A) (initial : World),
    let firstRun := (JuliaLean.base.array.Models1Group14.findfirst pairs test a).run initial
    let lastRun := (JuliaLean.base.array.Models1Group14.findlast pairs reversePairs test a).run initial
    (∀ error afterPairs,
      (pairs a).run initial = (.error error, afterPairs) →
      firstRun = (.error error, afterPairs) ∧ lastRun = (.error error, afterPairs)) ∧
    (∀ ps afterPairs error afterReverse,
      (pairs a).run initial = (.ok ps, afterPairs) →
      (reversePairs ps).run afterPairs = (.error error, afterReverse) →
      lastRun = (.error error, afterReverse))

theorem pairSearchConstructionInvariant_proven : PairSearchConstructionInvariant := by
  intro World A K E Pairs Reversed _ _ pairs reversePairs test a initial
  constructor
  · intro error afterPairs hp
    change pairs a initial = (.error error, afterPairs) at hp
    simp [Bind.bind, Pure.pure, JuliaLean.base.array.Models1Group14.findfirst,
      JuliaLean.base.array.Models1Group14.findlast, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
      StateT.run, StateT.bind, StateT.pure, hp]
  · intro ps afterPairs error afterReverse hp hr
    change pairs a initial = (.ok ps, afterPairs) at hp
    change reversePairs ps afterPairs = (.error error, afterReverse) at hr
    simp [Bind.bind, Pure.pure, JuliaLean.base.array.Models1Group14.findlast, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
      StateT.run, StateT.bind, StateT.pure, hp, hr]

/-- Supplementary independent selection contract for the concrete finite-pairs
instance: the result is the first/last key among matching pairs, or `nothing`
when there is no match. The expected answer filters the mathematical input
sequence rather than copying either short-circuit search loop.

The machine-size bound is the representation invariant of this concrete finite
Julia collection. Keys are arbitrary and need not be one-based integers.
Pure predicates here are one concrete interface instance; the separate full
boundary properties retain the effectful/error cases. Julia documentation:
base/array.jl:2483-2517,2679-2710; source:2518-2523,2711-2716. -/
def PairSearchFiniteSelectionSpec : Prop :=
  ∀ (K E : Type) (ps : List (K × E)) (test : E → Bool),
    ps.length < 2 ^ 63 →
    let selected := ps.filter (fun pair => test pair.2)
    (JuliaLean.base.array.Models1Group14.findfirst (m := Except Error)
      (fun (_ : Unit) => pure ps) (fun value => pure (test value)) ()) =
        .ok (selected.head?.map Prod.fst) ∧
    (JuliaLean.base.array.Models1Group14.findlast (m := Except Error)
      (fun (_ : Unit) => pure ps) (fun pairs => pure pairs.reverse)
      (fun value => pure (test value)) ()) =
        .ok (selected.getLast?.map Prod.fst)
end JuliaLean.Proofs.base.array.Models1Group14


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.LegacyRetired

open JuliaLean JuliaLean.base.array JuliaLean.Registry

def UnitSearchBounds : Prop :=
  ∀ (V X R K D : Type) (first last : R → V) (value : V → Int) (target : X → Int)
    (firstKey : R → Except Error K) (subtract : X → V → D)
    (oftype : K → D → Except Error K) (add : K → K → K) (x : X) (r : R),
    let run := findfirstUnitRange first last value target firstKey subtract oftype add x r
    ((target x < value (first r) ∨ value (last r) < target x) → run = .ok none) ∧
    (value (first r) ≤ target x → target x ≤ value (last r) → run ≠ .ok none)

theorem unitSearchBounds : UnitSearchBounds := by
  intro V X R K D first last value target firstKey subtract oftype add x r
  constructor
  · intro outside
    have bad : ¬ (value (first r) ≤ target x ∧ target x ≤ value (last r)) := by omega
    simp [findfirstUnitRange, bad]
  · intro low high
    have inside : value (first r) ≤ target x ∧ target x ≤ value (last r) := ⟨low, high⟩
    cases hkey : firstKey r with
    | error e => simp [findfirstUnitRange, inside, hkey]
    | ok key =>
      cases hconvert : oftype key (subtract x (first r)) <;>
        simp [findfirstUnitRange, inside, hkey, hconvert]

def StepSearchBounds : Prop :=
  ∀ (V X R K S D Rem Q : Type) (isempty : R → Bool) (minimum maximum first : R → V)
    (step : R → S) (leLow : V → X → Bool) (leHigh : X → V → Bool)
    (sub : X → V → D) (rem : D → S → Except Error Rem) (iszero : Rem → Bool)
    (divide : D → S → Except Error Q) (plusOne : Q → Q)
    (convertKey : Q → Except Error K) (value : V → Int) (target : X → Int)
    (x : X) (r : R),
    leLow (minimum r) x = decide (value (minimum r) ≤ target x) →
    leHigh x (maximum r) = decide (target x ≤ value (maximum r)) →
    let run := findfirstStepRange isempty minimum maximum first step leLow leHigh sub rem
      iszero divide plusOne convertKey x r
    (isempty r = true → run = .ok none) ∧
    ((target x < value (minimum r) ∨ value (maximum r) < target x) → run = .ok none)

theorem stepSearchBounds : StepSearchBounds := by
  intro V X R K S D Rem Q isempty minimum maximum first step leLow leHigh sub rem iszero
    divide plusOne convertKey value target x r lowLaw highLaw
  constructor
  · intro empty
    simp [findfirstStepRange, empty]
  · intro outside
    have bad : (decide (value (minimum r) ≤ target x) &&
        decide (target x ≤ value (maximum r))) = false := by
      rcases outside with below | above
      · have lowFalse : ¬ value (minimum r) ≤ target x := by omega
        simp [lowFalse]
      · have highFalse : ¬ target x ≤ value (maximum r) := by omega
        simp [highFalse]
    cases he : isempty r <;>
      simp only [findfirstStepRange, he, lowLaw, highLaw, bad] <;> rfl

def RangeSearchDispatch : Prop :=
  ∀ (V R K : Type) (first : R → V) (zero one : V → V)
    (find : V → R → Except Error (Option K)) (x : V) (r : R),
    findlastRange2723 find x r = find x r ∧
    findlastRange2728 find x r = find x r ∧
    findfirstZeroRange first zero find r = find (zero (first r)) r ∧
    findfirstOneRange first one find r = find (one (first r)) r

theorem rangeSearchDispatch : RangeSearchDispatch := by
  intro V R K first zero one find x r
  exact ⟨rfl, rfl, rfl, rfl⟩

def RangeSearchBounds : Prop := UnitSearchBounds ∧ StepSearchBounds ∧ RangeSearchDispatch

theorem rangeSearchBounds : RangeSearchBounds :=
  ⟨unitSearchBounds, stepSearchBounds, rangeSearchDispatch⟩
end JuliaLean.Proofs.base.array.LegacyRetired


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array
end JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
theorem JuliaLean.Proofs.base.array.Completion.FindnextIdentityProtocol_proven : JuliaLean.Proofs.base.array.Completion.FindnextIdentityProtocol := by
  unfold JuliaLean.Proofs.base.array.Completion.FindnextIdentityProtocol
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion.findnextIdentity, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion.FindfirstIdentityProtocol_proven : JuliaLean.Proofs.base.array.Completion.FindfirstIdentityProtocol := by
  unfold JuliaLean.Proofs.base.array.Completion.FindfirstIdentityProtocol
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion.findfirstIdentity, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion.FindfirstArrayIdentityProtocol_proven : JuliaLean.Proofs.base.array.Completion.FindfirstArrayIdentityProtocol := by
  unfold JuliaLean.Proofs.base.array.Completion.FindfirstArrayIdentityProtocol
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion.findfirstArrayIdentity, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion.FindfirstArrayPredicateProtocol_proven : JuliaLean.Proofs.base.array.Completion.FindfirstArrayPredicateProtocol := by
  unfold JuliaLean.Proofs.base.array.Completion.FindfirstArrayPredicateProtocol
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion.findfirstArrayPredicate, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion.FindprevIdentityProtocol_proven : JuliaLean.Proofs.base.array.Completion.FindprevIdentityProtocol := by
  unfold JuliaLean.Proofs.base.array.Completion.FindprevIdentityProtocol
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion.findprevIdentity, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion.FindlastIdentityProtocol_proven : JuliaLean.Proofs.base.array.Completion.FindlastIdentityProtocol := by
  unfold JuliaLean.Proofs.base.array.Completion.FindlastIdentityProtocol
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion.findlastIdentity, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion.FindlastArrayIdentityProtocol_proven : JuliaLean.Proofs.base.array.Completion.FindlastArrayIdentityProtocol := by
  unfold JuliaLean.Proofs.base.array.Completion.FindlastArrayIdentityProtocol
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion.findlastArrayIdentity, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion.FindlastArrayPredicateProtocol_proven : JuliaLean.Proofs.base.array.Completion.FindlastArrayPredicateProtocol := by
  unfold JuliaLean.Proofs.base.array.Completion.FindlastArrayPredicateProtocol
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion.findlastArrayPredicate, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

namespace JuliaLean.Proofs.base.array
def entriesFindnext1 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-find-pure", juliaFile := "base/array.jl",
    juliaFns := ["findnext(testf::Function, A, start)", "findfirst(testf::Function, A)",
      "findprev(testf::Function, A, start)", "findlast(testf::Function, A)",
      "findall(testf::Function, A)", "findall(testf::F, A::AbstractArray) where {F<:Function}"],
    statement := "`multidimcov-array-v2-find-pure`: the predicate searches (`findnext`, `findprev`, `findfirst`, `findlast` on vectors with unassigned slots and starts of every `Integer` type, and `findfirst` on arrays of every nonempty shape) and `findall(f, A)` for every collection through either `collect` path and through `testf.(A)`.",
    source := "base/array.jl:2441-2469,2484-2517,2587-2665,2680-2710,2733-2783 (docstrings),2784-2791", status := .proven,
    prop := ``FindPureSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.MultidimcovArrayV2FindPure_proven,
    notes := "expected refuted: the file states ¬ FindPureSpec (theorem findPureSpec_refuted); repro/multidimcov-array-v2-find-pure.jl" },
  { id := "multidimcov-array-v2-find-bool", juliaFile := "base/array.jl",
    juliaFns := ["findnext(A, start)", "findfirst(A)", "findprev(A, start)", "findlast(A)",
      "findall(A)", "findall(A::AbstractArray{Bool})"],
    statement := "`multidimcov-array-v2-find-bool`: the `Bool` searches and `findall(A)` for `Bool` arrays of every shape (generic and `AbstractArray{Bool}` methods).",
    source := "base/array.jl:2367-2398,2401-2435,2552-2585,2588-2623,2795-2832 (docstrings),2833-2849", status := .proven,
    prop := ``FindBoolSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.MultidimcovArrayV2FindBool_proven,
    notes := "" }
]
def entriesFindnext2 : List JuliaLean.Registry.Entry := [
  { id := "arrayops-find-inrange", juliaFile := "base/array.jl",
    juliaFns := ["findnext(testf::Function, A, start)", "findprev(testf::Function, A, start)",
      "findfirst(testf::Function, A::Union{AbstractArray, AbstractString})",
      "findlast(testf::Function, A::Union{AbstractArray, AbstractString})"],
    statement := "`findnext(f, A, i)`, `findprev(f, A, i)`, `findfirst(f, A::AbstractArray)` and `findlast(f, A::AbstractArray)` (array.jl:2470, 2666, 2526, 2719; docstrings at 2441-2469, 2629-2665, 2483-2517, 2679-2710: \"Find the next index after or including `i` of an element of `A` for which `predicate` returns `true`, or `nothing` if not found\") for every start of any `Integer` type inside the keys: on a `Vector` whose slots may be unassigned, a forward search from `i ∈ 1:length(A)` returns the least matching position at or after `i` and a backward search the greatest one at or before `i`, `nothing` when there is none, and `UndefRefError` when an unassigned slot is read before a match; `findfirst`/`findlast` search the whole vector. On an array of any shape with no empty dimension, `findfirst` returns the first Cartesian key, in column-major order, whose element passes the test.",
    source := "base/array.jl:2470", status := .proven,
    prop := ``VectorStartSearchSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.ArrayopsFindInrange_proven,
    notes := "" },
  { id := "array-search-bool-start", juliaFile := "base/array.jl",
    juliaFns := ["findnext(A, start)", "findprev(A, start)", "findfirst(A::AbstractArray)",
      "findlast(A::AbstractArray)"],
    statement := "`findnext(A, i)`, `findprev(A, i)`, `findfirst(A::AbstractArray)` and `findlast(A::AbstractArray)` (array.jl:2399, 2586, 2439, 2627; docstrings at 2367-2398, 2552-2585, 2401-2435, 2588-2623: \"Find the next index after or including `i` of a `true` element of `A`, or `nothing` if not found\") on `Bool` arrays (which have no unassigned slot): `findnext(A, i) = findnext(identity, A, i)` and `findprev` likewise, for every start of any `Integer` type with an equal `Int` (any value: before, inside or after the keys), find the least `true` position at or after `i` (respectively the greatest at or before `i`), and `findfirst(A)`/`findlast(A)` search the whole vector; on a `Bool` array of any shape with no empty dimension, `findfirst(A)` returns the first Cartesian key of a `true` element in column-major order. The model's `findnextBool`/`findprevBool` forward a start of the key type unchanged, so the forwarders are stated for `Int` starts and the searches they reach for every `Integer` start.",
    source := "base/array.jl:2399", status := .proven,
    prop := ``BoolVectorStartSearchSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.ArraySearchBoolStart_proven,
    notes := "" },
  { id := "array-search-boolean-positions", juliaFile := "base/array.jl",
    juliaFns := ["findfirst(A::AbstractArray{Bool})", "findlast(A::AbstractArray{Bool})"],
    statement := "Boolean first and last searches select a true value at the first or last matching position and return nothing exactly when every element is false.",
    source := "base/array.jl:2436; 2624; first and last matching-key contract",
    status := .proven, prop := ``BooleanSearchPositionsSpec, thm := some ``booleanSearchPositionsSpec},
  { id := "array-search-last-complete", juliaFile := "base/array.jl",
    juliaFns := ["findlast(testf::Function, A)"],
    statement := "Last search returns nothing exactly when every iterated value fails the predicate.",
    source := "base/array.jl:2711-2717; findlast matching-key contract",
    status := .proven, prop := ``LastSearchComplete, thm := some ``lastSearchComplete}
]
def entriesFindnext3 : List JuliaLean.Registry.Entry := [
  { id := "array-findall-scalar", juliaFile := "base/array.jl",
    juliaFns := ["findall(x::Bool)", "findall(f::Function, x::Number)", "findall(Fix2{typeof(in)}, x::Number)"],
    statement := "A scalar search returns exactly the matching scalar's key, once, and returns no keys when the scalar does not match.",
    source := "base/array.jl:2851-2853; findall matching-key contract",
    status := .proven, prop := ``ScalarFindallSpec, thm := some ``scalarFindallSpec},
  { id := "array-search-oneto-first", juliaFile := "base/array.jl",
    juliaFns := ["findfirst(equalto, r::OneTo)", "findfirst(iszero, r::OneTo)", "findfirst(isone, r::OneTo)"],
    statement := "`findfirst(==(x), r::OneTo)` / `findfirst(isequal(x), r::OneTo)`, `findfirst(iszero, ::OneTo)` and `findfirst(isone, r::OneTo)` (array.jl:2529, 2532, 2533; `findfirst` docstring at array.jl:2483-2517: the first key of a matching element, or `nothing`) for a target of any `Integer` type and a `OneTo` of any BitInteger type (a normalized, nonnegative stop): the key is `convert(keytype(r), x)` exactly when `1 ≤ x ≤ stop`, and `nothing` otherwise; `iszero` is never found; `isone` is found at key `1` exactly when `r` is nonempty.",
    source := "base/array.jl:2483-2517, array.jl:2529", status := .proven,
    prop := ``OneToFirstSearchSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.ArraySearchOnetoFirst_proven,
    notes := "" }
]
def entriesFindnext4 : List JuliaLean.Registry.Entry := [
  { id := "tuples-findall-in-isequal", juliaFile := "base/array.jl",
    juliaFns := ["findall(pred::Fix2{typeof(in)}, x::Tuple)"],
    statement := "`findall(in(b), x::Tuple)` (array.jl:2962) and `findall(in(b), x::AbstractArray)` (array.jl:2961), through `_findin` with set.jl's `Set` (docstrings of `findall(f, A)` at array.jl:2733-2783 and of `in`): for every element type, the result holds the positions of the elements of `x` that are `==` to an element of `b`, in order.",
    source := "base/array.jl:2733-2783, array.jl:2961, array.jl:2962", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64153, #29124, #52639, #46222; see bugs/tuples-findall-in-isequal.yaml",
    prop := ``TupleMembershipAgreement, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.TuplesFindallInIsequal_refuted,
    notes := "expected refuted: the file states ¬ TupleMembershipAgreement (theorem tupleMembershipAgreement_refuted); repro/tuples-findall-in-isequal.jl" }
]
def entriesFindnext5 : List JuliaLean.Registry.Entry := [
  { id := "multidim-findfirst-empty-matrix", juliaFile := "base/array.jl",
    juliaFns := ["findfirst(testf::Function, A::AbstractArray)"],
    statement := "`findfirst(A)` / `findfirst(f, A)` (array.jl:2439, 2526; docstrings at array.jl:2401-2435 and 2483-2517: the first key of a `true`/matching element in the order of `keys(A)`, or `nothing`) on a multidimensional array of any shape, empty dimensions included (every dimension an `Int`): the result is the first Cartesian key in column-major order whose element passes the test, and no out-of-bounds element is read.",
    source := "base/array.jl:2401-2435, array.jl:2439", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #36938, #40120; see bugs/multidim-findfirst-empty-matrix.yaml",
    prop := ``FindfirstCartesian, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.MultidimFindfirstEmptyMatrix_refuted,
    notes := "expected refuted: the file states ¬ FindfirstCartesian (theorem findfirstCartesian_refuted); repro/multidim-findfirst-empty-matrix.jl" }
]
def entriesFindnext6 : List JuliaLean.Registry.Entry := [
  { id := "arraycov-indexin-isequal", juliaFile := "base/array.jl",
    juliaFns := ["indexin(a, b::AbstractArray)"],
    statement := "`indexin(a, b::AbstractArray)` (array.jl:2887; docstring at array.jl:2856-2886: \"Return an array containing the first index in `b` for each value in `a` that is a member of `b`. The output array contains `nothing` wherever `a` is not a member of `b`.\"), with dict.jl's `Dict` (`get!` keeping the first index, `get` with default `nothing`) for every element type: the result holds, for each value of `a`, the first index of `b` whose element is `==` to it (`in`'s membership), or `nothing`.",
    source := "base/array.jl:2856-2886, array.jl:2887", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #10593; see bugs/arraycov-indexin-isequal.yaml",
    prop := ``IndexinMembershipAgreement, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.ArraycovIndexinIsequal_refuted,
    notes := "expected refuted: the file states ¬ IndexinMembershipAgreement (theorem indexinMembershipAgreement_refuted); repro/arraycov-indexin-isequal.jl" },
  { id := "ranges-operations-findfirst-overflow", juliaFile := "base/array.jl",
    juliaFns := ["findfirst(==(::Integer), ::StepRange)", "findfirst(==(::Integer), ::AbstractUnitRange)"],
    statement := "A matching integer in an integer range returns a positive search index.",
    source := "base/array.jl:2484-2523 (docstring),2535-2547", status := .refuted,
    prop := ``RangeFindfirstPositive, thm := some ``rangeFindfirstPositive_refuted,
    issue := "none found (queries: findfirst StepRange Int8 overflow)",
    notes := "findfirst(==(Int8(100)), Int8(-100):Int8(2):Int8(120)) returns -27." },
  { id := "array-range-target-search-overflow", juliaFile := "base/array.jl",
    juliaFns := ["findfirst(::typeof(iszero), ::AbstractRange)", "findfirst(::typeof(isone), ::AbstractRange)",
      "findlast(::Union{Fix2{typeof(isequal),<:Integer},Fix2{typeof(==),<:Integer},typeof(iszero),typeof(isone)}, ::AbstractUnitRange{<:Integer})",
      "findlast(::Union{Fix2{typeof(isequal),T},Fix2{typeof(==),T},typeof(iszero),typeof(isone)}, ::StepRange{T,S})"],
    statement := "The documented search contract of `findfirst(iszero, r)`, `findfirst(isone, r)` (array.jl:2549, 2550, through `findfirst(==(zero(first(r))), r)`), `findlast(==(x), r)` (array.jl:2723, 2728, through `findfirst`) and the unit- and step-range `findfirst(==(x), r)` methods (array.jl:2535, 2541) they reach (`findfirst`/`findlast` docstrings at array.jl:2483-2517, 2679-2710: the first or last key of a matching element, or `nothing`): on a unit range `lo:hi` of any BitInteger element type, a target of any `Integer` type inside the range is found at the key `k` with `lo + (k - 1) = x`, and a target outside it gives `nothing`; on a step range of any BitInteger type with a nonzero step of either sign and a normalized stop, a value of the range (zero, one, or any `x`) is found at the key `k` whose element `start + (k - 1)*step` is that value, and a value not in the range gives `nothing`.",
    source := "base/array.jl:2483-2517, array.jl:2535, array.jl:2549, array.jl:2723", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64122, #63399; see bugs/array-range-target-search-overflow.yaml",
    prop := ``RangeTargetSearchSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.ArrayRangeTargetSearchOverflow_refuted,
    notes := "expected refuted: the file states ¬ RangeTargetSearchSpec (theorem rangeTargetSearchSpec_refuted); repro/array-range-target-search-overflow.jl" },
  { id := "array-findall-in-array-isequal", juliaFile := "base/array.jl",
    juliaFns := ["findall(pred::Fix2{typeof(in)}, x::AbstractArray)", "_findin(a::Union{AbstractArray, Tuple}, b::AbstractSet)",
      "_findin(a::Union{AbstractArray, Tuple}, b)"],
    statement := "`findall(in(b), x::AbstractArray)` (array.jl:2961) through `_findin(x, Set(b))` for every element type: the positions of the elements of `x` that are `==` to an element of `b`.",
    source := "base/array.jl:2961", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64153, #29124, #52639; see bugs/array-findall-in-array-isequal.yaml",
    prop := ``ArrayMembershipAgreement, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.ArrayFindallInArrayIsequal_refuted,
    notes := "expected refuted: the file states ¬ ArrayMembershipAgreement (theorem arrayMembershipAgreement_refuted); repro/array-findall-in-array-isequal.jl" },
  { id := "array-findall-in-sorted-isless", juliaFile := "base/array.jl",
    juliaFns := ["findall(pred::Fix2{typeof(in),<:Union{Array{<:Real},Real}}, x::Array{<:Real})",
      "_sortedfindin(v::Union{AbstractArray, Tuple}, w)"],
    statement := "`findall(in(b), x)` for `x::Array{<:Real}` and `b::Array{<:Real}` (array.jl:2952) for every `Real` element type (its `==`, `isless`, `hash` and `isequal` parameters; every float, integer, `Rational`, `BigFloat` or user `Real`): through the sorted merge `_sortedfindin` when both are sorted and `_findin` with set.jl's `Set` otherwise, the positions of the elements of `x` that are `==` to an element of `b`.",
    source := "base/array.jl:2952", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64153, #46222; see bugs/array-findall-in-sorted-isless.yaml",
    prop := ``SortedMembershipAgreement, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.ArrayFindallInSortedIsless_refuted,
    notes := "expected refuted: the file states ¬ SortedMembershipAgreement (theorem sortedMembershipAgreement_refuted); repro/array-findall-in-sorted-isless.jl" }
]
def entriesFindnext7 : List JuliaLean.Registry.Entry := [
  { id := "arrayops-findnext-start-below", juliaFile := "base/array.jl",
    juliaFns := ["findnext(predicate, A, start)", "findprev(predicate, A, start)"],
    statement := "`findnext(f, A, i)` and `findprev(f, A, i)` (array.jl:2470, 2666; docstrings at array.jl:2441-2469 and 2629-2665: \"Find the next index after or including `i` of an element of `A` for which `predicate` returns `true`, or `nothing` if not found\"; \"Find the previous index before or including `i` ...\") on a vector whose slots may be unassigned, for a start of every `Integer` type and every value: a start with no equal `Int` (the key type) raises `InexactError`; otherwise the forward search returns the least matching position at or after `i` and the backward search the greatest one at or before `i` (for every `i`, including starts before the first index and after the last), `nothing` when there is none, and `UndefRefError` when an unassigned slot is read before a match.",
    source := "base/array.jl:2441-2469, array.jl:2470", status := .refuted,
    prop := ``JuliaLean.Proofs.base.array.round4.FindAllStarts, thm := some ``JuliaLean.Proofs.base.array.round4.findAllStarts_refuted,
    issue := "#40120 open (duplicate); #54584 open (related); #33100 closed (related)",
    notes := "expected refuted: the file states ¬ FindAllStarts (theorem findAllStarts_refuted); repro/arrayops-findnext-start-below.jl" }
]
def entriesFindnext8 : List JuliaLean.Registry.Entry := [
  { id := "array-search-first-sound", juliaFile := "base/array.jl", juliaFns := ["findfirst(predicate, collection)"],
    statement := "A successful forward search returns a key of an element satisfying the predicate.", source := "base/array.jl:2484-2523,2680-2716 (docstrings)",
    status := .proven, prop := ``FirstSearchSound, thm := some ``firstSearchSound},
  { id := "array-search-first-complete", juliaFile := "base/array.jl", juliaFns := ["findfirst(predicate, collection)"],
    statement := "Forward search returns nothing exactly when no collection element satisfies the predicate.", source := "base/array.jl:2484-2523,2680-2716 (docstrings)",
    status := .proven, prop := ``FirstSearchComplete, thm := some ``firstSearchComplete},
  { id := "array-search-first-earliest", juliaFile := "base/array.jl", juliaFns := ["findfirst(predicate, collection)"],
    statement := "A successful forward search returns the first matching key in iteration order.", source := "base/array.jl:2484-2523,2680-2716 (docstrings)",
    status := .proven, prop := ``FirstSearchEarliest, thm := some ``firstSearchEarliest},
  { id := "array-search-last-sound", juliaFile := "base/array.jl", juliaFns := ["findlast(predicate, collection)"],
    statement := "A successful backward search returns a key of an element satisfying the predicate.", source := "base/array.jl:2484-2523,2680-2716 (docstrings)",
    status := .proven, prop := ``LastSearchSound, thm := some ``lastSearchSound},
  { id := "array-search-last-latest", juliaFile := "base/array.jl", juliaFns := ["findlast(predicate, collection)"],
    statement := "A successful backward search returns the last matching key in iteration order.", source := "base/array.jl:2484-2523,2680-2716 (docstrings)",
    status := .proven, prop := ``LastSearchLatest, thm := some ``lastSearchLatest}
]
def entriesFindnext9 : List JuliaLean.Registry.Entry := [
{ id := "array-findnext-identity-protocol", juliaFile := "base/array.jl",
  juliaFns := ["findnext(A, start)"],
  statement := "The identity-search overload forwards the identity predicate once to the method selected by the original collection type.",
  source := "base/array.jl:2399-2399", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion.FindnextIdentityProtocol, thm := some ``JuliaLean.Proofs.base.array.Completion.FindnextIdentityProtocol_proven,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." },
{ id := "array-findfirst-identity-protocol", juliaFile := "base/array.jl",
  juliaFns := ["findfirst(A)"],
  statement := "The identity-search overload forwards the identity predicate once to the method selected by the original collection type.",
  source := "base/array.jl:2436-2436", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion.FindfirstIdentityProtocol, thm := some ``JuliaLean.Proofs.base.array.Completion.FindfirstIdentityProtocol_proven,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." },
{ id := "array-findfirst-array-identity-protocol", juliaFile := "base/array.jl",
  juliaFns := ["findfirst(A::AbstractArray)"],
  statement := "Key discovery and its endpoint precede search, with failures preserving all preceding effects and suppressing later calls. Keys may be arbitrary.",
  source := "base/array.jl:2439-2439", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion.FindfirstArrayIdentityProtocol, thm := some ``JuliaLean.Proofs.base.array.Completion.FindfirstArrayIdentityProtocol_proven,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." },
{ id := "array-findfirst-array-predicate-protocol", juliaFile := "base/array.jl",
  juliaFns := ["findfirst(testf::Function, A::Union{AbstractArray, AbstractString})"],
  statement := "Key discovery and its endpoint precede search, with failures preserving all preceding effects and suppressing later calls. Keys may be arbitrary.",
  source := "base/array.jl:2526-2527", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion.FindfirstArrayPredicateProtocol, thm := some ``JuliaLean.Proofs.base.array.Completion.FindfirstArrayPredicateProtocol_proven,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." },
{ id := "array-findprev-identity-protocol", juliaFile := "base/array.jl",
  juliaFns := ["findprev(A, start)"],
  statement := "The identity-search overload forwards the identity predicate once to the method selected by the original collection type.",
  source := "base/array.jl:2586-2586", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion.FindprevIdentityProtocol, thm := some ``JuliaLean.Proofs.base.array.Completion.FindprevIdentityProtocol_proven,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." },
{ id := "array-findlast-identity-protocol", juliaFile := "base/array.jl",
  juliaFns := ["findlast(A)"],
  statement := "The identity-search overload forwards the identity predicate once to the method selected by the original collection type.",
  source := "base/array.jl:2624-2624", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion.FindlastIdentityProtocol, thm := some ``JuliaLean.Proofs.base.array.Completion.FindlastIdentityProtocol_proven,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." },
{ id := "array-findlast-array-identity-protocol", juliaFile := "base/array.jl",
  juliaFns := ["findlast(A::AbstractArray)"],
  statement := "Key discovery and its endpoint precede search, with failures preserving all preceding effects and suppressing later calls. Keys may be arbitrary.",
  source := "base/array.jl:2627-2627", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion.FindlastArrayIdentityProtocol, thm := some ``JuliaLean.Proofs.base.array.Completion.FindlastArrayIdentityProtocol_proven,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." },
{ id := "array-findlast-array-predicate-protocol", juliaFile := "base/array.jl",
  juliaFns := ["findlast(testf::Function, A::Union{AbstractArray, AbstractString})"],
  statement := "Key discovery and its endpoint precede search, with failures preserving all preceding effects and suppressing later calls. Keys may be arbitrary.",
  source := "base/array.jl:2719-2720", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion.FindlastArrayPredicateProtocol, thm := some ``JuliaLean.Proofs.base.array.Completion.FindlastArrayPredicateProtocol_proven,
  notes := "User-selected methods remain explicit operations at the original call sites. No callee correctness law is assumed." }
]
def entriesFindnext10 : List JuliaLean.Registry.Entry := [
{ id := "array-findnext-key-failures", juliaFile := "base/array.jl",
  juliaFns := ["findnext(testf::Function, A, start)"],
  statement := "Key discovery errors and divergence precede key conversion, element access and predicate evaluation. The iterator needs no finite rank or evaluation limit.",
  source := "base/array.jl:2470-2481", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion3.FindnextKeyFailures, thm := some ``JuliaLean.Proofs.base.array.Completion3.FindnextKeyFailures_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-findprev-key-failures", juliaFile := "base/array.jl",
  juliaFns := ["findprev(testf::Function, A, start)"],
  statement := "Key discovery errors and divergence precede key conversion, element access and predicate evaluation. The iterator needs no finite rank or evaluation limit.",
  source := "base/array.jl:2666-2677", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion3.FindprevKeyFailures, thm := some ``JuliaLean.Proofs.base.array.Completion3.FindprevKeyFailures_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.LegacyRetired

open JuliaLean.Registry
def entriesFindnext11 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-range-find-oneto", juliaFile := "base/array.jl", juliaFns := ["findfirst(p::Fix2{==/isequal}, r::OneTo)",
      "findfirst(::typeof(iszero), ::OneTo)", "findfirst(::typeof(isone), r::OneTo)"],
    statement := "For OneTo(n) with n <= typemax(Int), findfirst(==(x)), findfirst(isequal(x)) for any integer x, findfirst(iszero) and findfirst(isone) agree with the scan of collect(OneTo(n)).", source := "findfirst docstring base/array.jl:2489", status := .proven,
    prop := ``OneToFirstSearchSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.ArraySearchOnetoFirst_proven }
]
end JuliaLean.Proofs.base.array.LegacyRetired


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.LegacyRetired

open JuliaLean.Registry
def entriesFindnext12 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-range-find-bounds", juliaFile := "base/array.jl",
    juliaFns := ["findfirst(p::Fix2{==/isequal}, r::AbstractUnitRange{<:Integer})",
      "findfirst(p::Fix2{==/isequal}, r::StepRange{T,S})", "findfirst(::typeof(iszero), r::AbstractRange)",
      "findfirst(::typeof(isone), r::AbstractRange)", "findlast(p, r::AbstractUnitRange{<:Integer})",
      "findlast(p, r::StepRange{T,S})"],
    statement := "On unit and step ranges, findfirst/findlast with ==(x), isequal(x), iszero or isone return nothing for an empty range and for x outside [minimum(r), maximum(r)], never report a value between the endpoints of a unit range as missing, findlast equals findfirst, and iszero/isone search for zero/one of the element type.",
    source := "findfirst docstring base/array.jl:2489; comment base/array.jl:2727", status := .proven,
    prop := ``RangeSearchBounds, thm := some ``rangeSearchBounds,
    notes := "The scan contract itself is refuted by ranges-operations-findfirst-overflow. Bounds and routing are generic over endpoint, target, step, remainder, quotient and key types; the primitive integer comparisons obey their semantic value laws." }
]
end JuliaLean.Proofs.base.array.LegacyRetired


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array
def entriesFindnext13 : List JuliaLean.Registry.Entry := [
{ id := "array-scalar-findall-effects", juliaFile := "base/array.jl",
    juliaFns := ["findall(testf::Function, x::Number)"],
    statement := "Scalar findall observes the predicate once. Its errors and non-Bool TypeError preserve predicate effects without allocating a result; a Bool result produces a fresh valid Int vector containing exactly key 1 when true and no keys when false, preserving existing array headers and memory records after predicate effects.",
    source := "base/array.jl:2852; base/array.jl:2733–2783,2795–2832; base/number.jl:93,99; doc/src/manual/control-flow.md:180–207" , status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group14.FindallNumberEffectsAndAllocation, thm := none,
    notes := "All predicate observations and states are quantified, with no correctness law. Uses actual shared-store allocation/store models. Fresh array identity is required; fresh empty backing Memory is not promised." },
{ id := "array-scalar-findall-boundary-errors", juliaFile := "base/array.jl",
    juliaFns := ["findall(testf::Function, x::Number)", "findall(p::Fix2{typeof(in)}, x::Number)"],
    statement := "For every typed runtime state and predicate or membership operation, scalar findall preserves that operation's effects and propagates its error; a successful non-Bool return raises TypeError before any allocation or assignment. No allocator, membership or predicate correctness law is assumed.",
    source := "base/array.jl:2852–2853; doc/src/manual/control-flow.md:180–207; condition-error and state-retention invariant" , status := .proven,
    prop := ``JuliaLean.Proofs.base.array.Models1Group14.ScalarFindallBoundaryErrors,
    thm := some ``JuliaLean.Proofs.base.array.Models1Group14.scalarFindallBoundaryErrors_proven,
    notes := "The full typed-boundary error invariant supplements the concrete fresh-result allocation properties. Some Bool outcomes impose no unsupported law on arbitrary runtime allocators." },
{ id := "array-scalar-membership-findall-effects", juliaFile := "base/array.jl",
    juliaFns := ["findall(p::Fix2{typeof(in)}, x::Number)"],
    statement := "Scalar membership findall observes membership once, propagates its errors and non-Bool TypeError with effects intact, and otherwise returns a fresh valid Int vector with exactly the selected scalar key while preserving pre-existing array headers and memory records after membership effects.",
    source := "base/array.jl:2853; base/array.jl:2733–2783,2795–2832; base/number.jl:93,99; doc/src/manual/control-flow.md:180–207" , status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group14.FindallInNumberEffectsAndAllocation, thm := none,
    notes := "Membership remains the existing user-extensible interface. No Set/membership correctness law is assumed; all Bool/non-Bool/exception outcomes are included." }
]
def entriesFindnext14 : List JuliaLean.Registry.Entry := [
{ id := "array-findall-deferred-construction", juliaFile := "base/array.jl",
    juliaFns := ["findall(testf::Function, A)"],
    statement := "Generic predicate findall propagates failures and divergence in pair construction, type discovery and chosen result allocation before deferred element callbacks run. Exceptions retain their exact error channel, payload and mutation state. The statement quantifies all typed collections, arbitrary keys, user errors, runtime interfaces and states, with no finite-iteration restriction or callee correctness law.",
    source := "base/array.jl:2784-2787,684-694,821-853; deferred generator and allocation/error ordering",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group14.FindallDeferredConstructionInvariant,
    thm := none,
    notes := "Uses actual Filter/Generator iteration and typed/generic collect bodies, with growFirst/pushWiden and native Vector allocation/push/sizehint/append/copy bodies. General looping uses the installed Exec flat partial-fixpoint domain. Compiler/type operations and Storage primitives retain their explicit baseline boundary. Unchecked because Lean cannot initialize in this executor." },
{ id := "array-findall-repeated-keys", juliaFile := "base/array.jl",
    juliaFns := ["findall(testf::Function, A)"],
    statement := "When generic findall chooses its bottom-inferred typed branch, default_eltype preserves repeated evaluation of keys(A): failure of the second call, and of the third call after a Generator-valued first result and successful function-field observation, is propagated with the exact resulting state. Calls are not shared or hoisted.",
    source := "base/array.jl:2784-2787,821-831; macro argument evaluation and error ordering",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group14.FindallRepeatedKeysInvariant,
    thm := none,
    notes := "Every current typed interface and state is quantified. A returned Keys value may change between evaluations; the function-field interface retains errors. Existing compiler/type operations remain explicit runtime interfaces; no property assumes their correctness. Unchecked." },
{ id := "array-findall-bool-array-boundary", juliaFile := "base/array.jl",
    juliaFns := ["findall(A::AbstractArray{Bool})"],
    statement := "For every Bool-array interface and full mutable world, findall observes count, keys and the actual key object's element type before native result allocation, then constructs its live pairs iterator. The first error in any initial phase is returned with exactly its preceding effects. Every successful result is the vector allocated with that key type and native count.",
    source := "base/array.jl:2838-2849; base/array.jl:2793-2803; doc/src/manual/interfaces.md:9-54",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group14.BoolArrayFindallBoundaryInvariant,
    thm := none,
    notes := "Independent phase/error and result-handle invariant over arbitrary shared state and custom interfaces, with no count-consistency or no-alias premise. The body uses actual arrayUndef1 and typed Array stores. Count is the existing native-Int boundary; keys, type discovery and live pair iteration remain explicitly documented interfaces rather than claimed complete callee models." },
{ id := "array-pair-search-construction", juliaFile := "base/array.jl",
    juliaFns := ["findfirst(testf::Function, A)", "findlast(testf::Function, A)"],
    statement := "Generic first/last searches propagate pair-construction errors with the exact resulting state before testing any element. Last-search also preserves pair effects before propagating a reverse-iterator-construction error. All typed runtime operations and states are quantified without callee correctness laws.",
    source := "base/array.jl:2518-2523,2711-2716; initial error/effect invariants",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.array.Models1Group14.PairSearchConstructionInvariant,
    thm := some ``JuliaLean.Proofs.base.array.Models1Group14.pairSearchConstructionInvariant_proven,
    notes := "pairs, reverse-iterator construction, iteration, and checked Boolean predicates remain the existing explicit user/collection interfaces. Actual existing search loops are reused." },
{ id := "array-pair-search-selection", juliaFile := "base/array.jl",
    juliaFns := ["findfirst(testf::Function, A)", "findlast(testf::Function, A)"],
    statement := "For every machine-sized finite sequence of pairs with arbitrary keys and a pure Boolean predicate, generic first/last search returns the first/last matching key, or nothing when no pair matches.",
    source := "base/array.jl:2483-2523,2679-2716; documented first/last matching-key contracts",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group14.PairSearchFiniteSelectionSpec,
    thm := none,
    notes := "Supplementary concrete List/Except interface instance; mathematical filtering gives the expected answer. The separate construction invariants cover effects/errors in the generic boundary." }
]
end JuliaLean.Proofs.base.array

