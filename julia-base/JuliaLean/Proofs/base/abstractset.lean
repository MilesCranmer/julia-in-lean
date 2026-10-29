import JuliaLean.base.abstractset
import JuliaLean.Registry.Types

/-!
# Properties of `base/abstractset.jl`

The statements specify the public set contracts and the observable invariants of the
source-mirrored methods. Collection operations from other Base files remain typed interface inputs.
-/

namespace JuliaLean.Proofs.base.abstractset

open JuliaLean JuliaLean.base.abstractset JuliaLean.base.int JuliaLean.Registry

/-! ## Independent collection specifications -/

def HasMember {α : Type} (o : Calls α) (s : o.C) (x : α) : Prop :=
  o.member s x = .ok true

def HasElement {α : Type} (o : Calls α) (xs : List α) (x : α) : Bool :=
  xs.any (fun y => o.equal y x)

def HasCollectionElement {α : Type} (o : Calls α) (s : o.C) (x : α) : Prop :=
  HasElement o (o.elements s) x = true

def SubsetByMembership {α : Type} (o : Calls α) (a b : o.C) : Prop :=
  ∀ x, HasMember o a x → HasMember o b x

def EqualByMembership {α : Type} (o : Calls α) (a b : o.C) : Prop :=
  ∀ x, HasMember o a x ↔ HasMember o b x

def ProperSubsetByMembership {α : Type} (o : Calls α) (a b : o.C) : Prop :=
  SubsetByMembership o a b ∧ ¬ EqualByMembership o a b

def DisjointByMembership {α : Type} (o : Calls α) (a b : o.C) : Prop :=
  ∀ x, HasCollectionElement o a x → o.member b x = .ok false

def CollectionsOverlap {α : Type} (o : Calls α) (a b : o.C) : Prop :=
  ∃ x, HasCollectionElement o a x ∧ HasCollectionElement o b x

def distinctCount {α : Type} (equal : α → α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => if xs.any (fun y => equal x y) then distinctCount equal xs
      else 1 + distinctCount equal xs

def anyCollectionMember {α : Type} (o : Calls α) (sets : List o.C) (x : α) :
    Except o.Error Bool :=
  match sets with
  | [] => pure false
  | s :: rest => do
      if ← o.member s x then pure true else anyCollectionMember o rest x

def allCollectionMember {α : Type} (o : Calls α) (sets : List o.C) (x : α) :
    Except o.Error Bool :=
  match sets with
  | [] => pure true
  | s :: rest => do
      if ← o.member s x then allCollectionMember o rest x else pure false

def xorCollectionMember {α : Type} (o : Calls α) (sets : List o.C) (x : α) :
    Except o.Error Bool :=
  match sets with
  | [] => pure false
  | s :: rest => do
      let here ← o.member s x
      let later ← xorCollectionMember o rest x
      pure (here != later)

def xorSetifiedMembers {α : Type} (o : Calls α) (sets : List o.C) (x : α) :
    Except o.Error Bool :=
  match sets with
  | [] => pure false
  | s :: rest => do
      let set ← if o.isAbstractSet s then pure s else o.makeSet s
      let here ← o.member set x
      let later ← xorSetifiedMembers o rest x
      pure (here != later)

def SameMembers {α : Type} (o : Calls α) (a b : o.C) : Prop :=
  ∀ x, o.member a x = o.member b x

def SameOutcome {α : Type} (o : Calls α) (a b : Except o.Error o.C) : Prop :=
  match a, b with
  | .error e, .error f => e = f
  | .ok x, .ok y => SameMembers o x y
  | _, _ => False

def pushAll {α : Type} (o : Calls α) (items : List α) (s : o.C) : Except o.Error o.C :=
  match items with
  | [] => pure s
  | x :: xs => do
      let s ← o.push s x
      pushAll o xs s

def stableUnique {α : Type} (equal : α → α → Bool) (items : List α) : List α :=
  items.foldl (fun kept x =>
    if kept.any (fun y => equal y x) then kept else kept ++ [x]) []

inductive SubsequenceBy {α : Type} (equal : α → α → Bool) : List α → List α → Prop where
  | nil (ys : List α) : SubsequenceBy equal [] ys
  | skip {x : α} {xs ys : List α} :
      SubsequenceBy equal xs ys → SubsequenceBy equal xs (x :: ys)
  | keep {x y : α} {xs ys : List α} :
      equal x y = true → SubsequenceBy equal xs ys → SubsequenceBy equal (x :: xs) (y :: ys)

def VectorUnionBangOrderLaw {α : Type} (o : Calls α) (isArray : o.C → Bool)
    (isequal : α → α → Bool) (unionBang : o.C → List o.C → Except o.Error o.C) : Prop :=
  (∀ s T out, isArray s = true → o.emptyMutable s T = .ok out →
    isArray out = true ∧ o.elements out = []) ∧
  (∀ out inputs result, isArray out = true → unionBang out inputs = .ok result →
    o.elements result = stableUnique isequal (o.elements out ++ inputs.flatMap o.elements))

def VectorSymdiffBangOrderLaw {α : Type} (o : Calls α) (isArray : o.C → Bool)
    (isequal : α → α → Bool) (symdiffBang : o.C → List o.C → Except o.Error o.C) : Prop :=
  (∀ s T out, isArray s = true → o.emptyMutable s T = .ok out →
    isArray out = true ∧ o.elements out = []) ∧
  (∀ out inputs result, isArray out = true → symdiffBang out inputs = .ok result →
    SubsequenceBy isequal (o.elements result)
      (o.elements out ++ inputs.flatMap o.elements))

def VectorCopyOrderLaw {α : Type} (o : Calls α) (isArray : o.C → Bool) : Prop :=
  ∀ s result, isArray s = true → o.copy s = .ok result →
    isArray result = true ∧ o.elements result = o.elements s

def maxValuesCapacity : JuliaType → Int
  | .other => IntTy.max .i64
  | .bitInteger t => if BitIntegerSmall t then Int.ofNat (2 ^ t.bits) else IntTy.max .i64
  | .bool => 2
  | .nothing => 1
  | .union a b => min (maxValuesCapacity a + maxValuesCapacity b) (IntTy.max .i64)

def AddWithOverflowLaw (add : I64 → I64 → I64 × Bool) : Prop :=
  ∀ a b, 0 ≤ a.val → 0 ≤ b.val →
    (add a b).2 = decide (IntTy.max .i64 < a.val + b.val) ∧
    ((add a b).2 = false → (add a b).1.val = a.val + b.val)

def MaxValuesCapacity : Prop :=
  ∀ add T, AddWithOverflowLaw add → (maxValuesDispatch add T).val = maxValuesCapacity T

def ArrayOrderSpec : Prop :=
  ∀ (α : Type) (o : Calls α) (isArray : o.C → Bool) (isequal : α → α → Bool)
    (unionBang symdiffBang : o.C → List o.C → Except o.Error o.C),
    VectorUnionBangOrderLaw o isArray isequal unionBang →
    VectorSymdiffBangOrderLaw o isArray isequal symdiffBang →
    VectorCopyOrderLaw o isArray →
    (∀ s sets result, isArray s = true → o.isAbstractSet s = false →
      unionGeneric o unionBang s sets = .ok result →
      o.elements result = stableUnique isequal (o.elements s ++ sets.flatMap o.elements)) ∧
    (∀ s result, isArray s = true → o.isAbstractSet s = false →
      intersectUnary o unionBang s = .ok result →
      o.elements result = stableUnique isequal (o.elements s)) ∧
    (∀ s result, isArray s = true → o.isAbstractSet s = false →
      setdiffUnary o unionBang s = .ok result →
      o.elements result = stableUnique isequal (o.elements s)) ∧
    (∀ s sets result, isArray s = true → o.isAbstractSet s = false →
      symdiffGeneric o symdiffBang s sets = .ok result →
      SubsequenceBy isequal (o.elements result)
        (o.elements s ++ sets.flatMap o.elements)) ∧
    (∀ s result, isArray s = true → o.isAbstractSet s = false →
      symdiffAbstractSetUnary o symdiffBang s = .ok result →
      SubsequenceBy isequal (o.elements result) (o.elements s))


section
open JuliaLean JuliaLean.base.abstractset JuliaLean.base.int

/-- Stored elements, with the common equality chosen by the participating collections. -/
abbrev Stored {α : Type} (o : Calls α) (s : o.C) (x : α) : Prop := x ∈ o.elements s

def Included {α : Type} (o : Calls α) (a b : o.C) : Prop :=
  ∀ x, Stored o a x → Stored o b x

def SameStored {α : Type} (o : Calls α) (a b : o.C) : Prop :=
  ∀ x, Stored o a x ↔ Stored o b x

/-- The collection protocol on a common equality domain. All contents laws are conditional
on a successful primitive call, so conversion and allocation errors remain possible. -/
structure CollectionLaws {α : Type} [DecidableEq α] (o : Calls α) where
  size : o.C → I64
  length : ∀ s, o.length s = .ok (size s)
  intLength : ∀ n, o.intLength n = .ok n
  member : ∀ s x, o.member s x = .ok (decide (Stored o s x))
  equality : ∀ x y, o.equal x y = decide (x = y)
  setNodup : ∀ s, o.isAbstractSet s = true → (o.elements s).Nodup
  push : ∀ s x r, o.push s x = .ok r →
    (∀ z, Stored o r z ↔ z = x ∨ Stored o s z) ∧
    (o.isAbstractSet s = true → o.isAbstractSet r = true)
  pushTarget : ∀ s x r, o.push s x = .ok r → o.isAbstractSet r = true
  delete : ∀ s x r, o.delete s x = .ok r →
    (∀ z, Stored o r z ↔ Stored o s z ∧ z ≠ x) ∧
    (o.isAbstractSet s = true → o.isAbstractSet r = true)
  empty : ∀ s r, o.empty s = .ok r →
    (∀ z, ¬ Stored o r z) ∧ (o.isAbstractSet s = true → o.isAbstractSet r = true)
  emptyMutable : ∀ s T r, o.emptyMutable s T = .ok r →
    (∀ z, ¬ Stored o r z) ∧ (o.isAbstractSet s = true → o.isAbstractSet r = true)
  emptyDefault : ∀ s r, o.emptyMutableDefault s = .ok r →
    (∀ z, ¬ Stored o r z) ∧ (o.isAbstractSet s = true → o.isAbstractSet r = true)
  copy : ∀ s r, o.copy s = .ok r → SameStored o r s ∧
    (o.isAbstractSet s = true → o.isAbstractSet r = true)
  copyMutable : ∀ s r, o.copyMutable s = .ok r → SameStored o r s ∧
    (o.isAbstractSet s = true → o.isAbstractSet r = true)
  hint : ∀ s n shrink r, o.sizehint s n shrink = .ok r → SameStored o r s ∧
    (o.isAbstractSet s = true → o.isAbstractSet r = true)
  makeSet : ∀ s r, o.makeSet s = .ok r → SameStored o r s ∧ o.isAbstractSet r = true
  filter : ∀ pred s r, o.filterBang pred s = .ok r →
    (∀ x, Stored o r x ↔ Stored o s x ∧ pred x = .ok true) ∧
    (o.isAbstractSet s = true → o.isAbstractSet r = true)
  cardinalBound : ∀ a b, o.isAbstractSet a = true → Included o a b →
    (size a).val ≤ (size b).val
  cardinalEqual : ∀ a b, o.isAbstractSet a = true → o.isAbstractSet b = true →
    Included o a b → (size a).val = (size b).val → SameStored o a b
  cardinality : ∀ s xs, o.isAbstractSet s = true →
    (∀ x, Stored o s x ↔ x ∈ xs) →
    o.length s = .ok (int (Int.ofNat (distinctCount o.equal xs)))
  cardinalCover : ∀ (s : o.C) (domain : List α), o.isAbstractSet s = true → domain.Nodup →
    (∀ x, Stored o s x → x ∈ domain) → (size s).val = Int.ofNat domain.length →
    ∀ x ∈ domain, Stored o s x
  findmin : ∀ xs n k, o.findminLength xs = .ok (n, k) →
    ∃ before selected after, xs = before ++ selected :: after ∧ k = before.length + 1
  getindex : ∀ before selected after,
    o.getindex (before ++ selected :: after) (before.length + 1) = .ok selected
  setindex : ∀ before selected after replacement,
    o.setindex (before ++ selected :: after) replacement (before.length + 1) =
      .ok (before ++ replacement :: after)

/-- Either the represented element domain has exactly the computed capacity, or all
AbstractSet states under consideration stay strictly below that capacity. The generic
union contract without this premise is refuted by `dicts-union-max-values-break`. -/
def CapacityPremise {α : Type} [DecidableEq α] (o : Calls α) (L : CollectionLaws o) : Prop :=
  ∀ T itr, o.subtype (o.elementType itr) T = true →
    (∃ domain : List α, domain.Nodup ∧
      Int.ofNat domain.length = (maxValuesDispatch o.addWithOverflow T).val ∧
      ∀ x, x ∈ domain) ∨
    (∀ s, o.isAbstractSet s = true → (L.size s).val < (maxValuesDispatch o.addWithOverflow T).val)

theorem bool_finite_capacity (add : I64 → I64 → I64 × Bool) :
    ∃ domain : List Bool, domain.Nodup ∧
      Int.ofNat domain.length = (maxValuesDispatch add .bool).val ∧ ∀ x, x ∈ domain := by
  refine ⟨[false, true], by decide, rfl, ?_⟩
  intro x
  cases x <;> decide

theorem capacity_complete {α : Type} [DecidableEq α] (o : Calls α) (L : CollectionLaws o)
    (H : CapacityPremise o L) (T : JuliaType) (s itr : o.C)
    (hs : o.isAbstractSet s = true) (ht : o.subtype (o.elementType itr) T = true)
    (he : L.size s = maxValuesDispatch o.addWithOverflow T) : Included o itr s := by
  rcases H T itr ht with ⟨domain, hn, hlen, hu⟩ | hbelow
  · intro x hx
    exact L.cardinalCover s domain hs hn (fun z _ => hu z)
      (by rw [he]; exact hlen.symm) x (hu x)
  · have hb := hbelow s hs
    have hv := congrArg Subtype.val he
    omega

 theorem bind_ok {E A B : Type} (m : Except E A) (f : A → Except E B) (r : B)
    (h : m.bind f = .ok r) : ∃ a, m = .ok a ∧ f a = .ok r := by
  cases m with
  | error e => contradiction
  | ok a => exact ⟨a, rfl, h⟩

theorem stored_member {α : Type} [DecidableEq α] (o : Calls α) (L : CollectionLaws o)
    (s : o.C) (x : α) : o.member s x = .ok true ↔ Stored o s x := by
  simp [L.member]


end


section
open JuliaLean JuliaLean.base.abstractset JuliaLean.base.int

variable {α : Type} [DecidableEq α] (o : Calls α) (L : CollectionLaws o)
include L

def UnionOutput (s : o.C) (xs : List α) (r : o.C) : Prop :=
  (∀ z, Stored o r z ↔ Stored o s z ∨ z ∈ xs) ∧
  (o.isAbstractSet s = true → o.isAbstractSet r = true)

theorem unionLoop_spec (H : CapacityPremise o L) (T : JuliaType) (itr : o.C) (xs : List α)
    (hxs : xs.Subset (o.elements itr)) (s r : o.C)
    (h : unionBangIteratorLoop o T itr xs s = .ok r) : UnionOutput o s xs r := by
  induction xs generalizing s r with
  | nil =>
    simp [unionBangIteratorLoop, pure, Except.pure] at h
    subst r
    exact ⟨by simp [Stored], id⟩
  | cons a xs ih =>
    cases hp : o.push s a with
    | error e => simp [unionBangIteratorLoop, hp, bind, Except.bind] at h
    | ok p =>
      obtain ⟨hmem, hset⟩ := L.push s a p hp
      simp only [unionBangIteratorLoop, hp, bind, Except.bind] at h
      by_cases ht : o.subtype (o.elementType itr) T = true
      · simp only [ht, ite_true, L.length] at h
        by_cases hf : L.size p == maxValuesDispatch o.addWithOverflow T
        · simp only [hf, ite_true, pure, Except.pure, Except.ok.injEq] at h
          subst r
          have hfull := capacity_complete o L H T p itr (L.pushTarget s a p hp) ht (Subtype.ext (by simpa using hf))
          refine ⟨?_, hset⟩
          intro z
          have hr : z ∈ xs → Stored o p z := fun hz => hfull z (hxs (by simp [hz]))
          have hh := hmem z
          simp only [List.mem_cons]
          grind
        · simp only [hf, Bool.false_eq_true, ite_false] at h
          obtain ⟨hm, hs⟩ := ih (fun z hz => hxs (by simp [hz])) p r h
          refine ⟨?_, fun hs0 => hs (hset hs0)⟩
          intro z
          have hmz := hm z
          have hpz := hmem z
          simp only [List.mem_cons]
          grind
      · simp only [ht, ite_false] at h
        obtain ⟨hm, hs⟩ := ih (fun z hz => hxs (by simp [hz])) p r h
        refine ⟨?_, fun hs0 => hs (hset hs0)⟩
        intro z
        have hmz := hm z
        have hpz := hmem z
        simp only [List.mem_cons]
        grind

theorem unionIterator_spec (H : CapacityPremise o L) (T : JuliaType) (s itr r : o.C)
    (h : unionBangAbstractSetIterator o T s itr = .ok r) :
    UnionOutput o s (o.elements itr) r := by
  unfold unionBangAbstractSetIterator at h
  by_cases hl : o.hasLength itr = true
  · simp only [hl, ite_true, L.length, L.intLength, bind, Except.bind] at h
    cases hh : o.sizehint s (L.size s + L.size itr) false with
    | error e => simp [hh, bind, Except.bind] at h
    | ok p =>
      simp only [hh, bind, Except.bind] at h
      obtain ⟨hm, hs⟩ := unionLoop_spec o L H T itr (o.elements itr) (fun _ h => h) p r h
      obtain ⟨hp, hset⟩ := L.hint s _ false p hh
      exact ⟨fun z => (hm z).trans (or_congr (hp z) Iff.rfl), fun hz => hs (hset hz)⟩
  · simp only [hl, ite_false, pure, Except.pure, bind, Except.bind] at h
    exact unionLoop_spec o L H T itr (o.elements itr) (fun _ h => h) s r h

theorem unionMany_spec (H : CapacityPremise o L) (sets : List o.C) (s r : o.C)
    (h : unionBangAbstractSetMany o s sets = .ok r) :
    UnionOutput o s (sets.flatMap o.elements) r := by
  unfold unionBangAbstractSetMany at h
  induction sets generalizing s r with
  | nil =>
    simp [unionBangManyLoop, pure, Except.pure] at h
    subst r
    exact ⟨by simp [Stored], id⟩
  | cons itr rest ih =>
    obtain ⟨p, hp, hr⟩ := bind_ok _ _ r h
    obtain ⟨hm, hs⟩ := unionIterator_spec o L H (o.elementType s) s itr p hp
    obtain ⟨hm2, hs2⟩ := ih p r hr
    refine ⟨?_, fun ha => hs2 (hs ha)⟩
    intro z
    have h1 := hm z
    have h2 := hm2 z
    simp only [List.flatMap_cons, List.mem_append]
    grind

theorem deleteLoop_spec (xs : List α) (s r : o.C)
    (h : setdiffBangIteratorLoop o s xs = .ok r) :
    (∀ z, Stored o r z ↔ Stored o s z ∧ z ∉ xs) ∧
    (o.isAbstractSet s = true → o.isAbstractSet r = true) := by
  induction xs generalizing s r with
  | nil =>
    simp [setdiffBangIteratorLoop, pure, Except.pure] at h
    subst r
    exact ⟨by simp, id⟩
  | cons a xs ih =>
    obtain ⟨p, hp, hr⟩ := bind_ok _ _ r h
    obtain ⟨hm, hs⟩ := L.delete s a p hp
    obtain ⟨hm2, hs2⟩ := ih p r hr
    refine ⟨?_, fun ha => hs2 (hs ha)⟩
    intro z
    have h1 := hm z
    have h2 := hm2 z
    simp only [List.mem_cons]
    grind

theorem deleteMany_spec (sets : List o.C) (s r : o.C)
    (h : setdiffBangAbstractSetMany o s sets = .ok r) :
    (∀ z, Stored o r z ↔ Stored o s z ∧ z ∉ sets.flatMap o.elements) ∧
    (o.isAbstractSet s = true → o.isAbstractSet r = true) := by
  unfold setdiffBangAbstractSetMany at h
  induction sets generalizing s r with
  | nil =>
    simp [setdiffBangManyLoop, pure, Except.pure] at h
    subst r
    exact ⟨by simp, id⟩
  | cons itr rest ih =>
    obtain ⟨p, hp, hr⟩ := bind_ok _ _ r h
    obtain ⟨hm, hs⟩ := deleteLoop_spec o L (o.elements itr) s p hp
    obtain ⟨hm2, hs2⟩ := ih p r hr
    refine ⟨?_, fun ha => hs2 (hs ha)⟩
    intro z
    have h1 := hm z
    have h2 := hm2 z
    simp only [List.flatMap_cons, List.mem_append]
    grind

theorem subsetElements_spec (b : o.C) (xs : List α) :
    issubsetElements o b xs = .ok (decide (∀ x ∈ xs, Stored o b x)) := by
  induction xs with
  | nil => simp [issubsetElements, pure, Except.pure]
  | cons a xs ih =>
    simp only [issubsetElements, L.member, bind, Except.bind]
    by_cases ha : Stored o b a <;> simp [ha, ih, pure, Except.pure]


end


section
open JuliaLean JuliaLean.base.abstractset JuliaLean.base.int
variable {α : Type} [DecidableEq α] (o : Calls α) (L : CollectionLaws o)
include L

theorem mapfilterPush_spec (pred : α → Except o.Error Bool) (xs : List α) (s r : o.C)
    (h : mapfilterLoop o pred o.push xs s = .ok r) :
    (∀ z, Stored o r z ↔ Stored o s z ∨ (z ∈ xs ∧ pred z = .ok true)) ∧
    (o.isAbstractSet s = true → o.isAbstractSet r = true) := by
  induction xs generalizing s r with
  | nil =>
    simp [mapfilterLoop, pure, Except.pure] at h
    subst r
    exact ⟨by simp, id⟩
  | cons a xs ih =>
    cases he : pred a with
    | error e => simp [mapfilterLoop, he, bind, Except.bind] at h
    | ok accepted =>
      cases accepted with
      | false =>
        simp only [mapfilterLoop, he, bind, Except.bind, Bool.false_eq_true, ite_false] at h
        obtain ⟨hm, hs⟩ := ih s r h
        refine ⟨?_, hs⟩
        intro z
        have hz := hm z
        simp only [List.mem_cons]
        grind
      | true =>
        simp only [mapfilterLoop, he, bind, Except.bind, ite_true] at h
        obtain ⟨p, hp, hr⟩ := bind_ok _ _ r h
        obtain ⟨hm, hs⟩ := L.push s a p hp
        obtain ⟨hm2, hs2⟩ := ih p r hr
        refine ⟨?_, fun ha => hs2 (hs ha)⟩
        intro z
        have h1 := hm z
        have h2 := hm2 z
        simp only [List.mem_cons]
        grind

theorem mapfilterDelete_spec (pred : α → Except o.Error Bool) (xs : List α) (s r : o.C)
    (h : mapfilterLoop o pred o.delete xs s = .ok r) :
    (∀ z, Stored o r z ↔ Stored o s z ∧ ¬ (z ∈ xs ∧ pred z = .ok true)) ∧
    (o.isAbstractSet s = true → o.isAbstractSet r = true) := by
  induction xs generalizing s r with
  | nil =>
    simp [mapfilterLoop, pure, Except.pure] at h
    subst r
    exact ⟨by simp, id⟩
  | cons a xs ih =>
    cases he : pred a with
    | error e => simp [mapfilterLoop, he, bind, Except.bind] at h
    | ok accepted =>
      cases accepted with
      | false =>
        simp only [mapfilterLoop, he, bind, Except.bind, Bool.false_eq_true, ite_false] at h
        obtain ⟨hm, hs⟩ := ih s r h
        refine ⟨?_, hs⟩
        intro z
        have hz := hm z
        simp only [List.mem_cons]
        grind
      | true =>
        simp only [mapfilterLoop, he, bind, Except.bind, ite_true] at h
        obtain ⟨p, hp, hr⟩ := bind_ok _ _ r h
        obtain ⟨hm, hs⟩ := L.delete s a p hp
        obtain ⟨hm2, hs2⟩ := ih p r hr
        refine ⟨?_, fun ha => hs2 (hs ha)⟩
        intro z
        have h1 := hm z
        have h2 := hm2 z
        simp only [List.mem_cons]
        grind

theorem symdiffLoop_spec (xs : List α) (hn : xs.Nodup) (s r : o.C)
    (h : symdiffBangSetLoop o s xs = .ok r) :
    (∀ z, Stored o r z ↔ (Stored o s z ∧ z ∉ xs) ∨ (¬ Stored o s z ∧ z ∈ xs)) ∧
    (o.isAbstractSet s = true → o.isAbstractSet r = true) := by
  induction xs generalizing s r with
  | nil =>
    simp [symdiffBangSetLoop, pure, Except.pure] at h
    subst r
    exact ⟨by simp, id⟩
  | cons a xs ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [symdiffBangSetLoop, L.member, bind, Except.bind] at h
    by_cases ha : Stored o s a
    · simp only [ha, decide_true, ite_true] at h
      obtain ⟨p, hp, hr⟩ := bind_ok _ _ r h
      obtain ⟨hm, hs⟩ := L.delete s a p hp
      obtain ⟨hm2, hs2⟩ := ih hn'.2 p r hr
      refine ⟨?_, fun hz => hs2 (hs hz)⟩
      intro z
      have h1 := hm z
      have h2 := hm2 z
      simp only [List.mem_cons]
      grind
    · simp only [ha, decide_false, Bool.false_eq_true, ite_false] at h
      obtain ⟨p, hp, hr⟩ := bind_ok _ _ r h
      obtain ⟨hm, hs⟩ := L.push s a p hp
      obtain ⟨hm2, hs2⟩ := ih hn'.2 p r hr
      refine ⟨?_, fun hz => hs2 (hs hz)⟩
      intro z
      have h1 := hm z
      have h2 := hm2 z
      simp only [List.mem_cons]
      grind

end


section
open JuliaLean JuliaLean.base.abstractset JuliaLean.base.int
variable {α : Type} [DecidableEq α] (o : Calls α) (L : CollectionLaws o)
include L

theorem subsetSetRight_spec (a b : o.C) (r : Bool)
    (h : issubsetSetRight o a b = .ok r) : (r = true ↔ Included o a b) := by
  unfold issubsetSetRight at h
  simp only [L.length, bind, Except.bind] at h
  split at h
  · split at h
    · rename_i ht
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
      have hn : ¬ Included o a b := by
        intro hi
        have hb := L.cardinalBound a b ht.1 hi
        have hgt : (L.size b).val < (L.size a).val := ht.2
        omega
      simp [pure, Except.pure] at h
      subst r
      simp [hn]
    · rw [subsetElements_spec o L] at h
      rw [← Except.ok.inj h]
      simp [Included, Stored]
  · rw [subsetElements_spec o L] at h
    rw [← Except.ok.inj h]
    simp [Included, Stored]

theorem subset_spec (a b : o.C) (r : Bool)
    (h : issubset o a b = .ok r) : (r = true ↔ Included o a b) := by
  unfold issubset at h
  simp only [L.length, bind, Except.bind] at h
  split at h
  · split at h
    · rename_i ht
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
      have hn : ¬ Included o a b := by
        intro hi
        have hb := L.cardinalBound a b ht.1 hi
        have hgt : (L.size b).val < (L.size a).val := ht.2
        omega
      simp [pure, Except.pure] at h
      subst r
      simp [hn]
    · split at h
      · obtain ⟨p, hp, hr⟩ := bind_ok _ _ r h
        have hm : ∀ x, Stored o p x ↔ Stored o b x := (L.makeSet b p hp).1
        have hh := subsetSetRight_spec o L a p r hr
        simpa only [Included, hm] using hh
      · rw [subsetElements_spec o L] at h
        rw [← Except.ok.inj h]
        simp [Included, Stored]
  · rw [subsetElements_spec o L] at h
    rw [← Except.ok.inj h]
    simp [Included, Stored]

theorem equality_spec (a b : o.C) (ha : o.isAbstractSet a = true)
    (hb : o.isAbstractSet b = true) (r : Bool)
    (h : setEqualAbstractSet o a b = .ok r) : (r = true ↔ SameStored o a b) := by
  unfold setEqualAbstractSet at h
  simp only [L.length, bind, Except.bind] at h
  split at h
  · rename_i he
    have hs := subset_spec o L a b r h
    have heq : (L.size a).val = (L.size b).val := by simpa using he
    constructor
    · intro hr
      exact L.cardinalEqual a b ha hb (hs.mp hr) heq
    · intro hm
      exact hs.mpr (fun x hx => (hm x).mp hx)
  · rename_i he
    simp [pure, Except.pure] at h
    subst r
    have hn : ¬ SameStored o a b := by
      intro hm
      have h1 := L.cardinalBound a b ha (fun x hx => (hm x).mp hx)
      have h2 := L.cardinalBound b a hb (fun x hx => (hm x).mpr hx)
      have hv : L.size a = L.size b := Subtype.ext (by omega)
      exact he (by simpa using congrArg Subtype.val hv)
    simp [hn]

end


section
open JuliaLean JuliaLean.base.abstractset JuliaLean.base.int
variable {α : Type} [DecidableEq α] (o : Calls α) (L : CollectionLaws o)
include L

theorem unionGeneric_spec (H : CapacityPremise o L) (s : o.C) (inputs : List o.C) (r : o.C)
    (h : unionGeneric o (unionBangAbstractSetMany o) s inputs = .ok r) :
    (∀ x, Stored o r x ↔ x ∈ (s :: inputs).flatMap o.elements) ∧
    (o.isAbstractSet s = true → o.isAbstractSet r = true) := by
  obtain ⟨T, hT, hr⟩ := bind_ok _ _ r h
  obtain ⟨empty, he, hr⟩ := bind_ok _ _ r hr
  obtain ⟨hm, hs⟩ := unionMany_spec o L H (s :: inputs) empty r hr
  obtain ⟨hem, hes⟩ := L.emptyMutable s T empty he
  exact ⟨fun x => by simpa [hem x] using hm x, fun ha => hs (hes ha)⟩

theorem copyBang_spec (H : CapacityPremise o L) (dst src r : o.C) (hd : o.isAbstractSet dst = true)
    (h : copyBangAbstractSet o false dst src = .ok r) : SameStored o r src := by
  obtain ⟨empty, he, hr⟩ := bind_ok _ _ r h
  have hm := (unionMany_spec o L H [src] empty r hr).1
  have hem := (L.empty dst empty he).1
  intro x
  simpa [hem x] using hm x

theorem pushAll_spec (xs : List α) (s r : o.C)
    (h : pushAll o xs s = .ok r) : UnionOutput o s xs r := by
  induction xs generalizing s r with
  | nil =>
    simp [pushAll, pure, Except.pure] at h
    subst r
    exact ⟨by simp, id⟩
  | cons a xs ih =>
    obtain ⟨p, hp, hr⟩ := bind_ok _ _ r h
    obtain ⟨hm, hs⟩ := L.push s a p hp
    obtain ⟨hm2, hs2⟩ := ih p r hr
    refine ⟨?_, fun ha => hs2 (hs ha)⟩
    intro z
    have h1 := hm z
    have h2 := hm2 z
    simp only [List.mem_cons]
    grind

omit L [DecidableEq α] in
 theorem unionLoop_wider (T : JuliaType) (itr : o.C)
    (ht : o.subtype (o.elementType itr) T = false) (xs : List α) (s : o.C) :
    unionBangIteratorLoop o T itr xs s = pushAll o xs s := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih =>
    simp only [unionBangIteratorLoop, ht, Bool.false_eq_true, ite_false, pushAll]
    congr 1
    funext r
    exact ih r

theorem setdiffCopy_spec (s : o.C) (inputs : List o.C) (r : o.C)
    (h : setdiffAbstractSetMany o s inputs = .ok r) :
    (∀ x, Stored o r x ↔ Stored o s x ∧ x ∉ inputs.flatMap o.elements) ∧
    (o.isAbstractSet s = true → o.isAbstractSet r = true) := by
  obtain ⟨copied, hc, hr⟩ := bind_ok _ _ r h
  obtain ⟨hm, hs⟩ := deleteMany_spec o L inputs copied r hr
  obtain ⟨hcm, hcs⟩ := L.copyMutable s copied hc
  exact ⟨fun x => (hm x).trans (and_congr (hcm x) Iff.rfl), fun ha => hs (hcs ha)⟩

end


section
open JuliaLean JuliaLean.base.abstractset JuliaLean.base.int
variable {α : Type} [DecidableEq α] (o : Calls α) (L : CollectionLaws o)
include L

def IntersectOutput (s : o.C) (inputs : List o.C) (r : o.C) : Prop :=
  (∀ z, Stored o r z ↔ Stored o s z ∧ ∀ t ∈ inputs, Stored o t z) ∧
  (o.isAbstractSet s = true → o.isAbstractSet r = true)

theorem intersectSet_spec (s t r : o.C)
    (h : intersectBangAbstractSetSet o s t = .ok r) : IntersectOutput o s [t] r := by
  obtain ⟨hm, hs⟩ := L.filter (fun x => o.member t x) s r h
  refine ⟨?_, hs⟩
  intro z
  simpa [L.member] using hm z

theorem intersectIterator_spec (H : CapacityPremise o L) (s itr r : o.C)
    (h : intersectBangAbstractSetIterator o s itr = .ok r) : IntersectOutput o s [itr] r := by
  obtain ⟨empty, he, hnext⟩ := bind_ok _ _ r h
  obtain ⟨out, ho, hr⟩ := bind_ok _ _ r hnext
  obtain ⟨hem, hes⟩ := L.emptyMutable s _ empty he
  obtain ⟨hum, hus⟩ := unionIterator_spec o L H (o.elementType itr) empty itr out ho
  obtain ⟨him, his⟩ := intersectSet_spec o L s out r hr
  refine ⟨?_, his⟩
  intro z
  have hu : Stored o out z ↔ Stored o itr z := by simpa [hem z, Stored] using hum z
  simpa [hu] using him z

theorem intersectDispatch_spec (H : CapacityPremise o L) (s itr r : o.C)
    (h : intersectBangDispatch o s itr = .ok r) : IntersectOutput o s [itr] r := by
  unfold intersectBangDispatch at h
  split at h
  · exact intersectSet_spec o L s itr r h
  · exact intersectIterator_spec o L H s itr r h

theorem intersectManyBang_spec (H : CapacityPremise o L) (inputs : List o.C) (s r : o.C)
    (h : intersectBangAbstractSetMany o s inputs = .ok r) : IntersectOutput o s inputs r := by
  unfold intersectBangAbstractSetMany at h
  induction inputs generalizing s r with
  | nil =>
    simp [intersectBangManyLoop, pure, Except.pure] at h
    subst r
    exact ⟨by simp, id⟩
  | cons t ts ih =>
    obtain ⟨p, hp, hr⟩ := bind_ok _ _ r h
    obtain ⟨hm, hs⟩ := intersectDispatch_spec o L H s t p hp
    obtain ⟨hm2, hs2⟩ := ih p r hr
    refine ⟨?_, fun ha => hs2 (hs ha)⟩
    intro z
    have h1 := hm z
    have h2 := hm2 z
    simp only [List.mem_cons, forall_eq_or_imp] at *
    grind

theorem intersectTwo_spec (s itr r : o.C)
    (h : intersectAbstractSetTwo o s itr = .ok r) : IntersectOutput o s [itr] r := by
  unfold intersectAbstractSetTwo at h
  simp only [L.length, bind, Except.bind] at h
  split at h
  · obtain ⟨ty, hty, hnext⟩ := bind_ok _ _ r h
    obtain ⟨empty, he, hr⟩ := bind_ok _ _ r hnext
    obtain ⟨hem, hes⟩ := L.emptyMutable s ty empty he
    obtain ⟨hm, hs⟩ := mapfilterPush_spec o L (fun x => o.member itr x) (o.elements s) empty r hr
    refine ⟨?_, fun hs0 => hs (hes hs0)⟩
    intro z
    simpa [L.member, hem z, and_comm] using hm z
  · obtain ⟨ty, hty, hnext⟩ := bind_ok _ _ r h
    obtain ⟨empty, he, hr⟩ := bind_ok _ _ r hnext
    obtain ⟨hem, hes⟩ := L.emptyMutable s ty empty he
    obtain ⟨hm, hs⟩ := mapfilterPush_spec o L (fun x => o.member s x) (o.elements itr) empty r hr
    refine ⟨?_, fun hs0 => hs (hes hs0)⟩
    intro z
    simpa [L.member, hem z, and_comm] using hm z

theorem intersectTail_spec (H : CapacityPremise o L) (s itr : o.C) (inputs : List o.C) (r : o.C)
    (h : intersectAbstractSetTail o s itr inputs = .ok r) :
    IntersectOutput o s (itr :: inputs) r := by
  obtain ⟨ty, hty, hnext⟩ := bind_ok _ _ r h
  obtain ⟨ty2, hty2, hnext2⟩ := bind_ok _ _ r hnext
  simp only [bind, Except.bind] at hnext2
  split at hnext2
  · obtain ⟨p, hp, hr⟩ := bind_ok _ _ r hnext2
    obtain ⟨hm, hs⟩ := intersectTwo_spec o L s itr p hp
    obtain ⟨hm2, hs2⟩ := intersectManyBang_spec o L H inputs p r hr
    refine ⟨?_, fun ha => hs2 (hs ha)⟩
    intro z
    have h1 := hm z
    have h2 := hm2 z
    simp only [List.mem_cons, forall_eq_or_imp] at *
    grind
  · obtain ⟨empty, he, hnext3⟩ := bind_ok _ _ r hnext2
    obtain ⟨united, hu, hnext4⟩ := bind_ok _ _ r hnext3
    obtain ⟨p, hi, hr⟩ := bind_ok _ _ r hnext4
    obtain ⟨hem, hes⟩ := L.emptyMutable s ty empty he
    obtain ⟨hum, hus⟩ := unionMany_spec o L H [s] empty united hu
    obtain ⟨him, his⟩ := intersectIterator_spec o L H united itr p hi
    obtain ⟨hfm, hfs⟩ := intersectManyBang_spec o L H inputs p r hr
    refine ⟨?_, fun hs0 => hfs (his (hus (hes hs0)))⟩
    intro z
    have h1 := hum z
    have h2 := him z
    have h3 := hfm z
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_cons, forall_eq_or_imp, List.not_mem_nil, not_false_eq_true] at *
    have h0 := hem z
    grind

theorem intersectMany_spec (H : CapacityPremise o L) (s itr : o.C) (inputs : List o.C) (fuel : Nat) (r : o.C)
    (h : intersectAbstractSetMany o s itr inputs fuel = .ok r) :
    IntersectOutput o s (itr :: inputs) r := by
  induction fuel generalizing itr inputs with
  | zero => exact intersectTail_spec o L H s itr inputs r h
  | succ fuel ih =>
    simp only [intersectAbstractSetMany, L.length, bind, Except.bind] at h
    split at h
    · cases hf : o.findminLength inputs with
      | error e => simp [hf, bind, Except.bind] at h
      | ok pair =>
        obtain ⟨n, k⟩ := pair
        simp only [hf, bind, Except.bind] at h
        split at h
        · obtain ⟨before, selected, after, he, hk⟩ := L.findmin inputs n k hf
          subst inputs
          subst k
          simp only [L.setindex, L.getindex, bind, Except.bind] at h
          obtain ⟨hm, hs⟩ := ih selected (before ++ itr :: after) h
          refine ⟨?_, hs⟩
          intro z
          have hz := hm z
          simp only [List.mem_cons, List.mem_append, forall_eq_or_imp,
            or_imp, forall_and] at *
          grind
        · exact intersectTail_spec o L H s itr inputs r h
    · exact intersectTail_spec o L H s itr inputs r h


end


section
open JuliaLean JuliaLean.base.abstractset JuliaLean.base.int
variable {α : Type} [DecidableEq α] (o : Calls α) (L : CollectionLaws o)
include L

def membershipParity (inputs : List o.C) (z : α) : Bool :=
  match inputs with
  | [] => false
  | s :: rest => decide (Stored o s z) != membershipParity rest z

def SymdiffOutput (s : o.C) (inputs : List o.C) (r : o.C) : Prop :=
  (∀ z, decide (Stored o r z) = (decide (Stored o s z) != membershipParity o inputs z)) ∧
  (o.isAbstractSet s = true → o.isAbstractSet r = true)

theorem symdiffSet_spec (s itr r : o.C) (hi : o.isAbstractSet itr = true)
    (h : symdiffBangAbstractSetSet o s itr = .ok r) : SymdiffOutput o s [itr] r := by
  obtain ⟨hm, hs⟩ := symdiffLoop_spec o L (o.elements itr) (L.setNodup itr hi) s r h
  refine ⟨?_, hs⟩
  intro z
  have hz := hm z
  by_cases h1 : Stored o s z <;> by_cases h2 : Stored o itr z <;>
    simp_all [membershipParity, Stored]

theorem symdiffIterator_spec (s itr r : o.C)
    (h : symdiffBangAbstractSetIterator o s itr = .ok r) : SymdiffOutput o s [itr] r := by
  obtain ⟨set, he, hr⟩ := bind_ok _ _ r h
  have hm : ∀ x, Stored o set x ↔ Stored o itr x := (L.makeSet itr set he).1
  have hs := (L.makeSet itr set he).2
  obtain ⟨hout, hset⟩ := symdiffSet_spec o L s set r hs hr
  refine ⟨?_, hset⟩
  intro z
  simpa only [membershipParity, hm] using hout z

theorem symdiffDispatch_spec (s itr r : o.C)
    (h : symdiffBangDispatch o s itr = .ok r) : SymdiffOutput o s [itr] r := by
  unfold symdiffBangDispatch at h
  split at h
  · rename_i hi
    exact symdiffSet_spec o L s itr r hi h
  · exact symdiffIterator_spec o L s itr r h

theorem symdiffMany_spec (inputs : List o.C) (s r : o.C)
    (h : symdiffBangAbstractSetMany o s inputs = .ok r) : SymdiffOutput o s inputs r := by
  unfold symdiffBangAbstractSetMany at h
  induction inputs generalizing s r with
  | nil =>
    simp [symdiffBangManyLoop, pure, Except.pure] at h
    subst r
    exact ⟨by simp [membershipParity], id⟩
  | cons t ts ih =>
    obtain ⟨p, hp, hr⟩ := bind_ok _ _ r h
    obtain ⟨hm, hs⟩ := symdiffDispatch_spec o L s t p hp
    obtain ⟨hm2, hs2⟩ := ih p r hr
    refine ⟨?_, fun ha => hs2 (hs ha)⟩
    intro z
    rw [hm2 z, hm z]
    simp only [membershipParity, Bool.bne_false]
    cases decide (Stored o s z) <;> cases decide (Stored o t z) <;>
      cases membershipParity o ts z <;> rfl

theorem symdiffGeneric_spec (s : o.C) (inputs : List o.C) (r : o.C)
    (h : symdiffGeneric o (symdiffBangAbstractSetMany o) s inputs = .ok r) :
    (∀ x, decide (Stored o r x) = membershipParity o (s :: inputs) x) ∧
    (o.isAbstractSet s = true → o.isAbstractSet r = true) := by
  obtain ⟨T, hT, hr⟩ := bind_ok _ _ r h
  obtain ⟨empty, he, hr⟩ := bind_ok _ _ r hr
  obtain ⟨hm, hs⟩ := symdiffMany_spec o L (s :: inputs) empty r hr
  obtain ⟨hem, hes⟩ := L.emptyMutable s T empty he
  exact ⟨fun x => by simpa [hem x] using hm x, fun ha => hs (hes ha)⟩

end


section
open JuliaLean JuliaLean.base.abstractset JuliaLean.base.int
variable {α : Type} [DecidableEq α] (o : Calls α) (L : CollectionLaws o)
include L

def StrictlyIncluded (a b : o.C) : Prop := Included o a b ∧ ¬ SameStored o a b

theorem properSet_spec (a b : o.C) (ha : o.isAbstractSet a = true)
    (hb : o.isAbstractSet b = true) (r : Bool)
    (h : properSubsetAbstractSetSet o a b = .ok r) :
    (r = true ↔ StrictlyIncluded o a b) := by
  unfold properSubsetAbstractSetSet at h
  simp only [L.length, bind, Except.bind] at h
  split at h
  · rename_i hlt
    have hlt' : (L.size a).val < (L.size b).val := hlt
    have hs := subset_spec o L a b r h
    constructor
    · intro hr
      refine ⟨hs.mp hr, ?_⟩
      intro he
      have hrev := L.cardinalBound b a hb (fun x hx => (he x).mpr hx)
      omega
    · intro hh
      exact hs.mpr hh.1
  · rename_i hlt
    have hle : (L.size b).val ≤ (L.size a).val := by
      have hn : ¬ (L.size a).val < (L.size b).val := hlt
      omega
    simp [pure, Except.pure] at h
    subst r
    have hn : ¬ StrictlyIncluded o a b := by
      rintro ⟨hi, hn⟩
      have hbound := L.cardinalBound a b ha hi
      exact hn (L.cardinalEqual a b ha hb hi (by omega))
    simp [hn]

theorem properDispatch_spec (a b : o.C) (r : Bool)
    (h : properSubsetDispatch o a b = .ok r) :
    (r = true ↔ StrictlyIncluded o a b) := by
  unfold properSubsetDispatch at h
  split at h
  · rename_i ha
    split at h
    · rename_i hb
      exact properSet_spec o L a b ha hb r h
    · obtain ⟨set, he, hr⟩ := bind_ok _ _ r h
      obtain ⟨hm, hs⟩ := L.makeSet b set he
      have hm' : ∀ x, Stored o set x ↔ Stored o b x := hm
      have hh := properSet_spec o L a set ha hs r hr
      simpa only [StrictlyIncluded, Included, SameStored, hm'] using hh
  · split at h
    · rename_i hb
      obtain ⟨set, he, hr⟩ := bind_ok _ _ r h
      obtain ⟨hm, hs⟩ := L.makeSet a set he
      have hm' : ∀ x, Stored o set x ↔ Stored o a x := hm
      have hh := properSet_spec o L set b hs hb r hr
      simpa only [StrictlyIncluded, Included, SameStored, hm'] using hh
    · obtain ⟨setA, heA, hnext⟩ := bind_ok _ _ r h
      obtain ⟨setB, heB, hr⟩ := bind_ok _ _ r hnext
      obtain ⟨hmA, hsA⟩ := L.makeSet a setA heA
      obtain ⟨hmB, hsB⟩ := L.makeSet b setB heB
      have hmA' : ∀ x, Stored o setA x ↔ Stored o a x := hmA
      have hmB' : ∀ x, Stored o setB x ↔ Stored o b x := hmB
      have hh := properSet_spec o L setA setB hsA hsB r hr
      simpa only [StrictlyIncluded, Included, SameStored, hmA', hmB'] using hh

theorem issetequalOtherSet_spec (a b : o.C) (hb : o.isAbstractSet b = true) (r : Bool)
    (h : issetequalOtherAbstractSet o a b = .ok r) : (r = true ↔ SameStored o a b) := by
  unfold issetequalOtherAbstractSet at h
  simp only [L.length, bind, Except.bind] at h
  split at h
  · rename_i hlt
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hlt
    simp [pure, Except.pure] at h
    subst r
    have hn : ¬ SameStored o a b := by
      intro he
      have hbound := L.cardinalBound b a hb (fun x hx => (he x).mpr hx)
      have hh : (L.size a).val < (L.size b).val := hlt.2
      omega
    simp [hn]
  · obtain ⟨set, he, hr⟩ := bind_ok _ _ r h
    obtain ⟨hm, hs⟩ := L.makeSet a set he
    have hm' : ∀ x, Stored o set x ↔ Stored o a x := hm
    have hh := equality_spec o L set b hs hb r hr
    simpa only [SameStored, hm'] using hh

theorem issetequalSetOther_spec (a b : o.C) (ha : o.isAbstractSet a = true) (r : Bool)
    (h : issetequalAbstractSetOther o a b = .ok r) : (r = true ↔ SameStored o a b) := by
  obtain ⟨set, he, hr⟩ := bind_ok _ _ r h
  obtain ⟨hm, hs⟩ := L.makeSet b set he
  have hm' : ∀ x, Stored o set x ↔ Stored o b x := hm
  have hh := equality_spec o L a set ha hs r hr
  simpa only [SameStored, hm'] using hh

theorem issetequalGeneric_spec (a b : o.C) (r : Bool)
    (h : issetequalOtherOther o a b = .ok r) : (r = true ↔ SameStored o a b) := by
  unfold issetequalOtherOther at h
  split at h
  · obtain ⟨set, he, hr⟩ := bind_ok _ _ r h
    obtain ⟨hm, hs⟩ := L.makeSet b set he
    have hm' : ∀ x, Stored o set x ↔ Stored o b x := hm
    have hh := issetequalOtherSet_spec o L a set hs r hr
    simpa only [SameStored, hm'] using hh
  · split at h
    · obtain ⟨set, he, hr⟩ := bind_ok _ _ r h
      obtain ⟨hm, hs⟩ := L.makeSet a set he
      have hm' : ∀ x, Stored o set x ↔ Stored o a x := hm
      have hh := issetequalOtherSet_spec o L b set hs r hr
      simpa only [SameStored, hm', Iff.comm] using hh
    · obtain ⟨setA, heA, hnext⟩ := bind_ok _ _ r h
      obtain ⟨setB, heB, hr⟩ := bind_ok _ _ r hnext
      obtain ⟨hmA, hsA⟩ := L.makeSet a setA heA
      obtain ⟨hmB, hsB⟩ := L.makeSet b setB heB
      have hmA' : ∀ x, Stored o setA x ↔ Stored o a x := hmA
      have hmB' : ∀ x, Stored o setB x ↔ Stored o b x := hmB
      have hh := equality_spec o L setA setB hsA hsB r hr
      simpa only [SameStored, hmA', hmB'] using hh

theorem issetequal_spec (a b : o.C) (r : Bool)
    (h : issetequalDispatch o a b = .ok r) : (r = true ↔ SameStored o a b) := by
  unfold issetequalDispatch at h
  split at h
  · rename_i ha
    split at h
    · rename_i hb
      exact equality_spec o L a b ha hb r h
    · exact issetequalSetOther_spec o L a b ha r h
  · split at h
    · rename_i hb
      exact issetequalOtherSet_spec o L a b hb r h
    · exact issetequalGeneric_spec o L a b r h

end


section
open JuliaLean JuliaLean.base.abstractset JuliaLean.base.int

theorem maxValuesCapacity_bounds (T : JuliaType) :
    0 ≤ maxValuesCapacity T ∧ maxValuesCapacity T ≤ IntTy.max .i64 := by
  induction T with
  | other => decide
  | bitInteger t => cases t <;> decide
  | bool => decide
  | nothing => decide
  | union a b ha hb =>
    simp only [maxValuesCapacity]
    omega

theorem maxValuesCapacity_proven : MaxValuesCapacity := by
  intro add T h
  induction T with
  | other => rfl
  | bitInteger t => cases t <;> simp only [maxValuesDispatch] <;> decide
  | bool => rfl
  | nothing => rfl
  | union a b ha hb =>
    have hA := maxValuesCapacity_bounds a
    have hB := maxValuesCapacity_bounds b
    have hadd := h (maxValuesDispatch add a) (maxValuesDispatch add b)
      (by omega) (by omega)
    generalize hp : add (maxValuesDispatch add a) (maxValuesDispatch add b) = p at hadd
    obtain ⟨r, ov⟩ := p
    cases ov with
    | true =>
      have ht : IntTy.max .i64 < maxValuesCapacity a + maxValuesCapacity b := by
        simpa only [ha, hb, Bool.true_eq, decide_eq_true_eq] using hadd.1.symm
      have hm : (int (IntTy.max .i64)).val = IntTy.max .i64 := by decide
      simp only [maxValuesDispatch, maxValuesUnion, hp, ite_true, hm, maxValuesCapacity]
      omega
    | false =>
      have ht : ¬ IntTy.max .i64 < maxValuesCapacity a + maxValuesCapacity b := by
        have hh := hadd.1.symm
        simpa only [ha, hb, decide_eq_false_iff_not] using hh
      have hr : r.val = maxValuesCapacity a + maxValuesCapacity b := by
        simpa only [ha, hb] using hadd.2 rfl
      simp only [maxValuesDispatch, maxValuesUnion, hp, Bool.false_eq_true, ite_false,
        hr, maxValuesCapacity]
      omega

end


section
open JuliaLean JuliaLean.base.abstractset JuliaLean.base.int

theorem unionGeneric_order {α : Type} (o : Calls α) (isArray : o.C → Bool)
    (isequal : α → α → Bool) (unionBang : o.C → List o.C → Except o.Error o.C)
    (h : VectorUnionBangOrderLaw o isArray isequal unionBang) (s : o.C)
    (sets : List o.C) (result : o.C) (hs : isArray s = true)
    (hr : unionGeneric o unionBang s sets = .ok result) :
    o.elements result = stableUnique isequal (o.elements s ++ sets.flatMap o.elements) := by
  unfold unionGeneric at hr
  cases hp : o.promoteEltype s sets with
  | error e => simp [hp, bind, Except.bind] at hr
  | ok T =>
    cases he : o.emptyMutable s T with
    | error e => simp [hp, he, bind, Except.bind] at hr
    | ok out =>
      simp [hp, he, bind, Except.bind] at hr
      obtain ⟨ha, hn⟩ := h.1 s T out hs he
      have := h.2 out (s :: sets) result ha hr
      simpa [hn] using this

theorem symdiffGeneric_order {α : Type} (o : Calls α) (isArray : o.C → Bool)
    (isequal : α → α → Bool) (symdiffBang : o.C → List o.C → Except o.Error o.C)
    (h : VectorSymdiffBangOrderLaw o isArray isequal symdiffBang) (s : o.C)
    (sets : List o.C) (result : o.C) (hs : isArray s = true)
    (hr : symdiffGeneric o symdiffBang s sets = .ok result) :
    SubsequenceBy isequal (o.elements result) (o.elements s ++ sets.flatMap o.elements) := by
  unfold symdiffGeneric at hr
  cases hp : o.promoteEltype s sets with
  | error e => simp [hp, bind, Except.bind] at hr
  | ok T =>
    cases he : o.emptyMutable s T with
    | error e => simp [hp, he, bind, Except.bind] at hr
    | ok out =>
      simp [hp, he, bind, Except.bind] at hr
      obtain ⟨ha, hn⟩ := h.1 s T out hs he
      have := h.2 out (s :: sets) result ha hr
      simpa [hn] using this

theorem arrayOrderSpec_proven : ArrayOrderSpec := by
  intro α o isArray isequal unionBang symdiffBang hu hs hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s sets result ha _ hr
    exact unionGeneric_order o isArray isequal unionBang hu s sets result ha hr
  · intro s result ha hn hr
    simp [intersectUnary, unionDispatch, hn] at hr
    simpa using unionGeneric_order o isArray isequal unionBang hu s [] result ha hr
  · intro s result ha hn hr
    simp [setdiffUnary, unionDispatch, hn] at hr
    simpa using unionGeneric_order o isArray isequal unionBang hu s [] result ha hr
  · intro s sets result ha _ hr
    exact symdiffGeneric_order o isArray isequal symdiffBang hs s sets result ha hr
  · intro s result ha _ hr
    unfold symdiffAbstractSetUnary at hr
    cases he : o.copy s with
    | error e => simp [he, bind, Except.bind] at hr
    | ok out =>
      simp [he, bind, Except.bind] at hr
      obtain ⟨ho, hn⟩ := hc s out ha he
      have := hs.2 out [] result ho hr
      simpa [hn] using this

end

/-! ## Public contracts -/
def IdSetSymdiffIdentity : Prop :=
  ∀ (α : Type) (o : Calls α) (s itr : o.C) (x : α) (same : α → α → Bool),
    o.isAbstractSet s = true →
    (symdiffBangAbstractSetIterator o s itr).bind (fun result => o.member result x) = do
      let inSet ← o.member s x
      let inItr := (o.elements itr).any (fun y => same x y)
      pure (inSet != inItr)

def IssubsetVectorSemantics : Prop :=
  ∀ (α : Type) (o : Calls α) (a b : o.C),
    o.isAbstractSet a = false → o.isAbstractSet b = false →
    ((issubset o a b = .ok true) ↔ SubsetByMembership o a b)

def IdSetIssubsetIn : Prop :=
  ∀ (α : Type) (o : Calls α) (a b : o.C),
    o.isAbstractSet a = true →
    ((issubset o a b = .ok true) ↔ SubsetByMembership o a b)

def HasfastinSpec : Prop :=
  (∀ (T : Type), hasFastinTypeDefault T = false) ∧
  (∀ (T : Type), hasFastinSetDictRange T = true)

def IdSetIssetequalSubsets : Prop :=
  ∀ (α : Type) (o : Calls α) (a b : o.C),
    o.isAbstractSet a = true →
    (issetequalDispatch o a b = do
      let ab ← issubset o a b
      let ba ← issubset o b a
      pure (ab && ba))

def IsdisjointSizeIndependent : Prop :=
  ∀ (α : Type) (o : Calls α) (a b : o.C),
    ((isdisjoint o a b = .ok true) ↔ DisjointByMembership o a b)

def RangeMembershipSpec : Prop :=
  ∀ (α : Type) (o : Calls α) (a b : o.C),
    o.isIntegerRange a = true →
    ((isdisjointRange o a b = .ok true) ↔ ¬ CollectionsOverlap o a b)

def AbstractDisjointFilterSpec : Prop :=
  IsdisjointSizeIndependent ∧
  (∀ (α : Type) (o : Calls α) (a b : o.C),
    ((isdisjointRange o a b = .ok true) ↔ ¬ CollectionsOverlap o a b) ∧
    ((lessThanAbstractSet o a b = .ok true) ↔ ProperSubsetByMembership o a b) ∧
    ((lessEqualAbstractSet o a b = .ok true) ↔ SubsetByMembership o a b)) ∧
  (∀ (α : Type) (o : Calls α) (pred : α → Except o.Error Bool) (s : o.C) (x : α),
    (filterAbstractSet o pred s).bind (fun result => o.member result x) = do
      let inSet ← o.member s x
      let accepted ← pred x
      pure (inSet && accepted)) ∧
  (∀ (α : Type) (o : Calls α) (pred : α → Except o.Error Bool) (s : o.C) (x : α),
    (unsafeFilterAbstractSet o pred s).bind (fun result => o.member result x) = do
      let inSet ← o.member s x
      let accepted ← pred x
      pure (inSet && accepted))


section
open JuliaLean JuliaLean.base.abstractset JuliaLean.base.int
open JuliaLean.Proofs.base.abstractset

/-! Algebra contracts use one membership equality throughout. Successful primitive calls obey
CollectionLaws; a conversion or predicate error is not asserted to produce a collection. -/

def DictsSetUnion : Prop :=
  ∀ (α : Type) (o : Calls α) (s t : o.C),
    o.isAbstractSet s = true → o.isAbstractSet t = true →
    (∀ x, (unionBangAbstractSetMany o s [t]).bind (fun result => o.member result x) = do
      let left ← o.member s x
      let right ← o.member t x
      pure (left || right)) ∧
    (∀ result, unionBangAbstractSetMany o s [t] = .ok result →
      o.length result = .ok (int (Int.ofNat (distinctCount o.equal
        (o.elements s ++ o.elements t)))))

def DictsUnionMaxValuesBreak : Prop :=
  ∀ (α : Type) (o : Calls α) (T : JuliaType) (s itr : o.C),
    o.isAbstractSet s = true →
    SameOutcome o (unionBangAbstractSetIterator o T s itr)
      (pushAll o (o.elements itr) s)

def AbstractUnionSpec : Prop :=
  (∀ (α : Type) (o : Calls α) (s : o.C) (sets : List o.C),
    o.isAbstractSet s = true →
    ∀ x, (unionGeneric o (unionBangAbstractSetMany o) s sets).bind
      (fun result => o.member result x) = do
        let left ← o.member s x
        let right ← anyCollectionMember o sets x
        pure (left || right)) ∧
  (∀ (α : Type) (o : Calls α) (s : o.C) (sets : List o.C),
    o.isAbstractSet s = true →
    ∀ x, (unionBangAbstractSetMany o s sets).bind
      (fun result => o.member result x) = do
        let left ← o.member s x
        let right ← anyCollectionMember o sets x
        pure (left || right)) ∧
  (∀ (α : Type) (o : Calls α) (s : o.C) (sets : List o.C) (result : o.C),
    o.isAbstractSet s = true → unionBangAbstractSetMany o s sets = .ok result →
    o.length result = .ok (int (Int.ofNat (distinctCount o.equal
      (o.elements s ++ sets.flatMap o.elements))))) ∧
  (∀ (α : Type) (o : Calls α) (s : o.C) (x : α),
    o.isAbstractSet s = true →
    (unionAbstractSetUnary o s).bind (fun result => o.member result x) =
      o.member s x) ∧
  MaxValuesCapacity

/-- The finite-domain or below-capacity premise is explicit; the unrestricted union
case is covered by the refuted `dicts-union-max-values-break` entry. -/
def AbstractSetCoreSpec : Prop :=
  (∀ (T anyType : Type), eltypeAbstractSet (some T) anyType = T) ∧
  (∀ (anyType : Type), eltypeAbstractSet (none : Option Type) anyType = anyType) ∧
  (∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (H : CapacityPremise o L) (dst src r : o.C),
    o.isAbstractSet dst = true → copyBangAbstractSet o false dst src = .ok r → SameStored o r src) ∧
  (∀ (α : Type) (o : Calls α) (dst src : o.C), copyBangAbstractSet o true dst src = .ok dst)

theorem AbstractSetCoreSpec_proven : AbstractSetCoreSpec := by
  refine ⟨by intros; rfl, by intros; rfl, ?_, by intros; rfl⟩
  intro α _ o L H dst src r hd h
  exact copyBang_spec o L H dst src r hd h

/-- The finite-domain or below-capacity premise is explicit; the unrestricted union
case is covered by the refuted `dicts-union-max-values-break` entry. -/
def DictsSetUnionFinite : Prop :=
  ∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (H : CapacityPremise o L) (s t r : o.C),
    o.isAbstractSet s = true → unionBangAbstractSetMany o s [t] = .ok r →
    (∀ x, Stored o r x ↔ Stored o s x ∨ Stored o t x) ∧
    o.length r = .ok (int (Int.ofNat (distinctCount o.equal (o.elements s ++ o.elements t))))

theorem DictsSetUnionFinite_proven : DictsSetUnionFinite := by
  intro α _ o L H s t r hs h
  obtain ⟨hm, hset⟩ := unionMany_spec o L H [t] s r h
  have hm' : ∀ x, Stored o r x ↔ Stored o s x ∨ Stored o t x := by simpa using hm
  exact ⟨hm', L.cardinality r _ (hset hs) (by simpa [Stored] using hm')⟩

/-- The finite-domain or below-capacity premise is explicit; the unrestricted union
case is covered by the refuted `dicts-union-max-values-break` entry. -/
def DictsUnionMaxValuesBreakFinite : Prop :=
  MaxValuesCapacity ∧
  (∀ (α : Type) (o : Calls α) (T : JuliaType) (itr : o.C) (xs : List α) (s : o.C),
    o.subtype (o.elementType itr) T = false →
      unionBangIteratorLoop o T itr xs s = pushAll o xs s) ∧
  (∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (H : CapacityPremise o L)
      (T : JuliaType) (s itr r pushed : o.C),
    unionBangAbstractSetIterator o T s itr = .ok r →
    pushAll o (o.elements itr) s = .ok pushed → SameStored o r pushed)

theorem DictsUnionMaxValuesBreakFinite_proven : DictsUnionMaxValuesBreakFinite := by
  refine ⟨maxValuesCapacity_proven, ?_, ?_⟩
  · intro α o T itr xs s ht
    exact unionLoop_wider o T itr ht xs s
  · intro α _ o L H T s itr r pushed hr hp
    have h1 := (unionIterator_spec o L H T s itr r hr).1
    have h2 := (pushAll_spec o L (o.elements itr) s pushed hp).1
    exact fun x => (h1 x).trans (h2 x).symm

/-- The finite-domain or below-capacity premise is explicit; the unrestricted union
case is covered by the refuted `dicts-union-max-values-break` entry. -/
def AbstractUnionSpecFinite : Prop :=
  (∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (H : CapacityPremise o L) (s : o.C)
      (inputs : List o.C) (r : o.C),
    o.isAbstractSet s = true → unionGeneric o (unionBangAbstractSetMany o) s inputs = .ok r →
    (∀ x, Stored o r x ↔ x ∈ (s :: inputs).flatMap o.elements) ∧
    o.length r = .ok (int (Int.ofNat (distinctCount o.equal ((s :: inputs).flatMap o.elements))))) ∧
  (∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (H : CapacityPremise o L) (s : o.C)
      (inputs : List o.C) (r : o.C),
    o.isAbstractSet s = true → unionBangAbstractSetMany o s inputs = .ok r →
    (∀ x, Stored o r x ↔ x ∈ (s :: inputs).flatMap o.elements) ∧
    o.length r = .ok (int (Int.ofNat (distinctCount o.equal ((s :: inputs).flatMap o.elements))))) ∧
  (∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (s r : o.C),
    unionAbstractSetUnary o s = .ok r → SameStored o r s) ∧ MaxValuesCapacity

theorem AbstractUnionSpecFinite_proven : AbstractUnionSpecFinite := by
  refine ⟨?_, ?_, ?_, maxValuesCapacity_proven⟩
  · intro α _ o L H s inputs r hs h
    obtain ⟨hm, hset⟩ := unionGeneric_spec o L H s inputs r h
    exact ⟨hm, L.cardinality r _ (hset hs) hm⟩
  · intro α _ o L H s inputs r hs h
    obtain ⟨hm, hset⟩ := unionMany_spec o L H inputs s r h
    have hm' : ∀ x, Stored o r x ↔ x ∈ (s :: inputs).flatMap o.elements := by
      simpa [Stored] using hm
    exact ⟨hm', L.cardinality r _ (hset hs) hm'⟩
  · intro α _ o L s r h
    exact (L.copy s r h).1

def DictsSetIntersect : Prop :=
  ∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (s t r : o.C),
    o.isAbstractSet t = true → intersectBangAbstractSetMany o s [t] = .ok r →
    ∀ x, Stored o r x ↔ Stored o s x ∧ Stored o t x

theorem DictsSetIntersect_proven : DictsSetIntersect := by
  intro α _ o L s t r ht h
  have he : intersectBangAbstractSetSet o s t = .ok r := by
    cases hr : intersectBangAbstractSetSet o s t <;>
      simpa [intersectBangAbstractSetMany, intersectBangManyLoop, intersectBangDispatch,
        ht, hr, bind, Except.bind, pure, Except.pure] using h
  simpa using (intersectSet_spec o L s t r he).1

/-- The finite-domain or below-capacity premise is explicit; the unrestricted union
case is covered by the refuted `dicts-union-max-values-break` entry. -/
def AbstractIntersectSpec : Prop :=
  (∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (H : CapacityPremise o L)
      (s itr : o.C) (inputs : List o.C) (r : o.C),
    intersectAbstractSetMany o s itr inputs = .ok r →
    ∀ x, Stored o r x ↔ Stored o s x ∧ ∀ t ∈ itr :: inputs, Stored o t x) ∧
  (∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (H : CapacityPremise o L)
      (s : o.C) (inputs : List o.C) (r : o.C),
    intersectBangAbstractSetMany o s inputs = .ok r →
    ∀ x, Stored o r x ↔ Stored o s x ∧ ∀ t ∈ inputs, Stored o t x) ∧
  (∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (s itr r : o.C),
    intersectAbstractSetTwo o s itr = .ok r →
    ∀ x, Stored o r x ↔ Stored o s x ∧ Stored o itr x) ∧
  (∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (H : CapacityPremise o L) (s itr r : o.C),
    intersectBangAbstractSetIterator o s itr = .ok r →
    ∀ x, Stored o r x ↔ Stored o s x ∧ Stored o itr x) ∧
  (∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (s r : o.C),
    o.isAbstractSet s = true → intersectUnary o (unionBangAbstractSetMany o) s = .ok r → SameStored o r s)

theorem AbstractIntersectSpec_proven : AbstractIntersectSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro α _ o L H s itr inputs r h
    exact (intersectMany_spec o L H s itr inputs _ r h).1
  · intro α _ o L H s inputs r h
    exact (intersectManyBang_spec o L H inputs s r h).1
  · intro α _ o L s itr r h
    simpa using (intersectTwo_spec o L s itr r h).1
  · intro α _ o L H s itr r h
    simpa using (intersectIterator_spec o L H s itr r h).1
  · intro α _ o L s r hs h
    simp only [intersectUnary, unionDispatch, hs, ite_true] at h
    exact (L.copy s r h).1

def AbstractSetdiffSpec : Prop :=
  (∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o)
      (s : o.C) (inputs : List o.C) (r : o.C),
    setdiffAbstractSetMany o s inputs = .ok r →
    ∀ x, Stored o r x ↔ Stored o s x ∧ x ∉ inputs.flatMap o.elements) ∧
  (∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o)
      (s : o.C) (inputs : List o.C) (r : o.C),
    setdiffBangAbstractSetMany o s inputs = .ok r →
    ∀ x, Stored o r x ↔ Stored o s x ∧ x ∉ inputs.flatMap o.elements) ∧
  (∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (s itr r : o.C),
    setdiffBangAbstractSetIterator o s itr = .ok r →
    ∀ x, Stored o r x ↔ Stored o s x ∧ ¬ Stored o itr x) ∧
  (∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (s r : o.C),
    o.isAbstractSet s = true → setdiffUnary o (unionBangAbstractSetMany o) s = .ok r → SameStored o r s)

theorem AbstractSetdiffSpec_proven : AbstractSetdiffSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α _ o L s inputs r h
    exact (setdiffCopy_spec o L s inputs r h).1
  · intro α _ o L s inputs r h
    exact (deleteMany_spec o L inputs s r h).1
  · intro α _ o L s itr r h
    exact (deleteLoop_spec o L (o.elements itr) s r h).1
  · intro α _ o L s r hs h
    simp only [setdiffUnary, unionDispatch, hs, ite_true] at h
    exact (L.copy s r h).1

def DictsSetSymdiff : Prop :=
  ∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (s t r : o.C),
    o.isAbstractSet t = true → symdiffBangAbstractSetSet o s t = .ok r →
    ∀ x, decide (Stored o r x) = (decide (Stored o s x) != decide (Stored o t x))

theorem DictsSetSymdiff_proven : DictsSetSymdiff := by
  intro α _ o L s t r ht h
  simpa [membershipParity] using (symdiffSet_spec o L s t r ht h).1

def AbstractSymdiffSpec : Prop :=
  (∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o)
      (s : o.C) (inputs : List o.C) (r : o.C),
    symdiffGeneric o (symdiffBangAbstractSetMany o) s inputs = .ok r →
    ∀ x, decide (Stored o r x) = membershipParity o (s :: inputs) x) ∧
  (∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o)
      (s : o.C) (inputs : List o.C) (r : o.C),
    symdiffBangAbstractSetMany o s inputs = .ok r →
    ∀ x, decide (Stored o r x) = (decide (Stored o s x) != membershipParity o inputs x)) ∧
  (∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (s r : o.C),
    symdiffAbstractSetUnary o (symdiffBangAbstractSetMany o) s = .ok r → SameStored o r s) ∧
  (∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (s itr r : o.C),
    symdiffBangAbstractSetIterator o s itr = .ok r →
    ∀ x, decide (Stored o r x) = (decide (Stored o s x) != decide (Stored o itr x)))

theorem AbstractSymdiffSpec_proven : AbstractSymdiffSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α _ o L s inputs r h
    exact (symdiffGeneric_spec o L s inputs r h).1
  · intro α _ o L s inputs r h
    exact (symdiffMany_spec o L inputs s r h).1
  · intro α _ o L s r h
    obtain ⟨copied, hc, hr⟩ := bind_ok _ _ r h
    have hm := (symdiffMany_spec o L [] copied r hr).1
    have hcm := (L.copy s copied hc).1
    intro x
    have hx := hm x
    simp only [membershipParity, Bool.bne_false] at hx
    have hd : Stored o r x ↔ Stored o copied x := by
      by_cases h1 : Stored o r x <;> by_cases h2 : Stored o copied x <;> simp_all
    exact hd.trans (hcm x)
  · intro α _ o L s itr r h
    simpa [membershipParity] using (symdiffIterator_spec o L s itr r h).1

def DictsSetCompare : Prop :=
  ∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (a b : o.C),
    o.isAbstractSet a = true → o.isAbstractSet b = true →
    (∀ r, issubset o a b = .ok r → (r = true ↔ Included o a b)) ∧
    (∀ r, setEqualAbstractSet o a b = .ok r → (r = true ↔ SameStored o a b))

theorem DictsSetCompare_proven : DictsSetCompare := by
  intro α _ o L a b ha hb
  exact ⟨subset_spec o L a b, equality_spec o L a b ha hb⟩

def AbstractSubsetSpec : Prop :=
  (∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (a b : o.C),
    (∀ r, issubset o a b = .ok r → (r = true ↔ Included o a b)) ∧
    (∀ r, superset o a b = .ok r → (r = true ↔ Included o b a)) ∧
    (∀ r, properSubsetDispatch o a b = .ok r → (r = true ↔ StrictlyIncluded o a b)) ∧
    (∀ r, properSuperset o a b = .ok r → (r = true ↔ StrictlyIncluded o b a)) ∧
    notSubset o a b = (issubset o a b).map (!·) ∧ notSuperset o a b = notSubset o b a) ∧
  (∀ (α : Type) (o : Calls α) (a b : o.C),
    Fix2.apply (issubsetFix2 o b) a = issubset o a b ∧
    Fix2.apply (supersetFix2 o b) a = superset o a b ∧
    Fix2.apply (properSubsetFix2 o b) a = properSubsetDispatch o a b ∧
    Fix2.apply (properSupersetFix2 o b) a = properSuperset o a b ∧
    Fix2.apply (notSubsetFix2 o b) a = notSubset o a b ∧
    Fix2.apply (notSupersetFix2 o b) a = notSuperset o a b) ∧ HasfastinSpec

theorem AbstractSubsetSpec_proven : AbstractSubsetSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro α _ o L a b
    refine ⟨subset_spec o L a b, subset_spec o L b a,
      properDispatch_spec o L a b, properDispatch_spec o L b a, ?_, rfl⟩
    unfold notSubset
    cases issubset o a b <;> rfl
  · intros
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨by intros; rfl, by intros; rfl⟩

def AbstractSetequalSpec : Prop :=
  ∀ (α : Type) [DecidableEq α] (o : Calls α) (L : CollectionLaws o) (a b : o.C),
    (∀ r, issetequalDispatch o a b = .ok r → (r = true ↔ SameStored o a b)) ∧
    Fix2.apply (issetequalFix2 o b) a = issetequalDispatch o a b

theorem AbstractSetequalSpec_proven : AbstractSetequalSpec := by
  intro α _ o L a b
  exact ⟨issetequal_spec o L a b, rfl⟩

end

section
open JuliaLean JuliaLean.base.abstractset JuliaLean.base.int

namespace Observed
inductive Kind where
  | vector | valueSet | identitySet
  deriving DecidableEq, BEq
structure Collection where
  kind : Kind
  values : List Bool
  deriving DecidableEq

/-- The two values are the two signed zeros in `zeros`, and distinct equal arrays in `arrays`. -/
def eqKey (arrays : Bool) (kind : Kind) (x y : Bool) : Bool :=
  if arrays then if kind == .identitySet then x == y else true
  else if kind == .vector then true else x == y

def contains (arrays : Bool) (s : Collection) (x : Bool) : Bool :=
  s.values.any (fun y => eqKey arrays s.kind y x)

def insert (arrays : Bool) (s : Collection) (x : Bool) : Collection :=
  { s with values := x :: s.values.filter (fun y => !eqKey arrays s.kind y x) }

def erase (arrays : Bool) (s : Collection) (x : Bool) : Collection :=
  { s with values := s.values.filter (fun y => !eqKey arrays s.kind y x) }

def setify (arrays : Bool) (s : Collection) : Collection :=
  s.values.foldl (insert arrays) ⟨.valueSet, []⟩

def filterValues (pred : Bool → Except Unit Bool) : List Bool → Except Unit (List Bool)
  | [] => .ok []
  | x :: xs => do
    let keep ← pred x
    let rest ← filterValues pred xs
    return if keep then x :: rest else rest

abbrev calls (arrays : Bool) : Calls Bool where
  C := Collection
  Error := Unit
  elements := Collection.values
  equal := fun x y => if arrays then true else x == y
  hasLength := fun _ => true
  length := fun s => .ok (int s.values.length)
  hasFastIn := fun s => s.kind != .vector
  isAbstractSet := fun s => s.kind != .vector
  isIntegerRange := fun _ => false
  isEmptyRange := fun s => s.values.isEmpty
  member := fun s x => .ok (contains arrays s x)
  makeSet := fun s => .ok (setify arrays s)
  empty := fun s => .ok { s with values := [] }
  emptyMutable := fun s _ => .ok { s with values := [] }
  emptyMutableDefault := fun s => .ok { s with values := [] }
  copy := Except.ok
  copyMutable := Except.ok
  sizehint := fun s _ _ => .ok s
  push := fun s x => .ok (insert arrays s x)
  delete := fun s x => .ok (erase arrays s x)
  filterBang := fun pred s => do return { s with values := ← filterValues pred s.values }
  promoteEltype := fun _ _ => .ok .other
  elementType := fun _ => .other
  subtype := fun _ _ => true
  sameType := fun x y => decide (x = y)
  intLength := Except.ok
  findminLength := fun xs => match xs with
    | [] => .error ()
    | s :: _ => .ok (int s.values.length, 0)
  setindex := fun xs s k => .ok (xs.set k s)
  getindex := fun xs k => match xs[k]? with | some s => .ok s | none => .error ()
  extrema := fun s => .ok (s.values.headD false, s.values.getLastD false)
  step := fun _ => .ok false
  minimum := fun s => .ok (s.values.headD false)
  abs := Except.ok
  lessThan := fun x y => .ok (!x && y)
  mod := fun x y => if y then .ok false else .error ()
  addWithOverflow := fun a b => (a + b, decide (IntTy.max .i64 < a.val + b.val))

abbrev zeros : Calls Bool := calls false
abbrev arrays : Calls Bool := calls true

def pos : Collection := ⟨.vector, [false]⟩
def neg (n : Nat) : Collection := ⟨.vector, List.replicate n true⟩
def identities : Collection := ⟨.identitySet, [false, true]⟩
def oneValue : Collection := ⟨.valueSet, [true]⟩
def bothArrays : Collection := ⟨.vector, [false, true]⟩
def emptyIdentity : Collection := ⟨.identitySet, []⟩

end Observed

end

section
open JuliaLean JuliaLean.base.abstractset JuliaLean.base.int
open Observed
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private instance {E A : Type} [DecidableEq E] [DecidableEq A] : DecidableEq (Except E A)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl)
      else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl)
      else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (fun e => nomatch e)
  | .error _, .ok _ => isFalse (fun e => nomatch e)

theorem IssubsetVectorSemantics_refuted : ¬ IssubsetVectorSemantics := by
  intro h
  have hh := h Bool zeros pos (neg 71) (by decide) (by decide)
  have hall : SubsetByMembership zeros pos (neg 71) := by
    intro x hx
    cases x <;> unfold HasMember <;> decide
  have hf := hh.mpr hall
  exact (by decide : issubset zeros pos (neg 71) ≠ .ok true) hf

theorem IsdisjointSizeIndependent_refuted : ¬ IsdisjointSizeIndependent := by
  intro h
  have hh := (h Bool zeros pos (neg 70)).mp (by decide)
  have hf := hh false (by unfold HasCollectionElement; decide)
  exact (by decide : zeros.member (neg 70) false ≠ .ok false) hf

theorem IdSetIssubsetIn_refuted : ¬ IdSetIssubsetIn := by
  intro h
  have hh := h Bool arrays identities oneValue (by decide)
  have hall : SubsetByMembership arrays identities oneValue := by
    intro x hx
    cases x <;> unfold HasMember <;> decide
  have hf := hh.mpr hall
  exact (by decide : issubset arrays identities oneValue ≠ .ok true) hf

theorem IdSetIssetequalSubsets_refuted : ¬ IdSetIssetequalSubsets := by
  intro h
  have hf := h Bool arrays identities bothArrays (by decide)
  revert hf
  decide

theorem IdSetSymdiffIdentity_refuted : ¬ IdSetSymdiffIdentity := by
  intro h
  have hf := h Bool arrays emptyIdentity bothArrays false (fun x y => x == y) (by decide)
  revert hf
  decide

end

section
open JuliaLean JuliaLean.base.abstractset JuliaLean.base.int
open Observed

def RangeIsdisjointSpec : Prop :=
  RangeMembershipSpec ∧
  ∀ (α : Type) (o : Calls α) (a b : o.C), o.isIntegerRange a = true →
    ∃ r : Bool, isdisjointRange o a b = .ok r

abbrev zeroRangeCalls : Calls Bool :=
  { zeros with isIntegerRange := fun _ => true, hasFastIn := fun _ => true }

theorem RangeIsdisjointSpec_refuted : ¬ RangeIsdisjointSpec := by
  intro h
  obtain ⟨r, hr⟩ := h.2 Bool zeroRangeCalls (neg 3) (neg 2) rfl
  cases r <;> revert hr <;> decide

theorem AbstractDisjointFilterSpec_refuted : ¬ AbstractDisjointFilterSpec := by
  intro h
  exact IsdisjointSizeIndependent_refuted h.1

end

section
open JuliaLean JuliaLean.base.abstractset JuliaLean.base.int

namespace Sentinel
inductive Kind where
  | vector | finiteSet | huge
  deriving DecidableEq, BEq
structure Collection where
  kind : Kind
  values : List Int
  deriving DecidableEq

def positiveValues : List Int :=
  (List.range (IntTy.max .i64).toNat).map (fun n => Int.ofNat n + 1)

def elements (s : Collection) : List Int :=
  if s.kind == .huge then positiveValues ++ s.values else s.values

def member (s : Collection) (x : Int) : Bool :=
  if s.kind == .huge then decide (0 < x) || s.values.contains x else s.values.contains x

def push (s : Collection) (x : Int) : Collection :=
  if s.kind == .huge && decide (0 < x) then s
  else { s with values := x :: s.values.filter (fun y => y != x) }

abbrev calls : Calls Int where
  C := Collection
  Error := Unit
  elements := elements
  equal := fun x y => x == y
  hasLength := fun _ => true
  length := fun s => if s.kind == .huge then
    if s.values.isEmpty then .ok (int (IntTy.max .i64)) else .error ()
    else .ok (int s.values.length)
  hasFastIn := fun s => s.kind != .vector
  isAbstractSet := fun s => s.kind != .vector
  isIntegerRange := fun _ => false
  isEmptyRange := fun s => s.kind != .huge && s.values.isEmpty
  member := fun s x => .ok (member s x)
  makeSet := fun s => if s.kind == .huge then .error ()
    else .ok ⟨.finiteSet, s.values.eraseDups⟩
  empty := fun s => if s.kind == .huge then .error () else .ok { s with values := [] }
  emptyMutable := fun s _ => if s.kind == .huge then .error () else .ok { s with values := [] }
  emptyMutableDefault := fun s => if s.kind == .huge then .error () else .ok { s with values := [] }
  copy := Except.ok
  copyMutable := Except.ok
  sizehint := fun s _ _ => .ok s
  push := fun s x => .ok (push s x)
  delete := fun s x => if s.kind == .huge && decide (0 < x) then .error ()
    else .ok { s with values := s.values.filter (fun y => y != x) }
  filterBang := fun _ _ => .error ()
  promoteEltype := fun _ _ => .ok (.bitInteger .i64)
  elementType := fun _ => .bitInteger .i64
  subtype := fun a b => decide (a = b)
  sameType := fun a b => decide (a = b)
  intLength := Except.ok
  findminLength := fun _ => .error ()
  setindex := fun xs s k => .ok (xs.set (k - 1) s)
  getindex := fun xs k => match xs[k - 1]? with | some s => .ok s | none => .error ()
  extrema := fun _ => .error ()
  step := fun _ => .error ()
  minimum := fun _ => .error ()
  abs := fun x => .ok x.natAbs
  lessThan := fun x y => .ok (decide (x < y))
  mod := fun x y => if y == 0 then .error () else .ok (x % y)
  addWithOverflow := fun a b => (a + b, decide (IntTy.max .i64 < a.val + b.val))

def huge : Collection := ⟨.huge, []⟩
def withZero : Collection := ⟨.huge, [0]⟩
def iterator : Collection := ⟨.vector, [1, 0]⟩
def inputSet : Collection := ⟨.finiteSet, [1, 0]⟩
end Sentinel

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem DictsSetUnion_refuted : ¬ DictsSetUnion := by
  intro h
  have hf := (h Int Sentinel.calls Sentinel.huge Sentinel.inputSet (by decide) (by decide)).1 0
  revert hf
  decide

theorem DictsUnionMaxValuesBreak_refuted : ¬ DictsUnionMaxValuesBreak := by
  intro h
  have hf := h Int Sentinel.calls (.bitInteger .i64) Sentinel.huge Sentinel.iterator (by decide)
  change SameMembers Sentinel.calls Sentinel.huge Sentinel.withZero at hf
  have hh := hf 0
  revert hh
  decide

theorem AbstractUnionSpec_refuted : ¬ AbstractUnionSpec := by
  intro h
  have hf := h.2.1 Int Sentinel.calls Sentinel.huge [Sentinel.inputSet] (by decide) 0
  revert hf
  decide

end

/-! Nothing to promise:
- `sizehint!@4`: the AbstractSet fallback is a no-op capacity hint; it has no contents contract.
- `hasfastin(x)@369`: convenience forwarding to the type-level method, whose default is specified above.
- `_isdisjoint(a, b)@573`: a local branch helper with no independent public behavior.
- `_overlapping_range_isdisjoint(a, b)@610`: fallback dispatch helper covered by `isdisjoint`.
- `_overlapping_range_isdisjoint(a, b)@612`: private integer-range helper covered by `isdisjoint`.
- `mapfilter(pred, f, itr, res)@636`: private loop helper; its observable collection contract is stated through `filter`.
-/

/-! ## Registry entries -/

def entries : List Entry := [
  { id := "dicts-set-union-finite-capacity", juliaFile := "base/abstractset.jl",
    juliaFns := ["union!(s::AbstractSet, sets...)", "union!(s::AbstractSet{T}, itr)"],
    statement := "With common equality and a finite-domain or below-capacity premise, successful union! has union membership and cardinality; the general case is refuted by dicts-set-union.",
    source := "union! docstring base/abstractset.jl:62-112", status := .proven,
    prop := ``DictsSetUnionFinite, thm := some ``DictsSetUnionFinite_proven },
  { id := "dicts-union-max-values-break-finite-capacity", juliaFile := "base/abstractset.jl",
    juliaFns := ["union!(s::AbstractSet{T}, itr)", "max_values"],
    statement := "With the explicit capacity premise, successful optimized and full insertion have the same members; wider iterators preserve every push and exception without that premise.",
    source := "base/abstractset.jl:92-112", status := .proven,
    prop := ``DictsUnionMaxValuesBreakFinite, thm := some ``DictsUnionMaxValuesBreakFinite_proven },
  { id := "bitsetscov-abstractset-union-finite-capacity", juliaFile := "base/abstractset.jl",
    juliaFns := ["union(s, sets...)", "union(s::AbstractSet)", "union!(s::AbstractSet, sets...)", "max_values"],
    statement := "With common equality and the explicit capacity premise, successful unions preserve the union of stored elements and cardinality; unary copy and capacity arithmetic need no capacity premise.",
    source := "base/abstractset.jl:57-112", status := .proven,
    prop := ``AbstractUnionSpecFinite, thm := some ``AbstractUnionSpecFinite_proven },

  { id := "bitsetscov-abstractset-basic", juliaFile := "base/abstractset.jl",
    juliaFns := ["eltype(::Type{<:AbstractSet{T}})", "copy!(::AbstractSet, ::AbstractSet)"],
    statement := "An AbstractSet reports its declared element type; with common equality and the explicit capacity premise, successful copy! preserves source members.",
    source := "base/abstractset.jl:3,6-9; copy! collection contract", status := .proven,
    prop := ``AbstractSetCoreSpec, thm := some ``AbstractSetCoreSpec_proven },
  { id := "dicts-set-union", juliaFile := "base/abstractset.jl",
    juliaFns := ["union!(s::AbstractSet, sets...)", "union!(s::AbstractSet{T}, itr)"],
    statement := "After union!(s, t), membership is exactly membership in s or t, and the set length counts the distinct union.",
    source := "union! docstring base/abstractset.jl:62-84", status := .refuted,
    prop := ``DictsSetUnion, thm := some ``DictsSetUnion_refuted,
    issue := "none found (queries: union! max_values; max_values break; Set Bool InexactError)" },
  { id := "dicts-union-max-values-break", juliaFile := "base/abstractset.jl",
    juliaFns := ["union!(s::AbstractSet{T}, itr)", "max_values(::Type)", "max_values(T::Union)", "max_values(::Type{Bool})", "max_values(::Type{Nothing})"],
    statement := "The finite-keyspace early exit has the same result or exception as pushing every iterator element in order.",
    source := "union! docstring base/abstractset.jl:62-84; finite keyspace invariant", status := .refuted,
    prop := ``DictsUnionMaxValuesBreak, thm := some ``DictsUnionMaxValuesBreak_refuted,
    issue := "none found (queries: union! max_values; max_values break; Set Bool InexactError)" },
  { id := "bitsetscov-abstractset-union", juliaFile := "base/abstractset.jl",
    juliaFns := ["union(s, sets...)", "union(s::AbstractSet)", "union!(s::AbstractSet, sets...)", "union!(s::AbstractSet{T}, itr)", "max_values(::Type)", "max_values(T::Union)", "max_values(::Type{Bool})", "max_values(::Type{Nothing})", "max_values(T::Union{map(X -> Type{X}, BitIntegerSmall_types)...})"],
    statement := "Union preserves every input member and max_values gives the finite element capacity, saturating at typemax(Int) for union types.",
    source := "union and union! docstrings base/abstractset.jl:13-112", status := .refuted,
    prop := ``AbstractUnionSpec, thm := some ``AbstractUnionSpec_refuted,
    issue := "none found (queries: union! max_values; max_values break; Set Bool InexactError)" },
  { id := "abstractset-array-order", juliaFile := "base/abstractset.jl",
    juliaFns := ["union(s, sets...)", "intersect(s)", "setdiff(s)", "symdiff(s, sets...)", "symdiff(s)"],
    statement := "Array union keeps distinct elements in first-appearance order, while one-argument intersection and difference and symmetric difference retain source-relative order.",
    source := "union docstring base/abstractset.jl:13-24; intersect 120-121; setdiff 205-207; symdiff 258-263", status := .proven,
    prop := ``ArrayOrderSpec, thm := some ``arrayOrderSpec_proven },
  { id := "dicts-set-intersect", juliaFile := "base/abstractset.jl",
    juliaFns := ["intersect!(s::AbstractSet, s2::AbstractSet)"],
    statement := "With common equality and successful calls, intersect!(s,t) retains exactly elements in both sets; no capacity premise is required.",
    source := "intersect! docstring base/abstractset.jl:184-191", status := .proven,
    prop := ``DictsSetIntersect, thm := some ``DictsSetIntersect_proven },
  { id := "bitsetscov-abstractset-intersect", juliaFile := "base/abstractset.jl",
    juliaFns := ["intersect(s::AbstractSet, itr, itrs...)", "intersect(s)", "intersect(s::AbstractSet, itr)", "intersect!(s::AbstractSet, itrs...)", "intersect!(s::AbstractSet, s2::AbstractSet)", "intersect!(s::AbstractSet, itr)"],
    statement := "With common equality, successful intersection keeps elements present in every input; paths invoking union! have the explicit capacity premise, while the two-set and unary paths do not.",
    source := "intersect and intersect! docstrings base/abstractset.jl:114-200", status := .proven,
    prop := ``AbstractIntersectSpec, thm := some ``AbstractIntersectSpec_proven },
  { id := "bitsetscov-abstractset-setdiff", juliaFile := "base/abstractset.jl",
    juliaFns := ["setdiff(s::AbstractSet, itrs...)", "setdiff(s)", "setdiff!(s::AbstractSet, itrs...)", "setdiff!(s::AbstractSet, itr)"],
    statement := "With common equality and successful calls, set difference retains elements of the first set that occur in none of the other iterables.",
    source := "setdiff and setdiff! docstrings base/abstractset.jl:202-255", status := .proven,
    prop := ``AbstractSetdiffSpec, thm := some ``AbstractSetdiffSpec_proven },
  { id := "dicts-set-symdiff", juliaFile := "base/abstractset.jl",
    juliaFns := ["symdiff!(s::AbstractSet, itr::AbstractSet)"],
    statement := "With common equality and successful calls, symdiff!(s,t) has exclusive-or membership.",
    source := "symdiff! docstring base/abstractset.jl:281-289", status := .proven,
    prop := ``DictsSetSymdiff, thm := some ``DictsSetSymdiff_proven },
  { id := "iddicts-idset-symdiff", juliaFile := "base/abstractset.jl",
    juliaFns := ["symdiff(s, sets...)", "symdiff!(s::AbstractSet, itr)"],
    statement := "For an identity-based set, symmetric difference toggles membership by object identity for each input element.",
    source := "symdiff! docstring base/abstractset.jl:281-289; IdSet identity semantics", status := .refuted,
    prop := ``IdSetSymdiffIdentity, thm := some ``IdSetSymdiffIdentity_refuted,
    issue := "related #61893 (open); none found (queries: IdSet symdiff, symdiff Set itr, symdiff IdSet, symdiff, IdSet)" },
  { id := "bitsetscov-abstractset-symdiff", juliaFile := "base/abstractset.jl",
    juliaFns := ["symdiff(s, sets...)", "symdiff(s)", "symdiff!(s::AbstractSet, itrs...)", "symdiff!(s::AbstractSet, itr)", "symdiff!(s::AbstractSet, itr::AbstractSet)"],
    statement := "With common equality and successful calls, symmetric difference retains elements occurring in an odd number of input sets.",
    source := "symdiff and symdiff! docstrings base/abstractset.jl:258-304", status := .proven,
    prop := ``AbstractSymdiffSpec, thm := some ``AbstractSymdiffSpec_proven },
  { id := "dicts-set-compare", juliaFile := "base/abstractset.jl",
    juliaFns := ["issubset(a, b)", "==(a::AbstractSet, b::AbstractSet)"],
    statement := "With common equality and successful calls, issubset decides inclusion and AbstractSet equality decides equality of stored element sets.",
    source := "issubset docstring base/abstractset.jl:310-330; equality method base/abstractset.jl:622", status := .proven,
    prop := ``DictsSetCompare, thm := some ``DictsSetCompare_proven },
  { id := "dicts-issubset-vector-threshold", juliaFile := "base/abstractset.jl",
    juliaFns := ["issubset(a, b)"],
    statement := "For collections with linear membership, issubset returns true exactly when every member of a is a member of b, independent of the optimization threshold.",
    source := "issubset docstring base/abstractset.jl:310-330 (using in)", status := .refuted,
    prop := ``IssubsetVectorSemantics, thm := some ``IssubsetVectorSemantics_refuted,
    issue := "#61893" },
  { id := "iddicts-idset-issubset", juliaFile := "base/abstractset.jl",
    juliaFns := ["issubset(a, b)"],
    statement := "For an identity-based set a, issubset(a, b) is true exactly when every a member is in b.",
    source := "issubset docstring base/abstractset.jl:310-330", status := .refuted,
    prop := ``IdSetIssubsetIn, thm := some ``IdSetIssubsetIn_refuted,
    issue := "related #61893 (open); none found (queries: issubset IdSet, IdSet issubset, issubset AbstractSet length, issubset length shortcut, issubset)" },
  { id := "bitsetscov-abstractset-subset", juliaFile := "base/abstractset.jl",
    juliaFns := ["issubset(a, b)", "hasfastin(::Type)", "hasfastin(::Union{Type{<:AbstractSet},Type{<:AbstractDict},Type{<:AbstractRange}})", "⊇(a, b)", "issubset(a)", "⊇(a)", "⊊(a::AbstractSet, b::AbstractSet)", "⊊(a::AbstractSet, b)", "⊊(a, b::AbstractSet)", "⊊(a, b)", "⊋(a, b)", "⊋(a)", "⊊(a)", "⊈(a, b)", "⊉(a, b)", "⊉(a)", "⊈(a)"],
    statement := "With common equality and successful calls, subset, reverse and strict subset, their negations, and Fix2 wrappers agree with the stored-element relations.",
    source := "subset docstrings base/abstractset.jl:310-500", status := .proven,
    prop := ``AbstractSubsetSpec, thm := some ``AbstractSubsetSpec_proven },
  { id := "bitsetscov-abstractset-issetequal", juliaFile := "base/abstractset.jl",
    juliaFns := ["issetequal(a::AbstractSet, b::AbstractSet)", "issetequal(a::AbstractSet, b)", "issetequal(a, b::AbstractSet)", "issetequal(a, b)", "issetequal(a)"],
    statement := "With common equality and successful calls, issetequal decides equality of stored element sets; its Fix2 form applies the same comparison.",
    source := "issetequal docstring base/abstractset.jl:504-520,538-549", status := .proven,
    prop := ``AbstractSetequalSpec, thm := some ``AbstractSetequalSpec_proven },
  { id := "iddicts-idset-issetequal", juliaFile := "base/abstractset.jl",
    juliaFns := ["issetequal(a::AbstractSet, b::AbstractSet)", "issetequal(a::AbstractSet, b)", "issetequal(a, b::AbstractSet)", "==(a::AbstractSet, b::AbstractSet)"],
    statement := "For identity-based sets, issetequal agrees with the conjunction of subset checks in either argument order.",
    source := "issetequal docstring base/abstractset.jl:504-510", status := .refuted,
    prop := ``IdSetIssetequalSubsets, thm := some ``IdSetIssetequalSubsets_refuted,
    issue := "related #61893 (open), #41748 (closed); none found (queries: IdSet issetequal, issetequal IdSet, issetequal length, issetequal, IdSet ==)" },
  { id := "bitsetscov-isdisjoint-threshold", juliaFile := "base/abstractset.jl",
    juliaFns := ["isdisjoint(a, b)"],
    statement := "isdisjoint reports true exactly when the collections have no common members, regardless of which size-based search branch runs.",
    source := "isdisjoint docstring base/abstractset.jl:551-571", status := .refuted,
    prop := ``IsdisjointSizeIndependent, thm := some ``IsdisjointSizeIndependent_refuted,
    issue := "related #61893" },
  { id := "bitsetscov-isdisjoint-zero-step", juliaFile := "base/abstractset.jl",
    juliaFns := ["isdisjoint(a::AbstractRange{T}, b::AbstractRange{T})"],
    statement := "Integer range disjointness returns a Bool and agrees with whether the generated ranges share any element, including zero-step ranges.",
    source := "isdisjoint docstring base/abstractset.jl:551-571; range fast path base/abstractset.jl:586-618", status := .refuted,
    prop := ``RangeIsdisjointSpec, thm := some ``RangeIsdisjointSpec_refuted,
    issue := "related #47796; none found for zero-step isdisjoint" },
  { id := "bitsetscov-abstractset-disjoint-filter", juliaFile := "base/abstractset.jl",
    juliaFns := ["isdisjoint(a, b)", "isdisjoint(a::AbstractRange{T}, b::AbstractRange{T})", "isdisjoint(a)", "<(a::AbstractSet, b::AbstractSet)", "<=(a::AbstractSet, b::AbstractSet)", "filter(pred, s::AbstractSet)", "unsafe_filter!(pred, s::AbstractSet)"],
    statement := "Disjointness and range comparisons match member overlap, containment ordering matches subset relations, and filtering keeps exactly accepted members.",
    source := "isdisjoint docstring base/abstractset.jl:551-571; range methods 586-618; filtering methods 625-641", status := .refuted,
    prop := ``AbstractDisjointFilterSpec, thm := some ``AbstractDisjointFilterSpec_refuted,
    issue := "related #61893 (open) (queries: isdisjoint threshold; isdisjoint isequal; isdisjoint range; isdisjoint DivideError)" }
]

/-! ## Method -> property table

| Julia method | Property |
|---|---|
| eltype(::Type{<:AbstractSet{T}})@3 | bitsetscov-abstractset-basic |
| sizehint!(::AbstractSet, n)@4 | Nothing to promise |
| copy!(::AbstractSet, ::AbstractSet)@6 | bitsetscov-abstractset-basic |
| union(s, sets...)@57 | bitsetscov-abstractset-union, abstractset-array-order |
| union(s::AbstractSet)@58 | bitsetscov-abstractset-union |
| union!(s::AbstractSet, sets...)@85 | dicts-set-union, bitsetscov-abstractset-union |
| max_values(::Type)@92 | bitsetscov-abstractset-union |
| max_values(T::Union{map(X -> Type{X}, BitIntegerSmall_types)...})@93 | bitsetscov-abstractset-union |
| max_values(::Union)@95 | bitsetscov-abstractset-union |
| max_values(::Type{Bool})@102 | bitsetscov-abstractset-union |
| max_values(::Type{Nothing})@103 | bitsetscov-abstractset-union |
| union!(s::AbstractSet{T}, itr)@105 | dicts-set-union, dicts-union-max-values-break, bitsetscov-abstractset-union |
| intersect(s::AbstractSet, itr, itrs...)@155 | bitsetscov-abstractset-intersect |
| intersect(s)@173 | bitsetscov-abstractset-intersect, abstractset-array-order |
| intersect(s::AbstractSet, itr)@174 | bitsetscov-abstractset-intersect |
| intersect!(s::AbstractSet, itrs...)@192 | bitsetscov-abstractset-intersect |
| intersect!(s::AbstractSet, s2::AbstractSet)@198 | dicts-set-intersect, bitsetscov-abstractset-intersect |
| intersect!(s::AbstractSet, itr)@199 | bitsetscov-abstractset-intersect |
| setdiff(s::AbstractSet, itrs...)@222 | bitsetscov-abstractset-setdiff |
| setdiff(s)@223 | bitsetscov-abstractset-setdiff, abstractset-array-order |
| setdiff!(s::AbstractSet, itrs...)@244 | bitsetscov-abstractset-setdiff |
| setdiff!(s::AbstractSet, itr)@250 | bitsetscov-abstractset-setdiff |
| symdiff(s, sets...)@278 | bitsetscov-abstractset-symdiff, abstractset-array-order |
| symdiff(s)@279 | bitsetscov-abstractset-symdiff, abstractset-array-order |
| symdiff!(s::AbstractSet, itrs...)@290 | bitsetscov-abstractset-symdiff |
| symdiff!(s::AbstractSet, itr)@297 | iddicts-idset-symdiff, bitsetscov-abstractset-symdiff |
| symdiff!(s::AbstractSet, itr::AbstractSet)@299 | dicts-set-symdiff, bitsetscov-abstractset-symdiff |
| issubset(a, b)@335 | dicts-set-compare, dicts-issubset-vector-threshold, iddicts-idset-issubset, bitsetscov-abstractset-subset |
| hasfastin(::Type)@367 | bitsetscov-abstractset-subset |
| hasfastin(::Union{Type{<:AbstractSet},Type{<:AbstractDict},Type{<:AbstractRange}})@368 | bitsetscov-abstractset-subset |
| hasfastin(x)@369 | Nothing to promise |
| ⊇(a, b)@371 | bitsetscov-abstractset-subset |
| issubset(a)@384 | bitsetscov-abstractset-subset |
| ⊇(a)@397 | bitsetscov-abstractset-subset |
| ⊊(a::AbstractSet, b::AbstractSet)@421 | bitsetscov-abstractset-subset |
| ⊊(a::AbstractSet, b)@422 | bitsetscov-abstractset-subset |
| ⊊(a, b::AbstractSet)@423 | bitsetscov-abstractset-subset |
| ⊊(a, b)@424 | bitsetscov-abstractset-subset |
| ⊋(a, b)@425 | bitsetscov-abstractset-subset |
| ⊋(a)@438 | bitsetscov-abstractset-subset |
| ⊊(a)@450 | bitsetscov-abstractset-subset |
| ⊈(a, b)@473 | bitsetscov-abstractset-subset |
| ⊉(a, b)@474 | bitsetscov-abstractset-subset |
| ⊉(a)@487 | bitsetscov-abstractset-subset |
| ⊈(a)@500 | bitsetscov-abstractset-subset |
| issetequal(a::AbstractSet, b::AbstractSet)@521 | bitsetscov-abstractset-issetequal, iddicts-idset-issetequal |
| issetequal(a::AbstractSet, b)@522 | bitsetscov-abstractset-issetequal, iddicts-idset-issetequal |
| issetequal(a, b::AbstractSet)@524 | bitsetscov-abstractset-issetequal, iddicts-idset-issetequal |
| issetequal(a, b)@532 | bitsetscov-abstractset-issetequal |
| issetequal(a)@549 | bitsetscov-abstractset-issetequal |
| _isdisjoint(a, b)@573 | Nothing to promise |
| isdisjoint(a, b)@572 | bitsetscov-isdisjoint-threshold, bitsetscov-abstractset-disjoint-filter |
| isdisjoint(a::AbstractRange{T}, b::AbstractRange{T})@586 | bitsetscov-isdisjoint-zero-step, bitsetscov-abstractset-disjoint-filter |
| isdisjoint(a)@608 | bitsetscov-abstractset-disjoint-filter |
| _overlapping_range_isdisjoint(a::AbstractRange{T}, b::AbstractRange{T})@610 | Nothing to promise |
| _overlapping_range_isdisjoint(a::AbstractRange{T}, b::AbstractRange{T}) where T<:Integer@612 | Nothing to promise |
| ==(a::AbstractSet, b::AbstractSet)@622 | dicts-set-compare, bitsetscov-abstractset-subset |
| <(a::AbstractSet, b::AbstractSet)@625 | bitsetscov-abstractset-subset, bitsetscov-abstractset-disjoint-filter |
| <=(a::AbstractSet, b::AbstractSet)@626 | bitsetscov-abstractset-subset, bitsetscov-abstractset-disjoint-filter |
| filter(pred, s::AbstractSet)@630 | bitsetscov-abstractset-disjoint-filter |
| unsafe_filter!(pred, s::AbstractSet)@633 | bitsetscov-abstractset-disjoint-filter |
| mapfilter(pred, f, itr, res)@636 | Nothing to promise |
-/

end JuliaLean.Proofs.base.abstractset
