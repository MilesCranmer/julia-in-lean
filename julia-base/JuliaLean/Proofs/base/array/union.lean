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

open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def IntersectRangeVectorOrder : Prop :=
  ∀ (range vector : List Int),
    let promoteEltype := fun (_ _ : List Int) => ()
    let contains := fun (range : List Int) (value : Int) => decide (value ∈ range)
    let iteratorFilter := fun (test : Int → Bool) (values : List Int) => values.filter test
    let makeSet := fun (_ : Unit) (common : List Int) =>
      (do set common.eraseDups; pure () : StateT (List Int) (MutationM Int) Unit)
    let shrink := shrinkFilter (m := StateT (List Int) (MutationM Int))
      (fun (value : Int) (_ : Unit) => do return value ∈ (← get))
      (fun (_ : Unit) (value : Int) => modify (fun values => values.erase value))
    let vfilter := fun (t : Unit) (test : Int → StateT (List Int) (MutationM Int) Bool)
        (values : List Int) =>
      vectorfilter (literalFilterCollectOps (pure 0)
        (typedLiteral (fun n => liftM (mutableAllocate (α := Int) (some ⟨8, false, false⟩) 0 n))
          (fun a x i => liftM (mutableTypedSet (α := Int) a x i)) true)) t test values
    let forward := ((intersectVectorRange promoteEltype contains iteratorFilter makeSet shrink
      vfilter vector range).run []).run ⟨[], []⟩
    let backward := ((intersectRangeVector promoteEltype contains iteratorFilter makeSet shrink
      vfilter range vector).run []).run ⟨[], []⟩
    forward.1.map (fun (handle, _) => forward.2.contents handle) =
      .ok ((vector.filter (fun x => decide (x ∈ range))).eraseDups.map some) ∧
    backward.1.map (fun (handle, _) => backward.2.contents handle) =
      .ok ((range.filter (fun x => decide (x ∈ vector))).eraseDups.map some)

@[simp] theorem vector_ite_run (p : Prop) [Decidable p]
    (yes no : VectorM α β) (heap : VectorHeap α) :
    (if p then yes else no).run heap =
      if p then yes.run heap else no.run heap := by
  split <;> rfl

theorem tupleVectorGet_methodError {X A E V R : Type}
    (values : R → List I) (find : R → I → I → Jl R) (getRange : R → R → Jl R)
    (fill : X → E → Jl Unit) (size : A → Jl (List I))
    (get : A → List (List I) → Jl V) (set : X → List (List I) → V → Jl Unit)
    (x : X) (a : A) (default : E) (dims : List I) (vector : List I)
    (rest : List (IndcopyTupleIndex R))
    (hf : fill x default = .ok ()) (hs : size a = .ok dims) :
    JuliaLean.base.abstractarray.getIndexList fill size (tupleIndcopy values find getRange)
      get set x a (.vector vector :: rest) default = .error (.methodError "indcopy") := by
  simp [JuliaLean.base.abstractarray.getIndexList, hf, hs, tupleIndcopy, indcopyRangeEntry,
    List.mapM_cons, Bind.bind, Pure.pure, Except.bind, Except.pure]
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section VectorSets

variable {α : Type} [DecidableEq α]

/-- `filter!(pred, v)` on the tracked vector. -/
def vecFilter (pred : α → SetM α Bool) (_ : Unit) : SetM α Unit := do
  let ys ← (← get).vec.filterM pred
  modify fun st => { st with vec := ys }

/-- `push!(v, x)` on the tracked vector. -/
def vecPush (_ : Unit) (x : α) : SetM α Unit :=
  modify fun st => { st with vec := st.vec ++ [x] }

/-- `mapfilter(pred, push!, itr, v)` (abstractset.jl). -/
def mapfilterList (pred : α → SetM α Bool) (push : Unit → α → SetM α Unit) :
    List α → Unit → SetM α Unit
  | [], _ => pure ()
  | x :: xs, v => do
    if ← pred x then push v x
    mapfilterList pred push xs v

theorem dedupFrom_not_mem (seen : List α) :
    ∀ (xs : List α) (y : α), y ∈ dedupFrom seen xs → y ∉ seen := by
  intro xs
  induction xs generalizing seen with
  | nil => intro y hy; simp [dedupFrom] at hy
  | cons x xs ih =>
    intro y hy
    unfold dedupFrom at hy
    by_cases hx : x ∈ seen
    · simp only [hx, ite_true] at hy
      exact ih seen y hy
    · simp only [hx, ite_false, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hx
      · have := ih (seen ++ [x]) y hy
        simp only [List.mem_append, not_or] at this
        exact this.1

theorem firstIn_eq_filter_dedup :
    ∀ (xs keep seen : List α), keep.Nodup → (∀ x ∈ keep, x ∉ seen) →
      firstIn keep xs = (dedupFrom seen xs).filter (fun x => decide (x ∈ keep)) := by
  intro xs
  induction xs with
  | nil => intro keep seen _ _; simp [firstIn, dedupFrom]
  | cons x xs ih =>
    intro keep seen hnd hdis
    by_cases hs : x ∈ seen
    · have hk : x ∉ keep := fun hk => hdis x hk hs
      simp only [firstIn, dedupFrom, hs, hk, ite_true, ite_false]
      exact ih keep seen hnd hdis
    · by_cases hk : x ∈ keep
      · simp only [firstIn, dedupFrom, hs, hk, ite_true, ite_false, List.filter_cons,
          decide_true]
        congr 1
        rw [ih (keep.erase x) (seen ++ [x]) (hnd.erase x) (fun y hy hys => by
          rw [List.mem_append, List.mem_singleton] at hys
          rcases hys with hys | rfl
          · exact hdis y ((List.mem_erase_of_ne (by rintro rfl; exact hs hys)).mp hy) hys
          · exact (List.Nodup.not_mem_erase hnd) hy)]
        apply List.filter_congr
        intro y hy
        have hyx : y ≠ x := by
          intro hyx
          subst hyx
          have := dedupFrom_not_mem (seen ++ [y]) xs y hy
          simp at this
        simp only [List.mem_erase_of_ne hyx]
      · simp only [firstIn, dedupFrom, hs, hk, ite_false, List.filter_cons, decide_false]
        exact ih keep (seen ++ [x]) hnd (fun y hy hys => by
          rw [List.mem_append, List.mem_singleton] at hys
          rcases hys with hys | rfl
          · exact hdis y hy hys
          · exact hk hy)

/-- The `_grow_filter!(seen)` loop over `xs`. -/
theorem growFilter_filterAux (v : List α) :
    ∀ (xs acc seen : List α),
      (List.filterAuxM (growFilter setNotin setPush ()) xs acc).run ⟨v, seen⟩ =
        ((dedupFrom seen xs).reverse ++ acc, ⟨v, seen ++ dedupFrom seen xs⟩) := by
  intro xs
  induction xs with
  | nil => intro acc seen; simp [List.filterAuxM, dedupFrom]; rfl
  | cons x xs ih =>
    intro acc seen
    by_cases hx : x ∈ seen
    · simp only [List.filterAuxM, dedupFrom, hx, ite_true]
      have := ih acc seen
      simp [growFilter, uniqueFilter, setNotin, hx] at this ⊢
      exact this
    · simp only [List.filterAuxM, dedupFrom, hx, ite_false]
      have := ih (x :: acc) (seen ++ [x])
      simp [growFilter, uniqueFilter, setNotin, setPush, hx] at this ⊢
      exact this

/-- The `_shrink_filter!(keep)` loop over `xs`. -/
theorem shrinkFilter_filterAux (v : List α) :
    ∀ (xs acc keep : List α),
      (List.filterAuxM (shrinkFilter setIn setPop ()) xs acc).run ⟨v, keep⟩ =
        ((firstIn keep xs).reverse ++ acc, ⟨v, firstInRest keep xs⟩) := by
  intro xs
  induction xs with
  | nil => intro acc keep; simp [List.filterAuxM, firstIn, firstInRest]; rfl
  | cons x xs ih =>
    intro acc keep
    by_cases hx : x ∈ keep
    · simp only [List.filterAuxM, firstIn, firstInRest, hx, ite_true]
      have := ih (x :: acc) (keep.erase x)
      simp [shrinkFilter, uniqueFilter, setIn, setPop, hx] at this ⊢
      exact this
    · simp only [List.filterAuxM, firstIn, firstInRest, hx, ite_false]
      have := ih acc keep
      simp [shrinkFilter, uniqueFilter, setIn, hx] at this ⊢
      exact this

theorem growFilter_filterM (v xs seen : List α) :
    (xs.filterM (growFilter setNotin setPush ())).run ⟨v, seen⟩ =
      (dedupFrom seen xs, ⟨v, seen ++ dedupFrom seen xs⟩) := by
  have := growFilter_filterAux v xs [] seen
  simp only [List.append_nil] at this
  simp only [List.filterM, StateT.run_bind, this]
  change ((dedupFrom seen xs).reverse.reverse, _) = _
  rw [List.reverse_reverse]

theorem shrinkFilter_filterM (v xs keep : List α) :
    (xs.filterM (shrinkFilter setIn setPop ())).run ⟨v, keep⟩ =
      (firstIn keep xs, ⟨v, firstInRest keep xs⟩) := by
  have := shrinkFilter_filterAux v xs [] keep
  simp only [List.append_nil] at this
  simp only [List.filterM, StateT.run_bind, this]
  change ((firstIn keep xs).reverse.reverse, _) = _
  rw [List.reverse_reverse]

theorem dedupFrom_append (xs ys seen : List α) :
    dedupFrom seen (xs ++ ys) = dedupFrom seen xs ++ dedupFrom (seen ++ dedupFrom seen xs) ys := by
  induction xs generalizing seen with
  | nil => simp [dedupFrom]
  | cons x xs ih =>
    by_cases hx : x ∈ seen
    · simp only [List.cons_append, dedupFrom, hx, ite_true]
      exact ih seen
    · simp only [List.cons_append, dedupFrom, hx, ite_false, List.append_assoc,
        List.singleton_append]
      rw [ih (seen ++ [x])]
      simp

theorem firstIn_append (xs ys keep : List α) :
    firstIn keep (xs ++ ys) = firstIn keep xs ++ firstIn (firstInRest keep xs) ys := by
  induction xs generalizing keep with
  | nil => simp [firstIn, firstInRest]
  | cons x xs ih =>
    by_cases hx : x ∈ keep
    · simp only [List.cons_append, firstIn, firstInRest, hx, ite_true, ih]
    · simp only [List.cons_append, firstIn, firstInRest, hx, ite_false, ih]

theorem mapfilter_grow_run (v seen : List α) :
    ∀ xs, (mapfilterList (growFilter setNotin setPush ()) vecPush xs ()).run ⟨v, seen⟩ =
      ((), ⟨v ++ dedupFrom seen xs, seen ++ dedupFrom seen xs⟩) := by
  intro xs
  induction xs generalizing v seen with
  | nil => simp [mapfilterList, dedupFrom]; rfl
  | cons x xs ih =>
    by_cases hx : x ∈ seen
    · have := ih v seen
      simp [mapfilterList, growFilter, uniqueFilter, setNotin, dedupFrom, hx] at this ⊢
      exact this
    · have := ih (v ++ [x]) (seen ++ [x])
      simp [mapfilterList, growFilter, uniqueFilter, setNotin, setPush, vecPush, dedupFrom, hx]
        at this ⊢
      exact this

theorem mapfilter_shrink_run (v keep : List α) :
    ∀ xs, (mapfilterList (shrinkFilter setIn setPop ()) vecPush xs ()).run ⟨v, keep⟩ =
      ((), ⟨v ++ firstIn keep xs, firstInRest keep xs⟩) := by
  intro xs
  induction xs generalizing v keep with
  | nil => simp [mapfilterList, firstIn, firstInRest]; rfl
  | cons x xs ih =>
    by_cases hx : x ∈ keep
    · have := ih (v ++ [x]) (keep.erase x)
      simp [mapfilterList, shrinkFilter, uniqueFilter, setIn, setPop, vecPush, firstIn,
        firstInRest, hx] at this ⊢
      exact this
    · have := ih v keep
      simp [mapfilterList, shrinkFilter, uniqueFilter, setIn, firstIn, firstInRest, hx]
        at this ⊢
      exact this

/-- A `for` loop over a list whose body only updates the store. -/
theorem setForIn_run {β : Type} (F : β → PUnit → SetM α (ForInStep PUnit))
    (step : VecSet α → β → VecSet α)
    (hF : ∀ b st, (F b PUnit.unit).run st = (.yield PUnit.unit, step st b)) :
    ∀ (bs : List β) (st : VecSet α),
      (forIn bs PUnit.unit F).run st = (PUnit.unit, bs.foldl step st) := by
  intro bs
  induction bs with
  | nil => intro st; rfl
  | cons b bs ih =>
    intro st
    have h1 := hF b st
    simp only [List.forIn_cons, List.foldl_cons, StateT.run_bind, h1]
    exact ih (step st b)

theorem dedupFrom_nodup (seen : List α) : ∀ xs : List α, (dedupFrom seen xs).Nodup := by
  intro xs
  induction xs generalizing seen with
  | nil => simp [dedupFrom]
  | cons x xs ih =>
    unfold dedupFrom
    by_cases hx : x ∈ seen
    · simp only [hx, ite_true]; exact ih seen
    · simp only [hx, ite_false]
      refine List.nodup_cons.mpr ⟨fun hm => ?_, ih (seen ++ [x])⟩
      have := dedupFrom_not_mem (seen ++ [x]) xs x hm
      simp at this

theorem firstInRest_append (xs ys keep : List α) :
    firstInRest keep (xs ++ ys) = firstInRest (firstInRest keep xs) ys := by
  induction xs generalizing keep with
  | nil => simp [firstInRest]
  | cons x xs ih =>
    by_cases hx : x ∈ keep
    · simp only [List.cons_append, firstInRest, hx, ite_true, ih]
    · simp only [List.cons_append, firstInRest, hx, ite_false, ih]

/-- A membership test that does not change the store. -/
theorem setIn_filterAux (st : VecSet α) :
    ∀ (xs acc : List α), (List.filterAuxM (fun x => setIn x ()) xs acc).run st =
      ((xs.filter (fun x => decide (x ∈ st.set))).reverse ++ acc, st) := by
  intro xs
  induction xs with
  | nil => intro acc; simp [List.filterAuxM]; rfl
  | cons x xs ih =>
    intro acc
    by_cases hx : x ∈ st.set
    · have := ih (x :: acc)
      simp [List.filterAuxM, setIn, hx] at this ⊢
      exact this
    · have := ih acc
      simp [List.filterAuxM, setIn, hx] at this ⊢
      exact this

theorem setIn_filterM (st : VecSet α) (xs : List α) :
    (xs.filterM (fun x => setIn x ())).run st = (xs.filter (fun x => decide (x ∈ st.set)), st) := by
  have := setIn_filterAux st xs []
  simp only [List.append_nil] at this
  simp only [List.filterM, StateT.run_bind, this]
  change ((xs.filter _).reverse.reverse, _) = _
  rw [List.reverse_reverse]

def setEmpty : SetM α Unit := modify fun st => { st with set := [] }

/-- One `mapfilter(_grow_filter!(seen), push!, itr, v)` step. -/
def unionStep (st : VecSet α) (itr : List α) : VecSet α :=
  ⟨st.vec ++ dedupFrom st.set itr, st.set ++ dedupFrom st.set itr⟩

/-- One `mapfilter(_shrink_filter!(keep), push!, itr, v)` step. -/
def shrinkStep (st : VecSet α) (itr : List α) : VecSet α :=
  ⟨st.vec ++ firstIn st.set itr, firstInRest st.set itr⟩

theorem union_fold (itrs : List (List α)) :
    ∀ xs : List α, itrs.foldl unionStep ⟨dedupFrom [] xs, dedupFrom [] xs⟩ =
      ⟨dedupFrom [] (xs ++ itrs.flatten), dedupFrom [] (xs ++ itrs.flatten)⟩ := by
  induction itrs with
  | nil => intro xs; simp
  | cons itr itrs ih =>
    intro xs
    have h := dedupFrom_append xs itr []
    simp only [List.nil_append] at h
    have hs : unionStep ⟨dedupFrom [] xs, dedupFrom [] xs⟩ itr =
        ⟨dedupFrom [] (xs ++ itr), dedupFrom [] (xs ++ itr)⟩ := by
      simp only [unionStep, h]
    rw [List.foldl_cons, hs, ih (xs ++ itr), List.flatten_cons, List.append_assoc]

theorem shrink_fold (itrs : List (List α)) :
    ∀ (keep xs : List α), itrs.foldl shrinkStep ⟨firstIn keep xs, firstInRest keep xs⟩ =
      ⟨firstIn keep (xs ++ itrs.flatten), firstInRest keep (xs ++ itrs.flatten)⟩ := by
  induction itrs with
  | nil => intro keep xs; simp
  | cons itr itrs ih =>
    intro keep xs
    have hs : shrinkStep ⟨firstIn keep xs, firstInRest keep xs⟩ itr =
        ⟨firstIn keep (xs ++ itr), firstInRest keep (xs ++ itr)⟩ := by
      simp only [shrinkStep, firstIn_append, firstInRest_append]
    rw [List.foldl_cons, hs, ih keep (xs ++ itr), List.flatten_cons, List.append_assoc]

/-- `union!(v::AbstractVector, itrs...)` (array.jl:3180-3181) through `_grow!` (array.jl:3172-3178)
with `_grow_filter!` (array.jl:3169) and `_unique_filter!` (array.jl:3159-3167); `union!`
docstring in abstractset.jl: `v` ends holding every value of `v` and of the `itrs`, each once, in
order of first appearance. -/
def UnionBangSpec : Prop :=
  ∀ (α : Type) [DecidableEq α] (v seen : List α) (itrs : List (List α)),
    ((unionBang (m := SetM α) setEmpty (fun _ => pure zero) (fun s _ => pure s)
        (growFilter setNotin setPush) (grow vecFilter vecPush mapfilterList) () itrs).run
        ⟨v, seen⟩).2.vec = dedupFrom [] (v ++ itrs.flatten)

def oddSet (v : List α) (itrs : List (List α)) : List α :=
  (dedupFrom [] (v ++ itrs.flatten)).filter
    (fun x => ((v :: itrs).filter (fun l => decide (x ∈ l))).length % 2 == 1)

/-- `symdiff!(v::AbstractVector, itrs...)` (array.jl:3183-3184) through `_grow!` with
`_shrink_filter!` (array.jl:3170); `symdiff!` docstring in abstractset.jl: `v` ends holding the
values lying in an odd number of the arguments, each once, in order of first appearance across
`v, itrs...`. The set operation `symdiff!(Set{T}(), v, itrs...)` is the set of those values. -/
def SymdiffBangSpec : Prop :=
  ∀ (α : Type) [DecidableEq α] (v seen : List α) (itrs : List (List α)),
    ((symdiffBang (m := SetM α) setEmpty
        (fun _ _ itrs => modify fun st => { st with set := oddSet st.vec itrs })
        (shrinkFilter setIn setPop) (grow vecFilter vecPush mapfilterList) () itrs).run
        ⟨v, seen⟩).2.vec = oddSet v itrs

theorem shrink_keep (d : List α) (P : α → Bool) :
    d.filter (fun x => decide (x ∈ d.filter P)) = d.filter P := by
  apply List.filter_congr
  intro y hy
  simp [List.mem_filter, hy]

theorem unique_filter_odd (v : List α) (itrs : List (List α)) :
    firstIn (oddSet v itrs) (v ++ itrs.flatten) = oddSet v itrs := by
  unfold oddSet
  rw [firstIn_eq_filter_dedup _ _ [] ((dedupFrom_nodup [] _).filter _) (by simp)]
  exact shrink_keep _ _

def ShrinkBangSpec : Prop :=
  ∀ (α : Type) [DecidableEq α] (v seen : List α) (itrs : List (List α)),
    let shrinkWith := fun op v itrs => shrink (m := SetM α) setEmpty (growFilter setNotin setPush)
      vecFilter op (fun s x => setIn x s) v itrs
    let inAll := fun (x : α) => itrs.all (fun l => decide (x ∈ l))
    let inNone := fun (x : α) => itrs.all (fun l => decide (x ∉ l))
    ((intersectBang (fun _ itrs => modify fun st => { st with set := st.set.filter inAll })
        shrinkWith () itrs).run ⟨v, seen⟩).2.vec = (dedupFrom [] v).filter inAll ∧
    ((setdiffBang (fun _ itrs => modify fun st => { st with set := st.set.filter inNone })
        shrinkWith () itrs).run ⟨v, seen⟩).2.vec = (dedupFrom [] v).filter inNone

def IntersectSetdiffSpec : Prop :=
  ∀ (α : Type) [DecidableEq α] (st : VecSet α) (itr : List α) (itrs : List (List α)),
    let makeSet := fun (_ : Unit) (itr : List α) =>
      (modify fun st => { st with set := dedupFrom [] itr } : SetM α Unit)
    let filtered := fun (t : Unit) (test : α → SetM α Bool) (itr : List α) => do
      match ← (vectorfilter (m := ExceptT Error (SetM α))
          (literalFilterCollectOps (pure []) pure) t (fun x => ExceptT.lift (test x)) itr).run with
      | .ok ys => pure ys
      | .error _ => pure []
    let inAll := fun (x : α) => itrs.all (fun l => decide (x ∈ l))
    let inNone := fun (x : α) => itrs.all (fun l => decide (x ∉ l))
    ((intersect (fun _ _ => ()) makeSet
        (fun _ itrs => modify fun st => { st with set := st.set.filter inAll })
        (shrinkFilter setIn setPop) filtered itr itrs).run st).1 =
      (dedupFrom [] itr).filter inAll ∧
    ((setdiff (fun _ => ()) makeSet
        (fun _ itrs => modify fun st => { st with set := st.set.filter inNone })
        (shrinkFilter setIn setPop) filtered itr itrs).run st).1 =
      (dedupFrom [] itr).filter inNone

theorem firstIn_keep (itr : List α) (P : α → Bool) :
    firstIn ((dedupFrom [] itr).filter P) itr = (dedupFrom [] itr).filter P := by
  rw [firstIn_eq_filter_dedup _ _ [] ((dedupFrom_nodup [] _).filter _) (by simp)]
  exact shrink_keep _ _
end VectorSets
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- `_cat(n, x::Integer...)` (array.jl:2363), the method of `cat(x::Integer...; dims = n)`
(`cat` docstring in abstractarray.jl: "Concatenate the input arrays along the dimensions
specified in `dims`"): the integers are promoted to one type by `[x...]` (`vect`,
array.jl:183) and the result has dimensions `(1, ..., 1, length(x))` with `n - 1` leading ones,
holding them in order; `n < 1` raises `ArgumentError` (from `ntuple`). A failing promotion
raises its error. -/

def vectorIndcopy (find : List I → I → I → Jl (List I)) (get : List I → List I → Jl (List I))
    (dims : List I) (indices : List (List I)) : Jl (List (List I) × List (List I)) :=
  indcopyVector (fun dims : List I => JInt.wrap .i64 (dims.length : Int)) indcopyCoreGet
    (fun indices : List (List I) => JInt.wrap .i64 (indices.length : Int)) indcopyCoreGet
    find get pure dims indices
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

def freshVectorAllocation {Tag α : Type} (target : Tag) (n : Nat) (heap : VectorHeap α) :
    Except Error (HeapArray Tag × VectorHeap α) :=
  .ok (⟨heap.length, target, [n], [(1, n)]⟩, heap ++ [List.replicate n none])

/-- The concrete `findprev(testf, A, start)` on a fully assigned `Vector`. -/
abbrev vectorFindprev (xs : List α) (test : α → Except Error Bool) {t : IntTy}
    (start : JInt t) : Except Error (Option I) :=
  findprev (fun _ => one) (fun _ j => indexConvert j) (fun j k => decide (j.val < k.val))
    vectorGet test backwardRank prevVectorIndex xs start
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

/-- `setindex_shape_check(X, n)` (indices.jl: `length(X) == n` or `DimensionMismatch`) for a
vector `X` in mutable memory. -/
def mutableShapeCheck {α : Type} (x : Nat) (n : I) : MutationM α Unit := do
  let l ← mutableLength x
  if l ≠ n then
    throw (.dimensionMismatch ("tried to assign " ++ toString l.val ++ " elements to " ++
      toString n.val ++ " destinations"))

/-- `A[I] = X` (array.jl:1063) for vectors `A` and `X` in mutable memory and an index vector `I`
with `Int` entries `idx`: `checkbounds(A, I)` checks every index, `X` and `I` share no memory
with `A` so `unalias` returns them, `eachindex(X)` is `1:length(X)`, `I[k]` is
`getindex(::Vector, ::Int)`, `X[j]` reads the slot (raising `UndefRefError` when unassigned) and
each store is `setindex!(A::Array{T}, x, i::Int)` (array.jl:1031) with the conversion
`convert(T, x)`. -/
abbrev mutableVectorSetindex {α : Type} (already : α → Bool) (convert : α → Except Error α)
    (a x : Nat) (idx : List I) : MutationM α Nat :=
  setindexVector mutableShapeCheck (fun idx : List I => JInt.wrap .i64 idx.length)
    (fun a idx => idx.forM (fun i => mutableBounds a i)) (fun _ x => pure x)
    (fun _ idx => pure idx) (fun _ => pure one)
    (fun x => do pure (intRange one (← mutableLength x)))
    (fun idx k => stateExceptLift (vectorGet idx k)) mutableGet
    (fun a v i => do
      let _ ← setindexScalar already id (fun v => stateExceptLift (convert v)) mutableTypedSet
        a v i
      pure ())
    a x idx
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

/-- `pairs(A)` of a vector holding `xs`: `(i, A[i])` for `i` in `1:length(A)`. -/
def vectorPairs {α : Type} (xs : List α) : List (I × α) :=
  (xs.zipIdx 1).map (fun p => (JInt.wrap .i64 (p.2 : Int), p.1))

/-- The elements of a fully assigned store vector, read in order. -/
def vectorValues {K : Type} (a : VectorRef) : SetVecM K (List K) := do
  let n ← StateT.lift (mutableLength (α := K) a.handle)
  (intRange one n).mapM (fun i => StateT.lift (mutableGet a.handle i))

def oddMembership {K : Type} (equal : K → K → Bool) (args : List (List K)) (x : K) : Bool :=
  (args.filter (fun a => a.any (equal x))).length % 2 == 1

/-- `x ∉ s` (operators.jl `∉(x, itr) = !∈(x, itr)`). -/
def setLacksG {σ K : Type} (ops : JuliaLean.base.set.DictRuntime K) (x : K) (u : Unit) :
    SetVecG σ K Bool := do
  return !(← setHasG ops x u)

/-- `push!(s::Set{T}, x)` (set.jl), converting `x` with dict.jl's key conversion `key`. -/
def setAddG {σ K : Type} (ops : JuliaLean.base.set.DictRuntime K)
    (key : JuliaLean.base.dict.KeyConv K K) (_ : Unit) (x : K) : SetVecG σ K Unit := do
  let s ← setLiftRG (JuliaLean.base.set.setPush ops key x (← get))
  modify (fun _ => s)

/-- `sizehint!(s::Set, n)` (set.jl). -/
def setHintG {σ K : Type} (ops : JuliaLean.base.set.DictRuntime K) (_ : Unit) (n : I) :
    SetVecG σ K Unit := do
  let s ← setLiftRG (JuliaLean.base.set.setSizehint ops n true (← get))
  modify (fun _ => s)

/-- The elements of a vector, read in iteration order. -/
def vectorValuesG {σ K : Type} (v : VectorOf σ K) : SetVecG σ K (List K) := do
  let first ← liftV v.ops.firstindex
  let last ← liftV v.ops.lastindex
  (intRange first last).mapM (fun i => liftV (v.ops.getAt i))

/-- abstractset.jl's `mapfilter(pred, f, itr, res)` (abstractset.jl:636-641) for the stateful
`pred` and `f` that `_grow!` passes. -/
def vecMapfilterG {σ K : Type} (pred : K → SetVecG σ K Bool)
    (f : VectorOf σ K → K → SetVecG σ K Unit) (itr : List K) (res : VectorOf σ K) :
    SetVecG σ K Unit := do
  for x in itr do
    if ← pred x then f res x

/-- `_grow!(pred!, v, itrs)` (array.jl:3172). -/
abbrev vecGrowG {σ K : Type} : (K → SetVecG σ K Bool) → VectorOf σ K → List (List K) →
    SetVecG σ K (VectorOf σ K) :=
  grow (fun pred v => do let _ ← vecFilterBangG pred v; pure ())
    (fun v x => liftV (v.ops.pushBack x)) vecMapfilterG

/-- The documented outcome of an in-place set-like operator on a vector with slots `contents s`:
when every slot is assigned, holding `xs`, the vector is returned and afterwards holds
`expected xs` in a valid state; when a slot is unassigned, reading it raises `UndefRefError`. -/
def VectorResult {σ K : Type} (contents : σ → List (Option K)) (valid : σ → Prop) (s : σ)
    (run : Except Error (VectorOf σ K) × σ) (expected : List K → List K) : Prop :=
  (∀ xs, contents s = xs.map some → (∃ w, run.1 = .ok w) ∧ valid run.2 ∧
    contents run.2 = (expected xs).map some) ∧
  (none ∈ contents s → run.1 = .error .undefinedReference)

/-- `union!(v::AbstractVector{T}, itrs...)` (array.jl:3180; `union!` docstring in
abstractset.jl: "Construct the union of passed in sets and overwrite `s` with the result.
Maintain order with arrays.") through `_grow!` (array.jl:3172) with
`_grow_filter!(sizehint!(Set{T}(), length(v)))` (array.jl:3169, 3159), for every
`AbstractVector` (`EveryAbstractVector`) and every lawful `Set` runtime of the element type: `v`
ends holding every distinct value (under `isequal`) of `v` and the `itrs`, each once, in order of
first appearance; an unassigned slot of `v` raises `UndefRefError`. -/
def UnionBangSpec : Prop :=
  ∀ (K : Type) (ops : JuliaLean.base.set.DictRuntime K) (layout : MemoryLayoutMetadata) (itrs : List (List K)),
    JuliaLean.Proofs.base.set.DictRuntimeLawful ops →
    EveryAbstractVector layout itrs.flatten.length (fun σ V contents valid s =>
      VectorResult contents valid s
        (setVecRunG (unionBang (m := SetVecG σ K) setNewG
          (fun v : VectorOf σ K => liftV v.ops.length)
          (fun u n => do setHintG ops u n; pure u)
          (growFilter (setLacksG ops) (setAddG ops (identityKey ops))) vecGrowG
          (⟨V⟩ : VectorOf σ K) itrs) s)
        (fun xs => firstOccurrences ops.equal (xs ++ itrs.flatten)))

def SymdiffBangSpec : Prop :=
  ∀ (K : Type) (ops : JuliaLean.base.set.DictRuntime K) (layout : MemoryLayoutMetadata) (itrs : List (List K)),
    JuliaLean.Proofs.base.set.DictRuntimeLawful ops →
    EveryAbstractVector layout itrs.flatten.length (fun σ V contents valid s =>
      let symdiff := fun (_ : Unit) (v : VectorOf σ K) (itrs : List (List K)) => do
        let values ← vectorValuesG v
        setRunG ops (identityKey ops) (JuliaLean.base.abstractset.symdiffBangAbstractSetMany
          (setCallsKey K ops (identityKey ops))) (values :: itrs)
      VectorResult contents valid s
        (setVecRunG (symdiffBang (m := SetVecG σ K) setNewG symdiff
          (shrinkFilter (setHasG ops) (setRemoveG ops)) vecGrowG (⟨V⟩ : VectorOf σ K) itrs) s)
        (fun xs => (firstOccurrences ops.equal (xs ++ itrs.flatten)).filter
          (oddMembership ops.equal (xs :: itrs))))

def ShrinkBangSpec : Prop :=
  ∀ (K : Type) (ops : JuliaLean.base.set.DictRuntime K) (layout : MemoryLayoutMetadata) (itrs : List (List K)),
    JuliaLean.Proofs.base.set.DictRuntimeLawful ops →
    let inAll := fun (x : K) => itrs.all (fun l => l.any (ops.equal x))
    let inNone := fun (x : K) => itrs.all (fun l => !l.any (ops.equal x))
    EveryAbstractVector layout itrs.flatten.length (fun σ V contents valid s =>
      let shrinkWith := fun (operation : Unit → List (List K) → SetVecG σ K Unit)
          (v : VectorOf σ K) (itrs : List (List K)) =>
        shrink (m := SetVecG σ K) setNewG
          (growFilter (setLacksG ops) (setAddG ops (identityKey ops))) vecFilterBangG operation
          (fun u x => setHasG ops x u) v itrs
      VectorResult contents valid s
        (setVecRunG (intersectBang
          (fun _ itrs => setRunG ops (identityKey ops)
            (JuliaLean.base.abstractset.intersectBangAbstractSetMany
              (setCallsKey K ops (identityKey ops))) itrs)
          shrinkWith (⟨V⟩ : VectorOf σ K) itrs) s)
        (fun xs => (firstOccurrences ops.equal xs).filter inAll) ∧
      VectorResult contents valid s
        (setVecRunG (setdiffBang
          (fun _ itrs => setRunG ops (identityKey ops)
            (JuliaLean.base.abstractset.setdiffBangAbstractSetMany
              (setCallsKey K ops (identityKey ops))) itrs)
          shrinkWith (⟨V⟩ : VectorOf σ K) itrs) s)
        (fun xs => (firstOccurrences ops.equal xs).filter inNone))

def IntersectRangeVectorOrder : Prop :=
  ∀ (K : Type) (eq : K → K → Bool) (ops : JuliaLean.base.set.DictRuntime K) (isT : K → Bool)
    (convert : K → Except Error K) (layout : Option MemoryLayout) (range vector : List K) (s : MutableMemory K),
    JuliaLean.Proofs.base.set.DictRuntimeLawful ops → ConvertsTo isT convert →
    range.length < 2 ^ 62 → vector.length < 2 ^ 62 →
    (∀ x ∈ range ++ vector, isT x = true) →
    let key := convertingKey ops isT convert
    let promoteEltype := fun (_ _ : List K) => ()
    let contains := fun (range : List K) (value : K) => range.any (eq value)
    let iteratorFilter := fun (test : K → Bool) (values : List K) => values.filter test
    let makeSet := setFromValuesKey ops key
    let shrink := shrinkFilter (m := SetVecM K) (setHasG ops) (setRemoveG ops)
    let vfilter := setVecLiteralConv layout isT convert
    let forward := setVecRun (intersectVectorRange promoteEltype contains iteratorFilter makeSet
      shrink vfilter vector range) s
    let backward := setVecRun (intersectRangeVector promoteEltype contains iteratorFilter makeSet
      shrink vfilter range vector) s
    (∃ h, forward.1 = .ok h ∧ forward.2.contents h =
      ((firstOccurrences ops.equal vector).filter (fun x => range.any (ops.equal x))).map some) ∧
    (∃ h, backward.1 = .ok h ∧ backward.2.contents h =
      ((firstOccurrences ops.equal range).filter (fun x => vector.any (ops.equal x))).map some)

/-- `VectorResult` with the growth outcome `plan xs` of a vector holding `xs`: the documented
result when the growth succeeds, its error when it fails, and `UndefRefError` for an unassigned
slot (read by `filter!` before any growth). -/
def VectorResultPlanned {σ K : Type} (contents : σ → List (Option K)) (valid : σ → Prop) (s : σ)
    (run : Except Error (VectorOf σ K) × σ) (expected : List K → List K)
    (plan : List K → Except Error Unit) : Prop :=
  (∀ xs, contents s = xs.map some →
    (plan xs = .ok () → (∃ w, run.1 = .ok w) ∧ valid run.2 ∧
      contents run.2 = (expected xs).map some) ∧
    (∀ e, plan xs = .error e → run.1 = .error e)) ∧
  (none ∈ contents s → run.1 = .error .undefinedReference)
end round4
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- The range/vector overload delegates to the vector/range overload. -/
theorem MultidimcovIntersectRangeVector_refuted :
    ¬ JuliaLean.Proofs.base.array.IntersectRangeVectorOrder := by
  intro h
  have bad := (h [1, 2] [2, 1]).2
  change (Except.ok [some (2 : Int), some 1] : Except Error (List (Option Int))) =
    .ok [some 1, some 2] at bad
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
section SetProofs

variable {α : Type} [DecidableEq α]

theorem sets_bind_run {β γ : Type} (action : SetM α β) (next : β → SetM α γ)
    (st : VecSet α) :
    (action >>= next).run st = (next (action.run st).1).run (action.run st).2 := rfl

theorem sets_pure_run {β : Type} (x : β) (st : VecSet α) :
    (pure x : SetM α β).run st = (x, st) := rfl

theorem sets_modify_run (f : VecSet α → VecSet α) (st : VecSet α) :
    (modify f : SetM α Unit).run st = ((), f st) := rfl

theorem sets_growFilter_run (v seen : List α) :
    (vecFilter (growFilter setNotin setPush ()) ()).run ⟨v, seen⟩ =
      ((), ⟨dedupFrom seen v, seen ++ dedupFrom seen v⟩) := by
  change (let result := (v.filterM (growFilter setNotin setPush ())).run ⟨v, seen⟩
          ((), {result.2 with vec := result.1})) = _
  rw [growFilter_filterM]

theorem sets_shrinkFilter_run (v keep : List α) :
    (vecFilter (shrinkFilter setIn setPop ()) ()).run ⟨v, keep⟩ =
      ((), ⟨firstIn keep v, firstInRest keep v⟩) := by
  change (let result := (v.filterM (shrinkFilter setIn setPop ())).run ⟨v, keep⟩
          ((), {result.2 with vec := result.1})) = _
  rw [shrinkFilter_filterM]

theorem sets_inFilter_run (v keep : List α) :
    (vecFilter (fun x => setIn x ()) ()).run ⟨v, keep⟩ =
      ((), ⟨v.filter (fun x => decide (x ∈ keep)), keep⟩) := by
  change (let result := (v.filterM (fun x => setIn x ())).run ⟨v, keep⟩
          ((), {result.2 with vec := result.1})) = _
  rw [setIn_filterM]

theorem sets_grow_run (v seen : List α) (itrs : List (List α)) :
    (grow vecFilter vecPush mapfilterList (growFilter setNotin setPush ()) () itrs).run
      ⟨v, seen⟩ =
      ((), itrs.foldl unionStep ⟨dedupFrom seen v, seen ++ dedupFrom seen v⟩) := by
  have loop := setForIn_run
    (fun itr _ => do
      mapfilterList (growFilter setNotin setPush ()) vecPush itr ()
      pure (ForInStep.yield PUnit.unit))
    unionStep (by
      intro itr st
      rcases st with ⟨v, seen⟩
      simp only [sets_bind_run, mapfilter_grow_run, sets_pure_run, unionStep]) itrs
  simp only [grow, sets_bind_run, sets_growFilter_run, loop, sets_pure_run]

theorem sets_shrinkGrow_run (v keep : List α) (itrs : List (List α)) :
    (grow vecFilter vecPush mapfilterList (shrinkFilter setIn setPop ()) () itrs).run
      ⟨v, keep⟩ =
      ((), itrs.foldl shrinkStep ⟨firstIn keep v, firstInRest keep v⟩) := by
  have loop := setForIn_run
    (fun itr _ => do
      mapfilterList (shrinkFilter setIn setPop ()) vecPush itr ()
      pure (ForInStep.yield PUnit.unit))
    shrinkStep (by
      intro itr st
      rcases st with ⟨v, keep⟩
      simp only [sets_bind_run, mapfilter_shrink_run, sets_pure_run, shrinkStep]) itrs
  simp only [grow, sets_bind_run, sets_shrinkFilter_run, loop, sets_pure_run]

theorem sets_shrink_run (v seen : List α) (pred : α → Bool) (itrs : List (List α)) :
    (shrink (m := SetM α) setEmpty (growFilter setNotin setPush) vecFilter
      (fun _ _ => modify fun st => {st with set := st.set.filter pred})
      (fun s x => setIn x s) () itrs).run ⟨v, seen⟩ =
      ((), ⟨(dedupFrom [] v).filter pred, (dedupFrom [] v).filter pred⟩) := by
  change (do
    let _ ← vecFilter (growFilter setNotin setPush ()) ()
    modify fun st => {st with set := st.set.filter pred}
    vecFilter (fun x => setIn x ()) () : SetM α Unit).run ⟨v, []⟩ = _
  simp only [sets_bind_run, sets_growFilter_run, List.nil_append, sets_modify_run,
    sets_inFilter_run, shrink_keep]
end SetProofs
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2

open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

theorem ArrayUnionBangFirstAppearance_proven :
    JuliaLean.Proofs.base.array.UnionBangSpec := by
  intro α _ v seen itrs
  change ((grow vecFilter vecPush mapfilterList (growFilter setNotin setPush ()) ()
    itrs).run ⟨v, []⟩).2.vec = dedupFrom [] (v ++ itrs.flatten)
  rw [sets_grow_run]
  simp only [List.nil_append, union_fold]

theorem MultidimcovArrayV2SymdiffVector_proven :
    JuliaLean.Proofs.base.array.SymdiffBangSpec := by
  intro α _ v seen itrs
  change ((grow vecFilter vecPush mapfilterList (shrinkFilter setIn setPop ()) ()
    itrs).run ⟨v, oddSet v itrs⟩).2.vec = oddSet v itrs
  rw [sets_shrinkGrow_run, shrink_fold]
  exact unique_filter_odd v itrs

theorem MultidimcovArrayV2IntersectBangVector_proven :
    JuliaLean.Proofs.base.array.ShrinkBangSpec := by
  intro α _ v seen itrs
  dsimp only
  constructor
  · exact congrArg (fun result => result.2.vec)
      (sets_shrink_run v seen (fun x => itrs.all (fun l => decide (x ∈ l))) itrs)
  · exact congrArg (fun result => result.2.vec)
      (sets_shrink_run v seen (fun x => itrs.all (fun l => decide (x ∉ l))) itrs)

theorem MultidimcovArrayV2SetdiffBangVector_proven :
    JuliaLean.Proofs.base.array.ShrinkBangSpec :=
  MultidimcovArrayV2IntersectBangVector_proven
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2

open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array
section FilterLiftProofs

variable {α : Type} [DecidableEq α]

theorem sets_filterLiftAux_run (test : α → SetM α Bool) :
    ∀ (xs acc : List α) (st : VecSet α),
      ((List.filterAuxM (fun x => ExceptT.lift (test x) : α → ExceptT Error (SetM α) Bool)
          xs acc).run).run st =
        let result := (List.filterAuxM test xs acc).run st
        (.ok result.1, result.2) := by
  intro xs
  induction xs with
  | nil => intro acc st; rfl
  | cons x xs ih =>
    intro acc st
    simp only [List.filterAuxM, ExceptT.run_bind_lift, sets_bind_run, ih]

theorem sets_filterLift_run (test : α → SetM α Bool) (xs : List α) (st : VecSet α) :
    ((xs.filterM (fun x => ExceptT.lift (test x) : α → ExceptT Error (SetM α) Bool)).run).run st =
      let result := (xs.filterM test).run st
      (.ok result.1, result.2) := by
  simp only [List.filterM, ExceptT.run_bind, sets_bind_run, sets_filterLiftAux_run,
    ExceptT.run_pure, sets_pure_run]

theorem sets_vectorfilter_run (test : α → SetM α Bool) (xs : List α) (st : VecSet α) :
    ((vectorfilter (m := ExceptT Error (SetM α))
        (literalFilterCollectOps (pure []) pure) () (fun x => ExceptT.lift (test x)) xs).run).run st =
      let result := (xs.filterM test).run st
      (.ok result.1, result.2) := by
  have operation :
      vectorfilter (m := ExceptT Error (SetM α))
        (literalFilterCollectOps (pure []) pure) () (fun x => ExceptT.lift (test x)) xs =
      xs.filterM (fun x => ExceptT.lift (test x)) := by
    simp only [vectorfilter, typedComprehension, collectTyped, typedCollectDispatch,
      literalFilterCollectOps, collectSized, ite_true, pure_bind, bind_pure]
    rfl
  rw [operation]
  exact sets_filterLift_run test xs st
end FilterLiftProofs
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2

open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

theorem MultidimcovArrayV2IntersectVector_proven :
    JuliaLean.Proofs.base.array.IntersectSetdiffSpec := by
  intro α _ st itr itrs
  rcases st with ⟨v, seen⟩
  dsimp only
  constructor
  · simp only [intersect, sets_bind_run, sets_modify_run, sets_vectorfilter_run,
      shrinkFilter_filterM, sets_pure_run, firstIn_keep]
  · simp only [setdiff, sets_bind_run, sets_modify_run, sets_vectorfilter_run,
      shrinkFilter_filterM, sets_pure_run, firstIn_keep]

theorem MultidimcovArrayV2SetdiffVector_proven :
    JuliaLean.Proofs.base.array.IntersectSetdiffSpec :=
  MultidimcovArrayV2IntersectVector_proven
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion2
open JuliaLean JuliaLean.base.array
open JuliaLean.base.array.Completion2

/-- The original vector is filtered before the external iterators are traversed, and a filter error retains its resulting state. -/
def GrowFilterErrors : Prop :=
  ∀ (W E A X Itrs : Type) [ForIn (ExceptT Error (StateM W)) Itrs X]
    (filter : (E → ExceptT Error (StateM W) Bool) → A → ExceptT Error (StateM W) Unit)
    (push : A → E → ExceptT Error (StateM W) Unit)
    (mapfilter : (E → ExceptT Error (StateM W) Bool) →
      (A → E → ExceptT Error (StateM W) Unit) → X → A → ExceptT Error (StateM W) Unit)
    (pred : E → ExceptT Error (StateM W) Bool) (a : A) (itrs : Itrs)
    (before after : W) (error : Error),
    (filter pred a).run before = (.error error, after) →
    (JuliaLean.base.array.Completion2.grow filter push mapfilter pred a itrs).run before =
      (.error error, after)

/-- The range/vector overload uses vector-first intersection without changing either input. -/
def IntersectArgumentOrder : Prop :=
  ∀ (A R : Type) (a : A) (range : R) (initial : List Nat),
    (JuliaLean.base.array.Completion2.intersectRangeVector
      (fun a r => call 0 (.ok (a, r))) range a).run initial =
        (.ok (a, range), initial ++ [0])
end JuliaLean.Proofs.base.array.Completion2


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.LegacyRetired

open JuliaLean JuliaLean.base.array JuliaLean.Registry
open JuliaLean.Proofs.base.array.round4

def IntersectVectorRangeContents : Prop :=
  ∀ (K : Type) (ops : JuliaLean.base.set.DictRuntime K) (isT : K → Bool)
    (convert : K → Except Error K) (layout : Option MemoryLayout)
    (range vector : List K) (initial : MutableMemory K),
    JuliaLean.Proofs.base.set.DictRuntimeLawful ops → ConvertsTo isT convert →
    range.length < 2 ^ 62 → vector.length < 2 ^ 62 →
    (∀ x ∈ range ++ vector, isT x = true) →
    let key := convertingKey ops isT convert
    let forward := setVecRun (intersectVectorRange
      (fun (_ _ : List K) => ())
      (fun range value => range.any (ops.equal value))
      (fun test values => values.filter test)
      (setFromValuesKey ops key)
      (shrinkFilter (m := SetVecM K) (setHasG ops) (setRemoveG ops))
      (setVecLiteralConv layout isT convert) vector range) initial
    ∃ handle, forward.1 = .ok handle ∧ forward.2.contents handle =
      ((firstOccurrences ops.equal vector).filter
        (fun x => range.any (ops.equal x))).map some
end JuliaLean.Proofs.base.array.LegacyRetired


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array
end JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
theorem JuliaLean.Proofs.base.array.Completion2.GrowFilterErrors_proven : JuliaLean.Proofs.base.array.Completion2.GrowFilterErrors := by
  unfold JuliaLean.Proofs.base.array.Completion2.GrowFilterErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion2.grow, JuliaLean.base.array.grow, JuliaLean.base.array.push, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion2.IntersectArgumentOrder_proven : JuliaLean.Proofs.base.array.Completion2.IntersectArgumentOrder := by
  unfold JuliaLean.Proofs.base.array.Completion2.IntersectArgumentOrder
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion2.intersectRangeVector, JuliaLean.base.array.intersectRangeVector, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

namespace JuliaLean.Proofs.base.array
def entriesUnion1 : List JuliaLean.Registry.Entry := [
  { id := "array-union-bang-first-appearance", juliaFile := "base/array.jl",
    juliaFns := ["union!(v::AbstractVector{T}, itrs...) where {T}", "_grow!(pred!, v::AbstractVector, itrs)",
      "_grow_filter!(seen)", "_unique_filter!(pred::P, update!::U, state) where {P,U}"],
    statement := "`union!(v::AbstractVector{T}, itrs...)` (array.jl:3180; `union!` docstring in abstractset.jl: \"Construct the union of passed in sets and overwrite `s` with the result. Maintain order with arrays.\") through `_grow!` (array.jl:3172) with `_grow_filter!(sizehint!(Set{T}(), length(v)))` (array.jl:3169, 3159), for every `AbstractVector` (`EveryAbstractVector`) and every lawful `Set` runtime of the element type: `v` ends holding every distinct value (under `isequal`) of `v` and the `itrs`, each once, in order of first appearance; an unassigned slot of `v` raises `UndefRefError`.",
    source := "base/array.jl:3169, array.jl:3172, array.jl:3180", status := .proven,
    prop := ``UnionBangSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.ArrayUnionBangFirstAppearance_proven,
    notes := "" },
  { id := "multidimcov-array-v2-symdiff-vector", juliaFile := "base/array.jl",
    juliaFns := ["symdiff!(v::AbstractVector{T}, itrs...) where {T}", "_grow!(pred!, v::AbstractVector, itrs)",
      "_shrink_filter!(keep)", "_unique_filter!(pred::P, update!::U, state) where {P,U}"],
    statement := "`symdiff!(v::AbstractVector{T}, itrs...)` (array.jl:3183; `symdiff!` docstring in abstractset.jl: \"Construct the symmetric difference of the passed in sets, and overwrite `s` with the result. When `s` is an array, the order is maintained.\") through `_grow!` with `_shrink_filter!(symdiff!(Set{T}(), v, itrs...))` (abstractset.jl's `symdiff!`), for every `AbstractVector`: `v` ends holding the distinct values (under `isequal`) that lie in an odd number of `v, itrs...`, each once, in order of first appearance across `v, itrs...`; an unassigned slot of `v` raises `UndefRefError`.",
    source := "base/array.jl:3183", status := .proven,
    prop := ``SymdiffBangSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.MultidimcovArrayV2SymdiffVector_proven,
    notes := "" },
  { id := "multidimcov-array-v2-intersect-bang-vector", juliaFile := "base/array.jl",
    juliaFns := ["intersect!(v::AbstractVector, itrs...)", "_shrink!(shrinker!::F, v::AbstractVector, itrs) where F",
      "_grow_filter!(seen)", "_unique_filter!(pred::P, update!::U, state) where {P,U}"],
    statement := "`intersect!(v::AbstractVector, itrs...)` and `setdiff!(v::AbstractVector, itrs...)` (array.jl:3193-3194; docstrings in abstractset.jl: \"Intersect all passed in sets and overwrite `s` with the result. Maintain order with arrays.\"; \"Remove from set `s` (in-place) each element of each iterable from `itrs`. Maintain order with arrays.\") through `_shrink!` (array.jl:3186) with abstractset.jl's `intersect!`/`setdiff!` on the `Set`, for every `AbstractVector` and `itrs` of values of any types: `v` ends holding its distinct values (under `isequal`) that lie in every `itr` (respectively in none), in `v`'s order; an unassigned slot of `v` raises `UndefRefError`.",
    source := "base/array.jl:3186, array.jl:3193-3194", status := .proven,
    prop := ``ShrinkBangSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.MultidimcovArrayV2IntersectBangVector_proven,
    notes := "" },
  { id := "multidimcov-array-v2-setdiff-bang-vector", juliaFile := "base/array.jl",
    juliaFns := ["setdiff!(v::AbstractVector, itrs...)", "_shrink!(shrinker!::F, v::AbstractVector, itrs) where F",
      "_grow_filter!(seen)", "_unique_filter!(pred::P, update!::U, state) where {P,U}"],
    statement := "`intersect!(v::AbstractVector, itrs...)` and `setdiff!(v::AbstractVector, itrs...)` (array.jl:3193-3194; docstrings in abstractset.jl: \"Intersect all passed in sets and overwrite `s` with the result. Maintain order with arrays.\"; \"Remove from set `s` (in-place) each element of each iterable from `itrs`. Maintain order with arrays.\") through `_shrink!` (array.jl:3186) with abstractset.jl's `intersect!`/`setdiff!` on the `Set`, for every `AbstractVector` and `itrs` of values of any types: `v` ends holding its distinct values (under `isequal`) that lie in every `itr` (respectively in none), in `v`'s order; an unassigned slot of `v` raises `UndefRefError`.",
    source := "base/array.jl:3186, array.jl:3193-3194", status := .proven,
    prop := ``ShrinkBangSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.MultidimcovArrayV2SetdiffBangVector_proven,
    notes := "" },
  { id := "multidimcov-array-v2-intersect-vector", juliaFile := "base/array.jl",
    juliaFns := ["intersect(itr, itrs...)", "vectorfilter(T::Type, f, v)", "_shrink_filter!(keep)",
      "_unique_filter!(pred::P, update!::U, state) where {P,U}"],
    statement := "`intersect(itr, itrs...)` (array.jl:3198; docstring in abstractset.jl: \"Construct the set containing those elements which appear in all of the arguments. The first argument controls what kind of container is returned. If this is an array, it maintains the order in which elements first appear.\") for arguments holding values of any types: with `T = promote_eltype(itr, itrs...)` (`isT`), `Set{T}(itr)` (set.jl, keys converted by dict.jl), abstractset.jl's `intersect!`, `_shrink_filter!` and the typed literal, when every conversion `convert(T, x)` of a value of `itr` succeeds the result is a fresh valid vector of the distinct values of `itr` (under `isequal`) that appear in every other argument, in order of first appearance, converted to `T`; when a conversion fails, an error is raised.",
    source := "base/array.jl:3198", status := .proven,
    prop := ``IntersectSetdiffSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.MultidimcovArrayV2IntersectVector_proven,
    notes := "expected refuted: the file states ¬ IntersectSpec (theorem intersectSpec_refuted); repro/multidimcov-array-v2-intersect-vector.jl" },
  { id := "multidimcov-array-v2-setdiff-vector", juliaFile := "base/array.jl",
    juliaFns := ["setdiff(itr, itrs...)", "vectorfilter(T::Type, f, v)", "_shrink_filter!(keep)",
      "_unique_filter!(pred::P, update!::U, state) where {P,U}"],
    statement := "`setdiff(itr, itrs...)` (array.jl:3204; docstring in abstractset.jl: \"Construct the set of elements in `s` but not in any of the iterables in `itrs`. Maintain order with arrays.\") for arguments holding values of any types: with `T = eltype(itr)` (`isT`, which every value of `itr` satisfies), `Set{T}(itr)`, abstractset.jl's `setdiff!`, `_shrink_filter!` and the typed literal, the result is a fresh valid vector of the distinct values of `itr` (under `isequal`) lying in no other argument, in order of first appearance.",
    source := "base/array.jl:3204", status := .proven,
    prop := ``IntersectSetdiffSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.MultidimcovArrayV2SetdiffVector_proven,
    notes := "" }
]
def entriesUnion2 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-intersect-range-vector", juliaFile := "base/array.jl",
    juliaFns := ["intersect(v::AbstractVector, r::AbstractRange)", "intersect(r::AbstractRange, v::AbstractVector)"],
    statement := "`intersect(v::AbstractVector, r::AbstractRange)` and `intersect(r::AbstractRange, v::AbstractVector)` (array.jl:3210, 3216; `intersect` docstring in abstractset.jl: \"Construct the set containing those elements which appear in all of the arguments. ... If this is an array, it maintains the order in which elements first appear.\") for a range iterating `range` and a vector `vector` whose values may be of different `Real` types: `in(x, r)` with `==` (`eq`, the values' own, user-extensible), `T = promote_eltype(v, r)` (`isT`, `convert(T, x)` typed parameters), `Iterators.filter(in(r), v)`, `Set{T}(common)` and the typed literal: the result holds the distinct values (under `isequal`, the `Set` equality) of the first argument lying in the second, in order of first appearance in the first argument.",
    source := "base/array.jl:3210", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64265, #41769; see bugs/multidimcov-intersect-range-vector.yaml",
    prop := ``IntersectRangeVectorOrder, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.MultidimcovIntersectRangeVector_refuted,
    notes := "expected refuted: the file states ¬ IntersectRangeVectorOrder (theorem intersectRangeVectorOrder_refuted); repro/multidimcov-intersect-range-vector.jl" }
]
def entriesUnion3 : List JuliaLean.Registry.Entry := [
{ id := "array-grow-filter-errors", juliaFile := "base/array.jl",
  juliaFns := ["_grow!(pred!, v::AbstractVector, itrs)"],
  statement := "The original vector is filtered before the external iterators are traversed, and a filter error retains its resulting state.",
  source := "base/array.jl:3172-3178", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion2.GrowFilterErrors, thm := some ``JuliaLean.Proofs.base.array.Completion2.GrowFilterErrors_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-intersect-argument-order", juliaFile := "base/array.jl",
  juliaFns := ["intersect(r::AbstractRange, v::AbstractVector)"],
  statement := "The range/vector overload uses vector-first intersection without changing either input.",
  source := "base/array.jl:3216-3216", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion2.IntersectArgumentOrder, thm := some ``JuliaLean.Proofs.base.array.Completion2.IntersectArgumentOrder_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.LegacyRetired

open JuliaLean.Registry
def entriesUnion4 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-intersect-vector-range", juliaFile := "base/array.jl",
    juliaFns := ["intersect(v::AbstractVector, r::AbstractRange)", "vectorfilter(T::Type, f, v)",
      "_shrink_filter!(keep)"],
    statement := "intersect(v, r) for a vector v and a range r returns the distinct elements of v that lie in r, in v's order.",
    source := "intersect docstring base/abstractset.jl:114-154", status := .todo, prop := ``IntersectVectorRangeContents,
    notes := "The source range membership, Dict/Set uniqueness and vectorfilter allocation pipeline need a value-order certificate; the old stableUnique replacement proof cannot establish the installed execution." }
]
end JuliaLean.Proofs.base.array.LegacyRetired

