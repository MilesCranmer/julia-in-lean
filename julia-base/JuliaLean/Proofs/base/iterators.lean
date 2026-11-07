import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.base.essentials
import JuliaLean.base.iterators
import JuliaLean.Proofs.base.int
import JuliaLean.Proofs.base.sort
import JuliaLean.Proofs.base.iterators.protocol
import JuliaLean.Proofs.base.iterators.composition
import JuliaLean.Proofs.base.iterators.coverage_count
import JuliaLean.Proofs.base.iterators.coverage_wrappers
import JuliaLean.Proofs.base.iterators.coverage_product
import JuliaLean.Proofs.base.iterators.coverage_metadata
import JuliaLean.Proofs.base.anyall.IteratorMethods

namespace JuliaLean.Proofs.base.iterators

open JuliaLean JuliaLean.base.iterators
set_option linter.unusedVariables false
set_option maxErrors 300

namespace CountValue

/-- The count propositions use mathematical values; conversion is Core's checked integer primitive. -/
def toInt : Int → Jl JInt64 := JInt.convert IntTy.i64.name .i64

def rawTake {I : Type} (xs : I) (n : Int) : Jl (Take I) :=
  mkTake (fun value => pure (decide (value < 0))) toInt
    (fun message => .error (.argumentError message)) xs n

def rawDrop {I : Type} (xs : I) (n : Int) : Jl (Drop I) :=
  mkDrop (fun value => pure (decide (value < 0))) toInt
    (fun message => .error (.argumentError message)) xs n

def takeConstructor {I : Type} (xs : I) (n : JInt64) : Jl (Take I) :=
  mkTake (fun value => pure (JuliaLean.base.int.lt value (JInt.lit .i64 0)))
    (JuliaLean.base.int.convert .i64) (fun message => .error (.argumentError message)) xs n

def dropConstructor {I : Type} (xs : I) (n : JInt64) : Jl (Drop I) :=
  mkDrop (fun value => pure (JuliaLean.base.int.lt value (JInt.lit .i64 0)))
    (JuliaLean.base.int.convert .i64) (fun message => .error (.argumentError message)) xs n

def take {I : Type} (xs : I) (n : Int) : Jl (Take I) :=
  takeModel toInt takeConstructor xs n

def drop {I : Type} (xs : I) (n : Int) : Jl (Drop I) :=
  dropModel toInt dropConstructor xs n

def takeTake {I : Type} (xs : Take I) (n : Int) : Jl (Take I) :=
  takeTakeModel toInt (fun a b => pure (JuliaLean.base.int.jmin a b)) takeConstructor xs n

def dropDrop {I : Type} (xs : Drop I) (n : Int) : Jl (Drop I) :=
  dropDropModel toInt dropConstructor xs n

def dropTake {I D : Type} (convert : Int → Jl JInt64)
    (dropInner : I → JInt64 → Jl D) (xs : Take I) (n : Int) : Jl (Take D) :=
  dropTakeModel convert dropInner (fun a b => pure (JuliaLean.base.int.jmax a b))
    takeConstructor xs n

def repeated {I : Type} (xs : I) (n : Int) : Jl (Take (Repeated I)) :=
  repeatedNModel toInt (takeModel (JuliaLean.base.int.convert .i64) takeConstructor) xs n

def cycle {I : Type} (xs : I) (n : Int) : Jl (Flatten (Take (Repeated I))) :=
  cycleNModel repeated xs n

@[simp] theorem takeConstructor_eq {I : Type} (xs : I) (n : JInt64) :
    takeConstructor xs n = if n.val < 0 then
      .error (.argumentError "Take length must be non-negative") else .ok ⟨xs, n⟩ := by
  simp [takeConstructor, mkTake, JuliaLean.Proofs.base.int.lt_eq,
    JuliaLean.base.int.convert, JInt.convert, n.property, JInt.lit, JInt.wrap, wrapInt,
    IntTy.signed, IntTy.bits, Functor.map, Except.map]

@[simp] theorem dropConstructor_eq {I : Type} (xs : I) (n : JInt64) :
    dropConstructor xs n = if n.val < 0 then
      .error (.argumentError "Drop length must be non-negative") else .ok ⟨xs, n⟩ := by
  simp [dropConstructor, mkDrop, JuliaLean.Proofs.base.int.lt_eq,
    JuliaLean.base.int.convert, JInt.convert, n.property, JInt.lit, JInt.wrap, wrapInt,
    IntTy.signed, IntTy.bits, Functor.map, Except.map]

@[simp] theorem native_min (a b : JInt64) :
    JuliaLean.base.int.jmin a b = if a.val ≤ b.val then a else b := by
  apply Subtype.ext
  rw [JuliaLean.Proofs.base.int.jmin_val]
  by_cases h : a.val ≤ b.val <;> simp [h, Int.min_def]

@[simp] theorem native_max (a b : JInt64) :
    JuliaLean.base.int.jmax a b = JInt.lit .i64 (max a.val b.val) := by
  apply Subtype.ext
  rw [JuliaLean.Proofs.base.int.jmax_val]
  have ha := a.property
  have hb := b.property
  exact (wrapInt_of_inRange .i64 _ (by constructor <;> omega)).symm

theorem native_add (a b : JInt64) :
    JuliaLean.base.int.add_int a b = JInt.wrap .i64 (a.val + b.val) :=
  Subtype.ext (JuliaLean.Proofs.base.int.add_int_val a b)

@[simp] theorem convert_native (n : JInt64) : JuliaLean.base.int.convert .i64 n = .ok n := by
  simp [JuliaLean.base.int.convert, JInt.convert, n.property]


end CountValue

attribute [local simp] CountValue.toInt CountValue.rawTake CountValue.rawDrop
  CountValue.take CountValue.drop CountValue.takeTake CountValue.dropDrop CountValue.dropTake
  CountValue.repeated CountValue.cycle mkTake mkDrop takeModel dropModel takeTakeModel
  dropDropModel dropTakeModel repeatedNModel cycleNModel

inductive Observation (E α : Type) where
  | ok : α → Observation E α
  | error : E → Observation E α
  | diverged : Observation E α

def Observation.map (f : α → β) : Observation E α → Observation E β
  | .ok a => .ok (f a)
  | .error e => .error e
  | .diverged => .diverged

instance : Monad (Observation E) where
  pure := .ok
  bind x f := match x with
    | .ok a => f a
    | .error e => .error e
    | .diverged => .diverged

def observe (x : Exec E Unit α) : Observation E α :=
  match x () with
  | none => .diverged
  | some (.error e, ()) => .error e
  | some (.ok a, ()) => .ok a

def action (x : Observation E α) : Exec E Unit α :=
  fun () => match x with
  | .diverged => none
  | .error e => some (.error e, ())
  | .ok a => some (.ok a, ())

def liftJl (x : Jl α) : Exec JlError Unit α :=
  fun () => some (x, ())

def onlyPair (value : Option (α × S)) : Exec JlError Unit (α × S) :=
  liftJl (match value with | some pair => pure pair | none => .error (.methodError "NTuple{2,Any}"))

theorem onlyValue_total (itr : I) (run : I → Option S → Jl (Option (α × S))) (bounds : Bool) :
    (sourceMethod1661 (fun it state => liftJl (run it state)) onlyPair
      (fun message => liftJl (.error (.argumentError message))) itr bounds ()).isSome := by
  cases h : run itr none with
  | error error => simp [sourceMethod1661, liftJl, h, Bind.bind, JuliaLean.base.iterators.bind]
  | ok output =>
    cases output with
    | none => cases bounds <;> simp [sourceMethod1661, liftJl, h, onlyPair, Bind.bind, JuliaLean.base.iterators.bind]
    | some pair =>
      rcases pair with ⟨value, state⟩
      cases bounds <;> cases hs : run itr (some state) <;>
        simp [sourceMethod1661, liftJl, h, hs, onlyPair, Bind.bind, JuliaLean.base.iterators.bind, Pure.pure, JuliaLean.base.iterators.ret, Except.pure]
      all_goals split <;> simp_all [liftJl, JuliaLean.base.iterators.ret]

def onlyValue (itr : I) (run : I → Option S → Jl (Option (α × S))) (bounds : Bool := true) : Jl α :=
  (Option.get (sourceMethod1661 (fun it state => liftJl (run it state)) onlyPair
    (fun message => liftJl (.error (.argumentError message))) itr bounds ())
    (onlyValue_total itr run bounds)).1

def onlyIterator (itr : IteratorModel α S) : Jl α :=
  (Option.get (onlyModel (fun (it : IteratorModel α S) state => liftJl (it.run state)) onlyPair
    (fun message => liftJl (.error (.argumentError message))) itr true ())
    (onlyValue_total itr (fun it state => it.run state) true)).1

@[simp] theorem onlyValue_eq (itr : I) (run : I → Option S → Jl (Option (α × S))) (bounds : Bool) :
    onlyValue itr run bounds = (do
      let i ← run itr none
      if bounds && i.isNone then
        .error (.argumentError "Collection is empty, must contain exactly 1 element")
      else
        let (value, state) ← match i with
          | some pair => pure pair
          | none => .error (.methodError "NTuple{2,Any}")
        if bounds then
          if (← run itr (some state)).isSome then
            .error (.argumentError "Collection has multiple elements, must contain exactly 1 element")
          else pure value
        else pure value) := by
  cases h : run itr none with
  | error error => simp [onlyValue, sourceMethod1661, liftJl, h, Bind.bind, JuliaLean.base.iterators.bind, Except.bind]
  | ok output =>
    cases output with
    | none => cases bounds <;> simp [onlyValue, sourceMethod1661, liftJl, h, onlyPair, Bind.bind, JuliaLean.base.iterators.bind, Pure.pure, JuliaLean.base.iterators.ret, Except.pure, Except.bind]
    | some pair =>
      rcases pair with ⟨value, state⟩
      cases bounds <;> cases hs : run itr (some state) <;>
        simp [onlyValue, sourceMethod1661, liftJl, h, hs, onlyPair, Bind.bind, JuliaLean.base.iterators.bind, Pure.pure, JuliaLean.base.iterators.ret, Except.pure, Except.bind]
      all_goals split <;> simp_all [liftJl, JuliaLean.base.iterators.ret]

@[simp] theorem onlyIterator_eq (itr : IteratorModel α S) :
    onlyIterator itr = onlyValue itr (fun it state => it.run state) := rfl

def onlyFirstValue (length : I → Jl Nat) (first : I → Jl α) (itr : I) (bounds : Bool := true) : Jl α :=
  sourceMethod1673 length (fun n => pure (decide (n ≠ 1))) pure first
    (fun message => .error (.argumentError message)) itr bounds

def onlyDictValue (length : IdDictModel K V → Jl Nat)
    (first : IdDictModel K V → Jl (K × V)) (itr : IdDictModel K V)
    (bounds : Bool := true) : Jl (K × V) :=
  sourceMethod1680 length (fun n => pure (decide (n ≠ 1))) pure first
    (fun message => .error (.argumentError message)) itr bounds

def ordinalRangeRun (count : Nat) (state : Option Nat) : Exec JlError Unit (Option (Unit × Nat)) :=
  let remaining := state.getD count
  liftJl (pure (if remaining = 0 then none else some ((), remaining - 1)))

theorem ordinalLoop_eq (itr : IteratorModel α S) (count : Nat) :
    ∀ remaining state (value : Option (α × S)), state.getD count = remaining →
      nthLoop (fun it state => liftJl (it.run state)) ordinalRangeRun itr count state value () =
        some (nthAdvance itr.run remaining value, ()) := by
  intro remaining
  induction remaining with
  | zero =>
    intro state value h
    rw [nthLoop.eq_unfold]
    simp [ordinalRangeRun, h, liftJl, nthAdvance, Pure.pure, Except.pure]
  | succ remaining ih =>
    intro state value h
    rw [nthLoop.eq_unfold]
    simp only [ordinalRangeRun, h, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ↓reduceIte, Nat.add_sub_cancel, liftJl, Pure.pure, Except.pure]
    cases value with
    | none => rfl
    | some pair =>
      rcases pair with ⟨item, next⟩
      cases step : itr.run (some next) with
      | error error => simp [step, nthAdvance, Bind.bind, Except.bind]
      | ok output =>
        simpa [step, nthAdvance, Bind.bind, Except.bind] using ih (some remaining) output rfl

theorem ordinalLoop_start (itr : IteratorModel α S) (count : Nat) (value : Option (α × S)) :
    nthLoop (fun it state => liftJl (it.run state)) ordinalRangeRun itr count none value () =
      some (nthAdvance itr.run count value, ()) :=
  ordinalLoop_eq itr count count none value rfl

def nthValueAction (itr : IteratorModel α S) (n : Int) : Exec JlError Unit α :=
  nthGeneric (fun value => pure (decide (0 < value)))
    (fun value one => pure (value - one.val)) (fun _ last => pure last.toNat)
    ordinalRangeRun (fun it state => liftJl (it.run state))
    (fun _ _ => liftJl (.error .boundsError)) itr n

theorem nthValueAction_eq (itr : IteratorModel α S) (n : Int) :
    nthValueAction itr n () = some ((if n ≤ 0 then .error .boundsError else do
      match ← (itr.run none >>= nthAdvance itr.run (n - 1).toNat) with
      | none => .error .boundsError
      | some (value, _) => pure value), ()) := by
  unfold nthValueAction nthGeneric
  by_cases positive : 0 < n
  · have notNonpositive : ¬ n ≤ 0 := by omega
    simp only [positive, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      notNonpositive, Pure.pure, JuliaLean.base.iterators.ret, Bind.bind, JuliaLean.base.iterators.bind, liftJl]
    cases first : itr.run none with
    | error error => simp [first, Except.bind]
    | ok output =>
      simp only [first]
      simp only [JInt.lit, JInt.wrap, wrapInt, IntTy.bits, IntTy.signed,
        show (wrapInt .i64 1) = 1 by decide]
      rw [ordinalLoop_start]
      cases advance : nthAdvance itr.run (n.toNat - 1) output with
      | error error => simp [advance, Except.bind]
      | ok result => cases result <;>
          simp [advance, Except.bind, liftJl, JuliaLean.base.iterators.ret, Except.pure]
  · have nonpositive : n ≤ 0 := by omega
    simp [positive, nonpositive, liftJl, Bind.bind, JuliaLean.base.iterators.bind, Pure.pure, JuliaLean.base.iterators.ret]

def nthValue (itr : IteratorModel α S) (n : Int) : Jl α :=
  (Option.get (nthValueAction itr n ()) (by rw [nthValueAction_eq]; rfl)).1

def nthIterator (itr : IteratorModel α S) (n : Int) : Jl α :=
  nthModel (fun (it : IteratorModel α S) => pure it.iteratorSize) (fun _ it n => nthValue it n) itr n

@[simp] theorem nthValue_eq (itr : IteratorModel α S) (n : Int) :
    nthValue itr n = (if n ≤ 0 then .error .boundsError else do
      let first ← itr.run none
      match ← nthAdvance itr.run (n - 1).toNat first with
      | none => .error .boundsError
      | some (value, _) => pure value) := by
  unfold nthValue
  simp only [nthValueAction_eq, Option.get_some]
  by_cases h : n ≤ 0
  · simp [h]
  · simp only [if_neg h]
    cases itr.run none <;> rfl

@[simp] theorem nthIterator_eq (itr : IteratorModel α S) (n : Int) :
    nthIterator itr n = nthValue itr n := rfl

def nthZipValues (iters : List (IteratorModel α S)) (n : Int) : Jl (List α) :=
  nthZip nthIterator (fun f values => values.mapM f) ⟨iters⟩ n

def valueMod1 (n divisor : Int) : Jl Int :=
  (JuliaLean.base.operators.mod1
    (fun a b => if b = 0 then .error .divideError else pure (Int.fmod a b))
    (JuliaLean.base.number.iszero (fun _ => pure (0 : Int)) (fun a b => pure (decide (a = b))))
    pure n divisor).map (Sum.elim id id)

def nthCycleValue (length : I → Jl Nat) (nth : I → Int → Jl α)
    (itr : Cycle I) (n : Int) : Jl α :=
  (sourceMethod1758 length (fun k => pure (k == 0)) (fun n => pure (decide (0 < n)))
    (fun n k => valueMod1 n k) nth nth (fun _ _ => .error .boundsError) itr n).map (Sum.elim id id)

def nthFiniteCycleValue (length : I → Jl JInt64) (nth : I → Int → Jl α)
    (itr : Flatten (Take (Repeated I))) (n : Int) : Jl α :=
  (sourceMethod1767 length (fun a b => pure (JuliaLean.base.int.mul_int a b))
    (fun n product => pure (decide (product.val < n)))
    (fun k => pure (JuliaLean.base.int.eq k (JInt.lit .i64 0)))
    (fun n => pure (decide (0 < n))) (fun n k => valueMod1 n k.val)
    nth nth (fun _ _ => .error .boundsError) itr n).map (Sum.elim id id)

def nthCycleDispatchValue (tag : IteratorSizeTag) (itr : Cycle I) (n : Int)
    (dispatch : IteratorSizeTag → Cycle I → Int → Jl α) : Jl α :=
  sourceMethod1754 (fun (_ : Unit) => pure tag) () dispatch itr n

def nthFiniteDispatchValue (tag : IteratorSizeTag) (itr : Flatten (Take (Repeated I))) (n : Int)
    (dispatch : IteratorSizeTag → Flatten (Take (Repeated I)) → Int → Jl α) : Jl α :=
  sourceMethod1755 (fun (_ : Unit) => pure tag) () dispatch itr n

def observeJl (x : Jl α) : Observation JlError α := observe (liftJl x)

instance : MonadLift Jl (Observation JlError) where
  monadLift := observeJl

structure IteratorObservation (α S : Type) where
  run : Option S → Observation JlError (Option (α × S))
  isdone : Option S → Observation JlError (Option Bool)
  iteratorSize : IteratorSizeTag
  iteratorEltype : IteratorEltypeTag
  length : Jl Nat
  size : Jl (List Nat)

class AsObservation (I : Type) (α S : outParam Type) where
  view : I → IteratorObservation α S

instance : AsObservation (IteratorModel α S) α S where
  view it := ⟨(fun st => observeJl (it.run st)), (fun st => observeJl (it.isdone st)),
    it.iteratorSize, it.iteratorEltype, it.length, it.size⟩
instance : AsObservation (IteratorObservation α S) α S where
  view := id

class CollectRun (I : Type) (α S : outParam Type) (m : outParam (Type → Type)) where
  run : I → Option S → m (Option (α × S))

instance : CollectRun (IteratorModel α S) α S Jl where
  run := IteratorModel.run
instance : CollectRun (IteratorObservation α S) α S (Observation JlError) where
  run := IteratorObservation.run

def collectPrefix [Monad m] [CollectRun I α S m] (it : I) : Nat → Option S → m (List α)
  | 0, _ => pure []
  | n + 1, st => do
      match ← CollectRun.run it st with
      | none => pure []
      | some (x, next) => pure (x :: (← collectPrefix it n (some next)))

def takeObservation [AsObservation I α S] (xs : I) (t : Take I) :
    IteratorObservation α (JInt64 × S) where
  run st := observe (iterateTake (fun i s => action ((AsObservation.view i).run s)) t st)
  isdone st := observe (match st with
    | none => takeIsdone (fun i s => action ((AsObservation.view i).isdone s)) t
    | some (n, s) => takeIsdoneState (fun i s => action ((AsObservation.view i).isdone s)) t n (some s))
  iteratorSize := takeIteratorSizeOf (fun i => (AsObservation.view i).iteratorSize) t
  iteratorEltype := (AsObservation.view xs).iteratorEltype
  length := do
    let n ← takeLength (fun i => (AsObservation.view i).iteratorSize)
      (fun _ n => pure n.val.toNat) (fun i => (AsObservation.view i).length)
      pure (fun a b => pure (min a b)) t
    pure (n.elim id id)
  size := (AsObservation.view xs).size

def dropObservation [AsObservation I α S] (xs : I) (d : Drop I) : IteratorObservation α S where
  run st := observe (iterateDrop (fun i s => action ((AsObservation.view i).run s))
    (fun _ n => pure (List.range n.val.toNat))
    (fun r st => liftJl ((listIterator r).run st)) d st)
  isdone st := (AsObservation.view xs).isdone st
  iteratorSize := dropIteratorSizeOf (fun i => (AsObservation.view i).iteratorSize) d
  iteratorEltype := (AsObservation.view xs).iteratorEltype
  length := do
    let n ← dropLength (fun i => (AsObservation.view i).iteratorSize)
      (fun _ n => pure n.val.toNat) (fun i => (AsObservation.view i).length) pure
      (fun a b => pure (decide (a > b))) (fun a b => pure (a - b))
      (fun b a => pure (b - a)) (fun _ => pure 0) d
    pure (n.elim id (Sum.elim id id))
  size := (AsObservation.view xs).size

def takeWhileObservation [AsObservation I α S] (xs : I) (p : α → Bool) : IteratorObservation α S where
  run st := observe (takeWhile (fun i s => action ((AsObservation.view i).run s))
    (fun y => pure y.1) (fun pred x => pure (pred x)) ⟨p, xs⟩ st)
  isdone st := (AsObservation.view xs).isdone st
  iteratorSize := .sizeUnknown
  iteratorEltype := (AsObservation.view xs).iteratorEltype
  length := .error (.argumentError "iterator is of undefined length")
  size := .error (.argumentError "iterator is of undefined size")

def dropWhileObservation [AsObservation I α S] (xs : I) (p : α → Bool) : IteratorObservation α S where
  run st := match st with
    | some st => (AsObservation.view xs).run (some st)
    | none => observe (dropWhile (fun i s => action ((AsObservation.view i).run s))
        (fun y => pure y.1) (fun y => pure y.2) (fun pred x => pure (pred x)) ⟨p, xs⟩)
  isdone st := (AsObservation.view xs).isdone st
  iteratorSize := .sizeUnknown
  iteratorEltype := (AsObservation.view xs).iteratorEltype
  length := .error (.argumentError "iterator is of undefined length")
  size := .error (.argumentError "iterator is of undefined size")

def cycleObservation (it : Cycle (IteratorModel α S)) : IteratorObservation α S where
  run st := observe (iterateCycle (fun i s => liftJl (i.run s)) it st)
  isdone st := observeJl (match st with
    | none => isdoneCycle (fun i s => i.isdone s) it
    | some s => isdoneCycleState (fun i st => i.isdone st) it s)
  iteratorSize := .isInfinite
  iteratorEltype := (AsObservation.view it.xs).iteratorEltype
  length := .error (.argumentError "iterator is of undefined length")
  size := .error (.argumentError "iterator is of undefined size")

def flattenObservation [AsObservation OI I O] [AsObservation I α S]
    (it : Flatten OI) : IteratorObservation α (O × I × S) where
  run st := observe (match st with
    | none => flattenOuter (fun i s => action ((AsObservation.view i).run s))
        (fun i s => action ((AsObservation.view i).run s)) it none
    | some s => flattenState (fun i s => action ((AsObservation.view i).run s))
        (fun i s => action ((AsObservation.view i).run s)) it s)
  isdone _ := pure none
  iteratorSize := .sizeUnknown
  iteratorEltype := .eltypeUnknown
  length := .error (.argumentError "iterator is of undefined length")
  size := .error (.argumentError "iterator is of undefined size")

def filterObservation [AsObservation I α S] (xs : I) (p : α → Bool) : IteratorObservation α S where
  run st := observe (filterScan (fun i s => action ((AsObservation.view i).run s))
    pure (fun pred x => pure (pred x)) (fun _ => true) Prod.mk ⟨p, xs⟩ st)
  isdone st := (AsObservation.view xs).isdone st
  iteratorSize := .sizeUnknown
  iteratorEltype := (AsObservation.view xs).iteratorEltype
  length := .error (.argumentError "iterator is of undefined length")
  size := .error (.argumentError "iterator is of undefined size")

def restObservation [AsObservation I α S] (r : Rest I S) : IteratorObservation α S where
  run st := observe (iterateRest (fun i s => action ((AsObservation.view i).run s)) r st)
  isdone st := observe (isdoneRest (fun i s => action ((AsObservation.view i).isdone s)) r st)
  iteratorSize := sourceMethod739 (AsObservation.view r.itr).iteratorSize r
  iteratorEltype := sourceMethod736 (AsObservation.view r.itr).iteratorEltype r
  length := .error (.argumentError "iterator is of undefined length")
  size := .error (.argumentError "iterator is of undefined size")

def flattenListObservation (rows : List (List α)) :=
  flattenObservation (flattenModel (listIterator (rows.map listIterator)))

def repeatedListObservation (x : α) (n : Nat) :=
  let repeated := repeatedAsIterator (repeatedModel x)
  takeObservation repeated ⟨repeated, JInt.lit .i64 n⟩

def cycleOuterObservation (xs : List α) (n : Nat) :=
  repeatedListObservation (listIterator xs) n

def finiteCycleListObservation (xs : List α) (n : Nat) :=
  flattenObservation (flattenModel (cycleOuterObservation xs n))

def dropTakeObservation [AsObservation I α S] (xs : I) (td : Take (Drop I)) :=
  let d := dropObservation xs td.xs
  takeObservation d ⟨d, td.n⟩

def productTupleOfList (items : List I) :
    ProductTuple (fun _ : I => Unit) (fun _ => α) (fun _ => β) (fun _ => S) items :=
  match items with
  | [] => .nil
  | _ :: rest => .cons () (productTupleOfList rest)

def productValueList {ks : List I} : ProductValues (fun _ : I => α) ks → List α
  | .nil => []
  | .cons x xs => x :: productValueList xs

def productObservation (p : ProductIterator (List I))
    (done : I → Option S → Jl (Option Bool))
    (run : I → Option S → Jl (Option (α × S))) (defaultEltype : I → Type)
    (typeassert : I → α → Type → Jl β) :
    IteratorObservation (List β) (ProductStates (fun _ : I => β) (fun _ => S) p.iterators) :=
  let ops : ProductCalls Jl (fun _ : I => Unit) (fun _ => α) (fun _ => β) (fun _ => S) :=
    ⟨(fun i _ st => run i st), (fun i _ st => done i st),
      (fun i _ x => typeassert i x (defaultEltype i)), (fun i _ x => typeassert i x β)⟩
  let factors := productTupleOfList p.iterators
  { run := fun st => observeJl ((iterateProductTyped ops factors st).map
      (fun y => y.map fun (xs, st) => (productValueList xs, st)))
    isdone := fun st => observeJl (match st with
      | none => productIsdoneTyped ops factors
      | some st => pisdoneTyped ops factors st)
    iteratorSize := .sizeUnknown
    iteratorEltype := .hasEltype
    length := .error (.argumentError "iterator is of undefined length")
    size := .error (.argumentError "iterator size is not defined") }

def productListObservation (xs ys : List α) :=
  productObservation (productModel [listIterator xs, listIterator ys])
    (fun i st => i.isdone st) (fun i st => i.run st) (fun _ => α) (fun _ x _ => pure x)

def tupleOfList (items : List I) : TupleVals (fun _ : I => Unit) items :=
  match items with
  | [] => .nil
  | _ :: rest => .cons () (tupleOfList rest)

def tupleValueList {ks : List I} : TupleVals (fun _ : I => α) ks → List α
  | .nil => []
  | .cons x xs => x :: tupleValueList xs

def homogeneousZipLength (z : Zip (List (IteratorModel α S))) : Jl Nat :=
  zipLength (fun itr _ => pure itr.iteratorSize) (fun itr _ => itr.length)
    (fun a b => pure (min a b)) ⟨tupleOfList z.is⟩

def homogeneousZipMinimum (first : IteratorModel α S) (rest : List (IteratorModel α S)) : Jl (Option Nat) :=
  sourceMethod385 (fun itr _ => pure itr.iteratorSize) (fun itr _ => itr.length)
    (fun a b => pure (min a b)) (tupleOfList (first :: rest))

def zipSizeValues (size : I → Jl A) (two : A → A → Jl A) (z : Zip (List I)) : Jl A :=
  sourceMethod412 (fun itr _ => size itr) two ⟨tupleOfList z.is⟩

def zipAxesValues (axes : I → Jl A) (two : A → A → Jl A) (z : Zip (List I)) : Jl A :=
  sourceMethod413 (fun itr _ => axes itr) two ⟨tupleOfList z.is⟩

def zipObservation (z : Zip (List (IteratorModel α S))) :
    IteratorObservation (List α) (TupleVals (fun _ : IteratorModel α S => S) z.is) :=
  let ops : ZipCalls Jl (fun _ : IteratorModel α S => Unit) (fun _ => α) (fun _ => S) :=
    ⟨(fun i _ st => i.run st), (fun i _ st => i.isdone st)⟩
  let factors := zipModel (tupleOfList z.is)
  { run := fun st => observeJl (do
      let y ← match st with
        | none => zipStart ops factors
        | some st => zipState ops factors st
      pure (y.map fun (xs, st) => (tupleValueList xs, st)))
    isdone := fun st => observeJl (match st with
      | none => zipIsdoneStart ops factors
      | some st => zipIsdoneState ops factors st)
    iteratorSize := .sizeUnknown
    iteratorEltype := .eltypeUnknown
    length := homogeneousZipLength z
    size := .error (.argumentError "iterator size is not defined") }

def zipListObservation (xs ys : List α) := zipObservation (zipModel [listIterator xs, listIterator ys])

def takeStep (run : I → Option S → Jl (Option (α × S))) (t : Take I)
    (st : Option (JInt64 × S)) : Jl (Option (α × (JInt64 × S))) :=
  ((iterateTake (fun i s => liftJl (run i s)) t st ()).get (by
    cases st with
    | none =>
        simp only [iterateTake]
        split
        · rfl
        · cases h : run t.xs none with
          | error e => simp [liftJl, Bind.bind, Pure.pure, JuliaLean.base.iterators.bind, ret, h]
          | ok y => cases y <;> simp [liftJl, Bind.bind, Pure.pure, JuliaLean.base.iterators.bind, ret, h]
    | some pair =>
        rcases pair with ⟨n, s⟩
        simp only [iterateTake]
        split
        · rfl
        · cases h : run t.xs (some s) with
          | error e => simp [liftJl, Bind.bind, Pure.pure, JuliaLean.base.iterators.bind, ret, h]
          | ok y => cases y <;> simp [liftJl, Bind.bind, Pure.pure, JuliaLean.base.iterators.bind, ret, h])).1

def takeDone (done : I → Option S → Jl (Option Bool)) (t : Take I) : Jl (Option Bool) :=
  ((takeIsdone (fun i s => liftJl (done i s)) t ()).get
    (by simp [takeIsdone, liftJl])).1

def takeDoneState (done : I → Option S → Jl (Option Bool))
    (t : Take I) (st : JInt64 × Option S) : Jl (Option Bool) :=
  ((takeIsdoneState (fun i s => liftJl (done i s)) t st.1 st.2 ()).get (by
    cases h : done t.xs st.2 <;> simp [takeIsdoneState, liftJl, Bind.bind, Pure.pure, JuliaLean.base.iterators.bind, ret, h])).1

def dropStep (run : I → Option S → Jl (Option (α × S))) (d : Drop I)
    (st : Option S) : Observation JlError (Option (α × S)) :=
  observe (iterateDrop (fun i s => liftJl (run i s))
    (fun _ n => pure (List.range n.val.toNat))
    (fun r st => liftJl ((listIterator r).run st)) d st)

def restStep (run : I → Option S → Jl (Option (α × S)))
    (r : Rest I S) (st : Option S) : Jl (Option (α × S)) :=
  ((iterateRest (fun i s h => some (run i s, h)) r st ()).get
    (by simp [iterateRest])).1

def restDone (done : I → Option Q → Jl (Option Bool))
    (r : Rest I S) (st : Option Q) : Jl (Option Bool) :=
  ((isdoneRest (fun i s h => some (done i s, h)) r st ()).get
    (by simp [isdoneRest])).1

def peelStep (run : I → Option S → Jl (Option (α × S)))
    (itr : I) : Jl (Option (α × Rest I S)) :=
  ((peel (fun i s => liftJl (run i s)) itr ()).get (by
    cases h : run itr none with
    | error e => simp [peel, liftJl, Bind.bind, Pure.pure, JuliaLean.base.iterators.bind, ret, h]
    | ok y => cases y <;> simp [peel, liftJl, Bind.bind, Pure.pure, JuliaLean.base.iterators.bind, ret, h])).1

def takeWhileStep (apply : P → α → Bool)
    (run : I → Option S → Jl (Option (α × S))) (it : TakeWhile I P) (st : Option S) :=
  observe (takeWhile (fun i s => liftJl (run i s)) (fun y => pure y.1)
    (fun p x => pure (apply p x)) it st)

def dropWhileStep (apply : P → α → Bool)
    (run : I → Option S → Jl (Option (α × S))) (it : DropWhile I P) :=
  observe (dropWhile (fun i s => liftJl (run i s)) (fun y => pure y.1)
    (fun y => pure y.2) (fun p x => pure (apply p x)) it)

def filterStep (apply : F → α → Bool)
    (run : I → Option S → Jl (Option (α × S))) (it : Filter F I)
    (st : Option S) (isTuple2 : α × S → Bool := fun _ => true) :=
  observe (filterScan (fun i s => liftJl (run i s)) pure
    (fun f x => pure (apply f x)) isTuple2 Prod.mk it st)

def flattenStartStep (outer : IteratorModel (IteratorModel α S) O) :=
  observe (flattenOuter (fun i s => liftJl (i.run s)) (fun i s => liftJl (i.run s))
    (flattenModel outer) none)

def flattenStateStep (outer : IteratorModel (IteratorModel α S) O) (st : O × IteratorModel α S × S) :=
  observe (flattenState (fun i s => liftJl (i.run s)) (fun i s => liftJl (i.run s))
    (flattenModel outer) st)

def productExpectedStates (items : List I) (value : I → V) (state : I → S) :
    ProductStates (fun _ : I => V) (fun _ => S) items :=
  match items with
  | [] => .nil
  | i :: rest => .cons (value i, state i) (productExpectedStates rest value state)

def productLastObservation (last : I → Jl V) (p : ProductIterator (List I)) : Jl (List V) := do
  let values ← tupleLast (fun i _ => last i) (productModel (tupleOfList p.iterators))
  pure (tupleValueList values)

def productReverseObservation (reverse : I → Jl R) (p : ProductIterator (List I)) :
    Jl (ProductIterator (List R)) := do
  let p ← tupleReverse (fun i _ => reverse i) (productModel (tupleOfList p.iterators))
  pure (productModel (tupleValueList p.iterators))

def tupleOptions (inputs : List (I × Option S)) :
    TupleVals (fun _ : I × Option S => Option S) inputs :=
  match inputs with
  | [] => .nil
  | (_, st) :: rest => .cons st (tupleOptions rest)

def zipOrderObservation (run : I → Option S → Jl (Option (V × S)))
    (inputs : List (I × Option S)) : Jl (Option (List V × List (Option S))) := do
  let ops : ZipCalls Jl (fun _ : I × Option S => Unit) (fun _ => V) (fun _ => S) :=
    { run := fun i _ st => run i.1 st, done := fun _ _ _ => pure none }
  let values ← zipInOrder ops (tupleOfList inputs) (tupleOptions inputs)
  pure (values.map fun xs =>
    ((tupleValueList xs).map Prod.fst, (tupleValueList xs).map (fun x => some x.2)))

def zipAnyDoneObservation (done : I → Option S → Jl (Option Bool))
    (inputs : List (I × Option S)) : Jl (Option Bool) :=
  let ops : ZipCalls Jl (fun _ : I × Option S => Unit) (fun _ => Unit) (fun _ => S) :=
    { run := fun _ _ _ => pure none, done := fun i _ st => done i.1 st }
  zipAnyDone ops (tupleOfList inputs) (tupleOptions inputs)

def zipDoneScanObservation (done : I → Option S → Jl (Option Bool))
    (inputs : List (I × Option S)) : Jl (Bool × List (Option Bool)) := do
  let ops : ZipCalls Jl (fun _ : I × Option S => Unit) (fun _ => Unit) (fun _ => S) :=
    { run := fun _ _ _ => pure none, done := fun i _ st => done i.1 st }
  let (finished, ds) ← zipDoneScan ops (tupleOfList inputs) (tupleOptions inputs)
  pure (finished, tupleValueList ds)

def zipAllObservation (done : I → Option S → Jl (Option Bool))
    (run : I → Option S → Jl (Option (V × S)))
    (inputs : List (I × Option S)) : Jl (Option (List V × List (Option S))) := do
  let ops : ZipCalls Jl (fun _ : I × Option S => Unit) (fun _ => V) (fun _ => S) :=
    { run := fun i _ st => run i.1 st, done := fun i _ st => done i.1 st }
  let values ← zipIterateAll ops (tupleOfList inputs) (tupleOptions inputs)
  pure (values.map fun (xs, ss) => (tupleValueList xs, (tupleValueList ss).map some))

def allMissingObservation (ds : List (Option Bool)) : Bool :=
  tupleAllMissing (tupleMap (fun d _ => d) (tupleOfList ds))

def projectZipState {ks : List I}
    (result : Observation JlError (Option (List α × TupleVals (fun _ : I => S) ks))) :
    Observation JlError (Option (List α × List (Option S))) :=
  result.map (fun y => y.map fun (xs, st) => (xs, (tupleValueList st).map some))

inductive AnyCache where
  | any

structure StatefulSnapshot (I VS : Type) (Value : Type := VS) where
  itr : I
  nextvalstate : Option Value
  cacheType : JuliaLean.base.promotion.PType := .any
  assertValue : Option Value → JuliaLean.base.promotion.PType → Jl (Option Value) :=
    fun value _ => pure value
  cacheTypeOf : JuliaLean.base.promotion.PType → JuliaLean.base.promotion.PType :=
    fun _ => .any

def snapshotOps : StatefulOps IteratorError (StatefulSnapshot I VS Y) Unit I Y
    JuliaLean.base.promotion.PType where
  allocate itr ty value := fun heap => some (.ok (),
    { heap with itr := itr, nextvalstate := value, cacheType := heap.cacheTypeOf ty })
  iterator _ := fun heap => some (.ok heap.itr, heap)
  pending _ := fun heap => some (.ok heap.nextvalstate, heap)
  declaredCacheType _ := fun heap => some (.ok heap.cacheType, heap)
  setIterator _ itr := fun heap => some (.ok (), { heap with itr := itr })
  writeCacheRaw _ value := fun heap => some (.ok (), { heap with nextvalstate := value })
  assertCache value ty := fun heap => some ((heap.assertValue value ty).mapError IteratorError.julia, heap)

def snapshotOutcome (x : Exec IteratorError (StatefulSnapshot I VS Y) α)
    (heap : StatefulSnapshot I VS Y) : Observation IteratorError (α × StatefulSnapshot I VS Y) :=
  match x heap with
  | none => .diverged
  | some (.error e, _) => .error e
  | some (.ok a, heap) => .ok (a, heap)

def statefulAnySnapshot (run : I → Option S → Jl (Option (α × S))) (itr : I) :
    Observation IteratorError (StatefulSnapshot I AnyCache (α × S)) :=
  (snapshotOutcome (statefulAny snapshotOps
    (fun i heap => some ((run i none).mapError IteratorError.julia, heap)) .any itr)
    { itr := itr, nextvalstate := none }).map Prod.snd

def resetSnapshot (run : I → Option S → Jl (Option (α × S)))
    (s : StatefulSnapshot I VS (α × S)) : Observation IteratorError (StatefulSnapshot I VS (α × S)) :=
  (snapshotOutcome (resetStateful snapshotOps
    (fun i heap => some ((run i none).mapError IteratorError.julia, heap)) ()) s).map Prod.snd

def resetSnapshotTo (run : I → Option S → Jl (Option (α × S)))
    (s : StatefulSnapshot I VS (α × S)) (itr : I) :
    Observation IteratorError (StatefulSnapshot I VS (α × S)) :=
  (snapshotOutcome (resetStatefulTo snapshotOps
    (fun i heap => some ((run i none).mapError IteratorError.julia, heap)) () itr) s).map Prod.snd

def popSnapshot (run : I → Option S → Jl (Option (α × S)))
    (s : StatefulSnapshot I VS (α × S)) :
    Observation IteratorError (α × StatefulSnapshot I VS (α × S)) :=
  snapshotOutcome (popfirstStateful snapshotOps
    (fun i st heap => some ((run i (some st)).mapError IteratorError.julia, heap)) .eofError ()) s

def peekSnapshot (s : StatefulSnapshot I VS (α × S)) (sentinel : β) :
    Observation IteratorError (α ⊕ β) :=
  (snapshotOutcome (peekStateful snapshotOps () sentinel) s).map Prod.fst

def isdoneSnapshot (s : StatefulSnapshot I VS Y) : Observation IteratorError Bool :=
  (snapshotOutcome (isdoneStateful snapshotOps ()) s).map Prod.fst

def iterateSnapshot (run : I → Option S → Jl (Option (α × S)))
    (s : StatefulSnapshot I VS (α × S)) :
    Observation IteratorError (Option (α × Unit) × StatefulSnapshot I VS (α × S)) :=
  snapshotOutcome (iterateStateful snapshotOps
    (fun i st heap => some ((run i (some st)).mapError IteratorError.julia, heap)) .eofError ()) s

def collectSnapshots (run : I → Option S → Jl (Option (α × S))) :
    Nat → StatefulSnapshot I VS (α × S) →
      Observation IteratorError (List α × StatefulSnapshot I VS (α × S))
  | 0, s => pure ([], s)
  | fuel + 1, s => do
      let (step, s) ← iterateSnapshot run s
      match step with
      | none => pure ([], s)
      | some (x, _) =>
          let (xs, s) ← collectSnapshots run fuel s
          pure (x :: xs, s)

def statefulConstructorObservation
    (run : I → Option S → Jl (Option (α × S)))
    (typeof : I → JuliaLean.base.promotion.PType)
    (types : DescriptorOps JuliaLean.base.promotion.PType)
    (assertValue : Option (α × S) → JuliaLean.base.promotion.PType → Jl (Option (α × S)))
    (cacheTypeOf : JuliaLean.base.promotion.PType → JuliaLean.base.promotion.PType)
    (itr : I) : Observation IteratorError (StatefulSnapshot I Unit (α × S)) :=
  (snapshotOutcome (stateful snapshotOps types typeof
    (fun i heap => some ((run i none).mapError IteratorError.julia, heap)) itr)
    { itr := itr, nextvalstate := none, assertValue := assertValue,
      cacheTypeOf := cacheTypeOf }).map Prod.snd

def partitionNativeConstruct (c : I) (n : Int) (construct : I → Nat → PartitionIterator C) :
    Jl (PartitionIterator C) :=
  partition (fun n => pure (decide (n < 1))) (JInt.convert (IntTy.i64.name) .i64)
    (fun n => pure (toString n)) (fun message => .error (.argumentError message))
    (fun i n => pure (construct i n.val.toNat)) c n

def partitionListStep (run : I → Option S → Jl (Option (α × S)))
    (p : PartitionIterator I) (st : PartitionState S := .at none) :
    Observation JlError (Option (List α × PartitionState S)) :=
  let allocate : Unit → JInt64 → Exec JlError (List α) Unit := fun _ n heap =>
    match allocPartitionList (α := α) α n with
    | .error e => some (.error e, heap)
    | .ok xs => some (.ok (), xs)
  let store := fun (_ : Unit) (x : α) (_ : JInt64) (xs : List α) =>
    some (.ok (), xs ++ [x])
  let resize := fun (_ : Unit) (_ : JInt64) (xs : List α) => some (.ok (), xs)
  match partitionGeneric (fun _ => ()) allocate store resize
      (fun i s heap => some (run i s, heap)) p st [] with
  | none => .diverged
  | some (.error e, _) => .error e
  | some (.ok result, xs) => .ok (result.map fun (_, st) => (xs, st))

def partitionGenericObservation (xs : List α) (n : Nat) :
    IteratorObservation (List α) (PartitionState Nat) where
  run st := partitionListStep (fun i s => i.run s)
    ⟨listIterator xs, JInt.lit .i64 n⟩ (st.getD (.at none))
  isdone _ := pure none
  iteratorSize := sourceMethod1461 .hasLength ⟨listIterator xs, JInt.lit .i64 n⟩
  iteratorEltype := sourceMethod1455 .hasEltype ⟨listIterator xs, JInt.lit .i64 n⟩
  length := partitionLength (fun i => i.length)
    (fun l k => pure ((l + k.val.toNat - 1) / k.val.toNat)) ⟨listIterator xs, JInt.lit .i64 n⟩
  size := do
    let len ← partitionLength (fun i => i.length)
      (fun l k => pure ((l + k.val.toNat - 1) / k.val.toNat)) ⟨listIterator xs, JInt.lit .i64 n⟩
    pure [len]

def partitionVectorObservation (it : PartitionIterator (List α)) :
    IteratorObservation (List α) JInt64 where
  run state := observeJl (iteratePartitionVectorI64
    (fun _ => pure (JInt.lit .i64 1))
    (fun xs => pure (JInt.lit .i64 xs.length))
    (fun s r => pure (s, r))
    (fun xs (s, r) => pure ((xs.drop (s.val - 1).toNat).take (r.val - s.val + 1).toNat)) it state)
  isdone state := pure (some ((state.getD (JInt.lit .i64 1)).val > Int.ofNat it.c.length))
  iteratorSize := sourceMethod1461 .hasLength it
  iteratorEltype := sourceMethod1456 it
  length := partitionLength (fun xs => pure xs.length)
    (fun l n => pure ((l + n.val.toNat - 1) / n.val.toNat)) it
  size := do
    let len ← partitionLength (fun xs => pure xs.length)
      (fun l n => pure ((l + n.val.toNat - 1) / n.val.toNat)) it
    pure [len]

def iterablePairsObservation (xs : List α) : IteratorModel (Nat × α) Nat where
  run st := iterateStatePairs (fun _ => pure (List.range xs.length))
    (fun _ => pure 0) (fun ys st => (listIterator ys).run (some st)) (pairsStringModel xs) st
  isdone st := (listIterator xs).isdone st
  iteratorSize := sourceMethod1704 .hasLength (pairsStringModel xs)
  iteratorEltype := .hasEltype
  length := iterableStatePairsLength (fun ys => pure ys.length) (pairsStringModel xs)
  size := pure [xs.length]

def pairsObservation (xs : List α) : IteratorModel (Nat × α) Nat :=
  let p : PairsModel Nat α (List Nat) (List α) :=
    pairsLinear (fun ys => List.range ys.length) xs
  { run := fun st => iteratePairs (fun ys => pure (List.range ys.length))
      (fun keys state => (listIterator keys).run state)
      (fun ys i => (listGet ys i).elim (.error .boundsError) pure)
      (fun key value => pure (key, value)) p st
    isdone := fun st => (listIterator xs).isdone st
    iteratorSize := .hasLength
    iteratorEltype := .hasEltype
    length := pairsMetadata (fun ys => pure (List.range ys.length)) (fun ks => pure ks.length) p
    size := pairsMetadata (fun ys => pure (List.range ys.length)) (fun ks => pure [ks.length]) p }

def reversePairsObservation (xs : List α) : IteratorModel (Nat × α) (List Nat × Nat) :=
  let p : PairsModel Nat α (List Nat) (List α) :=
    pairsLinear (fun ys => List.range ys.length) xs
  { run := fun st => iterateReversePairs (fun ys => pure (List.range ys.length))
      (fun keys => pure keys.reverse) (fun keys state => (listIterator keys).run state)
      (fun ys i => (listGet ys i).elim (.error .boundsError) pure)
      (fun key value => pure (key, value)) ⟨p⟩ st
    isdone := fun st => pure (some (xs.length ≤ (st.map Prod.snd).getD 0))
    iteratorSize := .hasLength
    iteratorEltype := .hasEltype
    length := pure xs.length
    size := pure [xs.length] }

def liftFoldValue [Monad m] : JuliaLean.base.reduce.FoldInit α → JuliaLean.base.reduce.FoldInit (m α)
  | .initial => .initial
  | .value a => .value (pure a)

def accumulateNativeStep
    (run : I → Option S → Exec JlError H (Option (α × S)))
    (rf : JuliaLean.base.reduce.Reducer (Exec JlError H β) α)
    (init : JuliaLean.base.reduce.FoldInit (Exec JlError H β)) (itr : I)
    (st : Option (JuliaLean.base.reduce.FoldInit β × S)) :
    Exec JlError H (Option (JuliaLean.base.reduce.FoldInit β ×
      (JuliaLean.base.reduce.FoldInit β × S))) :=
  match st with
  | none => accumulateStart run ⟨rf, itr, init⟩
  | some st => accumulateState
      (fun rf value x => forceFoldInit (rf.step (liftFoldValue value) x))
      run ⟨rf, itr, init⟩ st

def collectAccumulateNative
    (run : I → Option S → Exec JlError H (Option (α × S)))
    (rf : JuliaLean.base.reduce.Reducer (Exec JlError H β) α)
    (init : JuliaLean.base.reduce.FoldInit (Exec JlError H β)) (itr : I) :
    Nat → Option (JuliaLean.base.reduce.FoldInit β × S) →
      Exec JlError H (List (JuliaLean.base.reduce.FoldInit β))
  | 0, _ => pure []
  | depth + 1, st => do
      match ← accumulateNativeStep run rf init itr st with
      | none => pure []
      | some (value, next) =>
          pure (value :: (← collectAccumulateNative run rf init itr depth (some next)))

def callablePrefixScan
    (rf : JuliaLean.base.reduce.Reducer (Exec JlError H β) α) :
    Nat → JuliaLean.base.reduce.FoldInit β → List α →
      Exec JlError H (List (JuliaLean.base.reduce.FoldInit β))
  | 0, _, _ => pure []
  | _ + 1, _, [] => pure []
  | depth + 1, previous, x :: xs => do
      let value ← forceFoldInit (rf.step (liftFoldValue previous) x)
      pure (value :: (← callablePrefixScan rf depth value xs))

def accumulationPrefixSpec
    (rf : JuliaLean.base.reduce.Reducer (Exec JlError H β) α)
    (init : JuliaLean.base.reduce.FoldInit (Exec JlError H β))
    (xs : List α) (depth : Nat) : Exec JlError H (List (JuliaLean.base.reduce.FoldInit β)) := do
  match depth, xs with
  | 0, _ => pure []
  | _ + 1, [] => pure []
  | depth + 1, x :: xs =>
      let value ← forceFoldInit (match init with
        | .initial => JuliaLean.base.reduce.bottomRF_initial ⟨rf⟩ x
        | .value acc => JuliaLean.base.reduce.bottomRF_apply ⟨rf⟩ acc x)
      pure (value :: (← callablePrefixScan rf depth value xs))


def generatorObservation [AsObservation I α S]
    (g : JuliaLean.base.generator.Generator I (α → β)) : IteratorObservation β S where
  run st := JuliaLean.base.generator.iterateGenerator (fun f x => pure (f x))
    (fun itr state => (AsObservation.view itr).run state) pure g st
  isdone st := (AsObservation.view g.iter).isdone st
  iteratorSize := (AsObservation.view g.iter).iteratorSize
  iteratorEltype := .eltypeUnknown
  length := (AsObservation.view g.iter).length
  size := (AsObservation.view g.iter).size

def findeachObservation
    (g : JuliaLean.base.generator.Generator
      (Filter ((K × V) → Bool) (IteratorModel (K × V) S)) ((K × V) → K)) :=
  generatorObservation ⟨g.f,filterObservation g.iter.itr g.iter.flt⟩

def reverseFlattenObservation (rows : List (List α)) :=
  let revGen := (sourceMethod1379 (m := Id) reverseListAsIterator reverseListAsIterator (flattenModel rows)).it
  let outer : IteratorObservation (IteratorModel α Int) Int := generatorObservation revGen
  flattenObservation ⟨outer⟩

def firstObservation [AsObservation I α S] (it : I) : Observation JlError α := do
  let actual ← (AsObservation.view it).run none
  observeJl (firstIterModel
    { run := fun _ => pure actual
      isdone := fun _ => pure none
      iteratorSize := .sizeUnknown
      iteratorEltype := .eltypeUnknown
      length := .error (.argumentError "iterator is of undefined length")
      size := .error (.argumentError "iterator is of undefined size") })

def lastFlattenObservation (rows : List (List α)) : Observation JlError α := do
  let actual ← firstObservation (reverseFlattenObservation rows)
  observeJl (lastFlatten
    (fun f => pure (sourceMethod1379 (m := Id) (I := List α)
      reverseListAsIterator reverseListAsIterator f))
    (fun _ => pure actual) (flattenModel rows))

namespace Round4

/-- A finite history, without requiring that the iterator ends after the history. -/
inductive History {α S : Type} {m : Type → Type} [Monad m] (run : Option S → m (Option (α × S))) :
    Option S → List α → Option S → Prop where
  | nil (st) : History run st [] st
  | cons {st x next xs final} : run st = pure (some (x, next)) →
      History run (some next) xs final → History run st (x :: xs) final


end Round4

def r6OrdinalList {α : Type} (xs : List α) (n : Int) : Jl α :=
  if n ≤ 0 then .error .boundsError else
    match listGet xs (n.toNat - 1) with
    | none => .error .boundsError
    | some value => .ok value


def r6CartesianRows {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: rest =>
      (r6CartesianRows rest).flatMap (fun tail => xs.map (fun x => x :: tail))


def r6WrappedCountProgression (start step : JInt64) : Nat → List JInt64
  | 0 => []
  | n + 1 => start :: r6WrappedCountProgression
      (JuliaLean.base.int.add_int start step) step n



def observeRun [Monad m] (run : Option S → m (Option (α × S))) : Nat → Option S → m (List α)
  | 0, _ => pure []
  | n + 1, st => do
      match ← run st with
      | none => pure []
      | some (x, next) => pure (x :: (← observeRun run n (some next)))


set_option linter.deprecated false

open JuliaLean
open JuliaLean.Registry
open JuliaLean.base.iterators

/-!
# Properties of `base/iterators.jl`

Specifications of the iterator adapters, trait combinators, metadata queries, and iteration
protocols modelled in `JuliaLean.base.iterators`, stated from the docstrings, the manual, and
collection invariants, with their proofs and refutations.

## Nothing to promise (pure forwarding / struct construction / trait plumbing)
- `map@56`: `map(f, arg, args...) = Base.Generator(f, arg, args...)` forwards directly to `Base.Generator` (also covered in `iteratorscov-cycle-repeated`).
- `reverse@113`: `reverse(itr) = Reverse(itr)` wraps an arbitrary iterator in `Reverse` (also covered in `iteratorscov-reverse-yields`).
- `eltype@128`: `eltype(::Type{Reverse{T}}) where {T} = eltype(T)` forwards the element type of the wrapped iterator (also covered in `iteratorscov-reverse-traits`).
- `length@129`: `length(r::Reverse) = length(r.itr)` forwards `length` to the wrapped iterator (also covered in `iteratorscov-reverse-traits`).
- `size@130`: `size(r::Reverse) = size(r.itr)` forwards `size` to the wrapped iterator (also covered in `iteratorscov-reverse-traits`).
- `IteratorSize@131`: `IteratorSize(::Type{Reverse{T}}) where {T} = IteratorSize(T)` forwards the size trait of `T` (also covered in `iteratorscov-reverse-traits`).
- `IteratorEltype@132`: `IteratorEltype(::Type{Reverse{T}}) where {T} = IteratorEltype(T)` forwards the eltype trait of `T` (also covered in `iteratorscov-reverse-traits`).
- `last@133`: `last(r::Reverse) = first(r.itr)` forwards `last` on a reversed iterator to `first` of the underlying iterator (also covered in `iteratorscov-reverse-traits`).
- `reverse@156`: `reverse(R::AbstractRange) = Base.reverse(R)` delegates range reversal to `Base.reverse` (also covered in `iteratorscov-reverse-yields`).
- `reverse@157`: `reverse(G::Generator) = Generator(G.f, reverse(G.iter))` reconstructs the `Generator` over the reversed inner iterator (also covered in `iteratorscov-reverse-yields`).
- `reverse@158`: `reverse(r::Reverse) = r.itr` unwraps `Reverse` (also covered in `iteratorscov-reverse-yields`).
- `reverse@159`: `reverse(x::Union{Number,AbstractChar}) = x` is the identity on scalars (also covered in `iteratorscov-reverse-yields`).
- `reverse@160`: `reverse(p::Pair) = Base.reverse(p)` delegates pair reversal to `Base.reverse` (also covered in `iteratorscov-reverse-yields`).
- `enumerate@207`: `enumerate(iter) = Enumerate(iter)` wraps `iter` in `Enumerate` (also covered in `iterators-enumerate`).
- `length@209`: `length(e::Enumerate) = length(e.itr)` forwards `length` to `e.itr` (also covered in `iterators-enumerate`).
- `size@210`: `size(e::Enumerate) = size(e.itr)` forwards `size` to `e.itr` (also covered in `iteratorscov-enumerate`).
- `eltype@219`: `eltype(::Type{Enumerate{I}}) where {I} = TupleOrBottom(Int, eltype(I))` pairs `Int` with `eltype(I)` (also covered in `iteratorscov-enumerate`).
- `IteratorSize@221`: `IteratorSize(::Type{Enumerate{I}}) where {I} = IteratorSize(I)` forwards the size trait of `I` (also covered in `iteratorscov-enumerate`).
- `IteratorEltype@222`: `IteratorEltype(::Type{Enumerate{I}}) where {I} = IteratorEltype(I)` forwards the eltype trait of `I` (also covered in `iteratorscov-enumerate`).
- `pairs@281`: `pairs(::IndexLinear, A::AbstractArray) = Pairs(A, LinearIndices(A))` constructs `Pairs` with `LinearIndices(A)` (also covered in `iteratorscov-pairs-semantics`).
- `pairs@285`: `pairs(tuple::Tuple) = Pairs{Int}(tuple, keys(tuple))` constructs `Pairs` with `keys(tuple)` (also covered in `iteratorscov-pairs-semantics`).
- `pairs@286`: `pairs(nt::NamedTuple) = Pairs{Symbol}(nt, nothing)` constructs `Pairs` over a `NamedTuple` (also covered in `iteratorscov-pairs-semantics`).
- `pairs@287`: `pairs(v::Core.SimpleVector) = Pairs(v, LinearIndices(v))` constructs `Pairs` with `LinearIndices(v)` (also covered in `iteratorscov-pairs-semantics`).
- `pairs@288`: `pairs(A::AbstractVector) = pairs(IndexLinear(), A)` forwards vector `pairs` to linear indexing (also covered in `iteratorscov-pairs-semantics`).
- `pairs@291`: `pairs(::IndexCartesian, A::AbstractArray) = Pairs(A, CartesianIndices(A))` constructs `Pairs` with `CartesianIndices(A)` (also covered in `iteratorscov-pairs-semantics`).
- `pairs@292`: `pairs(A::AbstractArray) = pairs(IndexCartesian(), A)` forwards general array `pairs` to Cartesian indexing (also covered in `iteratorscov-pairs-semantics`).
- `length@294`: `length(v::Pairs) = length(keys(v))` forwards `length` to `keys(v)` (also covered in `iteratorscov-pairs-semantics`).
- `axes@295`: `axes(v::Pairs) = axes(keys(v))` forwards `axes` to `keys(v)` (also covered in `iteratorscov-pairs-semantics`).
- `size@296`: `size(v::Pairs) = size(keys(v))` forwards `size` to `keys(v)` (also covered in `iteratorscov-pairs-semantics`).
- `isdone@316`: `isdone(v::Pairs, state...) = isdone(keys(v), state...)` forwards `isdone` to `keys(v)` (also covered in `iteratorscov-pairs-semantics`).
- `IteratorSize@318`: `IteratorSize(::Type{<:Pairs{<:Any,<:Any,I}}) where {I} = IteratorSize(I)` forwards the key iterator's size trait (also covered in `iteratorscov-pairs-semantics`).
- `IteratorSize@319`: `IteratorSize(::Type{<:Pairs{<:Any,<:Any,<:AbstractUnitRange}}) = HasLength()` reports `HasLength()` for unit-range keys (also covered in `iteratorscov-pairs-semantics`).
- `haskey@326`: `haskey(v::Pairs, key) = key in keys(v)` delegates membership to `keys(v)` (also covered in `iteratorscov-pairs-semantics`).
- `values@328`: `values(v::Pairs) = getfield(v, :data)` projects the underlying data collection (also covered in `iteratorscov-pairs-semantics`).
- `getindex@329`: `getindex(v::Pairs, key) = values(v)[key]` delegates indexing to `values(v)` (also covered in `iteratorscov-pairs-semantics`).
- `setindex!@330`: `setindex!(v::Pairs, value, key) = (values(v)[key] = value; v)` delegates mutation to `values(v)` (also covered in `iteratorscov-pairs-semantics`).
- `get@331`: `get(v::Pairs, key, default) = get(values(v), key, default)` delegates default lookup to `values(v)` (also covered in `iteratorscov-pairs-semantics`).
- `get@332`: `get(f::Base.Callable, v::Pairs, key) = get(f, values(v), key)` delegates thunk lookup to `values(v)` (also covered in `iteratorscov-pairs-semantics`).
- `zip@379`: `zip(a...) = Zip(a)` wraps the tuple of iterators in `Zip` (also covered in `iterators-zip`).
- `_promote_tuple_shape@416`: `_promote_tuple_shape(a, b) = promote_shape(a, b)` forwards to `promote_shape` (also covered in `iteratorscov-zip-metadata`).
- `_promote_tuple_shape@418`: `_promote_tuple_shape(a) = a` is the unary identity base case (also covered in `iteratorscov-zip-metadata`).
- `last@519`: `last(z::Zip) = nth(z, length(z))` delegates `last` to `nth` at `length(z)` (also covered in `iteratorscov-zip-metadata`).
- `filter@576`: `filter(flt, itr) = Filter(flt, itr)` wraps `flt` and `itr` in `Filter` (also covered in `iteratorscov-filter`).
- `eltype@594`: `eltype(::Type{Filter{F,I}}) where {F,I} = eltype(I)` forwards `eltype(I)` (also covered in `iteratorscov-filter`).
- `IteratorEltype@595`: `IteratorEltype(::Type{Filter{F,I}}) where {F,I} = IteratorEltype(I)` forwards `IteratorEltype(I)` (also covered in `iteratorscov-filter`).
- `IteratorSize@596`: `IteratorSize(::Type{<:Filter}) = SizeUnknown()` reports `SizeUnknown()` (also covered in `iteratorscov-filter`).
- `reverse@598`: `reverse(f::Filter) = Filter(f.flt, reverse(f.itr))` wraps `reverse(f.itr)` in `Filter` (also covered in `iteratorscov-filter`).
- `last@599`: `last(f::Filter) = first(reverse(f))` delegates `last` to `first(reverse(f))` (also covered in `iteratorscov-filter`).
- `accumulate@641`: `accumulate(f, itr; init=...) = Accumulate(f, itr, init)` constructs `Accumulate` (also covered in `iterators-accumulate`).
- `length@661`: `length(itr::Accumulate) = length(itr.itr)` forwards `length` to `itr.itr` (also covered in `iteratorscov-accumulate`).
- `size@662`: `size(itr::Accumulate) = size(itr.itr)` forwards `size` to `itr.itr` (also covered in `iteratorscov-accumulate`).
- `IteratorSize@664`: `IteratorSize(::Type{<:Accumulate{<:Any,I}}) where {I} = IteratorSize(I)` forwards `IteratorSize(I)` (also covered in `iteratorscov-accumulate`).
- `IteratorEltype@665`: `IteratorEltype(::Type{<:Accumulate}) = EltypeUnknown()` reports `EltypeUnknown()` (also covered in `iteratorscov-accumulate`).
- `rest@696`: `rest(itr, state) = Rest(itr, state)` constructs `Rest` (also covered in `iteratorscov-rest`).
- `rest@697`: `rest(itr::Rest, state) = Rest(itr.itr, state)` replaces the state of an existing `Rest` (also covered in `iteratorscov-rest`).
- `rest@698`: `rest(itr) = itr` is the unary identity (also covered in `iteratorscov-rest`).
- `eltype@735`: `eltype(::Type{<:Rest{I}}) where {I} = eltype(I)` forwards `eltype(I)` (also covered in `iteratorscov-rest`).
- `IteratorEltype@736`: `IteratorEltype(::Type{<:Rest{I}}) where {I} = IteratorEltype(I)` forwards `IteratorEltype(I)` (also covered in `iteratorscov-rest`).
- `eltype@770`: `eltype(::Type{<:Count{T}}) where {T} = T` returns the type parameter `T` (also covered in `iteratorscov-countfrom-eltype`).
- `IteratorSize@774`: `IteratorSize(::Type{<:Count}) = IsInfinite()` reports `IsInfinite()` (also covered in `iteratorscov-countfrom-integers`).
- `eltype@818`: `eltype(::Type{Take{I}}) where {I} = eltype(I)` forwards `eltype(I)` (also covered in `iteratorscov-take`).
- `IteratorEltype@819`: `IteratorEltype(::Type{Take{I}}) where {I} = IteratorEltype(I)` forwards `IteratorEltype(I)` (also covered in `iteratorscov-take`).
- `eltype@875`: `eltype(::Type{Drop{I}}) where {I} = eltype(I)` forwards `eltype(I)` (also covered in `iteratorscov-drop`).
- `IteratorEltype@876`: `IteratorEltype(::Type{Drop{I}}) where {I} = IteratorEltype(I)` forwards `IteratorEltype(I)` (also covered in `iteratorscov-drop`).
- `iterate@891`: `iterate(it::Drop, state) = iterate(it.xs, state)` forwards subsequent iteration steps to `it.xs` (also covered in `iteratorscov-drop`).
- `isdone@892`: `isdone(it::Drop, state) = isdone(it.xs, state)` forwards `isdone` with state to `it.xs` (also covered in `iteratorscov-drop`).
- `takewhile@928`: `takewhile(pred, xs) = TakeWhile(pred, xs)` constructs `TakeWhile` (also covered in `iterators-takewhile-dropwhile`).
- `IteratorSize@937`: `IteratorSize(::Type{<:TakeWhile}) = SizeUnknown()` reports `SizeUnknown()` (also covered in `iteratorscov-while`).
- `eltype@938`: `eltype(::Type{TakeWhile{I,P}} where P) where {I} = eltype(I)` forwards `eltype(I)` (also covered in `iteratorscov-while`).
- `IteratorEltype@939`: `IteratorEltype(::Type{TakeWhile{I,P}} where P) where {I} = IteratorEltype(I)` forwards `IteratorEltype(I)` (also covered in `iteratorscov-while`).
- `dropwhile@976`: `dropwhile(pred, itr) = DropWhile(pred, itr)` constructs `DropWhile` (also covered in `iterators-takewhile-dropwhile`).
- `iterate@978`: `iterate(ibl::DropWhile, itr) = iterate(ibl.xs, itr)` forwards subsequent iteration steps to `ibl.xs` (also covered in `iteratorscov-while`).
- `IteratorSize@988`: `IteratorSize(::Type{<:DropWhile}) = SizeUnknown()` reports `SizeUnknown()` (also covered in `iteratorscov-while`).
- `eltype@989`: `eltype(::Type{DropWhile{I,P}}) where {I,P} = eltype(I)` forwards `eltype(I)` (also covered in `iteratorscov-while`).
- `IteratorEltype@990`: `IteratorEltype(::Type{DropWhile{I,P}}) where {I,P} = IteratorEltype(I)` forwards `IteratorEltype(I)` (also covered in `iteratorscov-while`).
- `findeach@1018`: `findeach(it) = findeach(identity, it)` forwards to `findeach` with `identity` (also covered in `iteratorscov-cycle-repeated`).
- `cycle@1058`: `cycle(xs) = Cycle(xs)` constructs `Cycle` (also covered in `iteratorscov-cycle-repeated`).
- `eltype@1061`: `eltype(::Type{Cycle{I}}) where {I} = eltype(I)` forwards `eltype(I)` (also covered in `iteratorscov-cycle-repeated`).
- `IteratorEltype@1062`: `IteratorEltype(::Type{Cycle{I}}) where {I} = IteratorEltype(I)` forwards `IteratorEltype(I)` (also covered in `iteratorscov-cycle-repeated`).
- `reverse@1074`: `reverse(it::Cycle) = Cycle(reverse(it.xs))` wraps `reverse(it.xs)` in `Cycle` (also covered in `iteratorscov-cycle-repeated`).
- `last@1075`: `last(it::Cycle) = last(it.xs)` forwards `last` to `it.xs` (also covered in `iteratorscov-cycle-repeated`).
- `repeated@1083`: `repeated(x) = Repeated(x)` constructs `Repeated` (also covered in `iterators-repeated-n`).
- `eltype@1113`: `eltype(::Type{Repeated{O}}) where {O} = O` returns `O` (also covered in `iteratorscov-cycle-repeated`).
- `reverse@1120`: `reverse(it::Union{Repeated,Take{<:Repeated}}) = it` is the identity on repeated iterators (also covered in `iteratorscov-cycle-repeated`).
- `last@1121`: `last(it::Union{Repeated,Take{<:Repeated}}) = first(it)` forwards `last` to `first` (also covered in `iteratorscov-cycle-repeated`).
- `product@1148`: `product(iters...) = ProductIterator(iters)` constructs `ProductIterator` (also covered in `iterators-product`).
- `reverse@1255`: `reverse(p::ProductIterator) = ProductIterator(Base.map(reverse, p.iterators))` maps `reverse` over factor iterators (also covered in `iteratorscov-product-methods`).
- `flatten@1291`: `flatten(itr) = Flatten(itr)` constructs `Flatten` (also covered in `iterators-flatten`).
- `eltype@1293`: `eltype(::Type{Flatten{I}}) where {I} = eltype(eltype(I))` delegates to the inner `eltype` (also covered in `iteratorscov-flatten-methods`).
- `last@1380`: `last(f::Flatten) = first(reverse(f))` delegates `last` to `first(reverse(f))` (also covered in `iteratorscov-flatten-methods`).
- `flatmap@1421`: `flatmap(f, c...) = flatten(map(f, c...))` composes `flatten` and `map` (also covered in `iteratorscov-cycle-repeated`).
- `PartitionIterator@1446`: `PartitionIterator(A::AbstractArray, n::Int) = PartitionIterator(vec(A), n)` forwards arrays through `vec(A)` (also covered in `iteratorscov-partition-methods`).
- `PartitionIterator@1447`: `PartitionIterator(v::AbstractVector, n::Int) = PartitionIterator{typeof(v)}(v, n)` constructs `PartitionIterator` (also covered in `iteratorscov-partition-methods`).
- `Stateful@1605`: `Stateful(x::Stateful) = x` is the identity on an existing `Stateful` (also covered in `iteratorscov-stateful-methods`).
- `convert@1606`: `convert(::Type{Stateful}, itr) = Stateful(itr)` forwards conversion to `Stateful(itr)` (also covered in `iteratorscov-stateful-methods`).
- `eltype@1626`: `eltype(::Type{<:Stateful{T}}) where {T} = eltype(T)` forwards `eltype(T)` (also covered in `iteratorscov-stateful-methods`).
- `IteratorEltype@1627`: `IteratorEltype(::Type{<:Stateful{T}}) where {T} = IteratorEltype(T)` forwards `IteratorEltype(T)` (also covered in `iteratorscov-stateful-methods`).
- `only@1659`: `only(x) = _only(x, iterate)` forwards to `_only` with `iterate` (also covered in `iteratorscov-only-nth-methods`).
- `only@1680`: `only(x::IdDict) = _only(x, first)` forwards to `_only` with `first` (also covered in `iteratorscov-only-nth-methods`).
- `IteratorSize@1704`: `IteratorSize(::Type{<:IterableStatePairs{T}}) where T = IteratorSize(T)` forwards `IteratorSize(T)` (also covered in `iteratorscov-iterable-state-pairs`).
- `length@1705`: `length(x::IterableStatePairs) = length(x.x)` forwards `length` to `x.x` (also covered in `iteratorscov-iterable-state-pairs`).
- `Base.eltype@1706`: `Base.eltype(::Type{IterableStatePairs{T}}) where T = Pair{<:Any, eltype(T)}` forms the pair element type (also covered in `iteratorscov-iterable-state-pairs`).
- `reverse@1714`: `reverse(x::IterableStatePairs) = IterableStatePairs(Iterators.reverse(x.x))` wraps `Iterators.reverse(x.x)` (also covered in `iteratorscov-iterable-state-pairs`).
- `reverse@1715`: `reverse(x::IterableStatePairs{<:Iterators.Reverse}) = IterableStatePairs(x.x.itr)` unwraps the inner `Reverse` (also covered in `iteratorscov-iterable-state-pairs`).
- `pairs@1725`: `pairs(s::AbstractString) = IterableStatePairs(s)` wraps `s` in `IterableStatePairs` (also covered in `iteratorscov-iterable-state-pairs`).
- `nth@1753`: `nth(itr, n::Integer) = _nth(IteratorSize(itr), itr, n)` dispatches on `IteratorSize(itr)` (also covered in `iteratorscov-only-nth-methods`).
- `nth@1754`: `nth(itr::Cycle{I}, n::Integer) where I = _nth(IteratorSize(I), itr, n)` dispatches on `IteratorSize(I)` (also covered in `iterators-nth-cycle-overflow`).
- `nth@1755`: `nth(itr::Flatten{Take{Repeated{O}}}, n::Integer) where O = _nth(IteratorSize(O), itr, n)` dispatches on `IteratorSize(O)` (also covered in `iterators-nth-cycle-overflow`).
- `nth@1810`: `nth(n::Integer) = Base.Fix2(nth, n)` constructs the curried `Fix2` adapter (also covered in `iteratorscov-only-nth-methods`).
- `eltype@425`: `eltype(::Type{Zip{Is}}) = TupleOrBottom(ntuple(n -> eltype(fieldtype(Is, n)), N)...)` forms the tuple of component element types (also covered in `iteratorscov-zip-metadata`).
- `IteratorSize@503`: `IteratorSize(::Type{Zip{Is}}) = zip_iteratorsize(...)` forwards to `zip_iteratorsize` over component traits (also covered in `iteratorscov-zip-traits`).
- `IteratorEltype@504`: `IteratorEltype(::Type{Zip{Is}}) = zip_iteratoreltype(...)` forwards to `zip_iteratoreltype` over component traits (also covered in `iteratorscov-zip-traits`).
- `eltype@1197`: `eltype(::Type{ProductIterator{I}}) = _prod_eltype(I)` forwards to `_prod_eltype` (also covered in `iteratorscov-product-methods`).
- `_prod_eltype@1198`: `_prod_eltype(::Type{Tuple{}}) = Tuple{}` is the empty product element type (also covered in `iteratorscov-product-methods`).
- `_prod_eltype@1199`: `_prod_eltype(::Type{I}) = TupleOrBottom(ntuple(n -> eltype(fieldtype(I, n)), N)...)` forms the tuple of factor element types (also covered in `iteratorscov-product-methods`).
- `eltype@1298`: `eltype(::Type{Flatten{I}}) = Any` falls back to `Any` when the outer eltype is unknown (also covered in `iteratorscov-flatten-methods`).
- `eltype@1301`: `eltype(::Type{Flatten{Tuple{}}}) = eltype(Tuple{})` forwards the empty tuple element type (also covered in `iteratorscov-flatten-methods`).
- `IteratorEltype@1305`: `IteratorEltype(::Type{Flatten{I}}) = _flatteneltype(I, IteratorEltype(I))` forwards to `_flatteneltype` (also covered in `iteratorscov-flatten-methods`).
- `IteratorEltype@1306`: `IteratorEltype(::Type{Flatten{Tuple{}}}) = IteratorEltype(Tuple{})` forwards `IteratorEltype(Tuple{})` (also covered in `iteratorscov-flatten-methods`).
- `_flatteneltype@1307`: `_flatteneltype(I, ::HasEltype) = IteratorEltype(eltype(I))` returns the inner iterator's eltype trait (also covered in `iteratorscov-flatten-methods`).
- `_flatteneltype@1308`: `_flatteneltype(I, et) = EltypeUnknown()` reports `EltypeUnknown()` when the outer eltype is unknown (also covered in `iteratorscov-flatten-methods`).
- `eltype@1449`: `eltype(::Type{PartitionIterator{T}}) = Vector{eltype(T)}` forms `Vector{eltype(T)}` for generic partitions (also covered in `iteratorscov-partition-methods`).
- `eltype@1451`: `eltype(::Type{PartitionIterator{T}}) where {T<:AbstractArray} = AbstractVector{eltype(T)}` forms `AbstractVector{eltype(T)}` for array partitions (also covered in `iteratorscov-partition-methods`).
- `eltype@1453`: `eltype(::Type{PartitionIterator{T}}) where {T<:Vector} = Base.SubArray{...}` forms the 1D `SubArray` view type for vector partitions (also covered in `iteratorscov-partition-methods`).
- `IteratorEltype@1455`: `IteratorEltype(::Type{PartitionIterator{T}}) = IteratorEltype(T)` forwards `IteratorEltype(T)` (also covered in `iteratorscov-partition-methods`).
- `IteratorEltype@1456`: `IteratorEltype(::Type{PartitionIterator{T}}) where {T<:AbstractArray} = EltypeUnknown()` reports `EltypeUnknown()` for general `AbstractArray` partitions (also covered in `iteratorscov-partition-methods`).
- `IteratorEltype@1457`: `IteratorEltype(::Type{PartitionIterator{T}}) where {T<:Vector} = IteratorEltype(T)` forwards `IteratorEltype(T)` for `Vector` partitions (also covered in `iteratorscov-partition-methods`).
- `IteratorSize@1625`: `IteratorSize(::Type{<:Stateful{T}}) = IteratorSize(T) isa IsInfinite ? IsInfinite() : SizeUnknown()` preserves `IsInfinite()` and otherwise reports `SizeUnknown()` (also covered in `iteratorscov-stateful-methods`).
-/

def nothingToPromise : List (String × String) := [
  ("map@56", "forwards directly to Base.Generator"),
  ("reverse@113", "wraps an iterator in Reverse"),
  ("eltype@128", "forwards eltype to the wrapped iterator type"),
  ("length@129", "forwards length to r.itr"),
  ("size@130", "forwards size to r.itr"),
  ("IteratorSize@131", "forwards IteratorSize to the wrapped iterator type"),
  ("IteratorEltype@132", "forwards IteratorEltype to the wrapped iterator type"),
  ("last@133", "forwards last(Reverse(itr)) to first(itr)"),
  ("reverse@156", "forwards range reversal to Base.reverse"),
  ("reverse@157", "reconstructs Generator over reverse(G.iter)"),
  ("reverse@158", "unwraps r.itr from Reverse"),
  ("reverse@159", "returns scalar numbers and characters unchanged"),
  ("reverse@160", "forwards pair reversal to Base.reverse"),
  ("enumerate@207", "wraps an iterator in Enumerate"),
  ("length@209", "forwards length to e.itr"),
  ("size@210", "forwards size to e.itr"),
  ("eltype@219", "constructs TupleOrBottom(Int, eltype(I))"),
  ("IteratorSize@221", "forwards IteratorSize to the wrapped iterator type"),
  ("IteratorEltype@222", "forwards IteratorEltype to the wrapped iterator type"),
  ("pairs@281", "constructs Pairs with LinearIndices(A)"),
  ("pairs@285", "constructs Pairs with keys(tuple)"),
  ("pairs@286", "constructs Pairs over a NamedTuple"),
  ("pairs@287", "constructs Pairs with LinearIndices(v)"),
  ("pairs@288", "forwards AbstractVector pairs to IndexLinear"),
  ("pairs@291", "constructs Pairs with CartesianIndices(A)"),
  ("pairs@292", "forwards AbstractArray pairs to IndexCartesian"),
  ("length@294", "forwards length to keys(v)"),
  ("axes@295", "forwards axes to keys(v)"),
  ("size@296", "forwards size to keys(v)"),
  ("isdone@316", "forwards isdone to keys(v)"),
  ("IteratorSize@318", "forwards IteratorSize of the key iterator"),
  ("IteratorSize@319", "reports HasLength for unit-range keys"),
  ("haskey@326", "forwards membership to keys(v)"),
  ("values@328", "returns the underlying data field"),
  ("getindex@329", "forwards getindex to values(v)"),
  ("setindex!@330", "forwards setindex! to values(v) and returns v"),
  ("get@331", "forwards default get lookup to values(v)"),
  ("get@332", "forwards callable fallback get lookup to values(v)"),
  ("zip@379", "wraps the argument tuple in Zip"),
  ("_promote_tuple_shape@416", "forwards two-shape promotion to promote_shape"),
  ("_promote_tuple_shape@418", "returns a single shape tuple unchanged"),
  ("last@519", "forwards last(z::Zip) to nth(z, length(z))"),
  ("filter@576", "constructs Filter(flt, itr)"),
  ("eltype@594", "forwards eltype(I)"),
  ("IteratorEltype@595", "forwards IteratorEltype(I)"),
  ("IteratorSize@596", "reports SizeUnknown for Filter"),
  ("reverse@598", "constructs Filter(f.flt, reverse(f.itr))"),
  ("last@599", "forwards last(f::Filter) to first(reverse(f))"),
  ("accumulate@641", "constructs Accumulate(f, itr, init)"),
  ("length@661", "forwards length to itr.itr"),
  ("size@662", "forwards size to itr.itr"),
  ("IteratorSize@664", "forwards IteratorSize(I)"),
  ("IteratorEltype@665", "reports EltypeUnknown for Accumulate"),
  ("rest@696", "constructs Rest(itr, state)"),
  ("rest@697", "replaces the state of an existing Rest"),
  ("rest@698", "returns itr unchanged when no state is given"),
  ("eltype@735", "forwards eltype(I)"),
  ("IteratorEltype@736", "forwards IteratorEltype(I)"),
  ("eltype@770", "returns the type parameter T of Count{T}"),
  ("IteratorSize@774", "reports IsInfinite for Count"),
  ("eltype@818", "forwards eltype(I)"),
  ("IteratorEltype@819", "forwards IteratorEltype(I)"),
  ("eltype@875", "forwards eltype(I)"),
  ("IteratorEltype@876", "forwards IteratorEltype(I)"),
  ("iterate@891", "forwards subsequent Drop iteration steps to it.xs"),
  ("isdone@892", "forwards state-ful isdone on Drop to it.xs"),
  ("takewhile@928", "constructs TakeWhile(pred, xs)"),
  ("IteratorSize@937", "reports SizeUnknown for TakeWhile"),
  ("eltype@938", "forwards eltype(I)"),
  ("IteratorEltype@939", "forwards IteratorEltype(I)"),
  ("dropwhile@976", "constructs DropWhile(pred, itr)"),
  ("iterate@978", "forwards subsequent DropWhile iteration steps to ibl.xs"),
  ("IteratorSize@988", "reports SizeUnknown for DropWhile"),
  ("eltype@989", "forwards eltype(I)"),
  ("IteratorEltype@990", "forwards IteratorEltype(I)"),
  ("findeach@1018", "forwards findeach(it) to findeach(identity, it)"),
  ("cycle@1058", "constructs Cycle(xs)"),
  ("eltype@1061", "forwards eltype(I)"),
  ("IteratorEltype@1062", "forwards IteratorEltype(I)"),
  ("reverse@1074", "constructs Cycle(reverse(it.xs))"),
  ("last@1075", "forwards last(it::Cycle) to last(it.xs)"),
  ("repeated@1083", "constructs Repeated(x)"),
  ("eltype@1113", "returns the type parameter O of Repeated{O}"),
  ("reverse@1120", "returns Repeated or Take{<:Repeated} unchanged"),
  ("last@1121", "forwards last on Repeated to first"),
  ("product@1148", "constructs ProductIterator(iters)"),
  ("reverse@1255", "maps reverse across P.iterators"),
  ("flatten@1291", "constructs Flatten(itr)"),
  ("eltype@1293", "forwards eltype(eltype(I))"),
  ("last@1380", "forwards last(f::Flatten) to first(reverse(f))"),
  ("flatmap@1421", "forwards flatmap(f, c...) to flatten(map(f, c...))"),
  ("PartitionIterator@1446", "forwards AbstractArray to PartitionIterator(vec(A), n)"),
  ("PartitionIterator@1447", "constructs PartitionIterator{typeof(v)}(v, n)"),
  ("StatefulSnapshot@1605", "returns an existing StatefulSnapshot unchanged"),
  ("convert@1606", "forwards conversion to StatefulSnapshot(itr)"),
  ("eltype@1626", "forwards eltype(T)"),
  ("IteratorEltype@1627", "forwards IteratorEltype(T)"),
  ("only@1659", "forwards only(x) to _only(x, iterate)"),
  ("only@1680", "forwards only(x::IdDict) to _only(x, first)"),
  ("IteratorSize@1704", "forwards IteratorSize(T)"),
  ("length@1705", "forwards length to x.x"),
  ("Base.eltype@1706", "constructs Pair{<:Any, eltype(T)}"),
  ("reverse@1714", "wraps Iterators.reverse(x.x) in IterableStatePairs"),
  ("reverse@1715", "unwraps x.x.itr into IterableStatePairs"),
  ("pairs@1725", "wraps AbstractString in IterableStatePairs"),
  ("nth@1753", "dispatches nth(itr, n) on IteratorSize(itr)"),
  ("nth@1754", "dispatches nth(itr::Cycle, n) on IteratorSize(I)"),
  ("nth@1755", "dispatches nth(itr::Flatten{Take{Repeated}}, n) on IteratorSize(O)"),
  ("nth@1810", "constructs Base.Fix2(nth, n)"),
  ("eltype@425", "constructs TupleOrBottom of component eltypes"),
  ("IteratorSize@503", "forwards Zip IteratorSize to zip_iteratorsize"),
  ("IteratorEltype@504", "forwards Zip IteratorEltype to zip_iteratoreltype"),
  ("eltype@1197", "forwards ProductIterator eltype to _prod_eltype"),
  ("_prod_eltype@1198", "returns Tuple{} for empty ProductIterator"),
  ("_prod_eltype@1199", "constructs TupleOrBottom of factor eltypes"),
  ("eltype@1298", "returns Any when outer eltype is unknown"),
  ("eltype@1301", "forwards eltype(Tuple{}) for empty Flatten"),
  ("IteratorEltype@1305", "forwards Flatten IteratorEltype to _flatteneltype"),
  ("IteratorEltype@1306", "forwards IteratorEltype(Tuple{}) for empty Flatten"),
  ("_flatteneltype@1307", "returns IteratorEltype(eltype(I)) when HasEltype"),
  ("_flatteneltype@1308", "returns EltypeUnknown when outer eltype is unknown"),
  ("eltype@1449", "returns Vector{eltype(T)} for generic PartitionIterator"),
  ("eltype@1451", "returns AbstractVector{eltype(T)} for AbstractArray PartitionIterator"),
  ("eltype@1453", "returns SubArray view type for Vector PartitionIterator"),
  ("IteratorEltype@1455", "forwards IteratorEltype(T) for PartitionIterator"),
  ("IteratorEltype@1456", "returns EltypeUnknown for AbstractArray PartitionIterator"),
  ("IteratorEltype@1457", "forwards IteratorEltype(T) for Vector PartitionIterator"),
  ("IteratorSize@1625", "preserves IsInfinite and otherwise returns SizeUnknown for StatefulSnapshot")
]

@[simp] theorem ok_bind {α β : Type} (x : α) (f : α → Jl β) :
    (Except.ok x >>= f) = f x := rfl

@[simp] theorem err_bind {α β : Type} (e : JlError) (f : α → Jl β) :
    (Except.error e >>= f) = .error e := rfl

@[simp] theorem pure_jl {α : Type} (x : α) : (pure x : Jl α) = .ok x := rfl

theorem ok_bind_iter {α β : Type} (x : α) (f : α → IteratorResult β) :
    (Except.ok x >>= f) = f x := rfl

@[simp] theorem pure_iter {α : Type} (x : α) :
    (pure x : IteratorResult α) = .ok x := rfl

@[simp] theorem liftM_jl_ok {α : Type} (x : α) :
    (liftM (Except.ok x : Jl α) : IteratorResult α) = .ok x := rfl

@[simp] theorem monadLift_jl_ok {α : Type} (x : α) :
    (MonadLift.monadLift (Except.ok x : Jl α) : IteratorResult α) = .ok x := rfl

@[simp] theorem listIterator_length {α : Type} (xs : List α) :
    (listIterator xs).length = .ok xs.length := rfl

/-- A finite iterator emits exactly the listed values and then stops. -/
def emitsExactly [Monad m] [CollectRun I α S m] (itr : I) (xs : List α) : Prop :=
  collectPrefix itr (xs.length + 1) none = pure xs

def collectAfterStep {α S : Type} (itr : IteratorModel α S) (f : Nat)
    (step : Jl (Option (α × S))) : Jl (List α) := do
  match ← step with
  | none => pure []
  | some (x, next) => pure (x :: (← collectPrefix itr f (some next)))

theorem collectPrefix_succ {α S : Type} (itr : IteratorModel α S) (f : Nat) (state : Option S) :
    collectPrefix itr (f + 1) state = collectAfterStep itr f (itr.run state) := rfl

@[simp] theorem collectAfterStep_none {α S : Type} (itr : IteratorModel α S) (f : Nat) :
    collectAfterStep itr f (.ok none) = .ok [] := rfl

@[simp] theorem collectAfterStep_some {α S : Type} (itr : IteratorModel α S) (f : Nat)
    (x : α) (next : S) :
    collectAfterStep itr f (.ok (some (x, next))) =
      (do pure (x :: (← collectPrefix itr f (some next)))) := rfl

def protocolIterator {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (isdone : I → Option S → Jl (Option Bool)) (itr : I) : IteratorModel α S where
  run := fun state => iterate itr state
  isdone := fun state => isdone itr state
  iteratorSize := .sizeUnknown
  iteratorEltype := .eltypeUnknown
  length := .error (.argumentError "iterator is of undefined length")
  size := .error (.argumentError "iterator is of undefined size")

def followsFrom [Monad m] [CollectRun I α S m] (itr : I) (state : Option S) (xs : List α) : Prop :=
  collectPrefix itr (xs.length + 1) state = pure xs

def followsProtocol {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (isdone : I → Option S → Jl (Option Bool)) (itr : I) (xs : List α) : Prop :=
  followsFrom (protocolIterator iterate isdone itr) none xs

theorem followsFrom_nil {α S : Type} (itr : IteratorModel α S) (state : Option S)
    (h : followsFrom itr state []) : itr.run state = .ok none := by
  change collectPrefix itr 1 state = .ok [] at h
  rw [collectPrefix_succ] at h
  cases hr : itr.run state with
  | error e => simp [collectAfterStep, hr] at h
  | ok result =>
    cases result with
    | none => rfl
    | some pair =>
      cases ht : collectPrefix itr 0 (some pair.2) with
      | error e => simp [collectAfterStep, hr, ht] at h
      | ok rest => simp [collectAfterStep, hr, ht] at h

theorem followsFrom_cons {α S : Type} (itr : IteratorModel α S) (state : Option S)
    (x : α) (xs : List α) (h : followsFrom itr state (x :: xs)) :
    ∃ next, itr.run state = .ok (some (x, next)) ∧ followsFrom itr (some next) xs := by
  change collectPrefix itr ((xs.length + 1) + 1) state = .ok (x :: xs) at h
  rw [collectPrefix_succ] at h
  cases hr : itr.run state with
  | error e => simp [collectAfterStep, hr] at h
  | ok result =>
    cases result with
    | none => simp [collectAfterStep, hr] at h
    | some pair =>
      rcases pair with ⟨value, next⟩
      cases ht : collectPrefix itr (xs.length + 1) (some next) with
      | error e => simp [collectAfterStep, hr, ht] at h
      | ok rest =>
        have hcons : value :: rest = x :: xs := by
          simpa [collectAfterStep, hr, ht] using h
        rcases List.cons.inj hcons with ⟨hvalue, hrest⟩
        subst value
        refine ⟨next, rfl, ?_⟩
        change collectPrefix itr (xs.length + 1) (some next) = .ok xs
        rw [ht, hrest]

theorem followsFrom_cons_intro {α S : Type} (itr : IteratorModel α S) (state : Option S)
    (x : α) (xs : List α) (next : S)
    (hstep : itr.run state = .ok (some (x, next)))
    (htail : followsFrom itr (some next) xs) :
    followsFrom itr state (x :: xs) := by
  change collectPrefix itr (xs.length + 1) (some next) = .ok xs at htail
  change collectPrefix itr ((xs.length + 1) + 1) state = .ok (x :: xs)
  rw [collectPrefix_succ, hstep, collectAfterStep_some, htail]
  rfl
def takeProtocolState {S : Type} (n : Nat) : Option S → Option (Nat × S)
  | none => none
  | some state => some (n, state)

theorem dropAdvance_from_trace {α S : Type} (itr : IteratorModel α S) :
    ∀ (n : Nat) (state : Option S) (xs : List α),
      followsFrom itr state xs →
      ∃ nextState : Option S,
        dropAdvance itr.run n state = itr.run nextState ∧
        followsFrom itr nextState (xs.drop n) := by
  intro n
  induction n with
  | zero =>
      intro state xs h
      exact ⟨state, rfl, h⟩
  | succ n ih =>
      intro state xs h
      cases xs with
      | nil =>
          have hstop := followsFrom_nil itr state h
          refine ⟨state, ?_, ?_⟩
          · simp [dropAdvance, hstop]
          · simpa using h
      | cons x rest =>
          obtain ⟨next, hstep, htail⟩ := followsFrom_cons itr state x rest h
          obtain ⟨nextState, hadvance, hrest⟩ := ih (some next) rest htail
          refine ⟨nextState, ?_, ?_⟩
          · simp [dropAdvance, hstep, hadvance]
          · simpa using hrest

def enumerateFrom {α : Type} : JInt64 → List α → List (JInt64 × α)
  | _, [] => []
  | k, x :: xs => (k, x) :: enumerateFrom (k + JInt.lit .i64 1) xs

def enumerateSpec {α : Type} (xs : List α) : List (JInt64 × α) :=
  enumerateFrom (JInt.lit .i64 1) xs

def enumerateNatFrom {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | k, x :: xs => (k, x) :: enumerateNatFrom (k + 1) xs

def chunksSpec {α : Type} (n : Nat) (xs : List α) : List (List α) :=
  if n = 0 then [] else
    (List.range ((xs.length + n - 1) / n)).map fun i => (xs.drop (i * n)).take n

def productInt (xs : List JInt64) : Int := xs.foldl (fun acc x => acc * x.val) 1

def countChainGen {T S : Type} (add : T → S → T) : T → S → Nat → List T
  | _, _, 0 => []
  | start, step, n + 1 => start :: countChainGen add (add start step) step n

def countChain (start step : JInt64) : Nat → List JInt64 :=
  countChainGen (· + ·) start step

def scanAccum {α β : Type} (f : β → α → β) : β → List α → List β
  | _, [] => []
  | acc, x :: xs => let next := f acc x; next :: scanAccum f next xs

def accumulateSpecGen {α β T : Type} (f : β → α → β) (bottomRF : T → α → β) (init : T) : List α → List β
  | [] => []
  | x :: xs =>
      let first := bottomRF init x
      first :: scanAccum f first xs

def accumulateSpec {α : Type} (f : α → α → α) (init : Option α) : List α → List α :=
  accumulateSpecGen f (fun state x => match state with | none => x | some acc => f acc x) init

/-! ## Core list-iterator lemmas -/

theorem listGet_eq_drop_head? {α : Type} (xs : List α) (i : Nat) :
    listGet xs i = (xs.drop i).head? := by
  induction xs generalizing i with
  | nil => simp [listGet]
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simpa [listGet, List.drop] using ih i

theorem listIterator_run_some {α : Type} (xs : List α) (i : Nat) :
    (listIterator xs).run (some i) =
      match xs.drop i with
      | [] => .ok none
      | x :: _ => .ok (some (x, i + 1)) := by
  simp only [listIterator, Option.getD_some, listGet_eq_drop_head?]
  cases xs.drop i <;> rfl

theorem listIterator_run_none {α : Type} (xs : List α) :
    (listIterator xs).run none = (listIterator xs).run (some 0) := rfl

@[simp] theorem listIterator_isdone_some {α : Type} (xs : List α) (i : Nat) :
    (listIterator xs).isdone (some i) = .ok (some (decide (xs.length ≤ i))) := rfl

theorem jint_convert_i64_val_of_lt (b : Nat) (hb : b < 2 ^ 63) :
    ∃ n64 : JInt64, JInt.convert (IntTy.i64.name) .i64 (b : Int) = .ok n64 ∧ n64.val = (b : Int) := by
  have hr : IntTy.i64.min ≤ (b : Int) ∧ (b : Int) ≤ IntTy.i64.max := by
    change -(2 ^ 63 : Int) ≤ (b : Int) ∧ (b : Int) ≤ 2 ^ 63 - 1
    omega
  exact ⟨⟨(b : Int), hr⟩, by simp [JInt.convert, hr], rfl⟩

@[simp] theorem jint_convert_i64_self (n : JInt64) :
    JInt.convert (IntTy.i64.name) .i64 n.val = .ok n := by
  simp [JInt.convert, n.property]

theorem jint_convert_i64_out (n : Int) (h : n < -(2 ^ 63) ∨ 2 ^ 63 ≤ n) :
    JInt.convert (IntTy.i64.name) .i64 n = .error (.inexactError "Int64") := by
  have hnot : ¬ (IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max) := by
    change ¬ (-(2 ^ 63 : Int) ≤ n ∧ n ≤ 2 ^ 63 - 1)
    omega
  simp [JInt.convert, hnot, IntTy.name]

def TakeIsemptyCorrect : Prop :=
  ∀ {α : Type} (xs : List α) (n : JInt64), 0 ≤ n.val →
    let base := listIterator xs
    let t : Take (IteratorModel α Nat) := ⟨base, n⟩
    let isdoneFn : Take (IteratorModel α Nat) → List (α × (JInt64 × Nat)) → Option Bool :=
      fun it _ => match takeDone (fun _ s => it.xs.isdone s) it with | .ok b => b | .error _ => none
    let iterateFn : Take (IteratorModel α Nat) → List (α × (JInt64 × Nat)) → Option ((α × (JInt64 × Nat)) × List (α × (JInt64 × Nat))) :=
      fun it _ => match takeStep (fun _ s => it.xs.run s) it none with | .ok (some step) => some (step, []) | _ => none
    (JuliaLean.base.essentials.isempty isdoneFn iterateFn t = true ↔
      takeStep (fun _ s => base.run s) t none = .ok none)

def PeelRestIsempty : Prop :=
  ∀ {α : Type} (xs : List α) (x : α) (rest : Rest (IteratorModel α Nat) Nat),
    peelStep (fun itr state => itr.run state) (listIterator xs) =
      .ok (some (x, rest)) →
    let isdoneFn : Rest (IteratorModel α Nat) Nat → List (α × Nat) → Option Bool :=
      fun r _ => match restDone (fun itr state => itr.isdone state) r none with | .ok b => b | .error _ => none
    let iterateFn : Rest (IteratorModel α Nat) Nat → List (α × Nat) → Option ((α × Nat) × List (α × Nat)) :=
      fun r _ => match restStep (fun itr state => itr.run state) r none with | .ok (some step) => some (step, []) | _ => none
    (JuliaLean.base.essentials.isempty isdoneFn iterateFn rest = true ↔
      restStep (fun itr state => itr.run state) rest none = .ok none)

theorem peelRestIsempty_refuted : ¬ PeelRestIsempty := by
  intro h
  exact nomatch (h [1] 1 ⟨listIterator [1], 1⟩ rfl).mpr rfl


def NthCycleCorrect : Prop :=
  ∀ {α : Type} (xs : List α) (m k : Nat) (x : α),
    0 < xs.length → 1 ≤ k → k ≤ xs.length * m →
      listGet xs ((k - 1) % xs.length) = some x →
      ∃ cyc, CountValue.cycle (listIterator xs) (Int.ofNat m) = .ok cyc ∧
        nthFiniteCycleValue (fun it => (it.length.map fun n => JInt.lit .i64 (Int.ofNat n)))
          (fun it n => nthIterator it n) cyc (Int.ofNat k) = .ok x

theorem nthCycleCorrect_refuted : ¬ NthCycleCorrect := by
  intro h
  obtain ⟨cyc, hcyc, hnth⟩ := h [1, 2, 3] (2 ^ 62) 1 1 (by decide) (by decide) (by decide) rfl
  cases hcyc
  exact nomatch hnth

def NthAnyIntegerType : Prop :=
  ∀ (r : UnitRangeIndices JInt64) (n : IntegerArg),
    nthArrayIntegerArg
      (fun range => pure (.bit .i64 range.start))
      (fun range index => unitRangeIndexIntegerArg range.start.val range.stop.val index)
      r n =
      let index := r.start.val + n.toInt - 1
      if 1 ≤ n.toInt ∧ r.start.val ≤ index ∧ index ≤ r.stop.val then .ok index
      else .error .boundsError

theorem nthAnyIntegerType_refuted : ¬ NthAnyIntegerType := by
  intro h
  exact nomatch h
    { start := JInt.lit .i64 (-5), stop := JInt.lit .i64 (-3) }
    (.bit .u64 (JInt.lit .u64 1))

def ProductLengthExact : Prop :=
  ∀ (mul : JInt64 → JInt64 → Jl JInt64)
    (reduce : (JInt64 → JInt64 → Jl JInt64) → List JInt64 → JInt64 → Jl JInt64),
    (∀ a b, mul a b = checkedMulI64 a b) →
    (∀ values init, reduce mul values init = checkedProductFold mul init values) →
    ∀ (sizes : List JInt64), (∀ x ∈ sizes, 0 ≤ x.val) →
      -(2 ^ 63) ≤ productInt sizes → productInt sizes ≤ 2 ^ 63 - 1 →
        productLength (fun s : JInt64 => pure [s]) (fun s : JInt64 => pure s)
          (fun _ => .hasLength) (productModel sizes) mul =
            .ok (JInt.lit .i64 (productInt sizes))

theorem productLengthExact_refuted : ¬ ProductLengthExact := by
  intro h
  exact nomatch h checkedMulI64 (fun m vs init => checkedProductFold m init vs)
    (fun _ _ => rfl) (fun _ _ => rfl)
    [JInt.lit .i64 (2 ^ 32), JInt.lit .i64 (2 ^ 32), JInt.lit .i64 0]
    (by decide) (by decide) (by decide)

def ProductLastNonempty : Prop :=
  ∀ (ranges : List (JInt64 × JInt64)) (vals : List JInt64),
    productLastObservation (fun r : JInt64 × JInt64 => pure r.2) (productModel ranges) = .ok vals →
      ∀ r ∈ ranges, r.1.val ≤ r.2.val

theorem productLastNonempty_refuted : ¬ ProductLastNonempty := by
  intro h
  have h0 := h [(JInt.lit .i64 1, JInt.lit .i64 2), (JInt.lit .i64 1, JInt.lit .i64 0)]
    [JInt.lit .i64 2, JInt.lit .i64 0] rfl
    (JInt.lit .i64 1, JInt.lit .i64 0) (by decide)
  revert h0
  decide

def CycleFirstN : Prop :=
  ∀ (xs : List Int) (n : Nat), n < 2 ^ 63 →
    let cyc := cycleObservation (cycleModel (listIterator xs))
    ∃ t ys, CountValue.take cyc (Int.ofNat n) = .ok t ∧
      collectPrefix (takeObservation cyc t) (n + 1) none = .ok ys ∧
      (takeLength (fun _ => cycleIteratorSize) (fun _ _ => pure t.n.val.toNat)
        (fun _ => cyc.length) (fun r => pure r) (fun a b => pure (min a b)) t).map
          (Sum.elim id id) = .ok ys.length

theorem cycleFirstN_refuted : ¬ CycleFirstN := by
  intro h
  obtain ⟨t, ys, ht, hys, hlen⟩ := h [] 3 (by decide)
  cases ht
  cases hys
  exact nomatch hlen

def partitionI64IndexOps : IntegerIndexOps JInt64 where
  greaterThan := fun a b => a.val > b.val
  add := (· + ·)
  subtract := (· - ·)
  fromInt := JInt.wrap .i64
  one := JInt.lit .i64 1
  minimum := fun a b => if b < a then b else a
def partitionIntIndexOps : IntegerIndexOps Int where
  greaterThan := fun a b => decide (a > b)
  add := (· + ·)
  subtract := (· - ·)
  fromInt := id
  one := 1
  minimum := min


def PartitionRangeChunks : Prop :=
  ∀ (fi li : JInt64) (n : Nat) (state : Option JInt64) (chunk : JInt64 × JInt64) (next : JInt64),
    fi.val ≤ li.val → 0 < n →
      partitionIndexed (m := Jl) (fun r : JInt64 × JInt64 => pure r.1) (fun r : JInt64 × JInt64 => pure r.2)
        (fun a b => pure (decide (a.val > b.val)))
        (fun a b => pure (a + b)) (fun a b => pure (a - b))
        (fun a b => pure (if b < a then b else a))
        (fun s r => pure (s, r))
        (fun _ (s, r) => pure (s, if s ≤ r then r else s - JInt.lit .i64 1))
        (fun a b => pure (a + b))
        ⟨(fi, li), JInt.lit .i64 (Int.ofNat n)⟩ state = .ok (some (chunk, next)) →
        chunk.1.val ≤ chunk.2.val ∧
        chunk.2.val - chunk.1.val + 1 ≤ Int.ofNat n ∧
        chunk.1.val = (state.getD fi).val ∧
        chunk.2.val = min ((state.getD fi).val + Int.ofNat n - 1) li.val ∧
        next.val = chunk.2.val + 1


def PartitionFirstChunk : Prop :=
  ∀ (xs : List Int) (n : Nat), xs ≠ [] → 0 < n →
    ∃ nextState,
      partitionListStep (fun itr st => itr.run st)
        ⟨listIterator xs, JInt.lit .i64 (Int.ofNat n)⟩ (.at none) =
          .ok (some (xs.take n, nextState))

theorem partitionFirstChunk_refuted : ¬ PartitionFirstChunk := by
  intro h
  obtain ⟨_, h0⟩ := h [1, 2, 3] (2 ^ 62) (by decide) (by decide)
  exact nomatch h0

def FirstNAnyInteger : Prop :=
  ∀ (t : IntTy) (xs : List Int) (n : JInt t), 0 ≤ n.val →
    let base := listIterator xs
    ∃ take drop, CountValue.take base n.val = .ok take ∧
      CountValue.drop base n.val = .ok drop ∧
      emitsExactly (takeObservation base take) (xs.take n.val.toNat) ∧
      emitsExactly (dropObservation base drop) (xs.drop n.val.toNat)

theorem firstNAnyInteger_refuted : ¬ FirstNAnyInteger := by
  intro h
  obtain ⟨_, _, htake, _⟩ := h .u64 [1, 2, 3] (JInt.typemax .u64) (by decide)
  exact nomatch htake

def ProductOneFactor : Prop :=
  ∀ (xs : List Int) (isdoneAfter : Option Nat → Jl (Option Bool)),
    (∀ st, isdoneAfter st = .ok (some (xs.length ≤ st.getD xs.length))) →
    let base := { listIterator xs with isdone := fun st =>
      match st with | none => pure (some xs.isEmpty) | some s => isdoneAfter (some s) }
    emitsExactly (productObservation (productModel [base])
      (fun _ state => isdoneAfter state) (fun itr state => itr.run state)
      (fun _ => Int) (fun _ value _ => pure value))
      (xs.map fun x => [x])

theorem productOneFactor_refuted : ¬ ProductOneFactor := by
  intro h
  exact nomatch h [1] (fun st => .ok (some (1 ≤ st.getD 1))) (fun _ => rfl)


def CountfromEltype : Prop :=
  let oneunit : Bool ⊕ JInt64 → Jl (Bool ⊕ JInt64)
    | .inl _ => pure (.inl true)
    | .inr _ => pure (.inr (JInt.lit .i64 1))
  let add : Bool ⊕ JInt64 → Bool ⊕ JInt64 → Bool ⊕ JInt64
    | .inl a, .inl b => .inr (JInt.lit .i64 (if a then 1 else 0) + JInt.lit .i64 (if b then 1 else 0))
    | .inl a, .inr y => .inr (JInt.lit .i64 (if a then 1 else 0) + y)
    | .inr x, .inl b => .inr (x + JInt.lit .i64 (if b then 1 else 0))
    | .inr x, .inr y => .inr (x + y)
  ∀ (start : Bool ⊕ JInt64) (k : Nat) (xs : List (Bool ⊕ JInt64)),
    (do
      let c ← countOne oneunit start
      collectPrefix (countAsIterator add c) k none) = .ok xs →
      ∀ x ∈ xs, x.isLeft = start.isLeft
theorem countfromEltype_refuted : ¬ CountfromEltype := by
  intro h
  exact nomatch h (.inl true) 2 [.inl true, .inr (JInt.lit .i64 2)] rfl (.inr (JInt.lit .i64 2))
    (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))

def ProductIntersect : Prop :=
  ∀ (intersect : List Int → List Int → Jl (List Int))
      (broadcast : (List Int → List Int → Jl (List Int)) →
        List (List Int) → List (List Int) → Jl (List (List Int)))
      (left right : List (List Int)), left.length ≠ right.length →
    (∀ common ∈ List.zipWith (fun xs ys => xs.filter (fun x => ys.contains x)) left right,
      common ≠ []) →
      match intersectProductM intersect broadcast (productModel left) (productModel right) with
      | .error _ => False
      | .ok p => p.iterators.any List.isEmpty

theorem dropAdvance_listIterator {α : Type} (xs : List α) (n : Nat) :
    ∀ (st : Option Nat),
      dropAdvance (listIterator xs).run n st =
        (listIterator xs).run (some (st.getD 0 + n)) := by
  induction n with
  | zero =>
    intro st
    cases st <;> simp [dropAdvance] <;> rfl
  | succ n ih =>
    intro st
    have hst : (listIterator xs).run st = (listIterator xs).run (some (st.getD 0)) := by
      cases st <;> rfl
    simp only [dropAdvance, hst, listIterator_run_some]
    cases hd : xs.drop (st.getD 0) with
    | nil =>
      have hnil : xs.drop (st.getD 0 + (n + 1)) = [] := by
        have := List.drop_eq_nil_iff.mp hd
        exact List.drop_eq_nil_iff.mpr (by omega)
      simp [hnil]
    | cons x rest =>
      simp only [ok_bind]
      rw [ih (some (st.getD 0 + 1))]
      simp only [Option.getD_some]
      have heq : st.getD 0 + 1 + n = st.getD 0 + (n + 1) := by omega
      rw [heq, listIterator_run_some]

def TakeCorrect : Prop :=
  (∀ {α : Type} (xs : List α) (n : JInt64), 0 ≤ n.val →
    let base := listIterator xs
    let take := takeObservation base ⟨base, n⟩
    emitsExactly take (xs.take n.val.toNat) ∧ take.length = .ok (min n.val.toNat xs.length)) ∧
  (∀ {I α S : Type} (iterate : I → Option S → Jl (Option (α × S))) (it : Take I) (s : S),
    takeStep iterate it (some (JInt.lit .i64 0, s)) = .ok none ∧
    (it.n.val = 0 → takeStep iterate it none = .ok none)) ∧
  (∀ {I : Type} (iteratorSize : I → IteratorSizeTag) (length : I → Jl Nat) (t : Take I) (m : Nat),
    length t.xs = .ok m →
    (takeLength (m := Jl) iteratorSize (fun _ _ => pure t.n.val.toNat) length (fun r => pure r)
      (fun a b => pure (min a b)) t).map (Sum.elim id id) =
      .ok (if iteratorSize t.xs == .isInfinite then t.n.val.toNat else min m t.n.val.toNat))

def TakeTakeCorrect : Prop :=
  (∀ {α : Type} (xs : List α) (a b : JInt64), 0 ≤ a.val → 0 ≤ b.val →
    let base := listIterator xs
    ∃ t, CountValue.takeTake ⟨base, a⟩ b.val = .ok t ∧
      emitsExactly (takeObservation base t) (xs.take (min a.val.toNat b.val.toNat))) ∧
  (∀ {I : Type} (xs : I) (a b : JInt64), 0 ≤ a.val → 0 ≤ b.val →
    CountValue.takeTake ⟨xs, a⟩ b.val = .ok ⟨xs, JInt.lit .i64 (min a.val b.val)⟩) ∧
  (∀ {I : Type} (xs : I) (a b : JInt64), 0 ≤ a.val → b.val < 0 →
    CountValue.takeTake ⟨xs, a⟩ b.val = .error (.argumentError "Take length must be non-negative")) ∧
  (∀ {I : Type} (xs : I) (a : JInt64) (b : Int), (b < -(2 ^ 63) ∨ 2 ^ 63 ≤ b) →
    CountValue.takeTake ⟨xs, a⟩ b = .error (.inexactError "Int64"))

def DropCorrect : Prop :=
  (∀ {α : Type} (xs : List α) (n : JInt64), 0 ≤ n.val →
    let base := listIterator xs
    let drop := dropObservation base ⟨base, n⟩
    emitsExactly drop (xs.drop n.val.toNat) ∧ drop.length = .ok (xs.length - n.val.toNat)) ∧
  (∀ {I α S : Type} (iterate : I → Option S → Jl (Option (α × S))) (it : Drop I) (s : S),
    dropStep iterate it (some s) = observeJl (iterate it.xs (some s)) ∧
    iterateDropState iterate it s = iterate it.xs (some s)) ∧
  (∀ {I : Type} (iteratorSize : I → IteratorSizeTag) (length : I → Jl Nat) (d : Drop I) (m : Nat),
    length d.xs = .ok m →
    (dropLength (m := Jl) iteratorSize (fun _ _ => pure d.n.val.toNat) length (fun r => pure r)
      (fun a b => pure (decide (a > b))) (fun a b => pure (a - b))
      (fun a b => pure (a - b)) (fun _ => pure 0) d).map (Sum.elim id (Sum.elim id id)) =
      .ok (if iteratorSize d.xs == .isInfinite then m else m - d.n.val.toNat))

theorem drop_takeWhile_length {α : Type} (ys : List α) (p : α → Bool) :
    ys.drop (ys.takeWhile p).length = ys.dropWhile p := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    by_cases hp : p y
    · simp [hp, ih]
    · simp [hp]

def TakeWhileDropWhile : Prop :=
  (∀ {α : Type} (p : α → Bool) (xs : List α),
    emitsExactly (takeWhileObservation (listIterator xs) p) (xs.takeWhile p) ∧
      emitsExactly (dropWhileObservation (listIterator xs) p) (xs.dropWhile p) ∧
      xs.takeWhile p ++ xs.dropWhile p = xs) ∧
  (∀ {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (isdone : I → Option S → Jl (Option Bool)) (it : I) (xs : List α) (p : α → Bool),
    followsProtocol iterate isdone it xs →
    emitsExactly (takeWhileObservation (protocolIterator iterate isdone it) p)
      (xs.takeWhile p) ∧
    emitsExactly (dropWhileObservation (protocolIterator iterate isdone it) p)
      (xs.dropWhile p)) ∧
  (∀ {I P α S : Type} (apply : P → α → Bool) (iterate : I → Option S → Jl (Option (α × S)))
    (pred : P) (xs : I) (state : Option S) (s : S),
    takewhileModel pred xs = ⟨pred, xs⟩ ∧
    dropwhileModel pred xs = ⟨pred, xs⟩ ∧
    iterateDropWhileState iterate (dropwhileModel pred xs) s = iterate xs (some s) ∧
    takeWhileStep apply iterate (takewhileModel pred xs) state =
      (do
        match ← iterate xs state with
        | none => pure none
        | some y => if apply pred y.1 then pure (some y) else pure none))

theorem enumerateFrom_length {α : Type} (k : JInt64) (xs : List α) :
    (enumerateFrom k xs).length = xs.length := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => simp [enumerateFrom, ih]

theorem enumerateSpec_length {α : Type} (xs : List α) :
    (enumerateSpec xs).length = xs.length :=
  enumerateFrom_length (JInt.lit .i64 1) xs

theorem enumerateAsIterator_run_some {α : Type} (xs : List α) (k : JInt64) (i : Nat) :
    (enumerateAsIterator (listIterator xs)).run (some (k, i)) =
      match xs.drop i with
      | [] => .ok none
      | x :: _ => .ok (some ((k, x), (k + JInt.lit .i64 1, i + 1))) := by
  simp only [enumerateAsIterator, iterateEnumerate, listIterator_run_some]
  cases xs.drop i <;> rfl

def EnumerateCorrect : Prop :=
  (∀ {α : Type} (xs : List α),
    let itr := enumerateAsIterator (listIterator xs)
    emitsExactly itr (enumerateSpec xs) ∧
    enumerateLength (fun i => i.length) (enumerateModel (listIterator xs)) = .ok xs.length) ∧
  (∀ {I α S : Type} (iterate : I → Option S → Jl (Option (α × S))) (itr : I) (i : JInt64) (s : S),
    enumerateModel itr = ⟨itr⟩ ∧
    iterateEnumerate iterate (enumerateModel itr) none =
      (do
        match ← iterate itr none with
        | none => pure none
        | some (x, next) => pure (some ((JInt.lit .i64 1, x), (JInt.lit .i64 2, next)))) ∧
    iterateEnumerate iterate (enumerateModel itr) (some (i, s)) =
      (do
        match ← iterate itr (some s) with
        | none => pure none
        | some (x, next) => pure (some ((i, x), (i + JInt.lit .i64 1, next))))) ∧
  (∀ {I R α S : Type} (r : Reverse (Enumerate I)) (reverse : I → Jl R) (length : R → Jl JInt64)
    (k : JInt64) (ri : R) (st : Option S) (iterRi : R → Option S → Jl (Option (α × S))),
    sourceMethod224 reverse length iterRi (fun a b => pure (a - b)) r =
      (do
        let ri ← reverse r.itr.itr
        let len ← length ri
        sourceMethod228 iterRi (fun a b => pure (a - b)) r (len, ri, none)) ∧
    sourceMethod228 iterRi (fun a b => pure (a - b)) r (k, ri, st) =
      (do
        match ← iterRi ri st with
        | none => pure none
        | some (value, next) => pure (some ((k, value), (k - JInt.lit .i64 1, ri, next)))))

theorem zipWith_map_inl_inr {α β : Type} (xs : List α) (ys : List β) :
    List.zipWith (fun a b => [a, b]) (xs.map Sum.inl) (ys.map Sum.inr) =
      List.zipWith (fun x y => [Sum.inl x, Sum.inr y]) xs ys := by
  induction xs generalizing ys with
  | nil => simp [List.zipWith]
  | cons x xs ih =>
    cases ys with
    | nil => simp [List.zipWith]
    | cons y ys => simp [List.zipWith, ih]

def ZipCorrect : Prop :=
  (∀ {α : Type} (xs ys : List α),
    let itr := zipListObservation xs ys
    emitsExactly itr (List.zipWith (fun x y => [x, y]) xs ys) ∧
      itr.length = .ok (min xs.length ys.length)) ∧
  (∀ {α β : Type} (xs : List α) (ys : List β),
    let itr := zipListObservation (xs.map Sum.inl) (ys.map Sum.inr)
    emitsExactly itr (List.zipWith (fun x y => [Sum.inl x, Sum.inr y]) xs ys) ∧
      itr.length = .ok (min xs.length ys.length)) ∧
  (∀ {α S : Type} (i1 i2 : IteratorModel α S) (m n : Nat),
    (i1.iteratorSize == .isInfinite) = false →
    (i2.iteratorSize == .isInfinite) = false →
    i1.length = .ok m → i2.length = .ok n →
    homogeneousZipLength (zipModel [i1, i2]) = .ok (min m n))

def ZipReverse : Prop :=
  (∀ {α : Type} (xs ys : List α),
    xs.length = ys.length →
      reverseZipModel (fun i => (listIterator i).iteratorSize) (fun i => (listIterator i).length)
        (fun i => pure i.reverse)
        (zipModel [xs, ys]) =
          .ok (zipModel [xs.reverse, ys.reverse]) ∧
      emitsExactly (zipListObservation xs.reverse ys.reverse)
        (List.zipWith (fun x y => [x, y]) xs ys).reverse) ∧
  (∀ {α : Type} (xs ys : List α),
    xs.length ≠ ys.length →
      ∃ msg, reverseZipModel (fun i => (listIterator i).iteratorSize) (fun i => (listIterator i).length)
        (fun i => pure i.reverse)
        (zipModel [xs, ys]) =
          .error (.argumentError msg)) ∧
  (∀ {α β : Type} (xs : List α) (ys : List β),
    xs.length = ys.length →
      emitsExactly (zipListObservation (xs.reverse.map Sum.inl) (ys.reverse.map Sum.inr))
        (List.zipWith (fun x y => [Sum.inl x, Sum.inr y]) xs ys).reverse) ∧
  (∀ {I R : Type} (iteratorSize : I → IteratorSizeTag) (length : I → Jl Nat)
    (reverseEach : I → Jl R) (z : Zip (List I)) (same : Bool) (len : Option Nat),
    zipLengthsFiniteEqualOn iteratorSize length z.is = .ok (same, len) →
    reverseZipModel iteratorSize length reverseEach z =
      if !same then .error (.argumentError "Cannot reverse zipped iterators of unknown, infinite, or unequal lengths")
      else (do
        let revIs ← z.is.mapM reverseEach
        pure (zipModel revIs)))
def ProductCorrect : Prop :=
  (∀ {α : Type} (factors : List (List α)) (depth : Nat),
    factors ≠ [] →
    let p : ProductIterator (List (IteratorModel α Nat)) :=
      productModel (factors.map listIterator)
    let itr :=
      productObservation p
        (fun item state => item.isdone state)
        (fun item state => item.run state)
        (fun _ => α)
        (fun _ value _ => pure value)
    observeRun itr.run depth none =
      .ok ((r6CartesianRows factors).take depth)) ∧
  (∀ {α : Type}, iterateEmptyProduct (α := α) = ([], true)) ∧
  (∀ {α S : Type} (state : S),
    iterateEmptyProductState (α := α) state = none)

theorem listIterator_map_run_some {α β : Type} (f : α → β) (xs : List α) (i : Nat) :
    (listIterator (xs.map f)).run (some i) =
      match xs.drop i with
      | [] => .ok none
      | x :: _ => .ok (some (f x, i + 1)) := by
  rw [listIterator_run_some, ← List.map_drop]
  cases xs.drop i <;> rfl

def FlattenCorrect : Prop :=
  (∀ {α : Type} (rows : List (List α)),
    emitsExactly (flattenListObservation rows) rows.flatten) ∧
  (∀ {α O S : Type} (outer : IteratorModel (IteratorModel α S) O),
    outer.run none = .ok none →
    flattenStartStep outer = .ok none) ∧
  (∀ {α O S : Type} (outer : IteratorModel (IteratorModel α S) O)
    (inner : IteratorModel α S) (nextOuter : O) (value : α) (nextInner : S),
    outer.run none = .ok (some (inner, nextOuter)) →
    inner.run none = .ok (some (value, nextInner)) →
    flattenStartStep outer = .ok (some (value, (nextOuter, inner, nextInner))) ∧
    (flattenObservation (flattenModel outer)).run none =
      .ok (some (value, (nextOuter, inner, nextInner)))) ∧
  (∀ {α O S : Type} (outer : IteratorModel (IteratorModel α S) O)
    (outerState : O) (inner : IteratorModel α S) (innerState : S)
    (value : α) (nextInner : S),
    inner.run (some innerState) = .ok (some (value, nextInner)) →
    flattenStateStep outer (outerState, inner, innerState) =
      .ok (some (value, (outerState, inner, nextInner))))

theorem flatten_uniform_length {α : Type} (k : Nat) (rows : List (List α))
    (h : ∀ r ∈ rows, r.length = k) :
    rows.flatten.length = k * rows.length := by
  induction rows with
  | nil => simp
  | cons r rest ih =>
    have hr := h r (List.mem_cons_self ..)
    have hrest := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp [List.flatten_cons, hr, hrest, Nat.mul_add, Nat.mul_one, Nat.add_comm]

def FlattenTupleLength : Prop :=
  (∀ {α : Type} (k : Nat) (rows : List (List α)),
    (∀ r ∈ rows, r.length = k) →
      let outer := flattenModel (listIterator rows)
      if k * rows.length < 2 ^ 63 then
        flattenTupleLength (fun it => it.length) checkedMulNatI64 outer k =
          .ok rows.flatten.length ∧
        sourceMethod1332 (fun it => it.length) (.fixedTuple k) checkedMulNatI64 outer =
          .ok rows.flatten.length
      else
        flattenTupleLength (fun it => it.length) checkedMulNatI64 outer k =
          .error (.overflowError "checked_mul") ∧
        sourceMethod1332 (fun it => it.length) (.fixedTuple k) checkedMulNatI64 outer =
          .error (.overflowError "checked_mul")) ∧
  (∀ {I : Type} (length : I → Jl Nat) (f : Flatten I) (k m : Nat),
    length f.it = .ok m →
    flattenTupleLength length checkedMulNatI64 f k = checkedMulNatI64 k m ∧
    sourceMethod1332 length (.fixedTuple k) checkedMulNatI64 f = checkedMulNatI64 k m)

def CycleNCorrect : Prop :=
  (∀ {α : Type} (xs : List α) (n : JInt64), 0 ≤ n.val →
    ∃ c, CountValue.cycle (listIterator xs) n.val = .ok c ∧
      emitsExactly (finiteCycleListObservation xs n.val.toNat) (List.replicate n.val.toNat xs).flatten) ∧
  (∀ {I : Type} (xs : I) (n : JInt64), 0 ≤ n.val →
    CountValue.cycle xs n.val = .ok ⟨⟨repeatedModel xs, n⟩⟩) ∧
  (∀ {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (isdone : I → Option S → Jl (Option Bool)) (it : I) (xs : List α)
    (cycles : Nat),
    followsProtocol iterate isdone it xs →
    collectPrefix
      (cycleObservation (cycleModel (protocolIterator iterate isdone it)))
      (cycles * xs.length) none = .ok ((List.replicate cycles xs).flatten)) ∧
  (∀ {I : Type} (xs : I) (n : JInt64), n.val < 0 →
    CountValue.cycle xs n.val =
      .error (.argumentError "Take length must be non-negative")) ∧
  (∀ {I : Type} (xs : I) (n : Int), (n < -(2 ^ 63) ∨ 2 ^ 63 ≤ n) →
    CountValue.cycle xs n = .error (.inexactError "Int64"))

def RepeatedNCorrect : Prop :=
  (∀ {O : Type} (x : O) (n : JInt64), 0 ≤ n.val →
    ∃ repeated, CountValue.repeated x n.val = .ok repeated ∧
      emitsExactly (repeatedListObservation x n.val.toNat) (List.replicate n.val.toNat x) ∧
      (repeatedListObservation x n.val.toNat).length = .ok n.val.toNat) ∧
  (∀ {O : Type} (x : O) (n : JInt64), n.val < 0 →
    CountValue.repeated x n.val =
      .error (.argumentError "Take length must be non-negative")) ∧
  (∀ {O : Type} (x : O) (n : Int), (n < -(2 ^ 63) ∨ 2 ^ 63 ≤ n) →
    CountValue.repeated x n = .error (.inexactError "Int64"))

theorem partCount (L k i : Nat) (hk : 0 < k) :
    i < (L + k - 1) / k ↔ i * k < L := by
  have h := Nat.le_div_iff_mul_le hk (x := i + 1) (y := L + k - 1)
  rw [Nat.add_mul] at h
  simp only [Nat.one_mul] at h
  omega

theorem partTake {α : Type} (xs : List α) (a k : Nat) :
    (xs.drop a).take (min (a + k) xs.length - a) = (xs.drop a).take k := by
  by_cases h : a + k ≤ xs.length
  · rw [Nat.min_eq_left h]
    congr 1; omega
  · rw [Nat.min_eq_right (by omega)]
    have hl : (xs.drop a).length = xs.length - a := List.length_drop
    rw [← hl, List.take_length]
    symm
    exact List.take_of_length_le (by rw [hl]; omega)

def PartitionVectorCorrect : Prop :=
  (∀ {α : Type} (xs : List α) (n : Nat), 0 < n →
    let itr := partitionVectorObservation ⟨xs, JInt.lit .i64 (Int.ofNat n)⟩
    emitsExactly itr (chunksSpec n xs) ∧ itr.length = .ok ((xs.length + n - 1) / n)) ∧
  (∀ {I : Type} (length : I → Jl Nat) (itr : PartitionIterator I) (l : Nat),
    length itr.c = .ok l →
    partitionLength length (fun l k => pure ((l + k.val.toNat - 1) / k.val.toNat)) itr =
      .ok ((l + itr.n.val.toNat - 1) / itr.n.val.toNat))

def statefulCurAt {α : Type} (xs : List α) (i : Nat) : Option (α × Nat) :=
  match xs.drop i with
  | [] => none
  | x :: _ => some (x, i + 1)

def StatefulConsistent : Prop :=
  (∀ {α : Type} (xs : List α) (pos : Nat) (sentinel : α),
    let s : StatefulSnapshot (IteratorModel α Nat) (α × Nat) := { itr := listIterator xs, nextvalstate := statefulCurAt xs pos }
    let isdoneFn : StatefulSnapshot (IteratorModel α Nat) (α × Nat) → List (α × Unit) → Option Bool :=
      fun stf _ => match isdoneSnapshot stf with | .ok b => some b | _ => none
    let iterateFn : StatefulSnapshot (IteratorModel α Nat) (α × Nat) → List (α × Unit) → Option ((α × Unit) × List (α × Unit)) :=
      fun stf _ => match iterateSnapshot (fun _ st => (listIterator xs).run st) stf with
        | .ok (some step, _) => some (step, [])
        | _ => none
    isdoneSnapshot s = .ok (xs.drop pos).isEmpty ∧
    JuliaLean.base.essentials.isempty isdoneFn iterateFn s = (xs.drop pos).isEmpty ∧
    peekSnapshot s sentinel =
      .ok (match xs.drop pos with | [] => Sum.inr sentinel | x :: _ => Sum.inl x) ∧
    collectSnapshots (fun _ st => (listIterator xs).run st) ((xs.drop pos).length + 1) s =
      .ok (xs.drop pos, { itr := listIterator xs, nextvalstate := none }) ∧
    (xs.drop pos = [] →
      popSnapshot (fun _ st => (listIterator xs).run st) s = .error .eofError) ∧
    (∀ x rest, xs.drop pos = x :: rest →
      ∃ sNext, popSnapshot (fun _ st => (listIterator xs).run st) s = .ok (x, sNext) ∧
        iterateSnapshot (fun _ st => (listIterator xs).run st) s = .ok (some (x, ()), sNext) ∧
        collectSnapshots (fun _ st => (listIterator xs).run st) (rest.length + 1) sNext =
          .ok (rest, { itr := listIterator xs, nextvalstate := none }))) ∧
  (∀ {α : Type} (xs : List α),
    (do
      let s0 ← (statefulAnySnapshot (fun _ st => (listIterator xs).run st) (listIterator xs) : Observation IteratorError _)
      collectSnapshots (fun _ st => (listIterator xs).run st) (xs.length + 1) s0) =
    .ok (xs, ({ itr := listIterator xs, nextvalstate := none } :
      StatefulSnapshot (IteratorModel α Nat) AnyCache (α × Nat)))) ∧
  (∀ {I α S VS β : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (s : StatefulSnapshot I VS (α × S)) (sentinel : β),
    let isdoneFn : StatefulSnapshot I VS (α × S) → List (α × Unit) → Option Bool :=
      fun stf _ => match isdoneSnapshot stf with | .ok b => some b | _ => none
    let iterateFn : StatefulSnapshot I VS (α × S) → List (α × Unit) → Option ((α × Unit) × List (α × Unit)) :=
      fun stf _ => match iterateSnapshot iterate stf with
        | .ok (some step, _) => some (step, [])
        | _ => none
    JuliaLean.base.essentials.isempty isdoneFn iterateFn s = s.nextvalstate.isNone ∧
    isdoneSnapshot s = .ok s.nextvalstate.isNone ∧
    (s.nextvalstate = none →
      peekSnapshot s sentinel = .ok (Sum.inr sentinel) ∧
      popSnapshot iterate s = .error .eofError ∧
      iterateSnapshot iterate s = .ok (none, s))) ∧
  (∀ {I α S VS β : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (s : StatefulSnapshot I VS (α × S)) (sentinel : β) (value : α) (state : S),
    s.nextvalstate = some (value, state) →
    isdoneSnapshot s = .ok false ∧
    peekSnapshot s sentinel = .ok (Sum.inl value) ∧
    (∀ next, iterate s.itr (some state) = .ok next →
      popSnapshot iterate s = .ok (value, { s with nextvalstate := next }) ∧
      iterateSnapshot iterate s =
        .ok (some (value, ()), { s with nextvalstate := next }))) ∧
  (∀ {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
      (isdone : I → Option S → Jl (Option Bool)) (itr : I) (xs : List α),
      followsProtocol iterate isdone itr xs →
      ∃ s0 : StatefulSnapshot I AnyCache (α × S),
        (statefulAnySnapshot iterate itr : Observation IteratorError _) = .ok s0 ∧
        collectSnapshots iterate (xs.length + 1) s0 =
          .ok (xs, ({ itr := itr, nextvalstate := none } : StatefulSnapshot I AnyCache (α × S))))
def OnlyCorrect : Prop :=
  (∀ {α : Type} (xs : List α),
    (xs.length = 1 → ∃ x, xs = [x] ∧ onlyIterator (listIterator xs) = .ok x ∧
      onlyTupleDispatch xs = .ok x ∧ onlyNamedTupleDispatch xs = .ok x) ∧
    (xs.length ≠ 1 → ∃ m1 m2 m3,
      onlyIterator (listIterator xs) = .error (.argumentError m1) ∧
      onlyTupleDispatch xs = .error (.argumentError m2) ∧
      onlyNamedTupleDispatch xs = .error (.argumentError m3))) ∧
  (∀ {I α S : Type} (itr : I) (iterate : I → Option S → Jl (Option (α × S))),
    (iterate itr none = .ok none →
      onlyValue itr iterate true =
        .error (.argumentError "Collection is empty, must contain exactly 1 element")) ∧
    (∀ x st, iterate itr none = .ok (some (x, st)) → iterate itr (some st) = .ok none →
      onlyValue itr iterate true = .ok x) ∧
    (∀ x st y st2, iterate itr none = .ok (some (x, st)) → iterate itr (some st) = .ok (some (y, st2)) →
      onlyValue itr iterate true =
        .error (.argumentError "Collection has multiple elements, must contain exactly 1 element"))) ∧
  (∀ {Name α : Type} (k : Name) (x : α),
    sourceMethod1683 (⟨x⟩ : Tuple1 α) = x ∧
    sourceMethod1687 NamedTuple1.value (⟨k, x⟩ : NamedTuple1 Name α) = x)

theorem onlyCorrect : OnlyCorrect := by
  refine ⟨?_, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
  · intro α xs
    constructor
    · intro h
      cases xs with
      | nil => simp at h
      | cons x rest =>
        cases rest with
        | nil => exact ⟨x, rfl, rfl, rfl, rfl⟩
        | cons y ys => simp at h
    · intro h
      cases xs with
      | nil => exact ⟨_, _, _, rfl, rfl, rfl⟩
      | cons x rest =>
        cases rest with
        | nil => exact absurd rfl h
        | cons y ys => exact ⟨_, _, _, rfl, rfl, rfl⟩
  · intro I α S itr iterate
    refine ⟨?_, ?_, ?_⟩
    · intro h0; simp [onlyValue_eq, h0]
    · intro x st h0 h1; simp [onlyValue_eq, h0, h1]
    · intro x st y st2 h0 h1; simp [onlyValue_eq, h0, h1]
theorem scanAccum_length {α β : Type} (f : β → α → β) (acc : β) (xs : List α) :
    (scanAccum f acc xs).length = xs.length := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp [scanAccum, ih]

theorem accumulateSpecGen_length {α β T : Type} (f : β → α → β) (bottomRF : T → α → β)
    (init : T) (xs : List α) :
    (accumulateSpecGen f bottomRF init xs).length = xs.length := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [accumulateSpecGen, scanAccum_length]
theorem accumulateSpec_length {α : Type} (f : α → α → α) (init : Option α) (xs : List α) :
    (accumulateSpec f init xs).length = xs.length :=
  accumulateSpecGen_length f _ init xs

def AccumulateCorrect : Prop :=
  (∀ {α β H : Type}
      (rf : JuliaLean.base.reduce.Reducer (Exec JlError H β) α)
      (init : JuliaLean.base.reduce.FoldInit (Exec JlError H β))
      (xs : List α) (depth : Nat) (heap : H),
    collectAccumulateNative
      (fun ys st h => some ((listIterator ys).run st, h)) rf init xs depth none heap =
        accumulationPrefixSpec rf init xs depth heap ∧
    accumulateLength (fun (ys : List α) => pure ys.length)
      (accumulateModel rf xs init) = .ok xs.length) ∧
  (∀ {I α β S H : Type}
      (run : I → Option S → Jl (Option (α × S)))
      (done : I → Option S → Jl (Option Bool)) (itr : I) (xs : List α)
      (rf : JuliaLean.base.reduce.Reducer (Exec JlError H β) α)
      (init : JuliaLean.base.reduce.FoldInit (Exec JlError H β))
      (depth : Nat) (heap : H),
    followsProtocol run done itr xs →
      collectAccumulateNative (fun i st h => some (run i st, h))
        rf init itr depth none heap = accumulationPrefixSpec rf init xs depth heap)

theorem except_bind_assoc {ε α β γ : Type} (m : Except ε α) (f : α → Except ε β) (g : β → Except ε γ) :
    (m >>= fun a => f a >>= g) = ((m >>= f) >>= g) := by
  cases m <;> rfl

theorem nthAdvance_listIterator {α : Type} (xs : List α) (k i : Nat) :
    ((listIterator xs).run (some i) >>= nthAdvance (listIterator xs).run k) =
      (listIterator xs).run (some (i + k)) := by
  induction k generalizing i with
  | zero =>
    cases (listIterator xs).run (some i) <;> rfl
  | succ k ih =>
    rw [listIterator_run_some]
    cases hd : xs.drop i with
    | nil =>
      have hnil : xs.drop (i + (k + 1)) = [] := by
        have := List.drop_eq_nil_iff.mp hd
        exact List.drop_eq_nil_iff.mpr (by omega)
      simp [nthAdvance, listIterator_run_some, hnil]
    | cons x rest =>
      simp only [ok_bind, nthAdvance]
      rw [ih (i + 1)]
      congr 2
      omega

theorem nthModel_listIterator_pos {α : Type} (xs : List α) (n : Int) (hn : 1 ≤ n) :
    nthIterator (listIterator xs) n =
      match xs.drop (n.toNat - 1) with
      | [] => .error .boundsError
      | x :: _ => .ok x := by
  have hnotle : ¬ n ≤ 0 := by omega
  have heq : (n - 1).toNat = n.toNat - 1 := by omega
  simp only [nthIterator_eq, nthValue_eq]
  simp only [hnotle, ↓reduceIte, heq, listIterator_run_none]
  rw [except_bind_assoc, nthAdvance_listIterator, Nat.zero_add, listIterator_run_some]
  cases xs.drop (n.toNat - 1) <;> rfl

theorem jint_add_val {u : IntTy} (a b : JInt u) : (a + b).val = wrapInt u (a.val + b.val) := rfl
theorem jint_sub_val {u : IntTy} (a b : JInt u) : (a - b).val = wrapInt u (a.val - b.val) := rfl
theorem jint_rem_val {t u : IntTy} (a : JInt t) : (JInt.rem u a).val = wrapInt u a.val := rfl
theorem jint_lit_val (u : IntTy) (x : Int) : (JInt.lit u x).val = wrapInt u x := rfl

theorem nthArray_index_val (t : IntTy) (n : JInt t) :
    (JInt.rem (IntTy.promote .i64 t) (JInt.lit .i64 1) +
      JInt.rem (IntTy.promote .i64 t) n -
      JInt.lit (IntTy.promote .i64 t) 1).val = n.val := by
  have hn := n.property
  rw [jint_sub_val, jint_add_val, jint_rem_val, jint_rem_val, jint_lit_val, jint_lit_val]
  cases t <;>
    (simp [IntTy.promote, wrapInt, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] at hn ⊢;
     omega)

def NthVectorCorrect : Prop :=
  ∀ {α : Type} (xs : List α) (n : IntegerArg),
    nthArrayIntegerArg
      (fun _ => pure (.bit .i64 (JInt.lit .i64 1)))
      (fun values index => vectorGetIndexIntegerArg values index) xs n =
      r6OrdinalList xs n.toInt

theorem nthModel_listIterator_spec {α : Type} (xs : List α) (n : Int) :
    if 1 ≤ n ∧ n ≤ xs.length then
      ∃ x, listGet xs (n.toNat - 1) = some x ∧
        nthIterator (listIterator xs) n = .ok x ∧
        nthValue (listIterator xs) n = .ok x
    else
      nthIterator (listIterator xs) n = .error .boundsError ∧
      nthValue (listIterator xs) n = .error .boundsError := by
  by_cases h : 1 ≤ n ∧ n ≤ xs.length
  · simp only [h, and_self, ↓reduceIte, nthModel_listIterator_pos xs n h.1]
    have hdrop : xs.drop (n.toNat - 1) ≠ [] := by
      intro he; have := List.drop_eq_nil_iff.mp he; omega
    cases hd : xs.drop (n.toNat - 1) with
    | nil => exact absurd hd hdrop
    | cons x rest =>
      refine ⟨x, ?_, rfl, ?_⟩
      · rw [listGet_eq_drop_head?, hd]; rfl
      · change nthIterator (listIterator xs) n = .ok x
        rw [nthModel_listIterator_pos xs n h.1, hd]
  · simp only [h, ↓reduceIte]
    by_cases hn : n ≤ 0
    · simp [nthIterator_eq, nthValue_eq, hn]
    · have hpos : 1 ≤ n := by omega
      have hge : xs.length ≤ n.toNat - 1 := by omega
      have hnil : xs.drop (n.toNat - 1) = [] := List.drop_eq_nil_iff.mpr hge
      have hm := nthModel_listIterator_pos xs n hpos
      rw [hnil] at hm
      exact ⟨hm, hm⟩
def CountfromCorrect : Prop :=
  (∀ {A S R : Type} (add : A → S → R) (convertStart : A → R) (addNext : R → S → R)
    (start : A) (step : S) (k : Nat),
    (do
      let cTyped ← countTyped (fun a b => pure (add a b)) (fun a => pure (convertStart a)) start step
      collectPrefix (countAsIterator addNext cTyped) k none) =
      .ok (countChainGen addNext (convertStart start) step k)) ∧
  (∀ {A B T : Type} (promote : A → B → Jl (T × T)) (add : T → T → T)
    (start : A) (step : B) (s d : T) (k : Nat),
    promote start step = .ok (s, d) →
    (do
      let cProm ← countNumbers promote start step
      collectPrefix (countAsIterator add cProm) k none) = .ok (countChainGen add s d k)) ∧
  (∀ (t : IntTy) (start step : JInt t) (k : Nat),
    (do
      let cTyped ← countTyped (fun a b => pure (a + b)) pure start step
      collectPrefix (countAsIterator (· + ·) cTyped) k none) =
      .ok (countChainGen (· + ·) start step k) ∧
    (do
      let cProm ← countNumbers (fun a b => pure (a, b)) start step
      collectPrefix (countAsIterator (· + ·) cProm) k none) =
      .ok (countChainGen (· + ·) start step k))

theorem enumerateNatFrom_length {α : Type} (k : Nat) (xs : List α) :
    (enumerateNatFrom k xs).length = xs.length := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => simp [enumerateNatFrom, ih]

theorem drop_reverse_range (n i : Nat) (hi : i ≤ n) :
    (List.range n).reverse.drop i = (List.range (n - i)).reverse := by
  induction i generalizing n with
  | zero => simp
  | succ i ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.drop_succ_cons, Nat.add_sub_add_right]
    exact ih m (by omega)

theorem listGet_take_last {α : Type} (xs : List α) (m : Nat) (hm : m < xs.length) :
    ∃ x, listGet xs m = some x ∧ (xs.take (m + 1)).reverse = x :: (xs.take m).reverse := by
  induction xs generalizing m with
  | nil => simp at hm
  | cons a rest ih =>
    cases m with
    | zero => exact ⟨a, rfl, rfl⟩
    | succ m =>
      obtain ⟨x, hx, hrev⟩ := ih m (by simp at hm; omega)
      refine ⟨x, hx, ?_⟩
      simp only [List.take_succ_cons, List.reverse_cons, hrev, List.cons_append]

theorem enumerateNatFrom_take_succ {α : Type} (xs : List α) (k m : Nat) (x : α)
    (hx : listGet xs m = some x) (hm : m < xs.length) :
    (enumerateNatFrom k (xs.take (m + 1))).reverse =
      (k + m, x) :: (enumerateNatFrom k (xs.take m)).reverse := by
  induction xs generalizing k m with
  | nil => simp at hm
  | cons a rest ih =>
    cases m with
    | zero =>
      cases hx
      simp [enumerateNatFrom]
    | succ m =>
      have h := ih (k + 1) m hx (by simp at hm; omega)
      have heq : k + 1 + m = k + (m + 1) := by omega
      rw [heq] at h
      simp [List.take_succ_cons, enumerateNatFrom, h]


theorem listLastModel_append_singleton {α : Type} (ys : List α) (y : α) :
    listLastModel (ys ++ [y]) = .ok y := by
  induction ys with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b bs => exact ih


theorem firstIterModel_of_emitsExactly {α S : Type} (itr : IteratorModel α S) (ys : List α)
    (h : emitsExactly itr ys) :
    firstIterModel itr = (ys.head?).elim (.error .boundsError) pure := by
  unfold emitsExactly at h
  rw [collectPrefix_succ] at h
  unfold firstIterModel
  cases hrun : itr.run none with
  | error e =>
    rw [hrun] at h
    cases h
  | ok step =>
    rw [hrun] at h
    cases step with
    | none =>
      cases h
      rfl
    | some pair =>
      dsimp [collectAfterStep] at h
      cases htail : collectPrefix itr ys.length (some pair.2) with
      | error e =>
        rw [htail] at h
        cases h
      | ok rest =>
        rw [htail] at h
        injection h with hys
        subst hys
        rfl

theorem head?_append_of_ne_nil {α : Type} (l1 l2 : List α) (h : l1 ≠ []) :
    (l1 ++ l2).head? = l1.head? := by
  cases l1 with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem head_reverse_eq_listLastModel {α : Type} (ys : List α) :
    (ys.reverse.head?).elim (.error .boundsError) pure = listLastModel ys := by
  induction ys with
  | nil => rfl
  | cons x rest ih =>
    cases rest with
    | nil => rfl
    | cons y tail =>
      have hne : (y :: tail).reverse ≠ [] := by simp
      have hhead : ((x :: y :: tail).reverse).head? = ((y :: tail).reverse).head? := by
        rw [List.reverse_cons, head?_append_of_ne_nil _ _ hne]
      rw [hhead, ih]
      rfl

theorem listLastModel_err {α : Type} (ys : List α) (e : JlError)
    (h : listLastModel ys = .error e) : e = .boundsError := by
  rw [← head_reverse_eq_listLastModel ys] at h
  cases ho : ys.reverse.head? with
  | none =>
    rw [ho] at h
    injection h with he
    exact he.symm
  | some _ =>
    rw [ho] at h
    cases h

theorem reverseLast_eq_last_reverse {α : Type} (xs : List α) :
    reverseLast (fun ys : List α => (ys.head?).elim (.error .boundsError) pure) (reverseDefault xs) =
      listLastModel xs.reverse := by
  unfold reverseLast reverseDefault
  dsimp only
  rw [← head_reverse_eq_listLastModel xs.reverse, List.reverse_reverse]

theorem collectPrefix_generator {α β S : Type} (f : α → β) (itr : IteratorModel α S) :
    ∀ (fuel : Nat) (st : Option S) (ys : List α),
      collectPrefix itr fuel st = .ok ys →
      collectPrefix (generatorAsIterator (fun f x => pure (f x)) ⟨f, itr⟩) fuel st = .ok (ys.map f) := by
  intro fuel
  induction fuel with
  | zero =>
    intro st ys h
    simp [collectPrefix] at h
    subst h
    rfl
  | succ fuel ih =>
    intro st ys h
    rw [collectPrefix_succ] at h ⊢
    have hrun_gen : (generatorAsIterator (fun f x => pure (f x)) ⟨f, itr⟩).run st = (do
        match ← itr.run st with
        | none => pure none
        | some (x, next) => pure (some (f x, next))) := by
      cases step : itr.run st with
      | error error => simp [generatorAsIterator, JuliaLean.base.generator.iterateGenerator, step]
      | ok output =>
        cases output <;>
          simp [generatorAsIterator, JuliaLean.base.generator.iterateGenerator, step,
            Bind.bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
    rw [hrun_gen]
    cases hrun : itr.run st with
    | error e =>
      rw [hrun] at h
      cases h
    | ok step =>
      rw [hrun] at h
      cases step with
      | none =>
        cases h
        rfl
      | some pair =>
        dsimp [collectAfterStep] at h
        cases htail : collectPrefix itr fuel (some pair.2) with
        | error e =>
          rw [htail] at h
          cases h
        | ok rest =>
          rw [htail] at h
          injection h with hys
          subst hys
          dsimp [ok_bind, pure_jl, collectAfterStep]
          have mapped := ih (some pair.2) rest htail
          simp only [Pure.pure, Except.pure] at mapped
          rw [mapped]
          rfl

theorem emitsExactly_generator {α β S : Type} (f : α → β) (itr : IteratorModel α S) (ys : List α)
    (h : emitsExactly itr ys) :
    emitsExactly (generatorAsIterator (fun f x => pure (f x)) ⟨f, itr⟩) (ys.map f) := by
  unfold emitsExactly at h ⊢
  rw [List.length_map]
  exact collectPrefix_generator f itr (ys.length + 1) none ys h


theorem collectPrefix_repeatedInf {α : Type} (x : α) (k : Nat) :
    ∀ st, collectPrefix (repeatedAsIterator (repeatedModel x)) k st =
      .ok (List.replicate k x) := by
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro st
    rw [collectPrefix_succ]
    have hrun : (repeatedAsIterator (repeatedModel x)).run st = .ok (some (x, ())) := rfl
    rw [hrun, collectAfterStep_some, ih (some ()), ok_bind, pure_jl, List.replicate_succ]

theorem collectPartitionChunk_listIterator {α : Type} (xs : List α) :
    ∀ (k i : Nat),
      collectPartitionChunk (fun itr st => itr.run st) (listIterator xs) k (some i) =
        .ok ((xs.drop i).take k,
          if (xs.drop i).length < k then none else some (i + k)) := by
  intro k
  induction k with
  | zero =>
    intro i
    simp [collectPartitionChunk]
  | succ k ih =>
    intro i
    simp only [collectPartitionChunk, listIterator_run_some]
    cases hd : xs.drop i with
    | nil => simp
    | cons x rest =>
      have hdrop : xs.drop (i + 1) = rest := by rw [← List.drop_drop, hd]; rfl
      simp only [ok_bind, ih (i + 1), hdrop, List.length_cons, List.take_succ_cons, pure_jl]
      by_cases hlt : rest.length < k
      · have hlt' : rest.length + 1 < k + 1 := by omega
        simp [hlt, hlt']
      · have hlt' : ¬ (rest.length + 1 < k + 1) := by omega
        have hadd : i + 1 + k = i + (k + 1) := by omega
        simp [hlt, hlt', hadd]

theorem collectPartitionChunk_from_trace {I α S : Type}
    (iterate : I → Option S → Jl (Option (α × S)))
    (isdone : I → Option S → Jl (Option Bool)) (it : I) :
    ∀ (k : Nat) (state : Option S) (xs : List α),
      followsFrom (protocolIterator iterate isdone it) state xs →
      ∃ finalState,
        collectPartitionChunk iterate it k state = .ok (xs.take k, finalState) := by
  intro k
  induction k with
  | zero =>
      intro state xs _
      exact ⟨state, rfl⟩
  | succ k ih =>
      intro state xs h
      cases xs with
      | nil =>
          have hstop := followsFrom_nil (protocolIterator iterate isdone it) state h
          change iterate it state = .ok none at hstop
          exact ⟨none, by simp [collectPartitionChunk, hstop]⟩
      | cons x rest =>
          obtain ⟨next, hstep, htail⟩ :=
            followsFrom_cons (protocolIterator iterate isdone it) state x rest h
          change iterate it state = .ok (some (x, next)) at hstep
          obtain ⟨finalState, hchunk⟩ := ih (some next) rest htail
          refine ⟨finalState, ?_⟩
          simp [collectPartitionChunk, hstep, hchunk]



theorem allocPartitionVector_ok (n : Nat) (hn : n < 2 ^ 60) :
    allocPartitionVector n = .ok () := by
  unfold allocPartitionVector
  have h : ¬ (n ≥ 2 ^ 63 - 2 ∨ n * 8 ≥ 2 ^ 63 - 2) := by omega
  simp [h]


theorem flatMap_reverse_map_reverse {α β γ : Type} (xs : List α) (ys : List β) (f : α → β → γ) :
    (ys.reverse.flatMap fun y => xs.reverse.map fun x => f x y) =
      (ys.flatMap fun y => xs.map fun x => f x y).reverse := by
  induction ys with
  | nil => rfl
  | cons y rest ih =>
    rw [List.reverse_cons, List.flatMap_append, ih, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.map_reverse, ← List.reverse_append, List.flatMap_cons]

theorem nthZip_two_lists {α : Type} (xs ys : List α) (n : Int) :
    if 1 ≤ n ∧ n ≤ min xs.length ys.length then
      ∃ x y, listGet xs (n.toNat - 1) = some x ∧ listGet ys (n.toNat - 1) = some y ∧
        nthZipValues [listIterator xs, listIterator ys] n = .ok [x, y]
    else
      nthZipValues [listIterator xs, listIterator ys] n = .error .boundsError := by
  have hx := nthModel_listIterator_spec xs n
  have hy := nthModel_listIterator_spec ys n
  by_cases h : 1 ≤ n ∧ n ≤ min xs.length ys.length
  · have hx_cond : 1 ≤ n ∧ n ≤ xs.length := ⟨h.1, by omega⟩
    have hy_cond : 1 ≤ n ∧ n ≤ ys.length := ⟨h.1, by omega⟩
    simp only [hx_cond, and_self, ↓reduceIte] at hx
    simp only [hy_cond, and_self, ↓reduceIte] at hy
    obtain ⟨x, hgx, _, hnx⟩ := hx
    obtain ⟨y, hgy, _, hny⟩ := hy
    simp only [h, and_self, ↓reduceIte]
    refine ⟨x, y, hgx, hgy, ?_⟩
    unfold nthZipValues nthZip nthCurry
    dsimp [List.mapM, List.mapM.loop]
    rw [hnx, ok_bind, hny, ok_bind]
    rfl
  · simp only [h, ↓reduceIte]
    unfold nthZipValues nthZip nthCurry
    dsimp [List.mapM, List.mapM.loop]
    by_cases hx_cond : 1 ≤ n ∧ n ≤ xs.length
    · have hy_cond : ¬ (1 ≤ n ∧ n ≤ ys.length) := by omega
      simp only [hx_cond, and_self, ↓reduceIte] at hx
      simp only [hy_cond, ↓reduceIte] at hy
      obtain ⟨x, _, _, hnx⟩ := hx
      rw [hnx, ok_bind, hy.2]
      rfl
    · simp only [hx_cond, ↓reduceIte] at hx
      rw [hx.2]
      rfl

theorem jint_wrap_i64_val (x : Int) (hlo : -(2 ^ 63) ≤ x) (hhi : x ≤ 2 ^ 63 - 1) :
    (JInt.wrap .i64 x).val = x := by
  change wrapInt .i64 x = x
  simp [wrapInt, IntTy.signed, IntTy.bits]
  omega

theorem jint_lit_i64_val (x : Int) (hlo : -(2 ^ 63) ≤ x) (hhi : x ≤ 2 ^ 63 - 1) :
    (JInt.lit .i64 x).val = x :=
  jint_wrap_i64_val x hlo hhi

theorem except_map_ok_bind {α β γ : Type} (x : α) (f : α → β) (g : β → Jl γ) :
    (Except.map f (Except.ok x : Jl α) >>= g) = g (f x) := rfl

def pairsValuesSpec {K V I D : Type}
    (element : PairsModel K V I D → I → Jl (I × V)) (p : PairsModel K V I D) :
    List I → Jl (List (I × V))
  | [] => pure []
  | key :: rest => do
      let pair ← element p key
      let tail ← pairsValuesSpec element p rest
      pure (pair :: tail)


def PairsSemantics : Prop :=
  (∀ {α : Type} (xs : List α),
    let p : PairsModel Nat α (List Nat) (List α) :=
      pairsLinear (fun ys => List.range ys.length) xs
    let pTuple : PairsModel Nat α (UnitRangeIndices Nat) (TupleContainer α) :=
      pairsTuple (K := Nat) (V := α) (fun t => ⟨1, t.items.length⟩) ⟨xs⟩
    let keysData : List α → Jl (List Nat) := fun ys => pure (List.range ys.length)
    emitsExactly (pairsObservation xs) (enumerateNatFrom 0 xs) ∧
    emitsExactly (reversePairsObservation xs) (enumerateNatFrom 0 xs).reverse ∧
    lastPairs keysData listLastModel
      (fun ys i => (listGet ys i).elim (.error .boundsError) pure)
      (fun key value => pure (key, value)) p = listLastModel (enumerateNatFrom 0 xs) ∧
    (pairsObservation xs).length = .ok xs.length ∧
    (pairsObservation xs).size = .ok [xs.length] ∧
    pairsMetadata keysData (fun r => pure [r.length]) p = .ok [xs.length] ∧
    (∀ st, pairsMetadata keysData (fun keys => (listIterator keys).isdone st) p =
      .ok (some (decide (xs.length ≤ st.getD 0)))) ∧
    sourceMethod318 .hasLength p = .hasLength ∧
    sourceMethod319 pTuple = .hasLength ∧
    (∀ k : Nat, pairsMetadata keysData (fun keys => pure (decide (k ∈ keys))) p =
      .ok (decide (k < xs.length)))) ∧
  (∀ {K V I D S : Type} (p : PairsModel K V I D)
      (keysData : D → Jl I) (iterate : I → Option S → Jl (Option (I × S)))
      (isdone : I → Option S → Jl (Option Bool)) (getindexData : D → I → Jl V)
      (indices : List I) (state : Option S),
    let q : PairsModel I V I D := { data := p.data, itr := p.itr }
    match keysPairs keysData p with
    | .error e =>
        iteratePairs keysData iterate getindexData (fun key value => pure (key, value)) q state = .error e
    | .ok keys =>
        followsFrom (protocolIterator iterate isdone keys) state indices →
        collectPrefix
          (protocolIterator
            (fun (_ : PairsModel K V I D) st =>
              iteratePairs keysData iterate getindexData (fun key value => pure (key, value)) q st)
            (fun _ _ => .ok none) p)
          (indices.length + 1) state =
          pairsValuesSpec
            (fun (q : PairsModel K V I D) idx =>
              pairsElement getindexData (fun key value => pure (key, value))
                ({ data := q.data, itr := q.itr } : PairsModel I V I D) idx) p indices) ∧
  (∀ {K V I D : Type} (data : D) (selected : Option I)
      (keysData : D → Jl I) (idxFn : D → I),
    let p : PairsModel K V I D := ⟨data, selected⟩
    keysPairs keysData p = (match selected with | none => keysData data | some i => .ok i) ∧
    valuesPairsModel p = data ∧
    pairsLinear (K := K) (V := V) idxFn data = ⟨data, some (idxFn data)⟩ ∧
    pairsTuple (K := K) (V := V) idxFn data = ⟨data, some (idxFn data)⟩ ∧
    pairsNamedTuple (K := K) (V := V) idxFn data = ⟨data, none⟩ ∧
    pairsSimpleVector (K := K) (V := V) idxFn data = ⟨data, some (idxFn data)⟩ ∧
    pairsVector (pairsLinear (K := K) (V := V) idxFn) data = ⟨data, some (idxFn data)⟩ ∧
    pairsCartesian (K := K) (V := V) pure (fun d => pure (idxFn d)) data = .ok ⟨data, some (idxFn data)⟩ ∧
    pairsArray (fun (d : D) => (⟨d, some (idxFn d)⟩ : PairsModel K V I D)) data = ⟨data, some (idxFn data)⟩) ∧
  (∀ {K V I D R : Type} (getindex : D → K → Jl R) (p : PairsModel K V I D) (key : K),
    getindexPairs getindex p key = getindex p.data key) ∧
  (∀ {K V I D R H : Type} (setindex : D → K → R → Exec JlError H Unit)
      (getindex : D → K → Exec JlError H R) (p : PairsModel K V I D)
      (key : K) (value : R) (heap next : H),
    setindex p.data key value heap = some (.ok (), next) →
      setindexPairs setindex p value key heap = some (.ok p, next) ∧
      (do
        let p' ← setindexPairs setindex p value key
        getindexPairs getindex p' key) heap = getindex p.data key next) ∧
  (∀ {K V I D R : Type} (get : D → K → R → Jl R)
      (p : PairsModel K V I D) (key : K) (default : R),
    getPairs get p key default = get p.data key default) ∧
  (∀ {F K V I D R : Type} (getFn : F → D → K → Jl R)
      (f : F) (p : PairsModel K V I D) (key : K),
    getPairsWithFunction getFn f p key = getFn f p.data key)

theorem reverseListAsIterator_run_zero {α : Type} (xs : List α) :
    (reverseListAsIterator xs).run (some (0 : Int)) = .ok none := rfl

theorem reverseListAsIterator_run_succ {α : Type} (xs : List α) (m : Nat) (x : α)
    (hx : listGet xs m = some x) :
    (reverseListAsIterator xs).run (some ((m + 1 : Nat) : Int)) =
      .ok (some (x, (m : Int))) := by
  have hnotlt : ¬ ((m : Int) + 1 < 1) := by omega
  have hsub : (m : Int) + 1 - 1 = (m : Int) := by omega
  simp [reverseListAsIterator, iterateReverseList, reverseDefault, hnotlt, hx, hsub, Except.map]

def CycleRepeatedSemantics : Prop :=
  (∀ {α β : Type} (f : α → β) (xs : List α),
    emitsExactly (mapGeneratorAsIterator (mapModel id f (listIterator xs) [])) (xs.map f)) ∧
  (∀ {α β : Type} (f : α → List β) (xs : List α),
    let outer := mapGeneratorAsIterator (flatmapModel (m := Id)
      (fun f c => mapModel id f c []) (fun x => listIterator (f x)) (listIterator xs)).it
    emitsExactly (flattenObservation (flattenModel outer)) ((xs.map f).flatten)) ∧
  (∀ {It K V : Type} (pairsList : It → List (K × V)) (predicate : V → Bool) (it : It),
    emitsExactly
      (findeachObservation (sourceMethod1016 (m := Id) (fun x => listIterator (pairsList x))
        id (fun f x => f x) predicate it))
      (((pairsList it).filter fun pair => predicate pair.2).map Prod.fst)) ∧
  (∀ {It K : Type} (pairsList : It → List (K × Bool)) (it : It),
    sourceMethod1018 (m := Id) (K := K) (V := Bool) pairsList id it =
      sourceMethod1016 (m := Id) (K := K) (V := Bool) pairsList id (fun f x => f x) id it ∧
    emitsExactly
      (findeachObservation (sourceMethod1018 (m := Id) (K := K) (V := Bool)
        (fun x => listIterator (pairsList x)) id it))
      (((pairsList it).filter fun pair => pair.2).map Prod.fst)) ∧
  (∀ {It K V S : Type} (pairs : It → IteratorModel (K × V) S)
    (predicate : V → Bool) (it : It) (xs : List (K × V)),
    followsFrom (pairs it) none xs →
    emitsExactly
      (findeachObservation (sourceMethod1016 (m := Id) pairs id (fun f x => f x) predicate it))
      ((xs.filter fun pair => predicate pair.2).map Prod.fst)) ∧
  CycleNCorrect ∧
  RepeatedNCorrect ∧
  (∀ {α : Type} (xs : List α),
    let c := cycleModel (listIterator xs)
    cycleEltype α c = α ∧
    cycleIteratorEltype (fun it => it.iteratorEltype) c = .hasEltype ∧
    cycleIteratorSize = .isInfinite ∧
    isdoneCycle (fun _ st => (listIterator xs).isdone st) c = .ok (some xs.isEmpty) ∧
    (∀ i, isdoneCycleState (fun _ st => (listIterator xs).isdone st) c i = .ok (some false)) ∧
    lastCycle listLastModel (cycleModel xs) = listLastModel xs ∧
    (reverseCycle (m := Id) List.reverse (cycleModel xs)).xs = xs.reverse ∧
    emitsExactly (reverseListAsIterator (reverseCycle (m := Id) List.reverse (cycleModel xs)).xs) xs ∧
    (xs = [] → collectPrefix (cycleObservation c) 1 none = .ok []) ∧
    (∀ x0 rest, xs = x0 :: rest →
      collectPrefix (cycleObservation c) (rest.length + 2) none = .ok ((x0 :: rest) ++ [x0]))) ∧
  (∀ {O : Type} (x : O) (k : Nat),
    let r := repeatedModel x
    collectPrefix (repeatedAsIterator r) k none = .ok (List.replicate k x) ∧
    collectPrefix (repeatedAsIterator (reverseRepeated r)) k none = .ok (List.replicate k x) ∧
    repeatedEltype r = O ∧
    repeatedIteratorSize = .isInfinite ∧
    repeatedIteratorEltype = .hasEltype ∧
    reverseRepeated r = r ∧
    lastRepeated (fun it => firstIterModel (repeatedAsIterator it)) r = .ok x)

def IterableStatePairsSemantics : Prop :=
  (∀ {α : Type} (xs : List α),
    emitsExactly (iterablePairsObservation xs) (enumerateNatFrom 0 xs) ∧
    emitsExactly (reverseIterableStatePairsAsIterator xs)
      (((enumerateNatFrom 1 xs).reverse).map fun (i, v) => (Int.ofNat i, v))) ∧
  (∀ {T Keys V S : Type} (keys : T → Jl Keys) (firstKey lastKey : Keys → Jl S)
    (iterate : T → Option S → Jl (Option (V × S)))
    (x : IterableStatePairs T) (ks : Keys) (k0 kLast s : S),
    keys x.x = .ok ks →
    firstKey ks = .ok k0 →
    lastKey ks = .ok kLast →
    iterateStatePairs keys firstKey (fun i st => iterate i (some st)) x none =
      (do
        match ← iterate x.x (some k0) with
        | none => pure none
        | some (value, next) => pure (some ((k0, value), next))) ∧
    iterateStatePairs keys firstKey (fun i st => iterate i (some st)) x (some s) =
      (do
        match ← iterate x.x (some s) with
        | none => pure none
        | some (value, next) => pure (some ((s, value), next))) ∧
    iterateReverseIterableStatePairs keys lastKey (fun r st => iterate r.itr st) ⟨reverseDefault x.x⟩ none =
      (do
        match ← iterate x.x (some kLast) with
        | none => pure none
        | some (value, next) => pure (some ((kLast, value), next))) ∧
    iterateReverseIterableStatePairs keys lastKey (fun r st => iterate r.itr st) ⟨reverseDefault x.x⟩ (some s) =
      (do
        match ← iterate x.x (some s) with
        | none => pure none
        | some (value, next) => pure (some ((s, value), next)))) ∧
  (∀ {T α : Type} (length : T → Jl α) (x : IterableStatePairs T) (sz : IteratorSizeTag)
    (_keyType eltype : Type) (reverse : T → T),
    iterableStatePairsLength length x = length x.x ∧
    sourceMethod1704 sz x = sz ∧
    sourceMethod1706 (fun _ => eltype) x = PairAnyFirst eltype ∧
    reverseIterableStatePairs (m := Id) reverse x = ⟨reverse x.x⟩ ∧
    reverseIterableStatePairsReverse ⟨reverseDefault x.x⟩ = x ∧
    pairsStringModel x.x = x)

def ProductShapeFinite : Prop :=
  ∀ tags, (∀ tag ∈ tags, tag = .hasLength ∨ ∃ n, tag = .hasShape n) →
    productIteratorSizeFold tags = .hasShape (tags.foldl (fun n tag =>
      n + match tag with | .hasLength => 1 | .hasShape d => d | _ => 0) 0)

theorem foldl_dims_shift (tags : List IteratorSizeTag) (acc : Nat) :
    tags.foldl (fun n tag => n + match tag with | .hasLength => 1 | .hasShape d => d | _ => 0) acc =
      acc + tags.foldl (fun n tag => n + match tag with | .hasLength => 1 | .hasShape d => d | _ => 0) 0 := by
  induction tags generalizing acc with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (acc + _), ih (match t with | .hasLength => 1 | .hasShape d => d | _ => 0)]
    omega

theorem productShapeFinite : ProductShapeFinite := by
  intro tags htags
  induction tags with
  | nil => rfl
  | cons a rest ih =>
    have ha := htags a (List.mem_cons_self ..)
    cases rest with
    | nil =>
      rcases ha with rfl | ⟨d, rfl⟩ <;> simp [productIteratorSizeFold, productIteratorSizePair]
    | cons b tail =>
      have hrest : ∀ tag ∈ b :: tail, tag = .hasLength ∨ ∃ n, tag = .hasShape n :=
        fun tag h => htags tag (List.mem_cons_of_mem _ h)
      have ih' := ih hrest
      show productIteratorSizePair a (productIteratorSizeFold (b :: tail)) = _
      rw [ih']
      rcases ha with rfl | ⟨d, rfl⟩
      · simp only [productIteratorSizePair, List.foldl_cons, Nat.zero_add]
        congr 1
        rw [foldl_dims_shift]
        conv => rhs; rw [foldl_dims_shift]
        omega
      · simp only [productIteratorSizePair, List.foldl_cons, Nat.zero_add]
        congr 1
        rw [foldl_dims_shift]
        conv => rhs; rw [foldl_dims_shift]
        omega

def ProductIelSpec : Prop :=
  sourceMethod1188 = .hasEltype ∧
  ∀ {T F : Type} (fieldtype : T → Nat → F)
      (trait : F → IteratorEltypeTag) (p : ProductIterator T) (N : Nat),
    0 < N →
      (productIteratorEltype fieldtype trait N p = .ok .hasEltype ↔
        ∀ k, k < N → trait (fieldtype p.iterators (k + 1)) = .hasEltype) ∧
      (productIteratorEltype fieldtype trait N p = .ok .eltypeUnknown ↔
        ∃ k, k < N ∧ trait (fieldtype p.iterators (k + 1)) = .eltypeUnknown)

private theorem productEltypeResult_of_nonempty (tags : List IteratorEltypeTag)
    (hne : tags ≠ []) :
    ((if tags.any (fun tag => tag == .eltypeUnknown) then
      .ok .eltypeUnknown
     else
      match tags.getLast? with
      | some last => .ok last
      | none => .error .boundsError) : Jl IteratorEltypeTag) =
    .ok (if tags.any (fun tag => tag == .eltypeUnknown) then
      .eltypeUnknown else .hasEltype) := by
  induction tags with
  | nil => contradiction
  | cons tag rest ih =>
    cases tag with
    | eltypeUnknown => simp
    | hasEltype =>
      cases rest with
      | nil => simp
      | cons next rest =>
        have hi := ih (by simp)
        simpa using hi

theorem productIelSpec_proven : ProductIelSpec := by
  constructor
  · rfl
  · intro T F fieldtype trait p N hN
    let tags := (List.range N).map
      (fun k => trait (fieldtype p.iterators (k + 1)))
    have hne : tags ≠ [] := by
      intro h
      simp [tags] at h
      omega
    have hresult :
        productIteratorEltype fieldtype trait N p =
          .ok (if tags.any (fun tag => tag == .eltypeUnknown) then
            .eltypeUnknown else .hasEltype) := by
      change ((if tags.any (fun tag => tag == .eltypeUnknown) then
        .ok .eltypeUnknown
       else
        match tags.getLast? with
        | some last => .ok last
        | none => .error .boundsError) : Jl IteratorEltypeTag) = _
      exact productEltypeResult_of_nonempty tags hne
    constructor
    · constructor
      · intro heq k hk
        rw [hresult] at heq
        have hnot : tags.any (fun tag => tag == .eltypeUnknown) = false := by
          cases hany : tags.any (fun tag => tag == .eltypeUnknown) with
          | false => rfl
          | true => simp [hany] at heq
        have hmem : trait (fieldtype p.iterators (k + 1)) ∈ tags := by
          exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
        have htag := (List.any_eq_false.mp hnot)
          (trait (fieldtype p.iterators (k + 1))) hmem
        cases hv : trait (fieldtype p.iterators (k + 1)) <;> simp_all
      · intro hall
        rw [hresult]
        have hnot : tags.any (fun tag => tag == .eltypeUnknown) = false := by
          apply List.any_eq_false.mpr
          intro tag htag
          rcases List.mem_map.mp htag with ⟨k, hk, hEq⟩
          have hkN := List.mem_range.mp hk
          subst tag
          simp [hall k hkN]
        simp [hnot]
    · constructor
      · intro heq
        rw [hresult] at heq
        have hany : tags.any (fun tag => tag == .eltypeUnknown) = true := by
          cases hbool : tags.any (fun tag => tag == .eltypeUnknown) with
          | false => simp [hbool] at heq
          | true => rfl
        rcases List.any_eq_true.mp hany with ⟨tag, htag, hunknown⟩
        rcases List.mem_map.mp htag with ⟨k, hk, hEq⟩
        refine ⟨k, List.mem_range.mp hk, ?_⟩
        subst tag
        cases hv : trait (fieldtype p.iterators (k + 1)) <;> simp_all
      · rintro ⟨k, hk, hval⟩
        have hmem : trait (fieldtype p.iterators (k + 1)) ∈ tags := by
          exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
        have hany : tags.any (fun tag => tag == .eltypeUnknown) = true := by
          apply List.any_eq_true.mpr
          exact ⟨_, hmem, by simp [hval]⟩
        rw [hresult]
        simp [hany]


theorem sourceMethod1171_listIterators {α : Type} (xss : List (List α)) :
    sourceMethod1171 (fun itr => itr.size) (fun itr => itr.length)
      (fun itr => itr.iteratorSize) (xss.map listIterator) =
    .ok (xss.map List.length) := by
  induction xss with
  | nil => rfl
  | cons xs rest ih =>
    simp [sourceMethod1171, sourceMethod1173, listIterator, ih]

theorem sourceMethod1179_listIterators {α : Type} (xss : List (List α)) :
    sourceMethod1179 (fun itr => itr.size) (fun itr => itr.length)
      (fun itr => itr.iteratorSize) (xss.map listIterator) =
    .ok (xss.map List.length) := by
  induction xss with
  | nil => rfl
  | cons xs rest ih =>
    simp [sourceMethod1179, sourceMethod1181, listIterator, ih]

def ProductMethodSemantics : Prop :=
  ProductCorrect ∧
  (productIteratorSizeFold [.hasLength, .hasLength] = .hasShape 2) ∧
  ProductShapeFinite ∧
  ProductIelSpec ∧
  (∀ {α : Type} (xs ys : List α),
    (do
      let revP ← observeJl (productReverseObservation (fun (l : List α) => pure l.reverse) (productModel [xs, ys]))
      collectPrefix
        (productObservation (productModel (revP.iterators.map listIterator))
          (fun itr st => itr.isdone st) (fun itr st => itr.run st)
          (fun _ => α) (fun _ value _ => pure value))
        (((ys.flatMap fun y => xs.map fun x => [x, y]).reverse).length + 1) none) =
      .ok ((ys.flatMap fun y => xs.map fun x => [x, y]).reverse) ∧
    (xs = [] ∨ ys = [] → productLastObservation listLastModel (productModel [xs, ys]) = .error .boundsError) ∧
    (xs ≠ [] → ys ≠ [] →
      productLastObservation listLastModel (productModel [xs, ys]) =
        listLastModel (ys.flatMap fun y => xs.map fun x => [x, y]))) ∧
  (∀ {α : Type} (xss : List (List α)),
    sourceMethod1169 (fun itr => itr.size) (fun itr => itr.length)
      (fun itr => itr.iteratorSize) (productModel (xss.map listIterator)) =
        .ok (xss.map List.length) ∧
    sourceMethod1177 (fun itr => itr.size) (fun itr => itr.length)
      (fun itr => itr.iteratorSize) (productModel (xss.map listIterator)) =
        .ok (xss.map List.length) ∧
    sourceMethod1185 (fun iters => sourceMethod1177 (fun itr => itr.size)
      (fun itr => itr.length) (fun itr => itr.iteratorSize) (productModel iters))
      (productModel (xss.map listIterator)) = .ok xss.length) ∧
  (∀ {I : Type} (a : I) (typeof : I → String) (sz : IteratorSizeTag),
    sourceMethod1174 (Dim := Nat) a sz typeof =
      .error (.argumentError s!"Cannot compute size for object of type {typeof a}") ∧
    sourceMethod1182 a sz typeof =
      .error (.argumentError s!"Cannot compute indices for object of type {typeof a}")) ∧
  (∀ {I α S : Type} (s : Bool) (it : IteratorModel α S) (its : List (IteratorModel α S))
    (eltype : I → Type) (tupleOrBottom : List Type → Type) (items : List I),
    iterateEmptyProduct (α := α) = ([], true) ∧
    iterateEmptyProductState (α := α) s = none ∧
    isdoneEmptyProductState s = .ok (some true) ∧
    sourceMethod1188 = .hasEltype ∧
    sourceMethod1189 (fun i : IteratorModel α S => i.iteratorEltype) it = it.iteratorEltype ∧
    productIteratorEltype (fun ts n => ts.getD (n - 1) it)
      (fun i : IteratorModel α S => i.iteratorEltype)
      (it :: its).length (productModel (it :: its)) =
      .ok (productEltypeFold ((it :: its).map fun i => i.iteratorEltype)) ∧
    sourceMethod1197 eltype (productModel ([] : List I)) tupleOrBottom =
      tupleOrBottom sourceMethod1198 ∧
    sourceMethod1199 eltype items tupleOrBottom = tupleOrBottom (items.map eltype)) ∧
  (∀ {I α β S : Type} (isdone : I → Option S → Jl (Option Bool))
    (iterate : I → Option S → Jl (Option (α × S))) (p : ProductIterator (List I))
    (defaultEltype : I → Type) (typeassert : I → α → Type → Jl β)
    (value : I → α) (state : I → S) (converted : I → β),
    (productObservation p isdone iterate defaultEltype typeassert).isdone none = .ok (some false) →
    (∀ i, i ∈ p.iterators →
      iterate i none = .ok (some (value i, state i)) ∧
      typeassert i (value i) (defaultEltype i) = .ok (converted i)) →
    (productObservation p isdone iterate defaultEltype typeassert).run none =
      .ok (some
        (p.iterators.map converted,
          productExpectedStates p.iterators converted state)))

theorem flatten_reverse_map_reverse {α : Type} (rows : List (List α)) :
    (rows.reverse.map List.reverse).flatten = rows.flatten.reverse := by
  induction rows with
  | nil => rfl
  | cons r rest ih =>
    rw [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.flatten_append, ih, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [List.flatten_cons, List.reverse_append]

theorem flatten_iteratorsize_iff (sz : IteratorSizeTag) (eltypeKnown : Bool) (kind : FlattenInnerKind) :
    (sourceMethod1322 sz eltypeKnown kind = .hasLength ↔
      (eltypeKnown = true ∧
        (kind = .emptyTuple ∨
          ((sz = .hasLength ∨ ∃ d, sz = .hasShape d) ∧
            (kind = .bottom ∨ (∃ n, kind = .fixedTuple n) ∨ kind = .number))))) ∧
    (sourceMethod1322 sz eltypeKnown kind ≠ .hasLength →
      sourceMethod1322 sz eltypeKnown kind = .sizeUnknown) := by
  cases sz <;> cases eltypeKnown <;> cases kind <;>
    simp [sourceMethod1322, sourceMethod1318, sourceMethod1319, sourceMethod1320,
      sourceMethod1310, sourceMethod1313, sourceMethod1314, sourceMethod1315, sourceMethod1316]

def FlattenMethodSemantics : Prop :=
  FlattenCorrect ∧ FlattenTupleLength ∧
  (∀ {α : Type} (rows : List (List α)),
    emitsExactly (reverseFlattenObservation rows) rows.flatten.reverse ∧
    lastFlattenObservation rows = observeJl (listLastModel rows.flatten)) ∧
  (∀ (sz : IteratorSizeTag) (eltypeKnown : Bool) (kind : FlattenInnerKind),
    (sourceMethod1322 sz eltypeKnown kind = .hasLength ↔
      (eltypeKnown = true ∧
        (kind = .emptyTuple ∨
          ((sz = .hasLength ∨ ∃ d, sz = .hasShape d) ∧
            (kind = .bottom ∨ (∃ n, kind = .fixedTuple n) ∨ kind = .number))))) ∧
    (sourceMethod1322 sz eltypeKnown kind ≠ .hasLength →
      sourceMethod1322 sz eltypeKnown kind = .sizeUnknown)) ∧
  (∀ (sz : IteratorSizeTag) (kind : FlattenInnerKind) (slurp : List FlattenInnerKind),
    sourceMethod1311 sz kind slurp = .error (.methodError "flatten_iteratorsize")) ∧
  (∀ {α : Type} (xs : List α),
    let f := flattenModel (listIterator xs)
    sourceMethod1332 (fun it => it.length) .bottom checkedMulNatI64 f = .ok 0 ∧
    sourceMethod1332 (fun it => it.length) .emptyTuple checkedMulNatI64 f = .ok 0 ∧
    sourceMethod1332 (fun it => it.length) .number checkedMulNatI64 f = .ok xs.length ∧
    sourceMethod1332 (fun it => it.length) .tuple checkedMulNatI64 f =
      .error (.argumentError "Iterates of the argument to Flatten are not known to have constant length") ∧
    sourceMethod1332 (fun it => it.length) .other checkedMulNatI64 f =
      .error (.argumentError "Iterates of the argument to Flatten are not known to have constant length") ∧
    sourceMethod1325 xs ([] : List α) = .error (.methodError "flatten_length") ∧
    flattenEmptyLength = 0) ∧
  (∀ {I : Type} (outerTag innerTag : IteratorEltypeTag) (it : I),
    flattenIteratorEltype (fun _ => outerTag) (fun _ => innerTag) id (flattenModel it) = .hasEltype ↔
      (outerTag = .hasEltype ∧ innerTag = .hasEltype)) ∧
  (∀ {I : Type} (eltype : Type)
      (nothing missing : JuliaLean.base.promotion.PType)
      (items : List JuliaLean.base.promotion.PType) (it : I),
    flattenEltype eltype (flattenModel it) = eltype ∧
    flattenTupleEltype (fun (_ : I) n => items.getD (n - 1) .bottom) id
      nothing missing it items.length =
        items.foldlM (typejoin nothing missing) .bottom ∧
    flattenNamedEltype (fun (_ : I) => items) id nothing missing it =
      items.foldlM (typejoin nothing missing) .bottom)

theorem partition_iteratorsize_iff {T : Type} (sz : IteratorSizeTag) (it : PartitionIterator T) :
    (sourceMethod1461 sz it = .hasLength ↔ (sz = .hasLength ∨ ∃ d, sz = .hasShape d)) ∧
    ((∀ d, sz ≠ .hasShape d) → sourceMethod1461 sz it = sz) := by
  cases sz <;> simp [sourceMethod1461, sourceMethod1459, sourceMethod1460]

def partitionIntRangeChunksSpec (last : Int) (n : Nat) :
    Nat → Int → List (Int × Int)
  | 0, _ => []
  | fuel + 1, start =>
      if start ≤ last then
        let stop := min (start + Int.ofNat n - 1) last
        (start, stop) :: partitionIntRangeChunksSpec last n fuel (stop + 1)
      else []

def PartitionMethodSemantics : Prop :=
  PartitionVectorCorrect ∧
  (∀ {I C : Type} (c : I) (n : Int) (construct : I → Nat → PartitionIterator C), n < 1 →
    partitionNativeConstruct c n construct = .error (.argumentError s!"cannot create partitions of length {n}")) ∧
  (∀ {α : Type} (xs : List α) (n : JInt64), 1 ≤ n.val →
    ∃ p, partitionNativeConstruct xs n.val (fun v k => sourceMethod1447 v (JInt.lit .i64 (Int.ofNat k))) = .ok p ∧
      emitsExactly (partitionVectorObservation p) (chunksSpec n.val.toNat xs) ∧
      (partitionVectorObservation p).length = .ok ((xs.length + n.val.toNat - 1) / n.val.toNat)) ∧
  (∀ {A V : Type} (vec : A → V) (a : A) (n : JInt64), 1 ≤ n.val →
    partitionNativeConstruct a n.val (fun x k => sourceMethod1447 (vec x) (JInt.lit .i64 (Int.ofNat k))) =
      .ok ⟨vec a, JInt.lit .i64 (Int.ofNat n.val.toNat)⟩ ∧
    partitionArray (m := Jl) (fun x => pure (vec x)) a n = .ok ⟨vec a, n⟩) ∧
  (∀ {α : Type} (xs : List α) (n : Nat), 0 < n → n < 2 ^ 60 →
    emitsExactly (partitionGenericObservation xs n) (chunksSpec n xs)) ∧
  (∀ {R Slice : Type} (firstindex lastindex : R → JInt64)
    (getSlice : R → JInt64 → JInt64 → Slice) (c : R) (s : JInt64) (n : Nat),
    let a := firstindex c
    let b := lastindex c
    let runRange := fun st =>
      partitionIndexed (m := Jl) (fun x => pure (firstindex x)) (fun x => pure (lastindex x))
        (fun x y => pure (decide (x.val > y.val)))
        (fun x y => pure (x + y)) (fun x y => pure (x - y))
        (fun x y => pure (if y < x then y else x))
        (fun x y => pure (x, y))
        (fun x (lo, hi) => pure (getSlice x lo hi))
        (fun x y => pure (x + y))
        ⟨c, JInt.lit .i64 (Int.ofNat n)⟩ st
    (s.val > b.val → runRange (some s) = .ok none) ∧
    (a.val > b.val → runRange none = .ok none) ∧
    (s.val ≤ b.val → 0 < n → (n : Int) < 2 ^ 63 → -(2 ^ 63) < s.val →
      s.val + (n : Int) < 2 ^ 63 → b.val < 2 ^ 63 - 1 →
      ∃ r r1 : JInt64,
        r.val = min (s.val + (n : Int) - 1) b.val ∧
        r1.val = r.val + 1 ∧
        runRange (some s) = .ok (some (getSlice c s r, r1)))) ∧
  (∀ {R Slice : Type} (firstindex lastindex : R → Int)
    (getSlice : R → Int → Int → Slice) (c : R) (s : Int) (n : Nat),
    s ≤ lastindex c →
      let r := min (s + Int.ofNat n - 1) (lastindex c)
      partitionIndexed (m := Jl) (fun x => pure (firstindex x)) (fun x => pure (lastindex x))
        (fun x y => pure (decide (x > y)))
        (fun x y => pure (x + y.val)) (fun x y => pure (x - y.val))
        (fun x y => pure (min x y))
        (fun x y => pure (x, y))
        (fun x (lo, hi) => pure (getSlice x lo hi))
        (fun x y => pure (x + y.val))
        ⟨c, JInt.lit .i64 (Int.ofNat n)⟩ (some s) =
        .ok (some (getSlice c s r, r + 1))) ∧
  (∀ {A View : Type} (firstindex lastindex : A → Int)
    (view : A → Int → Int → View) (c : A) (s : Int) (n : Nat),
    let a := firstindex c
    let b := lastindex c
    let runVec := fun st =>
      partitionIndexed (m := Jl) (fun x => pure (firstindex x)) (fun x => pure (lastindex x))
        (fun x y => pure (decide (x > y)))
        (fun x y => pure (x + y.val)) (fun x y => pure (x - y.val))
        (fun x y => pure (min x y))
        (fun x y => pure (x, y))
        (fun x (lo, hi) => pure (view x lo hi))
        (fun x y => pure (x + y.val))
        ⟨c, JInt.lit .i64 (Int.ofNat n)⟩ st
    (s > b → runVec (some s) = .ok none) ∧
    (a > b → runVec none = .ok none) ∧
    (s ≤ b →
      let r := min (s + Int.ofNat n - 1) b
      runVec (some s) = .ok (some (view c s r, r + 1)))) ∧
  (∀ {T : Type} (sz : IteratorSizeTag) (it : PartitionIterator T),
    (sourceMethod1461 sz it = .hasLength ↔ (sz = .hasLength ∨ ∃ d, sz = .hasShape d)) ∧
    ((∀ d, sz ≠ .hasShape d) → sourceMethod1461 sz it = sz) ∧
    sourceMethod1455 .hasEltype it = .hasEltype ∧
    sourceMethod1456 it = .eltypeUnknown ∧
    sourceMethod1457 .hasEltype it = .hasEltype) ∧
  (∀ {A V : Type} (vec : A → V) (a : A) (v : V) (n : JInt64) (eltype : Type),
    partitionArray (m := Jl) (fun x => pure (vec x)) a n = .ok ⟨vec a, n⟩ ∧
    sourceMethod1447 v n = ⟨v, n⟩ ∧
    sourceMethod1449 (Elem := Type) (fun _ => eltype) (sourceMethod1447 v n) = .vector eltype ∧
    sourceMethod1451 (Elem := Type) (fun _ => eltype) (sourceMethod1447 v n) = .abstractVector eltype ∧
    sourceMethod1453 (Elem := Type) (fun _ => eltype) (sourceMethod1447 v n) =
      .subArray eltype 1 v .unitRangeInt true) ∧
  (∀ {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (isdone : I → Option S → Jl (Option Bool)) (it : I) (xs : List α) (n : Nat),
    0 < n → n < 2 ^ 60 → followsProtocol iterate isdone it xs →
    let p : PartitionIterator I := ⟨it, JInt.lit .i64 (Int.ofNat n)⟩
    (xs = [] →
      partitionListStep iterate p (.at none) = .ok none) ∧
    (xs ≠ [] →
      ∃ finalState,
        collectPartitionChunk iterate it n none = .ok (xs.take n, finalState) ∧
        partitionListStep iterate p (.at none) =
          .ok (some (xs.take n, match finalState with
            | none => .cutShort
            | some state => .at (some state)))))

def StatefulApproximation : Prop :=
  (∀ (ops : DescriptorOps Type) (itrT vstate : Type),
    let next := ops.returnTypeDoiterate itrT vstate
    (¬ops.subtype vstate ops.stateTupleType →
      approxIterType ops itrT vstate = ops.anyType) ∧
    (ops.subtype vstate ops.stateTupleType →
      ops.subtype vstate ops.bottom →
      approxIterType ops itrT vstate = ops.bottom) ∧
    (ops.subtype vstate ops.stateTupleType →
      ¬ops.subtype vstate ops.bottom →
      ops.subtype itrT ops.bottom →
      approxIterType ops itrT vstate = ops.bottom) ∧
    (ops.subtype vstate ops.stateTupleType →
      ¬ops.subtype vstate ops.bottom →
      ¬ops.subtype itrT ops.bottom →
      (ops.subtype next vstate → approxIterType ops itrT vstate = vstate) ∧
      (¬ops.subtype next vstate → approxIterType ops itrT vstate = ops.anyType))) ∧
  (∀ (ops : DescriptorOps Type) (itrT : Type),
    approxIterTypeInitial ops itrT =
      approxIterType ops itrT (ops.returnTypeIterate itrT))

theorem statefulApproximation : StatefulApproximation := by
  refine ⟨?_, ?_⟩
  · intro ops itrT vstate
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      simp [approxIterType, h]
    · intro hvalid hempty
      simp [approxIterType, hvalid, hempty]
    · intro hvalid hnotempty hbottom
      simp [approxIterType, hvalid, hnotempty, hbottom]
    · intro hvalid hnotempty hnotbottom
      refine ⟨?_, ?_⟩
      · intro hstable
        simp [approxIterType, hvalid, hnotempty, hnotbottom, hstable]
      · intro hunstable
        simp [approxIterType, hvalid, hnotempty, hnotbottom, hunstable]
  · intro ops itrT
    rfl

def StatefulConstructorSemantics : Prop :=
  (∀ {I α S : Type} (run : I → Option S → Jl (Option (α × S)))
      (typeof : I → JuliaLean.base.promotion.PType)
      (stateTuple : JuliaLean.base.promotion.PType)
      (inferIterate : JuliaLean.base.promotion.PType → JuliaLean.base.promotion.PType)
      (inferDoiterate : JuliaLean.base.promotion.PType → JuliaLean.base.promotion.PType → JuliaLean.base.promotion.PType)
      (assertValue : Option (α × S) → JuliaLean.base.promotion.PType → Jl (Option (α × S)))
      (cacheTypeOf : JuliaLean.base.promotion.PType → JuliaLean.base.promotion.PType)
      (itr : I) (result checked : Option (α × S)),
    let types := descriptorOps stateTuple inferIterate inferDoiterate
    run itr none = .ok result →
    assertValue result (approxIterTypeInitial types (typeof itr)) = .ok checked →
      statefulConstructorObservation run typeof types assertValue cacheTypeOf itr =
        .ok
          { itr := itr, nextvalstate := checked,
            cacheType := cacheTypeOf (approxIterTypeInitial types (typeof itr)),
            assertValue := assertValue, cacheTypeOf := cacheTypeOf }) ∧
  (∀ {I α S : Type} (run : I → Option S → Jl (Option (α × S)))
      (typeof : I → JuliaLean.base.promotion.PType)
      (stateTuple : JuliaLean.base.promotion.PType)
      (inferIterate : JuliaLean.base.promotion.PType → JuliaLean.base.promotion.PType)
      (inferDoiterate : JuliaLean.base.promotion.PType → JuliaLean.base.promotion.PType → JuliaLean.base.promotion.PType)
      (assertValue : Option (α × S) → JuliaLean.base.promotion.PType → Jl (Option (α × S)))
      (cacheTypeOf : JuliaLean.base.promotion.PType → JuliaLean.base.promotion.PType)
      (itr : I) (result : Option (α × S)) (error : JlError),
    let types := descriptorOps stateTuple inferIterate inferDoiterate
    run itr none = .ok result →
    assertValue result (approxIterTypeInitial types (typeof itr)) = .error error →
      statefulConstructorObservation run typeof types assertValue cacheTypeOf itr = .error (.julia error)) ∧
  (∀ {I α S : Type} (run : I → Option S → Jl (Option (α × S)))
      (typeof : I → JuliaLean.base.promotion.PType)
      (stateTuple : JuliaLean.base.promotion.PType)
      (inferIterate : JuliaLean.base.promotion.PType → JuliaLean.base.promotion.PType)
      (inferDoiterate : JuliaLean.base.promotion.PType → JuliaLean.base.promotion.PType → JuliaLean.base.promotion.PType)
      (assertValue : Option (α × S) → JuliaLean.base.promotion.PType → Jl (Option (α × S)))
      (cacheTypeOf : JuliaLean.base.promotion.PType → JuliaLean.base.promotion.PType)
      (itr : I) (error : JlError),
    let types := descriptorOps stateTuple inferIterate inferDoiterate
    run itr none = .error error →
      statefulConstructorObservation run typeof types assertValue cacheTypeOf itr = .error (.julia error))

def StatefulMethodSemantics : Prop :=
  StatefulConsistent ∧
  (∀ {α : Type} (xs ys : List α),
    (do
      let s0 ← (statefulAnySnapshot (fun _ st => (listIterator xs).run st) (listIterator xs) : Observation IteratorError _)
      let (out1, s1) ← collectSnapshots (fun _ st => (listIterator xs).run st) (xs.length + 1) s0
      let s2 ← (resetSnapshot (fun _ st => (listIterator xs).run st) s1 : Observation IteratorError _)
      let (out2, s3) ← collectSnapshots (fun _ st => (listIterator xs).run st) (xs.length + 1) s2
      let s4 ← (resetSnapshotTo (fun (it : IteratorModel α Nat) st => it.run st) s3 (listIterator ys) : Observation IteratorError _)
      let (out3, _) ← collectSnapshots (fun _ st => (listIterator ys).run st) (ys.length + 1) s4
      pure (out1, out2, out3)) = .ok (xs, xs, ys)) ∧
  (∀ {α : Type} (xs : List α),
    let s : StatefulSnapshot (IteratorModel α Nat) (α × Nat) := { itr := listIterator xs, nextvalstate := statefulCurAt xs 0 }
    statefulAnySnapshot (fun _ st => (listIterator xs).run st) (listIterator xs) =
      .ok ({ itr := listIterator xs, nextvalstate := statefulCurAt xs 0 } :
        StatefulSnapshot (IteratorModel α Nat) AnyCache (α × Nat)) ∧
    sourceMethod1605 s = s ∧
    sourceMethod1606 (statefulAnySnapshot (fun _ st => (listIterator xs).run st)) (listIterator xs) =
      statefulAnySnapshot (fun _ st => (listIterator xs).run st) (listIterator xs) ∧
    sourceMethod1626 α s = α ∧
    sourceMethod1627 .hasEltype s = .hasEltype) ∧
  (∀ {I α S : Type} (iterate : I → Option S → Jl (Option (α × S))) (itr : I) (x : α) (st : S),
    sourceMethod1592 iterate itr none = .ok none ∧
    sourceMethod1592 iterate itr (some (x, st)) = iterate itr (some st)) ∧
  StatefulApproximation ∧
  StatefulConstructorSemantics ∧
  (∀ (tag : IteratorSizeTag),
    (sourceMethod1625 tag = .isInfinite ↔ tag = .isInfinite) ∧
    (tag ≠ .isInfinite → sourceMethod1625 tag = .sizeUnknown))

theorem nthAdvance_from_trace {α S : Type} (itr : IteratorModel α S) :
    ∀ (xs : List α) (state : Option S) (n : Nat),
      n < xs.length → followsFrom itr state xs →
      ∃ x next, listGet xs n = some x ∧
        (itr.run state >>= nthAdvance itr.run n) = .ok (some (x, next)) := by
  intro xs state n
  induction n generalizing xs state with
  | zero =>
      intro hn htrace
      cases xs with
      | nil => simp at hn
      | cons x rest =>
          obtain ⟨next, hstep, _⟩ := followsFrom_cons itr state x rest htrace
          refine ⟨x, next, ?_, ?_⟩
          · simp [listGet]
          · simp [hstep, nthAdvance]
  | succ n ih =>
      intro hn htrace
      cases xs with
      | nil => simp at hn
      | cons y rest =>
          simp only [List.length_cons] at hn
          have hlt : n < rest.length := by omega
          obtain ⟨next, hstep, htail⟩ := followsFrom_cons itr state y rest htrace
          obtain ⟨x, final, hget, hadv⟩ := ih rest (some next) hlt htail
          refine ⟨x, final, ?_, ?_⟩
          · simpa [listGet] using hget
          · rw [hstep]
            simp only [ok_bind, nthAdvance]
            exact hadv

theorem nthGeneric_from_protocol {I α S : Type}
    (iterate : I → Option S → Jl (Option (α × S)))
    (isdone : I → Option S → Jl (Option Bool)) (itr : I) (xs : List α) (n : Nat)
    (h : followsProtocol iterate isdone itr xs) (hn : n < xs.length) :
    ∃ x, listGet xs n = some x ∧
      nthValue (protocolIterator iterate isdone itr) (Int.ofNat (n + 1)) = .ok x := by
  obtain ⟨x, _, hget, hadv⟩ :=
    nthAdvance_from_trace (protocolIterator iterate isdone itr) xs none n hn h
  have hpos : 0 < Int.ofNat (n + 1) := by simp
  have hsub : (Int.ofNat (n + 1) - 1).toNat = n := by simp
  refine ⟨x, hget, ?_⟩
  rw [nthValue_eq]
  have hnot : ¬ Int.ofNat (n + 1) ≤ 0 := by omega
  rw [if_neg hnot]
  simp only [hsub, except_bind_assoc, hadv, ok_bind, pure_jl]

def OnlyNthMethodSemantics : Prop :=
  OnlyCorrect ∧ NthVectorCorrect ∧
    (∀ {α : Type} (xs : List α), onlyValue (listIterator xs) (fun itr st => itr.run st) = onlyIterator (listIterator xs)) ∧
    (∀ {α : Type} (x : α) (rest : List α),
      onlyValue (listIterator (x :: rest)) (fun itr st => itr.run st) false = .ok x ∧
      onlyValue (listIterator ([] : List α)) (fun itr st => itr.run st) false =
        .error (.methodError "NTuple{2,Any}")) ∧
    (∀ {K V Name α : Type} (d : IdDictModel K V) (xs : List α) (k : Name) (v : α),
      sourceMethod1683 (⟨v⟩ : Tuple1 α) = v ∧
      sourceMethod1687 NamedTuple1.value (⟨k, v⟩ : NamedTuple1 Name α) = v ∧
      (d.entries.length = 1 → ∃ kv, d.entries = [kv] ∧
        onlyFirstValue (fun dict : IdDictModel K V => pure dict.entries.length)
          (fun dict => listLastModel dict.entries) d = .ok kv ∧
        onlyDictValue (fun dict : IdDictModel K V => pure dict.entries.length)
          (fun dict => listLastModel dict.entries) d = .ok kv) ∧
      (d.entries.length ≠ 1 → ∃ m1,
        onlyFirstValue (fun dict : IdDictModel K V => pure dict.entries.length)
          (fun dict => listLastModel dict.entries) d = .error (.argumentError m1) ∧
        onlyDictValue (fun dict : IdDictModel K V => pure dict.entries.length)
          (fun dict => listLastModel dict.entries) d = .error (.argumentError m1)) ∧
      sourceMethod1684 xs =
        .error (.argumentError s!"Tuple contains {xs.length} elements, must contain exactly 1 element") ∧
      sourceMethod1688 xs =
        .error (.argumentError s!"NamedTuple contains {xs.length} elements, must contain exactly 1 element") ∧
      onlyFirstValue (fun ys : List α => pure ys.length) listLastModel xs false = listLastModel xs) ∧
    (∀ {α : Type} (xs : List α) (n : Int), nthValue (listIterator xs) n = nthIterator (listIterator xs) n) ∧
    (∀ {α S : Type} (itr : IteratorModel α S) (n : Int), nthCurry n (fun it k => nthIterator it k) itr = nthIterator itr n) ∧
    (∀ {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
      (isdone : I → Option S → Jl (Option Bool)) (itr : I) (xs : List α) (n : Nat),
      followsProtocol iterate isdone itr xs → n < xs.length →
      ∃ x, listGet xs n = some x ∧
        nthValue (protocolIterator iterate isdone itr) (Int.ofNat (n + 1)) = .ok x) ∧
    (∀ {α : Type} (xs ys : List α) (n : Int),
      if 1 ≤ n ∧ n ≤ min xs.length ys.length then
        ∃ x y, listGet xs (n.toNat - 1) = some x ∧ listGet ys (n.toNat - 1) = some y ∧
          nthZipValues [listIterator xs, listIterator ys] n = .ok [x, y]
      else
        nthZipValues [listIterator xs, listIterator ys] n = .error .boundsError) ∧
    (∀ {α : Type} (xs : List α) (cycles : Nat) (n : Int),
      (xs.length : Int) < 2 ^ 63 → (cycles : Int) < 2 ^ 63 → (xs.length : Int) * (cycles : Int) < 2 ^ 63 →
      let ftr : Flatten (Take (Repeated (IteratorModel α Nat))) :=
        ⟨⟨repeatedModel (listIterator xs), JInt.lit .i64 cycles⟩⟩
      let call := nthFiniteDispatchValue .hasLength ftr n
        (fun _ it k => nthFiniteCycleValue
          (fun o => Except.map (fun (l : Nat) => JInt.lit .i64 (Int.ofNat l)) o.length)
          (fun o idx => nthIterator o idx) it k)
      if 0 < xs.length ∧ 1 ≤ n ∧ n ≤ (xs.length : Int) * (cycles : Int) then
        ∃ x, listGet xs ((n.toNat - 1) % xs.length) = some x ∧ call = .ok x
      else
        call = .error .boundsError) ∧
    (∀ {α : Type} (xs : List α) (n : Int),
      (xs = [] →
        nthCycleDispatchValue .hasLength (cycleModel (listIterator xs)) n
          (fun _ c k => nthCycleValue (fun it => it.length) nthIterator c k) = .error .boundsError) ∧
      (0 < xs.length → n ≤ 0 →
        nthCycleDispatchValue .hasLength (cycleModel (listIterator xs)) n
          (fun _ c k => nthCycleValue (fun it => it.length) nthIterator c k) = .error .boundsError) ∧
      (0 < xs.length → 0 < n →
        ∃ x, listGet xs ((n.toNat - 1) % xs.length) = some x ∧
          nthCycleDispatchValue .hasLength (cycleModel (listIterator xs)) n
            (fun _ c k => nthCycleValue (fun it => it.length) nthIterator c k) = .ok x))


inductive TrueLen where
  | fin (n : Nat)
  | inf
  deriving Repr, DecidableEq

def AgreeSize : IteratorSizeTag → TrueLen → Prop
  | .hasLength, .fin _ => True
  | .hasShape _, .fin _ => True
  | .isInfinite, .inf => True
  | .sizeUnknown, _ => True
  | _, _ => False

def TrueLen.min : TrueLen → TrueLen → TrueLen
  | .fin a, .fin b => .fin (Nat.min a b)
  | .fin a, .inf => .fin a
  | .inf, l => l

def zipTrueLen : List TrueLen → TrueLen
  | [] => .inf
  | l :: ls => TrueLen.min l (zipTrueLen ls)

def AgreeSizeAll : List IteratorSizeTag → List TrueLen → Prop
  | [], [] => True
  | a :: as, l :: ls => AgreeSize a l ∧ AgreeSizeAll as ls
  | _, _ => False

theorem agree_zipIteratorSizePair (a b : IteratorSizeTag) (la lb : TrueLen)
    (ha : AgreeSize a la) (hb : AgreeSize b lb) :
    AgreeSize (zipIteratorSizePair a b) (TrueLen.min la lb) := by
  cases a <;> cases b <;> cases la <;> cases lb <;>
    try simp_all [zipIteratorSizePair, AgreeSize, TrueLen.min]
  rename_i m n _ _
  by_cases h : m = n <;> simp [h]



theorem promoteSizeShape1D_single (m n : Nat) :
    promoteSizeShape1D [m] [n] = .ok [min m n] := by
  simp [promoteSizeShape1D, sourceMethod415, Int.min_def]
  by_cases h : m ≤ n
  · simp [h]
  · simp [h, Nat.min_def]
def ZipMetadata : Prop :=
  (sourceMethod394 (m := Jl) (L := Nat) = .ok none) ∧
  (∀ {α : Type} (xs ys : List α),
    let inf : IteratorModel α Nat := { listIterator xs with iteratorSize := .isInfinite }
    homogeneousZipMinimum (listIterator xs) [inf, listIterator ys] =
      .ok (some (min xs.length ys.length)) ∧
    homogeneousZipMinimum inf [inf] = .ok none) ∧
  (∀ {α β : Type} (xs : List α) (ys : List β),
    (zipListObservation (xs.map Sum.inl) (ys.map Sum.inr)).length = .ok (min xs.length ys.length)) ∧
  (∀ {α : Type} (xs ys : List α),
    zipLengthsFiniteEqual [listIterator xs, listIterator ys] =
      .ok (decide (xs.length = ys.length), some xs.length) ∧
    zipLengthsFiniteEqualEmpty = (true, none)) ∧
  (∀ {α : Type} (xs ys zs : List α),
    zipSizeValues (fun itr => itr.size) promoteSizeShape1D
      (zipModel [listIterator xs, listIterator ys]) = .ok [min xs.length ys.length] ∧
    zipAxesValues (fun itr => itr.size) (promoteAxesShape1D min)
      (zipModel [listIterator xs, listIterator ys]) = .ok [min xs.length ys.length] ∧
    zipSizeValues (fun itr => itr.size) promoteSizeShape1D
      (zipModel [listIterator xs, listIterator ys, listIterator zs]) =
        .ok [min xs.length (min ys.length zs.length)] ∧
    zipAxesValues (fun itr => itr.size) (promoteAxesShape1D min)
      (zipModel [listIterator xs, listIterator ys, listIterator zs]) =
        .ok [min xs.length (min ys.length zs.length)] ∧
    zipSizeValues (fun itr => itr.size) promoteSizeShape1D
      (zipModel ([] : List (IteratorModel α Nat))) =
        .error (.methodError "_promote_tuple_shape") ∧
    zipAxesValues (fun itr => itr.size) (promoteAxesShape1D min)
      (zipModel ([] : List (IteratorModel α Nat))) =
        .error (.methodError "_promote_tuple_shape")) ∧
  (∀ {A : Type} (promoteShape : List A → List A → Jl (List A)) (a b : List A) (m n : Nat)
    (intersect : Nat → Nat → Nat) (mi ni : Int),
    sourceMethod414 (m := Id) intersect m n = [intersect m n] ∧
    sourceMethod415 (m := Id) (fun a b : Int => (min a b : Int)) mi ni = [min mi ni] ∧
    sourceMethod416 promoteShape a b = promoteShape a b ∧
    sourceMethod417 (Kind := Unit) (ks := [()])
      (promoteTupleShape2 (fun _ => (none : Option Empty)) Empty.elim (fun e _ => pure e)
        (fun _ => (none : Option Empty)) Empty.elim (fun e _ => pure e) promoteShape)
      a (.cons b .nil) = promoteShape a b ∧
    sourceMethod418 a = a) ∧
  (∀ {Is T : Type} (fieldTypes : Is → List T) (eltype : T → Type)
    (tupleOrBottom : List Type → Type) (z : Zip Is),
    sourceMethod425 fieldTypes eltype tupleOrBottom z = tupleOrBottom ((fieldTypes z.is).map eltype)) ∧
  (∀ {α : Type} (xs ys : List α),
    let call := sourceMethod519 (zipModel [listIterator xs, listIterator ys])
      (fun z => Except.map Int.ofNat (homogeneousZipLength z))
      (fun z n => nthZipValues z.is n)
    if 0 < min xs.length ys.length then
      ∃ x y, listGet xs (min xs.length ys.length - 1) = some x ∧
        listGet ys (min xs.length ys.length - 1) = some y ∧
        call = .ok [x, y]
    else
      call = .error .boundsError)


def LengthHelpersSpec : Prop :=
  (∀ {α : Type} (xs ys : List α),
    minLengthFinite (m := Jl) (fun l => pure l.length) (fun l => pure l.length)
      (fun m n => pure (min m n)) xs ys =
      .ok (List.zipWith Prod.mk xs ys).length ∧
    (diffLengthFinite (m := Jl) (fun l => pure l.length) (fun l => pure l.length)
      (fun m n => pure (decide (m > n))) (fun m n => pure (m - n))
      (fun n m => pure (n - m)) (fun _ => pure 0) xs ys).map (Sum.elim id id) =
      .ok (xs.drop ys.length).length) ∧
  (∀ (a b : Nat),
    minLengthBothInfinite (m := Jl) pure pure (fun m n => pure (min m n)) a b = .ok (min a b)) ∧
  (∀ (a b : Nat),
    minLengthRightInfinite (m := Jl) pure a b = .ok a) ∧
  (∀ (a b : Nat),
    minLengthLeftInfinite (m := Jl) pure a b = .ok b) ∧
  (∀ (a b : Nat),
    minLengthFinite (m := Jl) pure pure (fun m n => pure (min m n)) a b = .ok (min a b)) ∧
  (∀ (a b : Nat), (diffLengthRightInfinite a b).val = 0) ∧
  (∀ (a b : Nat), (diffLengthBothInfinite a b).val = 0) ∧
  (∀ (a b : Nat),
    diffLengthLeftInfinite (m := Jl) pure a b = .ok a) ∧
  (∀ (a b : Nat),
    (diffLengthFinite (m := Jl) pure pure (fun m n => pure (decide (m > n)))
      (fun m n => pure (m - n)) (fun n m => pure (n - m)) (fun _ => pure 0)
      a b).map (Sum.elim id id) = .ok (a - b))

def TakeSound : Prop :=
  TakeTakeCorrect ∧
  (∀ {α : Type} (xs : List α) (n : JInt64), 0 ≤ n.val →
    let base := listIterator xs
    emitsExactly (takeObservation base ⟨base, n⟩) (xs.take n.val.toNat)) ∧
  (∀ {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (isdone : I → Option S → Jl (Option Bool)) (it : I) (xs : List α) (n : JInt64), 0 ≤ n.val →
    followsProtocol iterate isdone it xs →
    emitsExactly
      (takeObservation (protocolIterator iterate isdone it)
        ⟨protocolIterator iterate isdone it, n⟩)
      (xs.take n.val.toNat)) ∧
  (∀ {I : Type} (xs : I) (n : JInt64), 0 ≤ n.val →
    CountValue.rawTake xs n.val = .ok ⟨xs, n⟩ ∧
    CountValue.take xs n.val = .ok ⟨xs, n⟩) ∧
  (∀ {I : Type} (xs : I) (n : Int),
    (n < 0 → CountValue.rawTake xs n = .error (.argumentError "Take length must be non-negative")) ∧
    (2 ^ 63 ≤ n → CountValue.rawTake xs n = .error (.inexactError "Int64") ∧
      CountValue.take xs n = .error (.inexactError "Int64"))) ∧
  (∀ {I : Type} (it : IteratorSizeTag) (eltype : Type) (iel : I → IteratorEltypeTag)
    (isz : I → IteratorSizeTag) (t : Take I),
    takeEltype eltype t = eltype ∧
    takeIteratorEltype iel t = iel t.xs ∧
    takeIteratorSize it = .hasLength ∧
    takeIteratorSizeUnknown it = .sizeUnknown ∧
    (takeIteratorSizeOf isz t = .sizeUnknown ↔ isz t.xs = .sizeUnknown) ∧
    (isz t.xs ≠ .sizeUnknown → takeIteratorSizeOf isz t = .hasLength)) ∧
  (∀ {α : Type} (xs : List α) (n rem : JInt64) (i : Nat), 0 ≤ n.val → 0 ≤ rem.val →
    let itr := takeObservation (listIterator xs) ⟨listIterator xs, n⟩
    itr.isdone (some (rem, i)) = .ok (some (decide (rem.val = 0 ∨ xs.length ≤ i))) ∧
    (itr.isdone (some (rem, i)) = .ok (some true) ↔ itr.run (some (rem, i)) = .ok none))

def DropSound : Prop :=
  (∀ {α : Type} (xs : List α) (n : JInt64), 0 ≤ n.val →
    let base := listIterator xs
    emitsExactly (dropObservation base ⟨base, n⟩) (xs.drop n.val.toNat)) ∧
  (∀ {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (isdone : I → Option S → Jl (Option Bool)) (it : I) (xs : List α) (n : JInt64), 0 ≤ n.val →
    followsProtocol iterate isdone it xs →
    emitsExactly
      (dropObservation (protocolIterator iterate isdone it)
        ⟨protocolIterator iterate isdone it, n⟩)
      (xs.drop n.val.toNat)) ∧
  (∀ {I : Type} (xs : I) (n : JInt64), 0 ≤ n.val →
    CountValue.rawDrop xs n.val = .ok ⟨xs, n⟩ ∧
    CountValue.drop xs n.val = .ok ⟨xs, n⟩) ∧
  (∀ {I : Type} (xs : I) (n : Int),
    (n < 0 → CountValue.rawDrop xs n = .error (.argumentError "Drop length must be non-negative")) ∧
    (2 ^ 63 ≤ n → CountValue.rawDrop xs n = .error (.inexactError "Int64") ∧
      CountValue.drop xs n = .error (.inexactError "Int64"))) ∧
  (∀ {α : Type} (xs : List α) (a : Nat) (b : JInt64), a < 2 ^ 63 → 0 ≤ b.val →
    ∃ td, CountValue.dropTake (JInt.convert (IntTy.i64.name) .i64) (fun it k => CountValue.drop it k.val) ⟨listIterator xs, JInt.lit .i64 a⟩ b.val = .ok td ∧
      emitsExactly (dropTakeObservation (listIterator xs) td) ((xs.drop b.val.toNat).take (a - b.val.toNat))) ∧
  (∀ {I D : Type} (xs : I) (a : Nat) (b : JInt64) (dropInner : I → Int → Jl D) (d : D),
    a < 2 ^ 63 → 0 ≤ b.val → dropInner xs b.val = .ok d →
    CountValue.dropTake (JInt.convert (IntTy.i64.name) .i64) (fun it k => dropInner it k.val) ⟨xs, JInt.lit .i64 a⟩ b.val = .ok ⟨d, JInt.lit .i64 (Int.ofNat (a - b.val.toNat))⟩) ∧
  (∀ {I : Type} (xs : I) (a : Nat) (b : JInt64), b.val < 0 →
    CountValue.dropTake (JInt.convert (IntTy.i64.name) .i64) (fun it k => CountValue.drop it k.val) ⟨xs, JInt.lit .i64 a⟩ b.val =
      .error (.argumentError "Drop length must be non-negative")) ∧
  (∀ {I : Type} (xs : I) (a b : Nat), a + b < 2 ^ 63 →
    CountValue.dropDrop ⟨xs, JInt.lit .i64 a⟩ (Int.ofNat b) = .ok ⟨xs, JInt.lit .i64 (Int.ofNat (a + b))⟩) ∧
  (∀ {I S : Type} (it : IteratorSizeTag) (eltype : Type) (iel : I → IteratorEltypeTag)
    (isz : I → IteratorSizeTag) (isdone : I → Option S → Jl (Option Bool)) (d : Drop I) (s : S),
    dropEltype eltype d = eltype ∧
    dropIteratorEltype iel d = iel d.xs ∧
    isdoneDrop isdone d s = isdone d.xs (some s) ∧
    dropIteratorSizeFinite it = .hasLength ∧
    dropIteratorSizeUnknown it = .sizeUnknown ∧
    dropIteratorSizeInfinite it = .isInfinite ∧
    (dropIteratorSizeOf isz d = .isInfinite ↔ isz d.xs = .isInfinite) ∧
    (dropIteratorSizeOf isz d = .sizeUnknown ↔ isz d.xs = .sizeUnknown))

def CountfromInts : Prop :=
  ∀ (start step : JInt64) (depth : Nat),
    let count := countNumbers (m := Jl) (fun a b => .ok (a, b)) start step
    match count with
    | .error _ => False
    | .ok c =>
        countEltype c = JInt64 ∧
        observeRun (countAsIterator JuliaLean.base.int.add_int c).run depth none =
          .ok (r6WrappedCountProgression c.start c.step depth)

private theorem countAsIteratorRun {T S : Type} (add : T → S → T)
    (it : Count T S) (state : Option T) :
    (countAsIterator add it).run state =
      .ok (some (state.getD it.start, add (state.getD it.start) it.step)) := by
  simp [countAsIterator, iterateCountState]

private theorem observeCountAsIterator {T S : Type}
    (add : T → S → T) (it : Count T S) :
    ∀ depth state,
      observeRun (countAsIterator add it).run depth state =
        .ok (countChainGen add (state.getD it.start) it.step depth) := by
  intro depth
  induction depth with
  | zero =>
      intro state
      rfl
  | succ depth ih =>
      intro state
      simp [observeRun, countAsIteratorRun, ih, countChainGen]

private theorem countChainGenInt_eq_r6 (start step : JInt64) :
    ∀ depth,
      countChainGen JuliaLean.base.int.add_int start step depth =
        r6WrappedCountProgression start step depth := by
  intro depth
  induction depth generalizing start with
  | zero => rfl
  | succ depth ih =>
      simp [countChainGen, r6WrappedCountProgression, ih]

theorem countfromInts_proven : CountfromInts := by
  intro start step depth
  change
    countEltype (⟨start, step⟩ : Count JInt64 JInt64) = JInt64 ∧
    observeRun
      (countAsIterator JuliaLean.base.int.add_int
        (⟨start, step⟩ : Count JInt64 JInt64)).run depth none =
      .ok (r6WrappedCountProgression start step depth)
  constructor
  · rfl
  · rw [← countChainGenInt_eq_r6 start step depth]
    exact observeCountAsIterator JuliaLean.base.int.add_int
      (⟨start, step⟩ : Count JInt64 JInt64) depth none


def FilterSound : Prop :=
  ∀ {α : Type} (xs : List α) (predicate : α → Bool) (depth : Nat),
    observeRun (filterObservation (listIterator xs) predicate).run depth none =
      .ok ((xs.filter predicate).take depth)
private theorem action_observeJl {α : Type} (result : Jl α) :
    action (observeJl result) = liftJl result := by
  cases result <;> rfl

private def filterListNext {α : Type} (predicate : α → Bool) :
    List α → Option (α × Nat × List α)
  | [] => none
  | x :: rest =>
      if predicate x then some (x, 1, rest)
      else
        match filterListNext predicate rest with
        | none => none
        | some (y, n, tail) => some (y, n + 1, tail)

private def filterListNextAt {α : Type} (predicate : α → Bool)
    (i : Nat) (xs : List α) : Option (α × Nat) :=
  match filterListNext predicate xs with
  | none => none
  | some (x, n, _) => some (x, i + n)

private theorem filterListNext_spec {α : Type} (predicate : α → Bool) :
    ∀ (xs : List α),
      match filterListNext predicate xs with
      | none => xs.filter predicate = []
      | some (x, n, tail) =>
          xs.filter predicate = x :: tail.filter predicate ∧ xs.drop n = tail := by
  intro xs
  induction xs with
  | nil => simp [filterListNext]
  | cons x rest ih =>
      by_cases hp : predicate x
      · simp [filterListNext, hp]
      · cases h : filterListNext predicate rest with
        | none =>
            simpa [filterListNext, hp, h] using ih
        | some hit =>
            rcases hit with ⟨y, n, tail⟩
            have hspec : rest.filter predicate = y :: tail.filter predicate ∧
                rest.drop n = tail := by
              simpa [h] using ih
            simp [filterListNext, hp, h, hspec, List.drop_succ_cons]

private theorem filterScan_listDrop {α : Type} (xs : List α)
    (predicate : α → Bool) :
    ∀ (i : Nat) (ys : List α), xs.drop i = ys →
      filterScan (fun it st => liftJl (it.run st)) ret
        (fun f x => ret (f x)) (fun _ => true) Prod.mk
        ⟨predicate, listIterator xs⟩ (some i) =
          fun _ => some (.ok (filterListNextAt predicate i ys), ()) := by
  intro i ys hdrop
  funext heap
  cases heap
  induction ys generalizing i with
  | nil =>
      rw [filterScan.eq_def]
      simp [liftJl, Pure.pure, ret, listIterator_run_some, hdrop,
        filterListNextAt, filterListNext]
  | cons x rest ih =>
      have hdropNext : xs.drop (i + 1) = rest := by
        rw [← List.drop_drop, hdrop]
        rfl
      by_cases hp : predicate x
      · rw [filterScan.eq_def]
        simp [liftJl, Pure.pure, ret, listIterator_run_some, hdrop, hp,
          filterListNextAt, filterListNext]
      · rw [filterScan.eq_def]
        simp [liftJl, ret, listIterator_run_some, hdrop, hp]
        rw [ih (i + 1) hdropNext]
        cases hnext : filterListNext predicate rest with
        | none => simp [filterListNextAt, filterListNext, hp, hnext]
        | some hit =>
            rcases hit with ⟨y, n, tail⟩
            simp [filterListNextAt, filterListNext, hp, hnext]
            omega

private theorem filterStep_listDrop {α : Type} (xs : List α)
    (predicate : α → Bool) :
    ∀ (i : Nat) (ys : List α), xs.drop i = ys →
      filterStep (fun f x => f x) (fun it st => it.run st)
        ⟨predicate, listIterator xs⟩ (some i) =
          .ok (filterListNextAt predicate i ys) := by
  intro i ys hdrop
  change observe
      (filterScan (fun it st => liftJl (it.run st)) ret
        (fun f x => ret (f x)) (fun _ => true) Prod.mk
        ⟨predicate, listIterator xs⟩ (some i)) =
    .ok (filterListNextAt predicate i ys)
  rw [filterScan_listDrop xs predicate i ys hdrop]
  rfl

private theorem filterObservation_run_list {α : Type} (xs : List α)
    (predicate : α → Bool) (st : Option Nat) :
    (filterObservation (listIterator xs) predicate).run st =
      filterStep (fun f x => f x) (fun it state => it.run state)
        ⟨predicate, listIterator xs⟩ st := by
  cases st <;>
    simp [filterObservation, filterStep, AsObservation.view, action_observeJl]

private theorem filterListRun_sound {α : Type} (xs : List α)
    (predicate : α → Bool) :
    ∀ (depth : Nat) (i : Nat),
      observeRun (filterObservation (listIterator xs) predicate).run depth (some i) =
        .ok (((xs.drop i).filter predicate).take depth) := by
  intro depth
  induction depth with
  | zero =>
      intro i
      rfl
  | succ depth ih =>
      intro i
      rw [observeRun, filterObservation_run_list,
        filterStep_listDrop xs predicate i (xs.drop i) rfl]
      cases hnext : filterListNext predicate (xs.drop i) with
      | none =>
          have hspec : (xs.drop i).filter predicate = [] := by
            simpa [hnext] using filterListNext_spec predicate (xs.drop i)
          simp [filterListNextAt, hnext, hspec, Bind.bind, Pure.pure]
      | some hit =>
          rcases hit with ⟨x, n, tail⟩
          have hspec : (xs.drop i).filter predicate = x :: tail.filter predicate ∧
              (xs.drop i).drop n = tail := by
            simpa [hnext] using filterListNext_spec predicate (xs.drop i)
          have hstate : xs.drop (i + n) = tail := by
            calc
              xs.drop (i + n) = (xs.drop i).drop n := by rw [← List.drop_drop]
              _ = tail := hspec.2
          simp only [filterListNextAt, hnext, Bind.bind, Pure.pure]
          rw [ih (i + n), hstate]
          simp [hspec.1, List.take_succ_cons]

private theorem observeRun_initial_eq {α S : Type} {m : Type → Type}
    [Monad m] (run : Option S → m (Option (α × S)))
    (initial next : Option S) (hrun : run initial = run next) (depth : Nat) :
    observeRun run depth initial = observeRun run depth next := by
  cases depth with
  | zero => rfl
  | succ depth => simp [observeRun, hrun]

theorem filterSound_proven : FilterSound := by
  intro α xs predicate depth
  have hrun :
      (filterObservation (listIterator xs) predicate).run none =
        (filterObservation (listIterator xs) predicate).run (some 0) := by
    rw [filterObservation_run_list, filterObservation_run_list]
    change observe
        (filterScan (fun it st => liftJl (it.run st)) ret
          (fun f x => ret (f x)) (fun _ => true) Prod.mk
          ⟨predicate, listIterator xs⟩ none) =
      observe
        (filterScan (fun it st => liftJl (it.run st)) ret
          (fun f x => ret (f x)) (fun _ => true) Prod.mk
          ⟨predicate, listIterator xs⟩ (some 0))
    congr 1
    funext heap
    cases heap
    rw [filterScan.eq_def, filterScan.eq_def]
    simp [liftJl, listIterator_run_none]
  rw [observeRun_initial_eq _ none (some 0) hrun depth]
  exact filterListRun_sound xs predicate depth 0

def AccumulateSound : Prop :=
  AccumulateCorrect ∧
  (∀ {I T N : Type} {F : Type}
      (length size : I → Jl N) (trait : I → IteratorSizeTag)
      (f : F) (itr : I) (init : T),
    let a := accumulateModel f itr init
    accumulateLength length a = length itr ∧
    accumulateSize size a = size itr ∧
    accumulateIteratorSize trait a = trait itr ∧
    accumulateIteratorEltype = .eltypeUnknown) ∧
  (∀ {I α β S H : Type} (run : I → Option S → Jl (Option (α × S)))
      (rf : JuliaLean.base.reduce.Reducer (Exec JlError H β) α)
      (init : JuliaLean.base.reduce.FoldInit (Exec JlError H β))
      (itr : I) (xs : List α) (final : Option S) (heap : H),
    Round4.History (fun st => run itr st) none xs final →
      collectAccumulateNative (fun i st h => some (run i st, h))
        rf init itr xs.length none heap = accumulationPrefixSpec rf init xs xs.length heap) ∧
  (∀ {I α β S H : Type} (run : I → Option S → Jl (Option (α × S)))
      (rf : JuliaLean.base.reduce.Reducer (Exec JlError H β) α)
      (init : JuliaLean.base.reduce.FoldInit (Exec JlError H β))
      (itr : I) (previous : JuliaLean.base.reduce.FoldInit β) (state : S)
      (xs : List α) (final : Option S) (heap : H),
    Round4.History (fun st => run itr st) (some state) xs final →
      collectAccumulateNative (fun i st h => some (run i st, h))
        rf init itr xs.length (some (previous, state)) heap =
          callablePrefixScan rf xs.length previous xs heap)

def WhileSound : Prop :=
  TakeWhileDropWhile ∧
  (∀ {I P : Type} (pred : P) (xs : I) (eltype : Type) (iel : I → IteratorEltypeTag),
    let tw := takewhileModel pred xs
    let dw := dropwhileModel pred xs
    takewhileIteratorSize = .sizeUnknown ∧
    takewhileEltype eltype tw = eltype ∧
    takewhileIteratorEltype iel tw = iel xs ∧
    dropwhileIteratorSize = .sizeUnknown ∧
    dropwhileEltype eltype dw = eltype ∧
    dropwhileIteratorEltype iel dw = iel xs)

theorem enumerateLast_eq {α : Type} (xs : List α) :
    enumerateLast (fun ys => pure ys.length) listLastModel (enumerateModel xs) =
      listLastModel (enumerateNatFrom 1 xs) := by
  unfold enumerateLast enumerateModel
  simp only [pure_jl, ok_bind]
  cases hxs : xs.reverse with
  | nil =>
    have hnil : xs = [] := List.reverse_eq_nil_iff.mp hxs
    subst hnil
    rfl
  | cons lastX revRest =>
    have hlen : 0 < xs.length := by
      cases xs with
      | nil => simp at hxs
      | cons _ _ => simp
    obtain ⟨m, hm⟩ : ∃ m, xs.length = m + 1 := ⟨xs.length - 1, by omega⟩
    obtain ⟨x, hx, hrev⟩ := listGet_take_last xs m (by omega)
    have hrev_enum := enumerateNatFrom_take_succ xs 1 m x hx (by omega)
    have h1m : 1 + m = m + 1 := by omega
    rw [h1m, ← hm, List.take_length] at hrev_enum
    rw [← hm, List.take_length] at hrev
    have hlast_xs : listLastModel xs = .ok x := by
      have hre : xs = xs.reverse.reverse := (List.reverse_reverse _).symm
      rw [hre, hrev, List.reverse_cons, listLastModel_append_singleton]
    have hlast_enum : listLastModel (enumerateNatFrom 1 xs) = .ok (xs.length, x) := by
      have hre : enumerateNatFrom 1 xs = (enumerateNatFrom 1 xs).reverse.reverse :=
        (List.reverse_reverse _).symm
      rw [hre, hrev_enum, List.reverse_cons, listLastModel_append_singleton]
    rw [hlast_xs, ok_bind, hlast_enum]

def EnumerateSound : Prop :=
  EnumerateCorrect ∧
  (∀ {α : Type} (xs : List α),
    let e := enumerateModel (listIterator xs)
    emitsExactly (reverseEnumerateAsIterator xs)
      (((enumerateNatFrom 1 xs).reverse).map fun (i, v) => (JInt.lit .i64 (Int.ofNat i), v)) ∧
    enumerateLast (fun ys => pure ys.length) listLastModel (enumerateModel xs) =
      listLastModel (enumerateNatFrom 1 xs) ∧
    enumerateLength (fun i => i.length) e = .ok xs.length ∧
    enumerateSize (fun i => i.size) e = .ok [xs.length] ∧
    enumerateIteratorSize (fun i => i.iteratorSize) e = .hasLength ∧
    enumerateIteratorEltype (fun i => i.iteratorEltype) e = .hasEltype ∧
    enumerateEltype (fun _ => some α) tupleOrBottomPair e = some (JInt64 × α) ∧
    enumerateEltype (fun _ => none) tupleOrBottomPair e = none) ∧
  (∀ {I α N : Type} (length : I → Jl N) (size : I → Jl (List N)) (last : I → Jl α)
    (isz : I → IteratorSizeTag) (iel : I → IteratorEltypeTag) (itr : I),
    let e := enumerateModel itr
    enumerateLength length e = length itr ∧
    enumerateSize size e = size itr ∧
    enumerateLast length last e = (do pure ((← length itr), (← last itr))) ∧
    enumerateIteratorSize isz e = isz itr ∧
    enumerateIteratorEltype iel e = iel itr)


def ReverseYields : Prop :=
  ∀ {α β N : Type} [IsNumberOrAbstractChar N] (xs : List α) (f : α → β) (n : N) (a : α) (b : β),
    emitsExactly (reverseListAsIterator xs) xs.reverse ∧
    emitsExactly (reverseArrayAsIterator xs) xs.reverse ∧
    emitsExactly (reverseGenericAsIterator xs) xs.reverse ∧
    emitsExactly (reverseListAsIterator xs.reverse) xs ∧
    emitsExactly
      (generatorAsIterator (fun f x => pure (f x))
        (sourceMethod157 (m := Id) (fun _ => listIterator xs.reverse) ⟨f, listIterator xs⟩))
      (xs.map f).reverse ∧
    reverseUnwrap (reverseDefault xs) = xs ∧
    sourceMethod156 (m := Id) List.reverse xs = xs.reverse ∧
    sourceMethod159 n = n ∧
    sourceMethod160 Prod.swap (a, b) = (b, a) ∧
    sourceMethod160 Prod.swap (sourceMethod160 Prod.swap (a, b)) = (a, b) ∧
    sourceMethod153 (fun message => .error (.argumentError message)) ⟨.bottom⟩ =
      (.error (.argumentError "cannot iterate a reversed iterator of type Union{}") : Jl (Option (α × Nat))) ∧
    (∀ s : Nat, sourceMethod154 (fun message => .error (.argumentError message)) ⟨.bottom⟩ s =
      (.error (.argumentError "cannot iterate a reversed iterator of type Union{}") : Jl (Option (α × Nat))))

def ReverseTraits : Prop :=
  (∀ {α : Type} (xs : List α),
    emitsExactly (reverseListAsIterator xs.reverse) xs ∧
    reverseEltype α (reverseDefault xs) = α ∧
    reverseIteratorSize (fun _ => IteratorSizeTag.hasLength) (reverseDefault xs) = .hasLength ∧
    reverseIteratorEltype (fun _ => IteratorEltypeTag.hasEltype) (reverseDefault xs) = .hasEltype ∧
    reverseLength (fun ys => pure ys.length) (reverseDefault xs) = .ok xs.length ∧
    reverseSize (fun ys => pure [ys.length]) (reverseDefault xs) = .ok [xs.length] ∧
    reverseLast (fun ys : List α => (ys.head?).elim (.error .boundsError) pure) (reverseDefault xs) =
      listLastModel xs.reverse ∧
    sourceMethod153 (fun message => .error (.argumentError message)) ⟨.bottom⟩ =
      (.error (.argumentError "cannot iterate a reversed iterator of type Union{}") : Jl (Option (α × Nat))) ∧
    (∀ s : Nat, sourceMethod154 (fun message => .error (.argumentError message)) ⟨.bottom⟩ s =
      (.error (.argumentError "cannot iterate a reversed iterator of type Union{}") : Jl (Option (α × Nat))))) ∧
  (∀ {I α N : Type} (length : I → Jl N) (size : I → Jl (List N)) (first : I → Jl α)
    (isz : I → IteratorSizeTag) (iel : I → IteratorEltypeTag) (itr : I),
    let r := reverseDefault itr
    reverseEltype α r = α ∧
    reverseLength length r = length itr ∧
    reverseSize size r = size itr ∧
    reverseIteratorSize isz r = isz itr ∧
    reverseIteratorEltype iel r = iel itr ∧
    reverseLast first r = first itr)

def ZipProtocol : Prop :=
  (∀ {I S : Type} (isdone : I → Option S → Jl (Option Bool))
      (cs : List (I × Option S)),
    (∀ c ∈ cs, isdone c.1 c.2 = .ok (some false)) →
      zipAnyDoneObservation isdone cs = .ok (some false)) ∧
  (∀ {I S : Type} (isdone : I → Option S → Jl (Option Bool))
      (itr : I) (state : Option S) (rest : List (I × Option S)),
    isdone itr state = .ok (some true) →
      zipAnyDoneObservation isdone ((itr, state) :: rest) = .ok (some true)) ∧
  (∀ {I α S : Type} (iterate : I → Option S → Jl (Option (α × S))),
    zipOrderObservation iterate [] = .ok (some ([], []))) ∧
  (∀ {α : Type} (xs ys : List α) (i j : Nat),
    let factors := [listIterator xs, listIterator ys]
    let done := fun (itr : IteratorModel α Nat) st => itr.isdone st
    let run := fun (itr : IteratorModel α Nat) st => itr.run st
    zipAnyDoneObservation done (factors.map (fun itr => (itr, none))) =
      .ok (some (decide (xs.length ≤ 0 ∨ ys.length ≤ 0))) ∧
    zipAnyDoneObservation done [(listIterator xs, some i), (listIterator ys, some j)] =
      .ok (some (decide (xs.length ≤ i ∨ ys.length ≤ j))) ∧
    zipDoneScanObservation done [(listIterator xs, some i), (listIterator ys, some j)] =
      .ok (decide (xs.length ≤ i ∨ ys.length ≤ j),
        [some (decide (xs.length ≤ i)), some (decide (ys.length ≤ j))]) ∧
    observeJl (zipAllObservation done run (factors.map (fun itr => (itr, none)))) =
      projectZipState ((zipListObservation xs ys).run none) ∧
    observeJl (zipAllObservation done run [(listIterator xs, some i), (listIterator ys, some j)]) =
      projectZipState ((zipListObservation xs ys).run (some (.cons i (.cons j .nil)))) ∧
    observeJl (zipAllObservation done run (List.zip factors [some i, some j])) =
      projectZipState ((zipListObservation xs ys).run (some (.cons i (.cons j .nil))))) ∧
  (∀ {I α S : Type} (is : List I) (states : List (Option S))
      (isdone : I → Option S → Jl (Option Bool))
      (iterate : I → Option S → Jl (Option (α × S))),
    is.length = states.length →
    (∀ itr st, isdone itr st = .ok none) →
    zipDoneScanObservation isdone (List.zip is states) = .ok (false, List.replicate is.length none) ∧
    allMissingObservation (List.replicate is.length none) = true ∧
    zipAllObservation isdone iterate (List.zip is states) = zipOrderObservation iterate (List.zip is states))

namespace Round4


def observe {α S : Type} [Monad m] (run : Option S → m (Option (α × S))) :
    Nat → Option S → m (List α)
  | 0, _ => pure []
  | n + 1, st => do
      match ← run st with
      | none => pure []
      | some (x, next) => pure (x :: (← observe run n (some next)))

/-- A complete round is a source history followed by source exhaustion. -/
def CompleteHistory {α S : Type}
    [Monad m] (run : Option S → m (Option (α × S))) (xs : List α) : Prop :=
  ∃ final, History run none xs final ∧ run final = pure none

/-- Finite observations of repetition consist of complete rounds followed by a
possibly unfinished source prefix. An infinite source needs no complete round. -/
def CycleOutputSemantics : Prop :=
  (∀ {α S : Type} (itr : IteratorModel α S) (xs : List α),
    (∃ final, History (cycleObservation (cycleModel itr)).run none xs final) ↔
      ∃ (rounds : List (List α)) (tailValues : List α) (final : Option S),
        (∀ round ∈ rounds, round ≠ [] ∧ CompleteHistory itr.run round) ∧
        History itr.run none tailValues final ∧ xs = rounds.flatten ++ tailValues) ∧
  (∀ {α S : Type} (itr : IteratorModel α S), itr.run none = .ok none →
    ∀ depth : Nat,
      observe (cycleObservation (cycleModel itr)).run depth none = .ok [])


/-- Exactly the already-installed approved text, including its Nat-state domain. -/
def NthZipNonpositive : Prop :=
  ∀ {α : Type} (iters : List (IteratorModel α Nat)) (n : Int), n ≤ 0 →
    nthZipValues iters n = .error .boundsError

def isFiniteSizeTag : IteratorSizeTag → Bool
  | .hasLength => true
  | .hasShape _ => true
  | _ => false

/-- Exactly the already-installed approved text. -/
def AndTraitsSpec : Prop :=
  (∀ a b : IteratorSizeTag, andIteratorSizeDispatch a b = andIteratorSizeDispatch b a) ∧
  (∀ a : IteratorSizeTag, andIteratorSizeDispatch a a = a) ∧
  (∀ a b : IteratorSizeTag,
    isFiniteSizeTag (andIteratorSizeDispatch a b) = (isFiniteSizeTag a && isFiniteSizeTag b)) ∧
  (∀ (a b : IteratorSizeTag) (n : Nat),
    andIteratorSizeDispatch a b = .hasShape n ↔ a = .hasShape n ∧ b = .hasShape n) ∧
  (∀ a b : IteratorSizeTag,
    andIteratorSizeDispatch a b = .isInfinite ↔ a = .isInfinite ∧ b = .isInfinite) ∧
  (∀ a b : IteratorEltypeTag,
    andIteratorEltypeDispatch a b = andIteratorEltypeDispatch b a ∧
    (andIteratorEltypeDispatch a b = .hasEltype ↔ a = .hasEltype ∧ b = .hasEltype))


/-- Both optimizer specializations retain the complete suffix contract. -/
def DropDropCorrect : Prop :=
  (∀ {α S : Type} (itr : IteratorModel α S) (a b : Int), 0 ≤ a → 0 ≤ b →
    ∃ first second, CountValue.drop itr a = .ok first ∧ CountValue.dropDrop first b = .ok second ∧
      ∀ depth : Nat,
        observe (dropStep (fun xs st => xs.run st) second) (depth + 1) none =
          observeJl ((observe itr.run (a.toNat + b.toNat + depth + 1) none).map
            (List.drop (a.toNat + b.toNat)))) ∧
  (∀ {α S : Type} (itr : IteratorModel α S) (a b : Int), 0 ≤ a → 0 ≤ b →
    ∃ first second, CountValue.take itr a = .ok first ∧
      CountValue.dropTake (JInt.convert (IntTy.i64.name) .i64) (fun xs n => CountValue.drop xs n.val) first b = .ok second ∧
      ∀ depth : Nat,
        observe (dropTakeObservation itr second).run (depth + 1) none =
          observeJl ((observe itr.run (min a.toNat (b.toNat + depth + 1)) none).map
            (List.drop b.toNat)))

/-- peek/peel promise: peel's actual returned Rest reconstructs every observed prefix. -/
def PeelReconstructs : Prop :=
  ∀ {α S : Type} (itr : IteratorModel α S) (depth : Nat),
    (do
      match ← peelStep (fun xs st => xs.run st) itr with
      | none => pure []
      | some (x, r) =>
          pure (x :: (← observe (restStep (fun xs st => xs.run st) r) depth none))) =
      observe itr.run (depth + 1) none

/-- Independent counter/value association on every forward observation. -/
def EnumerateForward : Prop :=
  ∀ {α S : Type} (itr : IteratorModel α S) (depth : Nat),
    observe (iterateEnumerate (fun xs st => xs.run st) (enumerateModel itr)) depth none =
      (observe itr.run depth none).map
        (fun xs => xs.zipIdx |>.map (fun (x, k) => (JInt.lit .i64 (Int.ofNat k + 1), x)))

/-- The stateful reverse-enumeration method retains values and decrements machine counters.
The arbitrary R method is the caller's reverse-iterator extension, not a replacement Reverse. -/
def EnumerateReverseState : Prop :=
  ∀ {I R α S : Type} (run : R → Option S → Jl (Option (α × S)))
      (r : Reverse (Enumerate I)) (ri : R) (counter : JInt64) (start : S) (depth : Nat),
    observe
      (fun st =>
        match st with
        | none => sourceMethod228 run (fun a b => pure (a - b)) r (counter, ri, some start)
        | some (i, source, next) => sourceMethod228 run (fun a b => pure (a - b)) r (i, source, some next))
      depth none =
      (observe (run ri) depth (some start)).map
        (fun xs => xs.zipIdx |>.map
          (fun (x, k) => (JInt.lit .i64 (counter.val - Int.ofNat k), x)))


/-- Observable cardinality, independent of the implementation's state tests. -/
def cardinalityOne {α : Type} : Jl (List α) → Jl α
  | .error e => .error e
  | .ok [] => .error (.argumentError "Collection is empty, must contain exactly 1 element")
  | .ok [x] => .ok x
  | .ok (_ :: _ :: _) =>
      .error (.argumentError "Collection has multiple elements, must contain exactly 1 element")

def OnlyCorrect : Prop :=
  ∀ {α S : Type} (itr : IteratorModel α S),
    onlyIterator itr = cardinalityOne (observe itr.run 2 none)

/-- nth uses an ordinal position in the observation, including both missing-index cases. -/
def ordinalResult {α : Type} (n : Nat) : Jl (List α) → Jl α
  | .error e => .error e
  | .ok xs =>
      if xs.length = n then
        match xs.getLast? with
        | none => .error .boundsError
        | some x => .ok x
      else .error .boundsError

def NthProtocol : Prop :=
  ∀ {α S : Type} (itr : IteratorModel α S) (n : Int),
    nthIterator itr n =
      if n ≤ 0 then .error .boundsError
      else ordinalResult n.toNat (observe itr.run n.toNat none)

/-- Each successful in-order zip row contains one value and one state per iterator. -/
def ZipRowArity : Prop :=
  ∀ {I α S : Type} (run : I → Option S → Jl (Option (α × S)))
      (inputs : List (I × Option S)) (values : List α) (states : List (Option S)),
    zipOrderObservation run inputs = .ok (some (values, states)) →
      values.length = inputs.length ∧ states.length = inputs.length

/-- The ordinary zip entry point includes its zero-argument infinite sequence. -/
def EmptyZipInfinite : Prop :=
  ∀ {α S : Type} (depth : Nat),
    observe (zipObservation (zipModel ([] : List (IteratorModel α S)))).run depth none =
      .ok (List.replicate depth [])


/-- The public zero-argument constructor counts forever from one, with native Int wrap. -/
def CountDefaultProgression : Prop :=
  ∀ depth : Nat,
    observe
      (fun state => do
        let (value, next) ← iterateCountState (m := Jl)
          (fun a b => pure (JuliaLean.base.int.add_int a b))
          countfromDefault (state.getD countfromDefault.start)
        pure (some (value, next)))
      depth none =
        .ok ((List.range depth).map (fun k => JInt.lit .i64 (Int.ofNat k + 1)))

/-- Information content of the source-dispatched zip traits, over arbitrary arity. -/
def ZipTraitInformation : Prop :=
  (∀ {α S : Type} (iters : List (IteratorModel α S)),
    zipIteratorEltype (zipModel iters) = .hasEltype ↔
      ∀ itr ∈ iters, itr.iteratorEltype = .hasEltype) ∧
  (∀ {α S : Type} (iters : List (IteratorModel α S)),
    zipIteratorSize (zipModel iters) = .isInfinite ↔
      ∀ itr ∈ iters, itr.iteratorSize = .isInfinite)

/-- Counts are mathematical cardinalities, so zero times infinity is zero. -/
inductive Count where
  | finite (n : Nat)
  | infinite
  deriving DecidableEq

def Count.product : List Count → Count
  | [] => .finite 1
  | .finite 0 :: _ => .finite 0
  | .finite (n + 1) :: rest =>
      match Count.product rest with
      | .finite k => .finite ((n + 1) * k)
      | .infinite => .infinite
  | .infinite :: rest =>
      match Count.product rest with
      | .finite 0 => .finite 0
      | _ => .infinite

def Count.agrees (tag : IteratorSizeTag) (count : Count) : Prop :=
  match tag with
  | .sizeUnknown => True
  | .hasShape 0 => count = .finite 1
  | .hasLength | .hasShape (_ + 1) => ∃ n, count = .finite n
  | .isInfinite => count = .infinite

inductive CountsAgree : List IteratorSizeTag → List Count → Prop where
  | nil : CountsAgree [] []
  | cons {tag count tags counts} :
      Count.agrees tag count → CountsAgree tags counts →
      CountsAgree (tag :: tags) (count :: counts)

def Count.minimum : List Count → Count
  | [] => .infinite
  | .infinite :: rest => Count.minimum rest
  | .finite n :: rest =>
      match Count.minimum rest with
      | .infinite => .finite n
      | .finite k => .finite (min n k)

/-- Shortest-component cardinality, source trait dispatch, and exact retained dimensions. -/
def ZipTraitsSound : Prop :=
  ZipTraitInformation ∧
  (∀ {α S : Type} (iters : List (IteratorModel α S)) (counts : List Count),
    CountsAgree (iters.map (fun itr => itr.iteratorSize)) counts →
      Count.agrees (zipIteratorSize (zipModel iters)) (Count.minimum counts)) ∧
  (∀ {α S : Type} (iters : List (IteratorModel α S)) (dimensions : Nat),
    zipIteratorSize (zipModel iters) = .hasShape dimensions ↔
      iters ≠ [] ∧ ∀ itr ∈ iters, itr.iteratorSize = .hasShape dimensions)

/-- No fit assumption, empty-factor exclusion, or bound on the number of factors. -/
def ProductSizeSound : Prop :=
  ∀ (tags : List IteratorSizeTag) (counts : List Count),
    CountsAgree tags counts →
      Count.agrees (prodIteratorSizeDispatch (tags ++ [.hasShape 0])) (Count.product counts)
/-- Finite product traits retain the sum of known dimensions, including zero dimensions.
The count claim also covers SizeUnknown inputs. -/
def ProductShapeFinite : Prop :=
  (∀ (tags : List IteratorSizeTag) (counts : List Count),
    (∀ tag ∈ tags, tag ≠ .isInfinite) → CountsAgree tags counts →
      Count.agrees (prodIteratorSizeDispatch (tags ++ [.hasShape 0])) (Count.product counts)) ∧
  (∀ dimensions : List Nat,
    prodIteratorSizeDispatch ((dimensions.map IteratorSizeTag.hasShape) ++ [.hasShape 0]) =
      .hasShape dimensions.sum)


/-- Generic partition length uses the installed native cld and preserves zero-count errors.
No statement about chunk storage or aliasing is inferred from this arithmetic component. -/
def PartitionNativeLength : Prop :=
  ∀ {I : Type} (length : I → Jl JInt64) (c : I) (n l : JInt64),
    length c = .ok l →
      (n.val = 0 → partitionLengthInt length (sourceMethod1447 c n) = .error .divideError) ∧
      (0 ≤ l.val → 0 < n.val →
        ∃ q, partitionLengthInt length (sourceMethod1447 c n) = .ok q ∧
          q.val * n.val ≥ l.val ∧ (q.val - 1) * n.val < l.val)

end Round4
theorem cycleEmptyObservation {α S : Type} (itr : IteratorModel α S)
    (hempty : itr.run none = .ok none) (depth : Nat) :
    Round4.observe (cycleObservation (cycleModel itr)).run depth none = .ok [] := by
  cases depth <;>
    simp [Round4.observe, cycleObservation, cycleModel, iterateCycle, hempty,
      observe, liftJl, Bind.bind, Pure.pure, JuliaLean.base.iterators.bind, ret]

private def cycleRunJl {α S : Type} (itr : IteratorModel α S) :
    Option S → Jl (Option (α × S))
  | none => itr.run none
  | some s => do
      match ← itr.run (some s) with
      | none => itr.run none
      | some pair => pure (some pair)

private theorem cycleObservationRun_eq {α S : Type}
    (itr : IteratorModel α S) (st : Option S) :
    (cycleObservation (cycleModel itr)).run st =
      observeJl (cycleRunJl itr st) := by
  cases st with
  | none => rfl
  | some s =>
      cases hrun : itr.run (some s) with
      | error e =>
          simp [cycleObservation, cycleModel, cycleRunJl, iterateCycle,
            observe, observeJl, liftJl, hrun, Bind.bind, Except.bind,
            Pure.pure, Except.pure, JuliaLean.base.iterators.bind, ret]
      | ok result =>
          cases result with
          | none =>
              cases hbase : itr.run none <;>
                simp [cycleObservation, cycleModel, cycleRunJl, iterateCycle,
                  observe, observeJl, liftJl, hrun, hbase, Bind.bind,
                  Except.bind, Pure.pure, Except.pure,
                  JuliaLean.base.iterators.bind, ret]
          | some pair =>
              simp [cycleObservation, cycleModel, cycleRunJl, iterateCycle,
                observe, observeJl, liftJl, hrun, Bind.bind, Except.bind,
                Pure.pure, Except.pure, JuliaLean.base.iterators.bind, ret]

private theorem observeJl_success_iff {α : Type} (result : Jl α) (value : α) :
    observeJl result = Observation.ok value ↔ result = .ok value := by
  cases result <;> simp [observeJl, observe, liftJl]

private theorem cycleObservationRun_success {α S : Type}
    (itr : IteratorModel α S) (st : Option S) (pair : α × S) :
    (cycleObservation (cycleModel itr)).run st = Observation.ok (some pair) ↔
      cycleRunJl itr st = .ok (some pair) := by
  rw [cycleObservationRun_eq]
  exact observeJl_success_iff _ _

private theorem history_append {α S : Type} {m : Type → Type} [Monad m]
    {run : Option S → m (Option (α × S))}
    {st mid final : Option S} {xs ys : List α}
    (h₁ : Round4.History run st xs mid)
    (h₂ : Round4.History run mid ys final) :
    Round4.History run st (xs ++ ys) final := by
  induction h₁ with
  | nil st =>
      simpa using h₂
  | cons hrun htail ih =>
      simpa only [List.cons_append] using
        (Round4.History.cons hrun (ih h₂))

private theorem history_final_some {α S : Type} {m : Type → Type} [Monad m]
    {run : Option S → m (Option (α × S))} :
    ∀ {st : Option S} {xs : List α} {final : Option S},
      Round4.History run st xs final → xs ≠ [] → ∃ s, final = some s := by
  intro st xs final h
  induction h with
  | nil st =>
      intro hne
      contradiction
  | cons hrun htail ih =>
      intro _
      cases htail with
      | nil st => exact ⟨_, rfl⟩
      | cons hrun htail => exact ih (by simp)

private theorem cycleHistory_of_source {α S : Type}
    (itr : IteratorModel α S) {st : Option S} {xs : List α} {final : Option S}
    (hsrc : Round4.History itr.run st xs final) :
    Round4.History (cycleObservation (cycleModel itr)).run st xs final := by
  induction hsrc with
  | nil st =>
      exact Round4.History.nil st
  | @cons st x next xs final hrun htail ih =>
      have hrunCycle : cycleRunJl itr st = .ok (some (x, next)) := by
        cases st <;>
          simp [cycleRunJl, hrun, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact Round4.History.cons
        ((cycleObservationRun_success itr st (x, next)).2 hrunCycle) ih

private theorem cycleHistory_of_source_start {α S : Type}
    (itr : IteratorModel α S) {st : Option S} {xs : List α} {final : Option S}
    (hstart : st = none ∨
      ∃ s, st = some s ∧ itr.run (some s) = .ok none)
    (hsrc : Round4.History itr.run none xs final) (hne : xs ≠ []) :
    Round4.History (cycleObservation (cycleModel itr)).run st xs final := by
  cases hsrc with
  | nil st =>
      contradiction
  | @cons _ x next xs final hrun htail =>
      have hrunCycle : cycleRunJl itr st = .ok (some (x, next)) := by
        rcases hstart with hnone | ⟨s, hst, hreset⟩
        · subst st
          simp [cycleRunJl, hrun]
        · subst st
          simp [cycleRunJl, hreset, hrun, Bind.bind, Except.bind,
            Pure.pure, Except.pure]
      exact Round4.History.cons
        ((cycleObservationRun_success itr st (x, next)).2 hrunCycle)
        (cycleHistory_of_source itr htail)

private theorem cycleHistory_decompose {α S : Type}
    (itr : IteratorModel α S) :
    ∀ {st : Option S} {xs : List α} {final : Option S},
      Round4.History (cycleObservation (cycleModel itr)).run st xs final →
      ∀ pref sourceFinal, sourceFinal = st →
        Round4.History itr.run none pref sourceFinal →
        ∃ (rounds : List (List α)) (tailValues : List α)
          (tailFinal : Option S),
          (∀ round ∈ rounds,
            round ≠ [] ∧ Round4.CompleteHistory itr.run round) ∧
          Round4.History itr.run none tailValues tailFinal ∧
          pref ++ xs = rounds.flatten ++ tailValues := by
  intro st xs final hcycle
  induction hcycle with
  | nil st =>
      intro pref sourceFinal hstate hprefix
      refine ⟨[], pref, sourceFinal, ?_, hprefix, ?_⟩
      · intro round hround
        cases hround
      · simp
  | @cons st x next xs final hstep htail ih =>
      intro pref sourceFinal hstate hprefix
      have hcycleRun :=
        (cycleObservationRun_success itr st (x, next)).1 hstep
      cases st with
      | none =>
          cases hstate
          have hsource : itr.run none = .ok (some (x, next)) := by
            simpa [cycleRunJl] using hcycleRun
          have hsingle :=
            Round4.History.cons hsource (Round4.History.nil (some next))
          have hpref' := history_append hprefix hsingle
          rcases ih (pref ++ [x]) (some next) rfl hpref' with
            ⟨rounds, tailValues, tailFinal, hrounds, htail', hvalues⟩
          refine ⟨rounds, tailValues, tailFinal, hrounds, htail', ?_⟩
          simpa [List.append_assoc] using hvalues
      | some s =>
          cases hstate
          cases hrun : itr.run (some s) with
          | error e =>
              simp [cycleRunJl, hrun] at hcycleRun
          | ok result =>
              cases result with
              | some pair =>
                  cases pair with
                  | mk y next' =>
                      have hpair : (y, next') = (x, next) := by
                        simpa [cycleRunJl, hrun] using hcycleRun
                      have hsource :
                          itr.run (some s) = .ok (some (x, next)) := by
                        rw [hrun]
                        simp [hpair]
                      have hsingle :=
                        Round4.History.cons hsource
                          (Round4.History.nil (some next))
                      have hpref' := history_append hprefix hsingle
                      rcases ih (pref ++ [x]) (some next) rfl hpref' with
                        ⟨rounds, tailValues, tailFinal, hrounds, htail', hvalues⟩
                      refine ⟨rounds, tailValues, tailFinal, hrounds, htail', ?_⟩
                      simpa [List.append_assoc] using hvalues
              | none =>
                  have hsource :
                      itr.run none = .ok (some (x, next)) := by
                    simpa [cycleRunJl, hrun, Bind.bind, Except.bind,
                      Pure.pure, Except.pure] using hcycleRun
                  have hpref_ne : pref ≠ [] := by
                    intro hnil
                    subst pref
                    cases hprefix
                  have hcomplete : Round4.CompleteHistory itr.run pref :=
                    ⟨some s, hprefix, hrun⟩
                  have hsingle :=
                    Round4.History.cons hsource (Round4.History.nil (some next))
                  rcases ih [x] (some next) rfl hsingle with
                    ⟨rounds, tailValues, tailFinal, hrounds, htail', hvalues⟩
                  refine ⟨pref :: rounds, tailValues, tailFinal,
                    ?_, htail', ?_⟩
                  · intro round hmem
                    simp only [List.mem_cons] at hmem
                    rcases hmem with heq | hmem
                    · cases heq
                      exact ⟨hpref_ne, hcomplete⟩
                    · exact hrounds round hmem
                  · calc
                      pref ++ (x :: xs) = pref ++ ([x] ++ xs) := by simp
                      _ = pref ++ (rounds.flatten ++ tailValues) :=
                        congrArg (List.append pref) hvalues
                      _ = (pref :: rounds).flatten ++ tailValues := by
                        simp [List.flatten_cons, List.append_assoc]

private theorem cycleHistory_of_segments {α S : Type}
    (itr : IteratorModel α S) :
    ∀ (st : Option S) (rounds : List (List α))
      (tailValues : List α) (tailFinal : Option S),
      (st = none ∨
        ∃ s, st = some s ∧ itr.run (some s) = .ok none) →
      (∀ round ∈ rounds,
        round ≠ [] ∧ Round4.CompleteHistory itr.run round) →
      Round4.History itr.run none tailValues tailFinal →
      ∃ final, Round4.History (cycleObservation (cycleModel itr)).run st
        (rounds.flatten ++ tailValues) final := by
  intro st rounds
  induction rounds generalizing st with
  | nil =>
      intro tailValues tailFinal hstart _ htail
      cases tailValues with
      | nil =>
          cases htail
          exact ⟨st, Round4.History.nil st⟩
      | cons x xs =>
          exact ⟨tailFinal,
            cycleHistory_of_source_start itr hstart htail (by simp)⟩
  | cons round rounds ih =>
      intro tailValues tailFinal hstart hrounds htail
      have hfirst := hrounds round (by simp)
      rcases hfirst with ⟨hne, ⟨roundFinal, hround, hend⟩⟩
      cases round with
      | nil =>
          simp at hne
      | cons x xs =>
          obtain ⟨s, hroundFinal⟩ := history_final_some hround (by simp)
          subst roundFinal
          have hroundCycle :=
            cycleHistory_of_source_start itr hstart hround (by simp)
          have hstartNext :
              (some s : Option S) = none ∨
                ∃ s', some s = some s' ∧ itr.run (some s') = .ok none :=
            Or.inr ⟨s, rfl, hend⟩
          have hroundsTail : ∀ r ∈ rounds,
              r ≠ [] ∧ Round4.CompleteHistory itr.run r := by
            intro r hr
            exact hrounds r (by simp [hr])
          obtain ⟨final, hcycleRest⟩ :=
            ih (some s) tailValues tailFinal hstartNext hroundsTail htail
          refine ⟨final, ?_⟩
          have hwhole := history_append hroundCycle hcycleRest
          simpa [List.flatten_cons, List.append_assoc] using hwhole

theorem cycleOutputSemantics_proven : Round4.CycleOutputSemantics := by
  refine ⟨?_, ?_⟩
  · intro α S itr xs
    constructor
    · rintro ⟨final, hcycle⟩
      rcases cycleHistory_decompose itr hcycle [] none rfl
        (Round4.History.nil none) with
        ⟨rounds, tailValues, tailFinal, hrounds, htail, hvalues⟩
      refine ⟨rounds, tailValues, tailFinal, hrounds, htail, ?_⟩
      simpa using hvalues
    · rintro ⟨rounds, tailValues, tailFinal, hrounds, htail, hvalues⟩
      obtain ⟨final, hcycle⟩ :=
        cycleHistory_of_segments itr none rounds tailValues tailFinal
          (Or.inl rfl) hrounds htail
      refine ⟨final, ?_⟩
      rw [hvalues]
      exact hcycle
  · intro α S itr hempty depth
    exact cycleEmptyObservation itr hempty depth

private theorem andIteratorEltypeHas_iff (a b : IteratorEltypeTag) :
    andIteratorEltypeDispatch a b = .hasEltype ↔
      a = .hasEltype ∧ b = .hasEltype := by
  cases a <;> cases b <;>
    simp [andIteratorEltypeDispatch, andIteratorEltypeSame, andIteratorEltypeOther]

private theorem zipIteratorEltypeMany_has_iff :
    ∀ a rest, zipIteratorEltypeMany a rest = .hasEltype ↔
      a = .hasEltype ∧ ∀ b ∈ rest, b = .hasEltype := by
  intro a rest
  induction rest generalizing a with
  | nil =>
      simp [zipIteratorEltypeMany, zipIteratorEltypeEmpty,
        andIteratorEltypeHas_iff]
  | cons b rest ih =>
      cases rest with
      | nil =>
          cases a <;> cases b <;>
            simp [zipIteratorEltypeMany, zipIteratorEltypeOne,
              andIteratorEltypeDispatch, andIteratorEltypeSame, andIteratorEltypeOther]
      | cons c cs =>
          simp [zipIteratorEltypeMany, andIteratorEltypeHas_iff, ih b,
            and_assoc]

private theorem zipIteratorEltype_has_iff {α S : Type}
    (iters : List (IteratorModel α S)) :
    zipIteratorEltype (zipModel iters) = .hasEltype ↔
      ∀ itr ∈ iters, itr.iteratorEltype = .hasEltype := by
  cases iters with
  | nil =>
      simp [zipIteratorEltype, zipModel, zipIteratorEltypeEmpty]
  | cons itr rest =>
      cases rest with
      | nil =>
          simp [zipIteratorEltype, zipModel, zipIteratorEltypeOne]
      | cons second rest =>
          simp [zipIteratorEltype, zipModel, zipIteratorEltypeMany_has_iff]

private theorem zipIteratorSizeDispatch2_infinite_iff (a b : IteratorSizeTag) :
    zipIteratorSizeDispatch2 a b = .isInfinite ↔
      a = .isInfinite ∧ b = .isInfinite := by
  cases a <;> cases b <;>
    simp [zipIteratorSizeDispatch2, zipIteratorSizeInfiniteOther,
      zipIteratorSizeNonInfiniteLeft, zipIteratorSizeInfiniteInfinite,
      zipIteratorSizeLengthInfinite, zipIteratorSizeShapeInfinite,
      zipIteratorSizeTwo, andIteratorSizeDispatch, andIteratorSizeSame,
      andIteratorSizeOther, andIteratorSizeSameShape, andIteratorSizeShapeShape,
      andIteratorSizeLengthShape, andIteratorSizeShapeLength] <;>
    try split <;> simp_all [andIteratorSizeDispatch, eq_comm] <;> omega

private theorem zipIteratorSizeMany_infinite_iff
    (a b : IteratorSizeTag) :
    ∀ cs, zipIteratorSizeMany a b cs = .isInfinite ↔
      a = .isInfinite ∧ b = .isInfinite ∧
        ∀ c ∈ cs, c = .isInfinite := by
  intro cs
  induction cs generalizing a b with
  | nil =>
      simp [zipIteratorSizeMany, zipIteratorSizeOne,
        zipIteratorSizeDispatch2_infinite_iff]
  | cons c cs ih =>
      simp [zipIteratorSizeMany, zipIteratorSizeDispatch2_infinite_iff,
        ih b c, and_assoc]

private theorem zipIteratorSize_infinite_iff {α S : Type}
    (iters : List (IteratorModel α S)) :
    zipIteratorSize (zipModel iters) = .isInfinite ↔
      ∀ itr ∈ iters, itr.iteratorSize = .isInfinite := by
  cases iters with
  | nil =>
      simp [zipIteratorSize, zipModel, zipIteratorSizeEmpty]
  | cons itr rest =>
      cases rest with
      | nil =>
          simp [zipIteratorSize, zipModel, zipIteratorSizeOne]
      | cons second rest =>
          cases rest with
          | nil =>
              simp [zipIteratorSize, zipModel,
                zipIteratorSizeDispatch2_infinite_iff]
          | cons third tail =>
              simp [zipIteratorSize, zipModel,
                zipIteratorSizeMany_infinite_iff,
                zipIteratorSizeDispatch2_infinite_iff]

theorem zipTraitInformation_proven : Round4.ZipTraitInformation := by
  constructor
  · exact zipIteratorEltype_has_iff
  · exact zipIteratorSize_infinite_iff

private theorem zipIteratorSizeDispatch2_shape_iff
    (a b : IteratorSizeTag) (d : Nat) :
    zipIteratorSizeDispatch2 a b = .hasShape d ↔
      a = .hasShape d ∧ b = .hasShape d := by
  cases a <;> cases b <;>
    simp [zipIteratorSizeDispatch2, zipIteratorSizeInfiniteOther,
      zipIteratorSizeNonInfiniteLeft, zipIteratorSizeInfiniteInfinite,
      zipIteratorSizeLengthInfinite, zipIteratorSizeShapeInfinite,
      zipIteratorSizeTwo, andIteratorSizeDispatch, andIteratorSizeSame,
      andIteratorSizeOther, andIteratorSizeSameShape, andIteratorSizeShapeShape,
      andIteratorSizeLengthShape, andIteratorSizeShapeLength, eq_comm] <;>
    split <;> simp_all [andIteratorSizeDispatch, eq_comm] <;> omega

private theorem zipIteratorSizeMany_shape_iff
    (a b : IteratorSizeTag) :
    ∀ cs d, zipIteratorSizeMany a b cs = .hasShape d ↔
      a = .hasShape d ∧ b = .hasShape d ∧
        ∀ c ∈ cs, c = .hasShape d := by
  intro cs
  induction cs generalizing a b with
  | nil =>
      intro d
      simp [zipIteratorSizeMany, zipIteratorSizeOne,
        zipIteratorSizeDispatch2_shape_iff]
  | cons c cs ih =>
      intro d
      simp [zipIteratorSizeMany, zipIteratorSizeDispatch2_shape_iff,
        ih b c d, and_assoc]

private theorem zipIteratorSize_shape_iff {α S : Type}
    (iters : List (IteratorModel α S)) (d : Nat) :
    zipIteratorSize (zipModel iters) = .hasShape d ↔
      iters ≠ [] ∧ ∀ itr ∈ iters, itr.iteratorSize = .hasShape d := by
  cases iters with
  | nil =>
      simp [zipIteratorSize, zipModel, zipIteratorSizeEmpty]
  | cons itr rest =>
      cases rest with
      | nil =>
          simp [zipIteratorSize, zipModel, zipIteratorSizeOne]
      | cons second rest =>
          cases rest with
          | nil =>
              simp [zipIteratorSize, zipModel,
                zipIteratorSizeDispatch2_shape_iff]
          | cons third tail =>
              simp [zipIteratorSize, zipModel,
                zipIteratorSizeMany_shape_iff,
                zipIteratorSizeDispatch2_shape_iff]

private def countMinWith : Round4.Count → Round4.Count → Round4.Count
  | .infinite, count => count
  | .finite n, .infinite => .finite n
  | .finite n, .finite k => .finite (min n k)

private theorem countMinimum_cons (ca : Round4.Count) (counts : List Round4.Count) :
    Round4.Count.minimum (ca :: counts) =
      countMinWith ca (Round4.Count.minimum counts) := by
  cases ca with
  | infinite => rfl
  | finite n =>
      cases hmin : Round4.Count.minimum counts <;>
        simp [Round4.Count.minimum, countMinWith, hmin]

private theorem countMinimum_pair (ca cb : Round4.Count) :
    Round4.Count.minimum [ca, cb] = countMinWith ca cb := by
  cases ca <;> cases cb <;> rfl

private theorem countMinimum_singleton (c : Round4.Count) :
    Round4.Count.minimum [c] = c := by
  cases c <;> rfl

private theorem zipIteratorSizeDispatch2_count_agrees
    (a b : IteratorSizeTag) (ca cb : Round4.Count) :
    Round4.Count.agrees a ca → Round4.Count.agrees b cb →
      Round4.Count.agrees (zipIteratorSizeDispatch2 a b) (countMinWith ca cb) := by
  intro ha hb
  cases a with
  | sizeUnknown =>
      cases b <;> cases ca <;> cases cb <;>
        simp_all [Round4.Count.agrees, countMinWith,
          zipIteratorSizeDispatch2, zipIteratorSizeInfiniteOther,
          zipIteratorSizeNonInfiniteLeft, zipIteratorSizeInfiniteInfinite,
          zipIteratorSizeLengthInfinite, zipIteratorSizeShapeInfinite,
          zipIteratorSizeTwo, andIteratorSizeDispatch, andIteratorSizeSame,
          andIteratorSizeOther, andIteratorSizeSameShape, andIteratorSizeShapeShape,
          andIteratorSizeLengthShape, andIteratorSizeShapeLength, eq_comm]
  | hasLength =>
      cases b <;> cases ca <;> cases cb <;>
        simp_all [Round4.Count.agrees, countMinWith,
          zipIteratorSizeDispatch2, zipIteratorSizeInfiniteOther,
          zipIteratorSizeNonInfiniteLeft, zipIteratorSizeInfiniteInfinite,
          zipIteratorSizeLengthInfinite, zipIteratorSizeShapeInfinite,
          zipIteratorSizeTwo, andIteratorSizeDispatch, andIteratorSizeSame,
          andIteratorSizeOther, andIteratorSizeSameShape, andIteratorSizeShapeShape,
          andIteratorSizeLengthShape, andIteratorSizeShapeLength, eq_comm]
  | isInfinite =>
      cases b with
      | hasShape d =>
          cases d <;> cases ca <;> cases cb <;>
            simp_all [Round4.Count.agrees, countMinWith,
              zipIteratorSizeDispatch2, zipIteratorSizeInfiniteOther,
              zipIteratorSizeNonInfiniteLeft, zipIteratorSizeInfiniteInfinite,
              zipIteratorSizeLengthInfinite, zipIteratorSizeShapeInfinite,
              zipIteratorSizeTwo, andIteratorSizeDispatch, andIteratorSizeSame,
              andIteratorSizeOther, andIteratorSizeSameShape, andIteratorSizeShapeShape,
              andIteratorSizeLengthShape, andIteratorSizeShapeLength, eq_comm]
      | _ =>
          cases ca <;> cases cb <;>
            simp_all [Round4.Count.agrees, countMinWith,
              zipIteratorSizeDispatch2, zipIteratorSizeInfiniteOther,
              zipIteratorSizeNonInfiniteLeft, zipIteratorSizeInfiniteInfinite,
              zipIteratorSizeLengthInfinite, zipIteratorSizeShapeInfinite,
              zipIteratorSizeTwo, andIteratorSizeDispatch, andIteratorSizeSame,
              andIteratorSizeOther, andIteratorSizeSameShape, andIteratorSizeShapeShape,
              andIteratorSizeLengthShape, andIteratorSizeShapeLength, eq_comm]
  | hasShape d1 =>
      cases b with
      | sizeUnknown =>
          cases ca <;> cases cb <;>
            simp_all [Round4.Count.agrees, countMinWith,
              zipIteratorSizeDispatch2, zipIteratorSizeInfiniteOther,
              zipIteratorSizeNonInfiniteLeft, zipIteratorSizeInfiniteInfinite,
              zipIteratorSizeLengthInfinite, zipIteratorSizeShapeInfinite,
              zipIteratorSizeTwo, andIteratorSizeDispatch, andIteratorSizeSame,
              andIteratorSizeOther, andIteratorSizeSameShape, andIteratorSizeShapeShape,
              andIteratorSizeLengthShape, andIteratorSizeShapeLength, eq_comm]
      | hasLength =>
          cases ca <;> cases cb <;>
            simp_all [Round4.Count.agrees, countMinWith,
              zipIteratorSizeDispatch2, zipIteratorSizeInfiniteOther,
              zipIteratorSizeNonInfiniteLeft, zipIteratorSizeInfiniteInfinite,
              zipIteratorSizeLengthInfinite, zipIteratorSizeShapeInfinite,
              zipIteratorSizeTwo, andIteratorSizeDispatch, andIteratorSizeSame,
              andIteratorSizeOther, andIteratorSizeSameShape, andIteratorSizeShapeShape,
              andIteratorSizeLengthShape, andIteratorSizeShapeLength, eq_comm]
      | isInfinite =>
          cases d1 <;> cases ca <;> cases cb <;>
            simp_all [Round4.Count.agrees, countMinWith,
              zipIteratorSizeDispatch2, zipIteratorSizeInfiniteOther,
              zipIteratorSizeNonInfiniteLeft, zipIteratorSizeInfiniteInfinite,
              zipIteratorSizeLengthInfinite, zipIteratorSizeShapeInfinite,
              zipIteratorSizeTwo, andIteratorSizeDispatch, andIteratorSizeSame,
              andIteratorSizeOther, andIteratorSizeSameShape, andIteratorSizeShapeShape,
              andIteratorSizeLengthShape, andIteratorSizeShapeLength, eq_comm]
      | hasShape d2 =>
          cases d1 with
          | zero =>
              cases d2 <;> cases ca <;> cases cb <;>
                simp_all [Round4.Count.agrees, countMinWith,
                  zipIteratorSizeDispatch2, zipIteratorSizeInfiniteOther,
                  zipIteratorSizeNonInfiniteLeft, zipIteratorSizeInfiniteInfinite,
                  zipIteratorSizeLengthInfinite, zipIteratorSizeShapeInfinite,
                  zipIteratorSizeTwo, andIteratorSizeDispatch, andIteratorSizeSame,
                  andIteratorSizeOther, andIteratorSizeSameShape, andIteratorSizeShapeShape,
                  andIteratorSizeLengthShape, andIteratorSizeShapeLength, eq_comm]
          | succ n1 =>
              cases d2 with
              | zero =>
                  cases ca <;> cases cb <;>
                    simp_all [Round4.Count.agrees, countMinWith,
                      zipIteratorSizeDispatch2, zipIteratorSizeInfiniteOther,
                      zipIteratorSizeNonInfiniteLeft, zipIteratorSizeInfiniteInfinite,
                      zipIteratorSizeLengthInfinite, zipIteratorSizeShapeInfinite,
                      zipIteratorSizeTwo, andIteratorSizeDispatch, andIteratorSizeSame,
                      andIteratorSizeOther, andIteratorSizeSameShape, andIteratorSizeShapeShape,
                      andIteratorSizeLengthShape, andIteratorSizeShapeLength, eq_comm]
              | succ n2 =>
                  cases ca <;> cases cb <;>
                    by_cases hdim : n1 = n2 <;>
                      simp_all [Round4.Count.agrees, countMinWith,
                        zipIteratorSizeDispatch2, zipIteratorSizeInfiniteOther,
                        zipIteratorSizeNonInfiniteLeft, zipIteratorSizeInfiniteInfinite,
                        zipIteratorSizeLengthInfinite, zipIteratorSizeShapeInfinite,
                        zipIteratorSizeTwo, andIteratorSizeDispatch, andIteratorSizeSame,
                        andIteratorSizeOther, andIteratorSizeSameShape, andIteratorSizeShapeShape,
                        andIteratorSizeLengthShape, andIteratorSizeShapeLength, eq_comm]
private theorem zipIteratorSizeMany_count_agrees
    (a b : IteratorSizeTag) (cs : List IteratorSizeTag)
    (ca cb : Round4.Count) (counts : List Round4.Count) :
    Round4.Count.agrees a ca → Round4.Count.agrees b cb →
      Round4.CountsAgree cs counts →
        Round4.Count.agrees (zipIteratorSizeMany a b cs)
          (Round4.Count.minimum (ca :: cb :: counts)) := by
  induction cs generalizing a b ca cb counts with
  | nil =>
      intro ha hb hcounts
      cases hcounts
      change Round4.Count.agrees (zipIteratorSizeDispatch2 a b)
        (Round4.Count.minimum [ca, cb])
      rw [countMinimum_pair]
      exact zipIteratorSizeDispatch2_count_agrees a b ca cb ha hb
  | cons c cs ih =>
      intro ha hb hcounts
      cases counts with
      | nil =>
          cases hcounts
      | cons ccount restCounts =>
          cases hcounts with
          | cons hcount hrest =>
              have hinner :=
                ih b c cb ccount restCounts hb hcount hrest
              have houter :=
                zipIteratorSizeDispatch2_count_agrees a
                  (zipIteratorSizeMany b c cs) ca
                  (Round4.Count.minimum (cb :: ccount :: restCounts))
                  ha hinner
              change Round4.Count.agrees
                (zipIteratorSizeDispatch2 a (zipIteratorSizeMany b c cs))
                (Round4.Count.minimum (ca :: cb :: ccount :: restCounts))
              rw [countMinimum_cons]
              exact houter
private theorem zipIteratorSize_count_agrees {α S : Type}
    (iters : List (IteratorModel α S)) (counts : List Round4.Count) :
    Round4.CountsAgree (iters.map (fun itr => itr.iteratorSize)) counts →
      Round4.Count.agrees (zipIteratorSize (zipModel iters))
        (Round4.Count.minimum counts) := by
  cases iters with
  | nil =>
      intro hcounts
      cases hcounts
      simp [zipIteratorSize, zipModel, zipIteratorSizeEmpty,
        Round4.Count.agrees, Round4.Count.minimum]
  | cons first rest =>
      cases rest with
      | nil =>
          intro hcounts
          cases counts with
          | nil =>
              cases hcounts
          | cons c restCounts =>
              cases hcounts with
              | cons hfirst htail =>
                  cases htail
                  rw [countMinimum_singleton]
                  simpa [zipIteratorSize, zipModel, zipIteratorSizeOne] using hfirst
      | cons second rest =>
          intro hcounts
          cases counts with
          | nil =>
              cases hcounts
          | cons c1 restCounts =>
              cases hcounts with
              | cons hfirst htail =>
                  cases restCounts with
                  | nil =>
                      cases htail
                  | cons c2 restCounts =>
                      cases htail with
                      | cons hsecond hrest =>
                          cases rest with
                          | nil =>
                              cases hrest
                              simpa [zipIteratorSize, zipModel,
                                Round4.Count.minimum, countMinimum_pair] using
                                (zipIteratorSizeDispatch2_count_agrees
                                  first.iteratorSize second.iteratorSize c1 c2
                                  hfirst hsecond)
                          | cons third rest =>
                              simpa [zipIteratorSize, zipModel] using
                                (zipIteratorSizeMany_count_agrees
                                  first.iteratorSize second.iteratorSize
                                  ((third :: rest).map
                                    (fun itr => itr.iteratorSize))
                                  c1 c2 restCounts hfirst hsecond hrest)

theorem zipTraitsSound_proven : Round4.ZipTraitsSound := by
  refine ⟨zipTraitInformation_proven, ?_, ?_⟩
  · exact zipIteratorSize_count_agrees
  · exact zipIteratorSize_shape_iff
theorem partitionNativeLength_proven : Round4.PartitionNativeLength := by
  intro I length c n l hlength
  constructor
  · intro hn0
    simp [partitionLengthInt, partitionLength, sourceMethod1447,
      mkPartitionIterator, JInt.cld, JInt.div, hlength, hn0]
  · intro hl hn
    obtain ⟨q, hq, hqval⟩ :=
      (JuliaLean.Proofs.base.sort.fldcld_pos l n hl hn).2
    have hresult : partitionLengthInt length (sourceMethod1447 c n) = .ok q := by
      simp [partitionLengthInt, partitionLength, sourceMethod1447,
        mkPartitionIterator, hlength, hq]
    obtain ⟨_, hfloorle, hceil, _⟩ :=
      JuliaLean.Proofs.base.sort.qfacts l.val n.val hl hn
    refine ⟨q, hresult, ?_⟩
    constructor
    · by_cases hdiv : l.val / n.val * n.val = l.val
      · have hqval' : q.val = l.val / n.val := by
          simpa [hdiv] using hqval
        rw [hqval', hdiv]
        omega
      · have hqval' : q.val = l.val / n.val + 1 := by
          simpa [hdiv] using hqval
        have hceil' : l.val < l.val / n.val * n.val + n.val := by
          simpa [Int.add_mul, Int.one_mul] using hceil
        rw [hqval', Int.add_mul, Int.one_mul]
        omega
    · by_cases hdiv : l.val / n.val * n.val = l.val
      · have hqval' : q.val = l.val / n.val := by
          simpa [hdiv] using hqval
        rw [hqval', Int.sub_mul, Int.one_mul, hdiv]
        omega
      · have hqval' : q.val = l.val / n.val + 1 := by
          simpa [hdiv] using hqval
        rw [hqval', Int.sub_mul, Int.one_mul, Int.add_mul, Int.one_mul]
        omega

theorem intAddEqualsJIntAdd {t : IntTy} (x y : JInt t) :
    JuliaLean.base.int.add_int x y = x + y := by
  apply Subtype.ext
  rw [JuliaLean.Proofs.base.int.add_int_val, jint_add_val]

theorem jintLitAddOne (start : Int) :
    JInt.lit .i64 start + JInt.lit .i64 1 = JInt.lit .i64 (start + 1) := by
  apply Subtype.ext
  rw [jint_add_val, jint_lit_val, jint_lit_val,
    JuliaLean.Proofs.base.int.wrapInt_add_left,
    JuliaLean.Proofs.base.int.wrapInt_add_right, jint_lit_val]
def enumerateIndexMap {α : Type} : Nat → List α → List (JInt64 × α)
  | _, [] => []
  | k, x :: xs =>
      (JInt.lit .i64 (Int.ofNat k + 1), x) :: enumerateIndexMap (k + 1) xs

theorem enumerateIndexMap_zipIdx {α : Type} (k : Nat) (xs : List α) :
    enumerateIndexMap k xs =
      (xs.zipIdx k).map
        (fun (x, i) => (JInt.lit .i64 (Int.ofNat i + 1), x)) := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
      simp [enumerateIndexMap, List.zipIdx_cons, ih]

theorem observeSuccessStep {α S : Type}
    (run : Option S → Jl (Option (α × S))) (depth : Nat) (state : Option S)
    (x : α) (next : S) (hstep : run state = .ok (some (x, next))) :
    Round4.observe run (depth + 1) state =
      (Round4.observe run depth (some next)).map (List.cons x) := by
  cases htail : Round4.observe run depth (some next) with
  | error e => simp [Round4.observe, hstep, htail, Except.map]
  | ok xs => simp [Round4.observe, hstep, htail, Except.map]

theorem ordinalResult_cons_bind {α : Type} (n : Nat) (x : α)
    (result : Jl (List α)) :
    Round4.ordinalResult (n + 2)
        (result >>= fun xs => Except.ok (x :: xs)) =
      Round4.ordinalResult (n + 1) result := by
  cases result with
  | error e => rfl
  | ok xs =>
      cases xs with
      | nil => simp [Round4.ordinalResult, List.length_cons]
      | cons y ys => simp [Round4.ordinalResult, List.length_cons]

theorem nthAdvance_ordinalResult {α S : Type}
    (run : Option S → Jl (Option (α × S))) :
    ∀ (n : Nat) (state : Option S),
      (do
        match ← nthAdvance run n (← run state) with
        | none => .error .boundsError
        | some (value, _) => pure value) =
        Round4.ordinalResult (n + 1) (Round4.observe run (n + 1) state) := by
  intro n
  induction n with
  | zero =>
      intro state
      cases hrun : run state with
      | error e => simp [Round4.observe, hrun, Round4.ordinalResult]
      | ok result =>
          cases result with
          | none => simp [Round4.observe, nthAdvance, hrun, Round4.ordinalResult]
          | some pair =>
              cases pair with
              | mk x next =>
                  simp [Round4.observe, nthAdvance, hrun, Round4.ordinalResult]
  | succ n ih =>
      intro state
      cases hrun : run state with
      | error e =>
          simp [Round4.observe, nthAdvance, hrun, Round4.ordinalResult]
      | ok result =>
          cases result with
          | none =>
              simp [Round4.observe, nthAdvance, hrun, Round4.ordinalResult]
          | some pair =>
              cases pair with
              | mk x next =>
                  have htail := ih (some next)
                  have hobserve :
                      Round4.observe run (n + 2) state =
                        (do
                          match ← run state with
                          | none => pure []
                          | some (value, following) =>
                              pure
                                (value :: (← Round4.observe run (n + 1)
                                  (some following)))) := rfl
                  rw [hobserve]
                  simp only [hrun, ok_bind, pure_jl, nthAdvance]
                  rw [← except_bind_assoc]
                  rw [ordinalResult_cons_bind]
                  simpa only [pure_jl] using htail

theorem nthProtocol_proven : Round4.NthProtocol := by
  intro α S itr n
  change nthValue itr n =
    if n ≤ 0 then .error .boundsError
    else Round4.ordinalResult n.toNat (Round4.observe itr.run n.toNat none)
  by_cases hn : n ≤ 0
  · simp [nthValue_eq, hn, Round4.ordinalResult]
  · have hdepth : (n - 1).toNat + 1 = n.toNat := by omega
    simp only [nthValue_eq, if_neg hn]
    have hstep := nthAdvance_ordinalResult itr.run ((n - 1).toNat) none
    rw [hdepth] at hstep
    exact hstep
theorem enumerateObserveFromState {I α S : Type} (itr : I)
    (run : I → Option S → Jl (Option (α × S))) :
    ∀ k depth (state : S),
      Round4.observe (iterateEnumerate run (enumerateModel itr)) depth
          (some (JInt.lit .i64 (Int.ofNat k + 1), state)) =
        (Round4.observe (run itr) depth (some state)).map (enumerateIndexMap k) := by
  intro k depth
  induction depth generalizing k with
  | zero => intro state; rfl
  | succ depth ih =>
      intro state
      cases hrun : run itr (some state) with
      | error e =>
          simp [Round4.observe, iterateEnumerate, enumerateModel, hrun, Except.map]
      | ok result =>
          cases result with
          | none =>
              simp [Round4.observe, iterateEnumerate, enumerateModel, hrun,
                Except.map, enumerateIndexMap]
          | some pair =>
              cases pair with
              | mk x next =>
                  have hcounter :
                      JInt.lit .i64 (Int.ofNat k + 1) + JInt.lit .i64 1 =
                        JInt.lit .i64 (Int.ofNat k + 1 + 1) :=
                    jintLitAddOne (Int.ofNat k + 1)
                  have hnat : Int.ofNat (k + 1) = Int.ofNat k + 1 := by simp
                  have hnextCounter :
                      JInt.lit .i64 (Int.ofNat k + 1 + 1) =
                        JInt.lit .i64 (Int.ofNat (k + 1) + 1) := by
                    rw [← hnat]
                  have hiter : iterateEnumerate run (enumerateModel itr)
                      (some (JInt.lit .i64 (Int.ofNat k + 1), state)) =
                        .ok (some ((JInt.lit .i64 (Int.ofNat k + 1), x),
                          (JInt.lit .i64 (Int.ofNat k + 1 + 1), next))) := by
                    simpa [iterateEnumerate, enumerateModel, hrun] using hcounter
                  have hleft := observeSuccessStep
                    (iterateEnumerate run (enumerateModel itr)) depth
                    (some (JInt.lit .i64 (Int.ofNat k + 1), state))
                    (JInt.lit .i64 (Int.ofNat k + 1), x)
                    (JInt.lit .i64 (Int.ofNat k + 1 + 1), next) hiter
                  have hright := observeSuccessStep (run itr) depth
                    (some state) x next hrun
                  have htail := ih (k + 1) next
                  rw [hleft, hright, hnextCounter, htail]
                  cases hsource : Round4.observe (run itr) depth (some next) with
                  | error e => simp [hsource, Except.map]
                  | ok xs => simp [hsource, Except.map, enumerateIndexMap]

theorem enumerateObserveNone {I α S : Type} (itr : I)
    (run : I → Option S → Jl (Option (α × S))) :
    ∀ depth,
      Round4.observe (iterateEnumerate run (enumerateModel itr)) depth none =
        (Round4.observe (run itr) depth none).map (enumerateIndexMap 0) := by
  intro depth
  cases depth with
  | zero => rfl
  | succ depth =>
      cases hrun : run itr none with
      | error e =>
          simp [Round4.observe, iterateEnumerate, enumerateModel, hrun, Except.map]
      | ok result =>
          cases result with
          | none =>
              simp [Round4.observe, iterateEnumerate, enumerateModel, hrun,
                Except.map, enumerateIndexMap]
          | some pair =>
              cases pair with
              | mk x next =>
                  have hcounter :
                      JInt.lit .i64 1 + JInt.lit .i64 1 = JInt.lit .i64 2 := by
                    simpa using jintLitAddOne 1
                  have hiter : iterateEnumerate run (enumerateModel itr) none =
                      .ok (some ((JInt.lit .i64 1, x), (JInt.lit .i64 2, next))) := by
                    simp [iterateEnumerate, enumerateModel, hrun, hcounter]
                  have hleft := observeSuccessStep
                    (iterateEnumerate run (enumerateModel itr)) depth none
                    (JInt.lit .i64 1, x) (JInt.lit .i64 2, next) hiter
                  have hright := observeSuccessStep (run itr) depth none x next hrun
                  have hcounterEq :
                      JInt.lit .i64 2 = JInt.lit .i64 (Int.ofNat 1 + 1) :=
                    hcounter.symm.trans (jintLitAddOne 1)
                  have htail := enumerateObserveFromState itr run 1 depth next
                  rw [hleft, hright, hcounterEq, htail]
                  cases hsource : Round4.observe (run itr) depth (some next) with
                  | error e => simp [hsource, Except.map]
                  | ok xs => simp [hsource, Except.map, enumerateIndexMap]

theorem enumerateForward_proven : Round4.EnumerateForward := by
  intro α S itr depth
  rw [enumerateObserveNone itr (fun xs st => xs.run st) depth]
  cases hobs : Round4.observe itr.run depth none with
  | error e => simp [hobs, Except.map]
  | ok xs => simp [hobs, enumerateIndexMap_zipIdx, Except.map]

def countDefaultRun (state : Option JInt64) : Jl (Option (JInt64 × JInt64)) := do
  let (value, next) ← iterateCountState
    (fun a b => pure (JuliaLean.base.int.add_int a b))
    countfromDefault (state.getD countfromDefault.start)
  pure (some (value, next))

@[simp] theorem countDefaultRun_none :
    countDefaultRun none =
      .ok (some (JInt.lit .i64 1, JInt.lit .i64 2)) := by
  simp [countDefaultRun, iterateCountState, countfromDefault,
    intAddEqualsJIntAdd, jintLitAddOne]

@[simp] theorem countDefaultRun_some (start : Int) :
    countDefaultRun (some (JInt.lit .i64 start)) =
      .ok (some (JInt.lit .i64 start, JInt.lit .i64 (start + 1))) := by
  simp [countDefaultRun, iterateCountState, countfromDefault,
    intAddEqualsJIntAdd, jintLitAddOne]

theorem countObserveFrom (start : Int) :
    ∀ depth,
      Round4.observe countDefaultRun depth (some (JInt.lit .i64 start)) =
        .ok ((List.range depth).map
          (fun k => JInt.lit .i64 (start + Int.ofNat k))) := by
  intro depth
  induction depth generalizing start with
  | zero => rfl
  | succ depth ih =>
      have htail := ih (start + 1)
      simp only [Round4.observe, countDefaultRun_some, ok_bind, pure_jl, htail]
      apply congrArg Except.ok
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      rw [List.cons.injEq]
      constructor
      · simp
      · apply List.map_congr_left
        intro k hk
        congr 1
        simp <;> omega

theorem countDefaultObserveNone (depth : Nat) :
    Round4.observe countDefaultRun (depth + 1) none =
      Round4.observe countDefaultRun (depth + 1) (some (JInt.lit .i64 1)) := by
  simp [Round4.observe]

theorem countDefaultProgression_proven : Round4.CountDefaultProgression := by
  intro depth
  change Round4.observe countDefaultRun depth none =
    .ok ((List.range depth).map (fun k => JInt.lit .i64 (Int.ofNat k + 1)))
  cases depth with
  | zero => rfl
  | succ depth =>
      rw [countDefaultObserveNone depth]
      simpa [Int.add_comm] using countObserveFrom 1 (depth + 1)

namespace Round5

def observe {α S : Type} [Monad m] (run : Option S → m (Option (α × S))) :
    Nat → Option S → m (List α)
  | 0, _ => pure []
  | n + 1, st => do
      match ← run st with
      | none => pure []
      | some (x, next) => pure (x :: (← observe run n (some next)))

inductive History {α S : Type} (run : Option S → Jl (Option (α × S))) :
    Option S → List α → Option S → Prop where
  | nil (st) : History run st [] st
  | cons {st x next xs final} : run st = .ok (some (x, next)) →
      History run (some next) xs final → History run st (x :: xs) final

/-- take docstring: an Int-representable nonnegative count requests that many
initial values. Larger counts fail at the public constructor's Int conversion. -/
def TakePrefix : Prop :=
  ∀ {α S : Type} (itr : IteratorModel α S) (n : Int), 0 ≤ n →
    if n ≤ IntTy.max .i64 then
      ∃ t, CountValue.take itr n = .ok t ∧
        ∀ depth : Nat,
          observe (takeStep (fun xs st => xs.run st) t) depth none =
            observe itr.run (min depth n.toNat) none
    else CountValue.take itr n = .error (.inexactError "Int64")

/-- drop docstring: the representable count selects the suffix of an arbitrary
finite or infinite protocol; larger counts fail before any source iteration. -/
def DropSuffix : Prop :=
  ∀ {α S : Type} (itr : IteratorModel α S) (n : Int), 0 ≤ n →
    if n ≤ IntTy.max .i64 then
      ∃ d, CountValue.drop itr n = .ok d ∧
        ∀ depth : Nat,
          observe (dropStep (fun xs st => xs.run st) d) (depth + 1) none =
            (observe itr.run (n.toNat + depth + 1) none).map (List.drop n.toNat)
    else CountValue.drop itr n = .error (.inexactError "Int64")

/-- Nested take uses each returned constructor result. Each public Int conversion
can fail independently, before the corresponding iteration contract applies. -/
def TakeTakeCorrect : Prop :=
  ∀ {α S : Type} (itr : IteratorModel α S) (a b : Int), 0 ≤ a → 0 ≤ b →
    if a ≤ IntTy.max .i64 then
      ∃ first, CountValue.take itr a = .ok first ∧
        if b ≤ IntTy.max .i64 then
          ∃ second, CountValue.takeTake first b = .ok second ∧
            ∀ depth : Nat,
              observe (takeStep (fun xs st => xs.run st) second) depth none =
                observe itr.run (min depth (min a.toNat b.toNat)) none
        else CountValue.takeTake first b = .error (.inexactError "Int64")
    else CountValue.take itr a = .error (.inexactError "Int64")

inductive Count where
  | finite (n : Nat)
  | infinite
  deriving DecidableEq

def Count.product : List Count → Count
  | [] => .finite 1
  | .finite 0 :: _ => .finite 0
  | .finite (n + 1) :: rest =>
      match Count.product rest with
      | .finite k => .finite ((n + 1) * k)
      | .infinite => .infinite
  | .infinite :: rest =>
      match Count.product rest with
      | .finite 0 => .finite 0
      | _ => .infinite

def Count.agrees (tag : IteratorSizeTag) (count : Count) : Prop :=
  match tag with
  | .sizeUnknown => True
  | .hasShape 0 => count = .finite 1
  | .hasLength | .hasShape (_ + 1) => ∃ n, count = .finite n
  | .isInfinite => count = .infinite

inductive CountsAgree : List IteratorSizeTag → List Count → Prop where
  | nil : CountsAgree [] []
  | cons {tag count tags counts} :
      Count.agrees tag count → CountsAgree tags counts →
      CountsAgree (tag :: tags) (count :: counts)

/-- Take and Drop do not lose or duplicate values across their common cut.
A finite source history is an observation, not a termination assumption.
Counts above typemax(Int) fail at both public Int conversions. -/
def TakeDropComplement : Prop :=
  TakePrefix ∧ DropSuffix ∧
  (∀ {α S : Type} (itr : IteratorModel α S) (n : Int), 0 ≤ n →
    if n ≤ IntTy.max .i64 then
      ∃ t d, CountValue.take itr n = .ok t ∧ CountValue.drop itr n = .ok d ∧
        ∀ (before after : List α) (cut final : Option S),
          History itr.run none before cut → before.length = n.toNat →
          History itr.run cut after final →
          observe (takeStep (fun xs st => xs.run st) t) before.length none = .ok before ∧
          observe (dropStep (fun xs st => xs.run st) d) after.length none = .ok after
    else CountValue.take itr n = .error (.inexactError "Int64") ∧
      CountValue.drop itr n = .error (.inexactError "Int64"))

/-- rest docstring: a supplied state must have been reached by at least one step.
Every subsequent observation is the original iterator's suffix, even if it is infinite. -/
def RestSound : Prop :=
  ∀ {α S : Type} (itr : IteratorModel α S) (history : List α) (st : S),
    history ≠ [] → History itr.run none history (some st) →
    (∀ depth : Nat,
      observe (restStep (fun xs s => xs.run s) (restWithState itr st)) depth none =
        observe itr.run depth (some st)) ∧
    (∀ (old : S) (depth : Nat),
      observe (restStep (fun xs s => xs.run s)
        (restOnRest (restWithState itr old) st)) depth none =
        observe itr.run depth (some st)) ∧
    (∀ T : Type, sourceMethod735 T (restWithState itr st) = T) ∧
    sourceMethod736 itr.iteratorEltype (restWithState itr st) = itr.iteratorEltype ∧
    sourceMethod739 itr.iteratorSize (restWithState itr st) =
      (if itr.iteratorSize = .isInfinite then .isInfinite else .sizeUnknown)

/-- Infinite repetition produces the same object at every depth. Finite repetition
uses its returned Take for representable counts and reports Int conversion failure
for larger counts. -/
def RepeatedOutputs : Prop :=
  (∀ {α : Type} (x : α) (depth : Nat),
    observe (m := Jl) (fun st => pure (iterateRepeated (repeatedModel x) st)) depth none =
      .ok (List.replicate depth x)) ∧
  (∀ {α : Type} (x : α) (n : Int), 0 ≤ n →
    if n ≤ IntTy.max .i64 then
      ∃ t, CountValue.repeated x n = .ok t ∧
        ∀ depth : Nat,
          observe (takeStep (fun rep st => pure (iterateRepeated rep st)) t) depth none =
            .ok (List.replicate (min depth n.toNat) x)
    else CountValue.repeated x n = .error (.inexactError "Int64"))

def isFiniteSizeTag : IteratorSizeTag → Bool
  | .hasLength => true
  | .hasShape _ => true
  | _ => false

/-- Public ProductIterator trait query, including empty tuples and zero-times-infinity.
fieldtype is the frozen model's reflection boundary; no type-query correctness law
or precomputed resulting trait is assumed. -/
def ProductSizeQuerySound : Prop :=
  Count.agrees sourceMethod1150 (.finite 1) ∧
  (∀ {T F : Type} (fieldtype : T → Nat → F) (trait : F → IteratorSizeTag)
      (p : ProductIterator T) (N : Nat) (counts : List Count),
    CountsAgree ((List.range N).map (fun k => trait (fieldtype p.iterators (k + 1)))) counts →
      Count.agrees (sourceMethod1151 fieldtype trait N p) (Count.product counts))

def shapeDimensions : IteratorSizeTag → Option Nat
  | .hasLength => some 1
  | .hasShape n => some n
  | _ => none

/-- Unknown-size factors remain in the count claim. Known finite shape/length
factors contribute all their dimensions, through the actual public query. -/
def ProductFiniteQuerySound : Prop :=
  ∀ {T F : Type} (fieldtype : T → Nat → F) (trait : F → IteratorSizeTag)
      (p : ProductIterator T) (N : Nat) (counts : List Count),
    let tags := (List.range N).map (fun k => trait (fieldtype p.iterators (k + 1)))
    (∀ tag ∈ tags, tag ≠ .isInfinite) → CountsAgree tags counts →
      Count.agrees (sourceMethod1151 fieldtype trait N p) (Count.product counts) ∧
      (∀ dimensions : List Nat, tags.mapM shapeDimensions = some dimensions →
        sourceMethod1151 fieldtype trait N p = .hasShape dimensions.sum)

/-- Zip's generic finite-length comparison uses the installed source fold. -/
def ZipFiniteEquality : Prop :=
  ∀ {I Len : Type} [DecidableEq Len]
      (trait : I → IteratorSizeTag) (length : I → Jl Len) (iters : List I),
    zipLengthsFiniteEqualOn trait length iters =
      ((iters.takeWhile (fun itr => isFiniteSizeTag (trait itr))).mapM length).map
        (fun lengths =>
          (iters.all (fun itr => isFiniteSizeTag (trait itr)) &&
            lengths.all (fun n => lengths.all (fun m => decide (n = m))),
           lengths.head?))

end Round5
@[simp]
theorem zipLengthsPairwiseEq_cons {Len : Type} [DecidableEq Len]
    (x : Len) (lengths : List Len) :
    (x :: lengths).all (fun n => (x :: lengths).all (fun m => decide (n = m))) =
      (lengths.all (fun n => lengths.all (fun m => decide (n = m))) &&
        (lengths.head?.isNone || lengths.head? == some x)) := by
  cases lengths with
  | nil => simp
  | cons y ys =>
      by_cases hxy : x = y
      · subst y
        simp [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
      · have hyx : y ≠ x := fun h => hxy h.symm
        simp [hxy, hyx]

theorem zipFiniteEquality_proven : Round5.ZipFiniteEquality := by
  intro I Len inst trait length iters
  induction iters with
  | nil => rfl
  | cons itr rest ih =>
      cases htag : trait itr with
      | sizeUnknown =>
          have hfinite : Round5.isFiniteSizeTag (trait itr) = false := by
            simp [Round5.isFiniteSizeTag, htag]
          simp [zipLengthsFiniteEqualOn, htag, hfinite, Round5.isFiniteSizeTag, Except.map]
      | isInfinite =>
          have hfinite : Round5.isFiniteSizeTag (trait itr) = false := by
            simp [Round5.isFiniteSizeTag, htag]
          simp [zipLengthsFiniteEqualOn, htag, hfinite, Round5.isFiniteSizeTag, Except.map]
      | hasLength =>
          have hfinite : Round5.isFiniteSizeTag (trait itr) = true := by
            simp [Round5.isFiniteSizeTag, htag]
          cases hlen : length itr with
          | error e =>
              simp [zipLengthsFiniteEqualOn, htag, hfinite, hlen,
                Round5.isFiniteSizeTag, Except.map]
          | ok m =>
              cases hlist : List.mapM length
                  (List.takeWhile (fun item =>
                    match trait item with
                    | .hasLength => true
                    | .hasShape _ => true
                    | _ => false) rest) with
              | error e =>
                  have hlist' :
                      List.mapM length
                        (List.takeWhile
                          (fun item => Round5.isFiniteSizeTag (trait item)) rest) =
                        .error e := by
                    simpa [Round5.isFiniteSizeTag] using hlist
                  have hfold : zipLengthsFiniteEqualOn trait length rest = .error e := by
                    calc
                      _ = Except.map
                          (fun lengths =>
                            (rest.all (fun item => Round5.isFiniteSizeTag (trait item)) &&
                              lengths.all (fun n => lengths.all (fun m => decide (n = m))),
                             lengths.head?))
                          (List.mapM length
                            (List.takeWhile
                              (fun item => Round5.isFiniteSizeTag (trait item)) rest)) := ih
                      _ = .error e := by rw [hlist']; rfl
                  simp [zipLengthsFiniteEqualOn, htag, hfinite, hlen,
                    Round5.isFiniteSizeTag, hfold, hlist, Except.map]
              | ok lengths =>
                  have hlist' :
                      List.mapM length
                        (List.takeWhile
                          (fun item => Round5.isFiniteSizeTag (trait item)) rest) =
                        .ok lengths := by
                    simpa [Round5.isFiniteSizeTag] using hlist
                  have hfold :
                      zipLengthsFiniteEqualOn trait length rest =
                        .ok
                          (rest.all (fun item => Round5.isFiniteSizeTag (trait item)) &&
                            lengths.all (fun n => lengths.all (fun m => decide (n = m))),
                           lengths.head?) := by
                    calc
                      _ = Except.map
                          (fun lengths =>
                            (rest.all (fun item => Round5.isFiniteSizeTag (trait item)) &&
                              lengths.all (fun n => lengths.all (fun m => decide (n = m))),
                             lengths.head?))
                          (List.mapM length
                            (List.takeWhile
                              (fun item => Round5.isFiniteSizeTag (trait item)) rest)) := ih
                      _ = .ok
                          (rest.all (fun item => Round5.isFiniteSizeTag (trait item)) &&
                            lengths.all (fun n => lengths.all (fun m => decide (n = m))),
                           lengths.head?) := by rw [hlist']; rfl
                  have hmap :
                      List.mapM length
                        (List.takeWhile
                          (fun item => Round5.isFiniteSizeTag (trait item))
                          (itr :: rest)) =
                        .ok (m :: lengths) := by
                    simp [Round5.isFiniteSizeTag, htag, hfinite, hlen, hlist]
                  have htraitAll :
                      (itr :: rest).all
                        (fun item => Round5.isFiniteSizeTag (trait item)) =
                        rest.all
                          (fun item => Round5.isFiniteSizeTag (trait item)) := by
                    simp [Round5.isFiniteSizeTag, htag]
                  simp only [zipLengthsFiniteEqualOn, htag, hfinite, hlen,
                    hfold, hmap, Except.map, ok_bind, err_bind, pure_jl]
                  rw [htraitAll]
                  rw [zipLengthsPairwiseEq_cons]
                  simp [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
      | hasShape n =>
          have hfinite : Round5.isFiniteSizeTag (trait itr) = true := by
            simp [Round5.isFiniteSizeTag, htag]
          cases hlen : length itr with
          | error e =>
              simp [zipLengthsFiniteEqualOn, htag, hfinite, hlen,
                Round5.isFiniteSizeTag, Except.map]
          | ok m =>
              cases hlist : List.mapM length
                  (List.takeWhile (fun item =>
                    match trait item with
                    | .hasLength => true
                    | .hasShape _ => true
                    | _ => false) rest) with
              | error e =>
                  have hlist' :
                      List.mapM length
                        (List.takeWhile
                          (fun item => Round5.isFiniteSizeTag (trait item)) rest) =
                        .error e := by
                    simpa [Round5.isFiniteSizeTag] using hlist
                  have hfold : zipLengthsFiniteEqualOn trait length rest = .error e := by
                    calc
                      _ = Except.map
                          (fun lengths =>
                            (rest.all (fun item => Round5.isFiniteSizeTag (trait item)) &&
                              lengths.all (fun n => lengths.all (fun m => decide (n = m))),
                             lengths.head?))
                          (List.mapM length
                            (List.takeWhile
                              (fun item => Round5.isFiniteSizeTag (trait item)) rest)) := ih
                      _ = .error e := by rw [hlist']; rfl
                  simp [zipLengthsFiniteEqualOn, htag, hfinite, hlen,
                    Round5.isFiniteSizeTag, hfold, hlist, Except.map]
              | ok lengths =>
                  have hlist' :
                      List.mapM length
                        (List.takeWhile
                          (fun item => Round5.isFiniteSizeTag (trait item)) rest) =
                        .ok lengths := by
                    simpa [Round5.isFiniteSizeTag] using hlist
                  have hfold :
                      zipLengthsFiniteEqualOn trait length rest =
                        .ok
                          (rest.all (fun item => Round5.isFiniteSizeTag (trait item)) &&
                            lengths.all (fun n => lengths.all (fun m => decide (n = m))),
                           lengths.head?) := by
                    calc
                      _ = Except.map
                          (fun lengths =>
                            (rest.all (fun item => Round5.isFiniteSizeTag (trait item)) &&
                              lengths.all (fun n => lengths.all (fun m => decide (n = m))),
                             lengths.head?))
                          (List.mapM length
                            (List.takeWhile
                              (fun item => Round5.isFiniteSizeTag (trait item)) rest)) := ih
                      _ = .ok
                          (rest.all (fun item => Round5.isFiniteSizeTag (trait item)) &&
                            lengths.all (fun n => lengths.all (fun m => decide (n = m))),
                           lengths.head?) := by rw [hlist']; rfl
                  have hmap :
                      List.mapM length
                        (List.takeWhile
                          (fun item => Round5.isFiniteSizeTag (trait item))
                          (itr :: rest)) =
                        .ok (m :: lengths) := by
                    simp [Round5.isFiniteSizeTag, htag, hfinite, hlen, hlist]
                  have htraitAll :
                      (itr :: rest).all
                        (fun item => Round5.isFiniteSizeTag (trait item)) =
                        rest.all
                          (fun item => Round5.isFiniteSizeTag (trait item)) := by
                    simp [Round5.isFiniteSizeTag, htag]
                  simp only [zipLengthsFiniteEqualOn, htag, hfinite, hlen,
                    hfold, hmap, Except.map, ok_bind, err_bind, pure_jl]
                  rw [htraitAll]
                  rw [zipLengthsPairwiseEq_cons]
                  simp [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
theorem productTraitCardinality_refuted : ¬ Round4.ProductSizeSound := by
  intro h
  have hcounts : Round4.CountsAgree
      [.hasLength, .isInfinite] [.finite 0, .infinite] := by
    apply Round4.CountsAgree.cons
    · exact ⟨0, rfl⟩
    · apply Round4.CountsAgree.cons
      · rfl
      · exact Round4.CountsAgree.nil
  have hbad := h [.hasLength, .isInfinite] [.finite 0, .infinite] hcounts
  simp [prodIteratorSizeDispatch, prodIteratorSizeDispatch2, sourceMethod1167,
    sourceMethod1155, sourceMethod1164, sourceMethod1165, Round4.Count.product,
    Round4.Count.agrees] at hbad

theorem productEmptyInfiniteQuery_refuted :
    ¬ Round5.ProductSizeQuerySound := by
  intro h
  let fieldtype : Unit → Nat → IteratorSizeTag :=
    fun _ index => if index = 1 then .hasLength else .isInfinite
  let p : ProductIterator Unit := ⟨()⟩
  have hcounts : Round5.CountsAgree
      [.hasLength, .isInfinite] [.finite 0, .infinite] := by
    constructor
    · exact ⟨0, rfl⟩
    · constructor
      · rfl
      · exact Round5.CountsAgree.nil
  have htags :
      (List.range 2).map (fun k => fieldtype p.iterators (k + 1)) =
        [.hasLength, .isInfinite] := by
    decide
  have hbad := h.2 fieldtype (fun tag => tag) p 2
    [.finite 0, .infinite] (by rw [htags]; exact hcounts)
  simp [sourceMethod1151, fieldtype, p, htags, sourceMethod1155,
    sourceMethod1167, sourceMethod1164, sourceMethod1165,
    prodIteratorSizeDispatch, prodIteratorSizeDispatch2,
    Round5.Count.product, Round5.Count.agrees] at hbad
  exact hbad

theorem takeModel_int_of_ge_max {I : Type} (xs : I) (n : Int)
    (hbig : 2 ^ 63 ≤ n) :
    CountValue.take xs n = .error (.inexactError "Int64") := by
  simp [CountValue.take, jint_convert_i64_out n (Or.inr hbig)]

theorem observeHistory {α S : Type}
    (run : Option S → Jl (Option (α × S))) :
    ∀ {start values final}, Round5.History run start values final →
      Round5.observe run values.length start = .ok values := by
  intro start values final h
  induction h with
  | nil st => rfl
  | cons hrun htail ih =>
      simp [Round5.observe, hrun, ih]

theorem dropAdvanceFromHistory {α S : Type}
    (run : Option S → Jl (Option (α × S))) :
    ∀ {start values final}, Round5.History run start values final →
      dropAdvance run values.length start = run final := by
  intro start values final h
  induction h with
  | nil st => rfl
  | cons hrun htail ih =>
      simp [dropAdvance, hrun, ih]

def dropFromRun {α S : Type}
    (run : Option S → Jl (Option (α × S))) (count : Nat)
    (initial : Option S) : Option S → Jl (Option (α × S))
  | none => dropAdvance run count initial
  | some state => run (some state)

theorem observeMapStateRound5 {α S : Type}
    (run : Option S → Jl (Option (α × S)))
    (stateMap : Option S → Option S)
    (hmap : ∀ state, stateMap (some state) = some state) :
    ∀ depth state,
      Round5.observe (fun state => run (stateMap state)) depth state =
        Round5.observe run depth (stateMap state) := by
  intro depth
  induction depth with
  | zero => intro state; rfl
  | succ depth ih =>
      intro state
      cases hrun : run (stateMap state) with
      | error e =>
          simp [Round5.observe, hrun]
      | ok result =>
          cases result with
          | none =>
              simp [Round5.observe, hrun]
          | some pair =>
              cases pair with
              | mk value next =>
                  simp [Round5.observe, hrun, hmap, ih]

theorem dropMapCons {α : Type} (count : Nat) (value : α)
    (result : Jl (List α)) :
    (result.map (List.cons value)).map (List.drop (count + 1)) =
      result.map (List.drop count) := by
  cases result with
  | error e => rfl
  | ok values =>
      change Except.ok (List.drop (count + 1) (value :: values)) =
        Except.ok (List.drop count values)
      rw [List.drop_succ_cons]

theorem observeDropFromRun {α S : Type}
    (run : Option S → Jl (Option (α × S))) :
    ∀ (count depth : Nat) (initial : Option S),
      Round5.observe (dropFromRun run count initial) (depth + 1) none =
        (Round5.observe run (count + depth + 1) initial).map
          (List.drop count) := by
  intro count
  induction count with
  | zero =>
      intro depth initial
      let stateMap : Option S → Option S :=
        fun state => match state with | none => initial | some state => some state
      have hmap : ∀ state, stateMap (some state) = some state := by
        intro state
        rfl
      have hobs := observeMapStateRound5 run stateMap hmap (depth + 1) none
      have hsame : dropFromRun run 0 initial =
          (fun state => run (stateMap state)) := by
        funext state
        cases state <;> rfl
      rw [hsame, hobs]
      cases hresult : Round5.observe run (depth + 1) initial with
      | error e => simp [hresult, Except.map, List.drop]
      | ok values => simp [hresult, Except.map, List.drop]
  | succ count ih =>
      intro depth initial
      cases hrun : run initial with
      | error e =>
          simp [Round5.observe, dropFromRun, dropAdvance, hrun,
            Except.map, List.drop]
      | ok result =>
          cases result with
          | none =>
              simp [Round5.observe, dropFromRun, dropAdvance, hrun,
                Except.map, List.drop]
          | some pair =>
              cases pair with
              | mk skipped next =>
                  have hleft :
                      Round5.observe (dropFromRun run (count + 1) initial)
                          (depth + 1) none =
                        Round5.observe (dropFromRun run count (some next))
                          (depth + 1) none := by
                    have hdropCount :
                        dropFromRun run (count + 1) initial =
                          dropFromRun run count (some next) := by
                      funext state
                      cases state with
                      | none => simp [dropFromRun, dropAdvance, hrun]
                      | some state => rfl
                    rw [hdropCount]
                  have hsource :
                      Round5.observe run (count + 1 + depth + 1) initial =
                        (Round5.observe run (count + depth + 1) (some next)).map
                          (List.cons skipped) := by
                    have hdepth :
                        count + 1 + depth + 1 =
                          (count + depth + 1) + 1 := by omega
                    rw [hdepth]
                    have hstep :
                        Round5.observe run ((count + depth + 1) + 1) initial =
                          (do
                            match ← run initial with
                            | none => pure []
                            | some (value, following) =>
                                pure (value :: (← Round5.observe run
                                  (count + depth + 1) (some following)))) := by
                      rfl
                    rw [hstep]
                    simp only [hrun, ok_bind, pure_jl]
                    rfl
                  rw [hleft, ih depth (some next), hsource, dropMapCons]


theorem historyAppendRound5 {α S : Type}
    (run : Option S → Jl (Option (α × S))) :
    ∀ {start before cut after final},
      Round5.History run start before cut →
      Round5.History run cut after final →
      Round5.History run start (before ++ after) final := by
  intro start before cut after final hbefore
  induction hbefore generalizing after final with
  | nil state =>
      intro hafter
      simpa using hafter
  | cons hrun htail ih =>
      intro hafter
      exact Round5.History.cons hrun (ih hafter)

theorem listDropAppendRound5 {α : Type} (before after : List α) :
    (before ++ after).drop before.length = after := by
  induction before with
  | nil => rfl
  | cons first remaining ih =>
      rw [List.length_cons, List.cons_append, List.drop_succ_cons]
      exact ih


theorem observeRepeatedModel {α : Type} (x : α) :
    ∀ depth (state : Option Unit),
      Round5.observe (m := Jl)
          (fun st => pure (iterateRepeated (repeatedModel x) st)) depth state =
        .ok (List.replicate depth x) := by
  intro depth
  induction depth with
  | zero => intro state; rfl
  | succ depth ih =>
      intro state
      have hrun : iterateRepeated (repeatedModel x) state = some (x, ()) := by
        cases state <;> rfl
      rw [Round5.observe]
      simp only [pure_jl, hrun, ok_bind]
      have htail :
          Round5.observe (m := Jl)
              (fun st => Except.ok (iterateRepeated (repeatedModel x) st))
              depth (some ()) = .ok (List.replicate depth x) := by
        simpa only [pure_jl] using ih (some ())
      rw [htail]
      simp [List.replicate_succ]

theorem sourceMethod1167_shapeTail (a b : IteratorSizeTag) (rest : List IteratorSizeTag) :
    sourceMethod1167 a b (rest ++ [.hasShape 0]) =
      prodIteratorSizeDispatch2 a
        (prodIteratorSizeDispatch2 b (rest.foldr prodIteratorSizeDispatch2 (.hasShape 0))) := by
  induction rest generalizing a b with
  | nil =>
      simp [sourceMethod1167, sourceMethod1155]
  | cons c rest ih =>
      simp only [List.cons_append, sourceMethod1167, List.foldr_cons]
      rw [ih b c]


theorem prodIteratorSizeDispatch_append_shape (tags : List IteratorSizeTag) :
    prodIteratorSizeDispatch (tags ++ [.hasShape 0]) =
      tags.foldr prodIteratorSizeDispatch2 (.hasShape 0) := by
  cases tags with
  | nil => rfl
  | cons a rest =>
      cases rest with
      | nil =>
          simp [prodIteratorSizeDispatch, prodIteratorSizeDispatch2, sourceMethod1155]
      | cons b rest =>
          cases rest with
          | nil =>
              change sourceMethod1167 a b ([] ++ [.hasShape 0]) =
                [a, b].foldr prodIteratorSizeDispatch2 (.hasShape 0)
              rw [sourceMethod1167_shapeTail a b []]
              rfl
          | cons c cs =>
              change sourceMethod1167 a b ((c :: cs) ++ [.hasShape 0]) =
                (a :: b :: c :: cs).foldr prodIteratorSizeDispatch2 (.hasShape 0)
              rw [sourceMethod1167_shapeTail a b (c :: cs)]
              rfl

theorem prodIteratorSizeFold_shapes (dimensions : List Nat) :
    (dimensions.map IteratorSizeTag.hasShape).foldr prodIteratorSizeDispatch2
        (.hasShape 0) = .hasShape dimensions.sum := by
  induction dimensions with
  | nil => rfl
  | cons dimension dimensions ih =>
      simp only [List.map_cons, List.foldr_cons]
      rw [ih]
      simp [prodIteratorSizeDispatch2, sourceMethod1160]

theorem prodIteratorSizeFold_classify (tags : List IteratorSizeTag) :
    (∀ tag ∈ tags, tag ≠ .isInfinite) →
    tags.foldr prodIteratorSizeDispatch2 (.hasShape 0) = .sizeUnknown ∨
      ∃ n, tags.foldr prodIteratorSizeDispatch2 (.hasShape 0) = .hasShape n := by
  induction tags with
  | nil =>
      intro _
      exact Or.inr ⟨0, rfl⟩
  | cons tag tags ih =>
      intro h
      have htail : ∀ t ∈ tags, t ≠ .isInfinite := by
        intro t ht
        exact h t (List.mem_cons_of_mem _ ht)
      cases tag with
      | sizeUnknown =>
          cases ih htail with
          | inl hunknown =>
              exact Or.inl (by
                simp [List.foldr_cons, prodIteratorSizeDispatch2, sourceMethod1166, hunknown])
          | inr hshape =>
              rcases hshape with ⟨n, hshape⟩
              exact Or.inl (by
                simp [List.foldr_cons, prodIteratorSizeDispatch2, sourceMethod1166, hshape])
      | hasLength =>
          cases ih htail with
          | inl hunknown =>
              exact Or.inl (by
                simp [List.foldr_cons, prodIteratorSizeDispatch2, sourceMethod1166, hunknown])
          | inr hshape =>
              rcases hshape with ⟨n, hshape⟩
              exact Or.inr ⟨n + 1, by
                simp [List.foldr_cons, prodIteratorSizeDispatch2, sourceMethod1158, hshape]⟩
      | hasShape dimension =>
          cases ih htail with
          | inl hunknown =>
              exact Or.inl (by
                simp [List.foldr_cons, prodIteratorSizeDispatch2, sourceMethod1166, hunknown])
          | inr hshape =>
              rcases hshape with ⟨n, hshape⟩
              exact Or.inr ⟨dimension + n, by
                simp [List.foldr_cons, prodIteratorSizeDispatch2, sourceMethod1160, hshape]⟩
      | isInfinite =>
          exact False.elim (h .isInfinite (by simp) rfl)

theorem finiteCountOfTagAgreement {tag : IteratorSizeTag} {count : Round4.Count}
    (h : Round4.Count.agrees tag count)
    (hunknown : tag ≠ .sizeUnknown) (hinfinite : tag ≠ .isInfinite) :
    ∃ n, count = .finite n := by
  cases tag with
  | sizeUnknown => exact False.elim (hunknown rfl)
  | isInfinite => exact False.elim (hinfinite rfl)
  | hasLength => exact h
  | hasShape dimension =>
      cases dimension with
      | zero => exact ⟨1, h⟩
      | succ dimension => exact h

theorem countProductFiniteCons (n : Nat) (counts : List Round4.Count) (k : Nat)
    (h : Round4.Count.product counts = .finite k) :
    Round4.Count.product (.finite n :: counts) = .finite (n * k) := by
  cases n with
  | zero => simp [Round4.Count.product]
  | succ n => simp [Round4.Count.product, h]

theorem productCountAgreement (tags : List IteratorSizeTag) :
    ∀ counts, (∀ tag ∈ tags, tag ≠ .isInfinite) →
      Round4.CountsAgree tags counts →
        Round4.Count.agrees (tags.foldr prodIteratorSizeDispatch2 (.hasShape 0))
          (Round4.Count.product counts) := by
  induction tags with
  | nil =>
      intro counts _ hcounts
      cases hcounts with
      | nil => simp [Round4.Count.agrees, Round4.Count.product]
  | cons tag tags ih =>
      intro counts hno hcounts
      have hnoTail : ∀ t ∈ tags, t ≠ .isInfinite := by
        intro t ht
        exact hno t (List.mem_cons_of_mem _ ht)
      have htailShape := prodIteratorSizeFold_classify tags hnoTail
      cases counts with
      | nil => cases hcounts
      | cons count counts =>
          cases hcounts with
          | cons hhead htail =>
              have htailAgreement := ih counts hnoTail htail
              cases tag with
              | sizeUnknown =>
                  cases htailShape with
                  | inl hunknown =>
                      simp [List.foldr_cons, prodIteratorSizeDispatch2, sourceMethod1166,
                        hunknown, Round4.Count.agrees]
                  | inr hshape =>
                      rcases hshape with ⟨dimension, hshape⟩
                      simp [List.foldr_cons, prodIteratorSizeDispatch2, sourceMethod1166,
                        hshape, Round4.Count.agrees]
              | hasLength =>
                  cases htailShape with
                  | inl hunknown =>
                      simp [List.foldr_cons, prodIteratorSizeDispatch2, sourceMethod1166,
                        hunknown, Round4.Count.agrees]
                  | inr hshape =>
                      rcases hshape with ⟨dimension, hshape⟩
                      have htailAg : Round4.Count.agrees (.hasShape dimension)
                          (Round4.Count.product counts) := by
                        simpa [hshape] using htailAgreement
                      have htailFinite :=
                        finiteCountOfTagAgreement htailAg (by simp) (by simp)
                      obtain ⟨k, hk⟩ := htailFinite
                      obtain ⟨n, hn⟩ :=
                        finiteCountOfTagAgreement hhead (by simp) (by simp)
                      rw [List.foldr_cons, hshape]
                      simp only [prodIteratorSizeDispatch2, sourceMethod1158]
                      rw [hn, countProductFiniteCons n counts k hk]
                      simp [Round4.Count.agrees]
              | hasShape dimension =>
                  cases htailShape with
                  | inl hunknown =>
                      simp [List.foldr_cons, prodIteratorSizeDispatch2, sourceMethod1166,
                        hunknown, Round4.Count.agrees]
                  | inr hshape =>
                      rcases hshape with ⟨tailDimension, hshape⟩
                      have htailAg : Round4.Count.agrees (.hasShape tailDimension)
                          (Round4.Count.product counts) := by
                        simpa [hshape] using htailAgreement
                      have htailFinite :=
                        finiteCountOfTagAgreement htailAg (by simp) (by simp)
                      obtain ⟨k, hk⟩ := htailFinite
                      obtain ⟨n, hn⟩ :=
                        finiteCountOfTagAgreement hhead (by simp) (by simp)
                      rw [List.foldr_cons, hshape]
                      simp only [prodIteratorSizeDispatch2, sourceMethod1160]
                      rw [hn, countProductFiniteCons n counts k hk]
                      cases hdim : dimension + tailDimension with
                      | zero =>
                          have hdimension : dimension = 0 := by omega
                          have htailDimension : tailDimension = 0 := by omega
                          have hcountOne : count = .finite 1 := by
                            simpa [hdimension, Round4.Count.agrees] using hhead
                          have hstartOne : n = 1 := by
                            rw [hn] at hcountOne
                            injection hcountOne with hstartOne
                          have htailOne : Round4.Count.product counts = .finite 1 := by
                            simpa [htailDimension, Round4.Count.agrees] using htailAg
                          have hcountTailOne : k = 1 := by
                            rw [hk] at htailOne
                            injection htailOne with hcountTailOne
                          simp [Round4.Count.agrees, hdim, hstartOne, hcountTailOne]
                      | succ totalDimension =>
                          simp [Round4.Count.agrees, hdim]
              | isInfinite =>
                  exact False.elim (hno .isInfinite (by simp) rfl)


private def round5CountToRound4 : Round5.Count → Round4.Count
  | .finite n => .finite n
  | .infinite => .infinite

private theorem round5CountAgreesToRound4
    (tag : IteratorSizeTag) (count : Round5.Count) :
    Round5.Count.agrees tag count ↔
      Round4.Count.agrees tag (round5CountToRound4 count) := by
  cases tag with
  | sizeUnknown =>
      cases count <;>
        simp [Round5.Count.agrees, Round4.Count.agrees, round5CountToRound4]
  | hasLength =>
      cases count <;>
        simp [Round5.Count.agrees, Round4.Count.agrees, round5CountToRound4]
  | hasShape n =>
      cases n with
      | zero =>
          cases count <;>
            simp [Round5.Count.agrees, Round4.Count.agrees, round5CountToRound4]
      | succ n =>
          cases count <;>
            simp [Round5.Count.agrees, Round4.Count.agrees, round5CountToRound4]
  | isInfinite =>
      cases count <;>
        simp [Round5.Count.agrees, Round4.Count.agrees, round5CountToRound4]

private theorem round5CountsAgreeToRound4 {tags : List IteratorSizeTag}
    {counts : List Round5.Count} (h : Round5.CountsAgree tags counts) :
    Round4.CountsAgree tags (counts.map round5CountToRound4) := by
  induction h with
  | nil => exact Round4.CountsAgree.nil
  | cons hhead htail ih =>
      exact Round4.CountsAgree.cons
        ((round5CountAgreesToRound4 _ _).mp hhead) ih

private theorem round5CountProductToRound4 :
    ∀ counts : List Round5.Count,
      round5CountToRound4 (Round5.Count.product counts) =
        Round4.Count.product (counts.map round5CountToRound4) := by
  intro counts
  induction counts with
  | nil => rfl
  | cons count counts ih =>
      cases count with
      | finite n =>
          cases n with
          | zero =>
              simp [Round5.Count.product, Round4.Count.product, round5CountToRound4]
          | succ n =>
              cases hprod : Round5.Count.product counts with
              | finite k =>
                  have htail :
                      Round4.Count.product (counts.map round5CountToRound4) =
                        .finite k := by
                    rw [← ih, hprod]
                    rfl
                  simp [Round5.Count.product, Round4.Count.product,
                    round5CountToRound4, hprod, htail]
              | infinite =>
                  have htail :
                      Round4.Count.product (counts.map round5CountToRound4) =
                        .infinite := by
                    rw [← ih, hprod]
                    rfl
                  simp [Round5.Count.product, Round4.Count.product,
                    round5CountToRound4, hprod, htail]
      | infinite =>
          cases hprod : Round5.Count.product counts with
          | finite k =>
              cases k with
              | zero =>
                  have htail :
                      Round4.Count.product (counts.map round5CountToRound4) =
                        .finite 0 := by
                    rw [← ih, hprod]
                    rfl
                  simp [Round5.Count.product, Round4.Count.product,
                    round5CountToRound4, hprod, htail]
              | succ k =>
                  have htail :
                      Round4.Count.product (counts.map round5CountToRound4) =
                        .finite (k + 1) := by
                    rw [← ih, hprod]
                    rfl
                  simp [Round5.Count.product, Round4.Count.product,
                    round5CountToRound4, hprod, htail]
          | infinite =>
              have htail :
                  Round4.Count.product (counts.map round5CountToRound4) =
                    .infinite := by
                rw [← ih, hprod]
                rfl
              simp [Round5.Count.product, Round4.Count.product,
                round5CountToRound4, hprod, htail]

private theorem round5ProductCountAgreement (tags : List IteratorSizeTag) :
    ∀ counts, (∀ tag ∈ tags, tag ≠ .isInfinite) →
      Round5.CountsAgree tags counts →
        Round5.Count.agrees (tags.foldr prodIteratorSizeDispatch2 (.hasShape 0))
          (Round5.Count.product counts) := by
  intro counts hno hcounts
  have hcounts4 := round5CountsAgreeToRound4 hcounts
  have hproduct4 :=
    productCountAgreement tags (counts.map round5CountToRound4) hno hcounts4
  rw [← round5CountProductToRound4 counts] at hproduct4
  exact (round5CountAgreesToRound4 _ _).2 hproduct4

private theorem productQueryShapeOfMapM (tags : List IteratorSizeTag)
    (dimensions : List Nat)
    (hmap : tags.mapM Round5.shapeDimensions = some dimensions) :
    tags.foldr prodIteratorSizeDispatch2 (.hasShape 0) =
      .hasShape dimensions.sum := by
  induction tags generalizing dimensions with
  | nil =>
      have hdimensions : dimensions = [] := by
        simpa using hmap.symm
      subst dimensions
      rfl
  | cons tag tags ih =>
      cases tag with
      | sizeUnknown =>
          simp [Round5.shapeDimensions, List.mapM_cons] at hmap
      | isInfinite =>
          simp [Round5.shapeDimensions, List.mapM_cons] at hmap
      | hasLength =>
          cases hrest : tags.mapM Round5.shapeDimensions with
          | none =>
              simp [Round5.shapeDimensions, List.mapM_cons, hrest] at hmap
          | some ds =>
              have hdimensions : 1 :: ds = dimensions := by
                simpa [Round5.shapeDimensions, List.mapM_cons, hrest] using hmap
              have htail := ih ds hrest
              rw [List.foldr_cons, htail, ← hdimensions]
              simp [prodIteratorSizeDispatch2, sourceMethod1158,
                List.sum_cons, Nat.add_comm]
      | hasShape d =>
          cases hrest : tags.mapM Round5.shapeDimensions with
          | none =>
              simp [Round5.shapeDimensions, List.mapM_cons, hrest] at hmap
          | some ds =>
              have hdimensions : d :: ds = dimensions := by
                simpa [Round5.shapeDimensions, List.mapM_cons, hrest] using hmap
              have htail := ih ds hrest
              rw [List.foldr_cons, htail, ← hdimensions]
              simp [prodIteratorSizeDispatch2, sourceMethod1160, List.sum_cons]

theorem productFiniteQuerySound_proven : Round5.ProductFiniteQuerySound := by
  intro T F fieldtype trait p N counts tags hno hcounts
  constructor
  · change Round5.Count.agrees
      (prodIteratorSizeDispatch (tags ++ [.hasShape 0]))
      (Round5.Count.product counts)
    rw [prodIteratorSizeDispatch_append_shape]
    exact round5ProductCountAgreement tags counts hno hcounts
  · intro dimensions hmap
    change prodIteratorSizeDispatch (tags ++ [.hasShape 0]) =
      .hasShape dimensions.sum
    rw [prodIteratorSizeDispatch_append_shape]
    exact productQueryShapeOfMapM tags dimensions hmap

theorem productShapeFinite_proven : Round4.ProductShapeFinite := by
  constructor
  · intro tags counts hno hcounts
    simpa [prodIteratorSizeDispatch_append_shape] using
      productCountAgreement tags counts hno hcounts
  · intro dimensions
    rw [prodIteratorSizeDispatch_append_shape]
    exact prodIteratorSizeFold_shapes dimensions


theorem observeMapState {α S : Type}
    (run : Option S → Jl (Option (α × S))) (stateMap : Option S → Option S)
    (h : ∀ state, stateMap (some state) = some state) :
    ∀ depth state,
      Round4.observe (fun st => run (stateMap st)) depth state =
        Round4.observe run depth (stateMap state) := by
  intro depth
  induction depth with
  | zero =>
      intro state
      rfl
  | succ depth ih =>
      intro state
      simp [Round4.observe, h, ih]
def enumerateReverseRun {I R α S : Type}
    (run : R → Option S → Jl (Option (α × S)))
    (r : Reverse (Enumerate I)) (counter : JInt64) (ri : R) (start : S)
    (state : Option (JInt64 × R × S)) :
    Jl (Option ((JInt64 × α) × (JInt64 × R × S))) :=
  match state with
  | none => sourceMethod228 run (fun a b => pure (a - b)) r (counter, ri, some start)
  | some (i, source, next) => sourceMethod228 run (fun a b => pure (a - b)) r (i, source, some next)

theorem enumerateReverseObserveSomeReset {I R α S : Type}
    (run : R → Option S → Jl (Option (α × S)))
    (r : Reverse (Enumerate I)) (baseCounter : JInt64) (baseRi : R) (baseStart : S)
    (counter : JInt64) (ri : R) (start : S) (depth : Nat) :
    Round4.observe (enumerateReverseRun run r baseCounter baseRi baseStart)
        depth (some (counter, ri, start)) =
      Round4.observe (enumerateReverseRun run r counter ri start) depth none := by
  let stateMap : Option (JInt64 × R × S) → Option (JInt64 × R × S) :=
    fun state => match state with
      | none => some (counter, ri, start)
      | some state => some state
  have hmap := observeMapState
    (enumerateReverseRun run r baseCounter baseRi baseStart)
    stateMap (by intro state; rfl) depth none
  have hruns :
      (fun state =>
        enumerateReverseRun run r baseCounter baseRi baseStart (stateMap state)) =
      enumerateReverseRun run r counter ri start := by
    funext state
    cases state with
    | none => rfl
    | some state =>
        rcases state with ⟨i, source, next⟩
        rfl
  rw [hruns] at hmap
  simpa [stateMap] using hmap.symm

theorem enumerateReverseCounterStep (counter : JInt64) (k : Nat) :
    JInt.lit .i64 (counter.val - Int.ofNat (k + 1)) =
      JInt.lit .i64 ((counter - JInt.lit .i64 1).val - Int.ofNat k) := by
  apply JuliaLean.Proofs.base.int.jint_eq
  have hone : (JInt.lit .i64 (1 : Int)).val = 1 := by
    exact jint_lit_i64_val 1 (by omega) (by omega)
  have hwrapOne : wrapInt .i64 1 = 1 := by
    rw [← jint_lit_val .i64 1]
    exact hone
  simp only [jint_lit_val, jint_sub_val, hwrapOne]
  rw [JuliaLean.Proofs.base.int.wrapInt_sub_left]
  congr 1
  have hkplus : Int.ofNat (k + 1) = (k : Int) + 1 := by simp
  rw [hkplus]
  simp only [Int.ofNat_eq_natCast]
  omega

theorem zipIdxSuccShift {α : Type} (xs : List α) (start : Nat) :
    xs.zipIdx (start + 1) =
      (xs.zipIdx start).map (fun (x, k) => (x, k + 1)) := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.zipIdx_cons, List.map_cons]
      rw [ih (start + 1)]

theorem zipIdxReverseCounterCons {α : Type} (counter : JInt64) (value : α)
    (xs : List α) :
    (value :: xs).zipIdx.map
        (fun (x, k) => (JInt.lit .i64 (counter.val - Int.ofNat k), x)) =
      (counter, value) :: xs.zipIdx.map
        (fun (x, k) =>
          (JInt.lit .i64 ((counter - JInt.lit .i64 1).val - Int.ofNat k), x)) := by
  have hcounter : JInt.lit .i64 counter.val = counter := by
    apply JuliaLean.Proofs.base.int.jint_eq
    rw [jint_lit_val, JuliaLean.Proofs.base.int.wrapInt_val]
  rw [List.zipIdx_cons]
  simp only [List.map_cons]
  rw [List.cons.injEq]
  constructor
  · apply Prod.ext
    simpa using hcounter
    · rfl
  · have hshift : xs.zipIdx 1 =
        (xs.zipIdx 0).map (fun (x, k) => (x, k + 1)) := by
      simpa using zipIdxSuccShift xs 0
    rw [hshift]
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro pair _
    rcases pair with ⟨x, k⟩
    exact congrArg (fun value : JInt64 => (value, x))
      (enumerateReverseCounterStep counter k)

theorem enumerateReverseState_proven : Round4.EnumerateReverseState := by
  intro I R α S run r ri counter start depth
  change Round4.observe (enumerateReverseRun run r counter ri start) depth none =
    (Round4.observe (run ri) depth (some start)).map
      (fun xs => xs.zipIdx |>.map
        (fun (x, k) => (JInt.lit .i64 (counter.val - Int.ofNat k), x)))
  induction depth generalizing counter start with
  | zero => rfl
  | succ depth ih =>
      cases hrun : run ri (some start) with
      | error e =>
          simp [Round4.observe, enumerateReverseRun, sourceMethod228,
            hrun, Except.map]
      | ok result =>
          cases result with
          | none =>
              simp [Round4.observe, enumerateReverseRun, sourceMethod228,
                hrun, Except.map]
          | some pair =>
              cases pair with
              | mk value next =>
                  let nextCounter := counter - JInt.lit .i64 1
                  have hstep :
                      enumerateReverseRun run r counter ri start none =
                        .ok (some ((counter, value), (nextCounter, ri, next))) := by
                    simp [enumerateReverseRun, sourceMethod228, hrun, nextCounter]
                  have hleft := observeSuccessStep
                    (enumerateReverseRun run r counter ri start) depth none
                    (counter, value) (nextCounter, ri, next) hstep
                  have hreset := enumerateReverseObserveSomeReset run r counter ri start
                    nextCounter ri next depth
                  have htail := ih nextCounter next
                  have hsource := observeSuccessStep
                    (run ri) depth (some start) value next hrun
                  rw [hleft, hreset, htail, hsource]
                  cases hobs : Round4.observe (run ri) depth (some next) with
                  | error e => simp [hobs, Except.map]
                  | ok xs =>
                      simp only [hobs, Except.map]
                      exact congrArg Except.ok
                        (zipIdxReverseCounterCons counter value xs).symm

theorem andTraitsSpec_proven : Round4.AndTraitsSpec := by
  constructor
  · intro a b
    cases a <;> cases b <;>
      simp [andIteratorSizeDispatch, andIteratorSizeSame, andIteratorSizeSameShape,
        andIteratorSizeShapeShape, andIteratorSizeLengthShape, andIteratorSizeShapeLength,
        andIteratorSizeOther, eq_comm] <;>
      split <;> simp_all [andIteratorSizeDispatch, andIteratorSizeSameShape,
        andIteratorSizeShapeShape, eq_comm]
  constructor
  · intro a
    cases a <;>
      simp [andIteratorSizeDispatch, andIteratorSizeSame, andIteratorSizeSameShape,
        andIteratorSizeShapeShape, andIteratorSizeLengthShape, andIteratorSizeShapeLength,
        andIteratorSizeOther]
  constructor
  · intro a b
    cases a <;> cases b <;>
      simp [andIteratorSizeDispatch, andIteratorSizeSame, andIteratorSizeSameShape,
        andIteratorSizeShapeShape, andIteratorSizeLengthShape, andIteratorSizeShapeLength,
        andIteratorSizeOther, Round4.isFiniteSizeTag] <;>
      split <;> simp_all [andIteratorSizeDispatch, andIteratorSizeSameShape,
        andIteratorSizeShapeShape, Round4.isFiniteSizeTag, eq_comm]
  constructor
  · intro a b n
    cases a <;> cases b <;>
      simp [andIteratorSizeDispatch, andIteratorSizeSame, andIteratorSizeSameShape,
        andIteratorSizeShapeShape, andIteratorSizeLengthShape, andIteratorSizeShapeLength,
        andIteratorSizeOther] <;>
      split <;> simp_all [andIteratorSizeDispatch, andIteratorSizeSameShape,
        andIteratorSizeShapeShape, eq_comm] <;> omega
  constructor
  · intro a b
    cases a <;> cases b <;>
      simp [andIteratorSizeDispatch, andIteratorSizeSame, andIteratorSizeSameShape,
        andIteratorSizeShapeShape, andIteratorSizeLengthShape, andIteratorSizeShapeLength,
        andIteratorSizeOther] <;>
      split <;> simp_all [andIteratorSizeDispatch, andIteratorSizeSameShape,
        andIteratorSizeShapeShape, eq_comm]
  · intro a b
    cases a <;> cases b <;>
      simp [andIteratorEltypeDispatch, andIteratorEltypeSame, andIteratorEltypeOther]

theorem onlyCorrect_proven : Round4.OnlyCorrect := by
  intro α S itr
  cases hfirst : itr.run none with
  | error e =>
      simp [onlyIterator_eq, onlyValue_eq, Round4.observe, Round4.cardinalityOne, hfirst]
  | ok result =>
      cases result with
      | none =>
          simp [onlyIterator_eq, onlyValue_eq, Round4.observe, Round4.cardinalityOne, hfirst]
      | some pair =>
          rcases pair with ⟨x, state⟩
          cases hsecond : itr.run (some state) with
          | error e =>
              simp [onlyIterator_eq, onlyValue_eq, Round4.observe, Round4.cardinalityOne,
                hfirst, hsecond]
          | ok result =>
              cases result with
              | none =>
                  simp [onlyIterator_eq, onlyValue_eq, Round4.observe, Round4.cardinalityOne,
                    hfirst, hsecond]
              | some pair =>
                  simp [onlyIterator_eq, onlyValue_eq, Round4.observe, Round4.cardinalityOne,
                    hfirst, hsecond]

theorem nthZipNonpositive_refuted : ¬ Round4.NthZipNonpositive := by
  intro h
  have hbad := h ([] : List (IteratorModel Unit Nat)) 0 (by decide)
  simp [nthZipValues, nthZip, nthCurry, List.mapM, List.mapM.loop] at hbad




@[simp] theorem restStep_run {I α S : Type}
    (run : I → Option S → Jl (Option (α × S))) (r : Rest I S) (st : Option S) :
    restStep run r st = run r.itr (some (st.getD r.st)) := rfl

@[simp] theorem peelStep_run {I α S : Type}
    (run : I → Option S → Jl (Option (α × S))) (itr : I) :
    peelStep run itr = (do
      match ← run itr none with
      | none => pure none
      | some (value, state) => pure (some (value, restWithState itr state))) := by
  cases h : run itr none with
  | error e => simp [peelStep, peel, liftJl, Bind.bind, Except.bind, Pure.pure, Except.pure,
      JuliaLean.base.iterators.bind, ret, h]
  | ok result => cases result <;> simp [peelStep, peel, liftJl, Bind.bind, Except.bind,
      Pure.pure, Except.pure, JuliaLean.base.iterators.bind, ret, h]

theorem restSound_proven : Round5.RestSound := by
  intro α S itr history st _ _
  have hobs (baseState : S) : ∀ depth state,
      Round5.observe (restStep (fun xs s => xs.run s) (restWithState itr baseState)) depth state =
        Round5.observe itr.run depth
          (match state with | none => some baseState | some current => some current) := by
    have hfun : restStep (fun xs s => xs.run s) (restWithState itr baseState) =
        (fun state => itr.run (match state with | none => some baseState | some current => some current)) := by
      funext state
      cases state <;> rfl
    intro depth state
    rw [hfun]
    exact observeMapStateRound5 itr.run
      (fun state => match state with | none => some baseState | some current => some current)
      (by intro state; rfl) depth state
  refine ⟨?_, ?_, (fun _ => rfl), rfl, ?_⟩
  · intro depth; simpa using hobs st depth none
  · intro old depth; simpa [restOnRest, restWithState] using hobs st depth none
  · cases itr.iteratorSize <;> rfl

theorem observeRestState {I α S : Type}
    (run : I → Option S → Jl (Option (α × S))) (i : Rest I S) :
    ∀ depth state,
      Round4.observe (fun st => restStep run i st) depth state =
        Round4.observe (fun st => run i.itr st) depth
          (match state with | none => some i.st | some s => some s) := by
  intro depth state
  have heq : (fun st => restStep run i st) =
      (fun st => run i.itr (match st with | none => some i.st | some s => some s)) := by
    funext st; cases st <;> rfl
  rw [heq]
  exact observeMapState (fun st => run i.itr st)
    (fun st => match st with | none => some i.st | some s => some s)
    (by intro s; rfl) depth state

theorem peelReconstructs_proven : Round4.PeelReconstructs := by
  intro α S itr depth
  cases hfirst : itr.run none with
  | error e => simp [peelStep_run, hfirst, Round4.observe]
  | ok result =>
    cases result with
    | none => simp [peelStep_run, hfirst, Round4.observe]
    | some pair =>
      rcases pair with ⟨value, state⟩
      have hrest := observeRestState (fun xs st => xs.run st)
        (restWithState itr state) depth none
      have hmap := congrArg (fun result : Jl (List α) => do
        let values ← result
        pure (value :: values)) hrest
      simpa only [peelStep_run, hfirst, Round4.observe, restWithState,
        ok_bind, pure_jl] using hmap

theorem tupleValueList_length {I α : Type} {ks : List I}
    (values : TupleVals (fun _ : I => α) ks) :
    (tupleValueList values).length = ks.length := by
  induction values <;> simp_all [tupleValueList]

theorem zipRowArity_proven : Round4.ZipRowArity := by
  intro I α S run inputs values states h
  let ops : ZipCalls Jl (fun _ : I × Option S => Unit) (fun _ => α) (fun _ => S) :=
    { run := fun i _ st => run i.1 st, done := fun _ _ _ => pure none }
  change (do
    let outputs ← zipInOrder ops (tupleOfList inputs) (tupleOptions inputs)
    pure (outputs.map fun xs =>
      ((tupleValueList xs).map Prod.fst, (tupleValueList xs).map (fun (x : α × S) => some x.2)))) =
      .ok (some (values, states)) at h
  cases hr : zipInOrder ops (tupleOfList inputs) (tupleOptions inputs) with
  | error e => simp [hr] at h
  | ok output =>
    cases output with
    | none => simp [hr] at h
    | some row =>
      have heq : (tupleValueList row).map Prod.fst = values ∧
          (tupleValueList row).map (fun x => some x.2) = states := by
        simpa [hr] using h
      rcases heq with ⟨hv, hs⟩
      rw [← hv, ← hs]
      simp [tupleValueList_length]

theorem emptyZipInfinite_proven : Round4.EmptyZipInfinite := by
  intro α S depth
  let run := (zipObservation (zipModel ([] : List (IteratorModel α S)))).run
  have hr (st : Option (TupleVals (fun _ : IteratorModel α S => S) [])) :
      run st = .ok (some ([], .nil)) := by
    cases st with
    | none => rfl
    | some states => cases states; rfl
  have hobs : ∀ d st,
      Round4.observe run d st = .ok (List.replicate d []) := by
    intro d
    induction d with
    | zero => intro st; rfl
    | succ d ih =>
      intro st
      rw [Round4.observe, hr st]
      simp [Bind.bind, Pure.pure, List.replicate_succ, ih]
  exact hobs depth none

theorem mkDrop_native {I : Type} (xs : I) (n : JInt64) (hn : 0 ≤ n.val) :
    CountValue.rawDrop xs n.val = .ok ⟨xs, n⟩ := by
  have hneg : ¬ n.val < 0 := by omega
  simp [CountValue.rawDrop, hneg, jint_convert_i64_self, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem dropModel_native {I : Type} (xs : I) (n : JInt64) (hn : 0 ≤ n.val) :
    CountValue.drop xs n.val = .ok ⟨xs, n⟩ := by
  simp [CountValue.drop, jint_convert_i64_self, hn, Bind.bind, Except.bind]

theorem dropDropCorrect_refuted : ¬ Round4.DropDropCorrect := by
  intro h
  let xs := listIterator ([] : List Unit)
  let m : JInt64 := ⟨2 ^ 63 - 1, by decide⟩
  let one : JInt64 := ⟨1, by decide⟩
  have hm : 0 ≤ m.val := by decide
  have hone : 0 ≤ one.val := by decide
  obtain ⟨first, second, hfirst, hsecond, _⟩ := h.1 xs m.val one.val hm hone
  have hdrop := dropModel_native xs m hm
  have hfirst_eq : first = ⟨xs, m⟩ := by
    rw [hdrop] at hfirst
    exact (Except.ok.inj hfirst).symm
  have hsum : one.val + m.val = 2 ^ 63 := by decide
  have hwrap : (JInt.wrap .i64 (2 ^ 63 : Int)).val = -(2 ^ 63 : Int) := by
    simp [JInt.wrap, wrapInt, IntTy.signed, IntTy.bits]
  have hbad : CountValue.dropDrop ⟨xs, m⟩ one.val =
      .error (.argumentError "Drop length must be non-negative") := by
    simp only [CountValue.dropDrop, dropDropModel, CountValue.toInt, jint_convert_i64_self,
      ok_bind, CountValue.native_add, CountValue.dropConstructor_eq]
    rw [hsum, hwrap]
    simp
  rw [hfirst_eq, hbad] at hsecond
  cases hsecond

theorem takeStep_equation {I α S : Type}
    (run : I → Option S → Jl (Option (α × S))) (t : Take I)
    (state : Option (JInt64 × S)) :
    takeStep run t state =
      (if ((state.map Prod.fst).getD t.n).val ≤ 0 then .ok none else do
        match ← run t.xs (state.map Prod.snd) with
        | none => pure none
        | some (value, next) =>
            pure (some (value,
              (JuliaLean.base.int.sub_int ((state.map Prod.fst).getD t.n)
                (JInt.lit .i64 1), next)))) := by
  cases state with
  | none =>
    by_cases hz : t.n.val ≤ 0
    · simp [takeStep, iterateTake, hz, ret, Bind.bind, Pure.pure]
    · cases hr : run t.xs none with
      | error e => simp [takeStep, iterateTake, hz, liftJl, hr, ret,
          Bind.bind, Except.bind, Pure.pure, Except.pure, JuliaLean.base.iterators.bind]
      | ok result => cases result <;>
          simp [takeStep, iterateTake, hz, liftJl, hr, ret,
            Bind.bind, Except.bind, Pure.pure, Except.pure, JuliaLean.base.iterators.bind]
  | some pair =>
    rcases pair with ⟨n, source⟩
    by_cases hz : n.val ≤ 0
    · simp [takeStep, iterateTake, hz, ret, Bind.bind, Pure.pure]
    · cases hr : run t.xs (some source) with
      | error e => simp [takeStep, iterateTake, hz, liftJl, hr, ret,
          Bind.bind, Except.bind, Pure.pure, Except.pure, JuliaLean.base.iterators.bind]
      | ok result => cases result <;>
          simp [takeStep, iterateTake, hz, liftJl, hr, ret,
            Bind.bind, Except.bind, Pure.pure, Except.pure, JuliaLean.base.iterators.bind]

theorem nativeCount_pred (n : JInt64) (hn : 0 < n.val) :
    (JuliaLean.base.int.sub_int n (JInt.lit .i64 1)).val = n.val - 1 := by
  rw [JuliaLean.Proofs.base.int.sub_int_val]
  change wrapInt .i64 (n.val - 1) = n.val - 1
  apply wrapInt_of_inRange
  have hmax := n.property.2
  change n.val ≤ 2 ^ 63 - 1 at hmax
  change -(2 ^ 63 : Int) ≤ n.val - 1 ∧ n.val - 1 ≤ 2 ^ 63 - 1
  constructor <;> omega

theorem observeTakePrefixFromState {I α S : Type}
    (run : I → Option S → Jl (Option (α × S))) (t : Take I) :
    ∀ depth (state : Option (JInt64 × S)),
      0 ≤ ((state.map Prod.fst).getD t.n).val →
      Round5.observe (takeStep run t) depth state =
        Round5.observe (run t.xs)
          (min depth ((state.map Prod.fst).getD t.n).val.toNat)
          (state.map Prod.snd) := by
  intro depth
  induction depth with
  | zero => intro state hn; rfl
  | succ depth ih =>
    intro state hn
    let n := (state.map Prod.fst).getD t.n
    let source := state.map Prod.snd
    change Round5.observe (takeStep run t) (depth + 1) state =
      Round5.observe (run t.xs) (min (depth + 1) n.val.toNat) source
    by_cases hz : n.val ≤ 0
    · have hzero : n.val.toNat = 0 := by omega
      simp [Round5.observe, takeStep_equation, hz, hzero, n, source,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    · have hpos : 0 < n.val := by omega
      let previous := JuliaLean.base.int.sub_int n (JInt.lit .i64 1)
      have hprevious : previous.val = n.val - 1 := nativeCount_pred n hpos
      have hpreviousNonneg : 0 ≤ previous.val := by omega
      have hnat : n.val.toNat = previous.val.toNat + 1 := by omega
      have hmin : min (depth + 1) n.val.toNat = min depth previous.val.toNat + 1 := by
        rw [hnat, Nat.succ_min_succ]
      rw [hmin]
      cases hr : run t.xs source with
      | error e =>
        simp [Round5.observe, takeStep_equation, show ¬ n.val ≤ 0 by omega,
          hr, n, source, Bind.bind, Except.bind, Pure.pure, Except.pure]
      | ok result =>
        cases result with
        | none =>
          simp [Round5.observe, takeStep_equation, show ¬ n.val ≤ 0 by omega,
            hr, n, source, Bind.bind, Except.bind, Pure.pure, Except.pure]
        | some pair =>
          rcases pair with ⟨value, next⟩
          have htail := ih (some (previous, next)) hpreviousNonneg
          simpa [Round5.observe, takeStep_equation, show ¬ n.val ≤ 0 by omega,
            hr, n, source, previous, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map]
            using congrArg (Except.map (List.cons value)) htail

theorem mkTake_native {I : Type} (xs : I) (n : JInt64) (hn : 0 ≤ n.val) :
    CountValue.rawTake xs n.val = .ok ⟨xs, n⟩ := by
  have hneg : ¬ n.val < 0 := by omega
  simp [CountValue.rawTake, hneg, jint_convert_i64_self, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem takeModel_native {I : Type} (xs : I) (n : JInt64) (hn : 0 ≤ n.val) :
    CountValue.take xs n.val = .ok ⟨xs, n⟩ := by
  simp [CountValue.take, jint_convert_i64_self, hn, Bind.bind, Except.bind]

theorem takePrefix_proven : Round5.TakePrefix := by
  intro α S itr n hn
  by_cases hfit : n ≤ IntTy.max .i64
  · simp only [if_pos hfit]
    have hbound : IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max := by
      change -(2 ^ 63 : Int) ≤ n ∧ n ≤ 2 ^ 63 - 1
      change n ≤ 2 ^ 63 - 1 at hfit
      omega
    let count : JInt64 := ⟨n, hbound⟩
    refine ⟨⟨itr, count⟩, takeModel_native itr count hn, ?_⟩
    intro depth
    simpa [count] using observeTakePrefixFromState
      (fun xs st => xs.run st) ⟨itr, count⟩ depth none hn
  · simp only [if_neg hfit]
    have hbig : 2 ^ 63 ≤ n := by
      change ¬ n ≤ 2 ^ 63 - 1 at hfit
      omega
    exact takeModel_int_of_ge_max itr n hbig

theorem takeTakeCorrect_proven : Round5.TakeTakeCorrect := by
  intro α S itr a b ha hb
  by_cases hA : a ≤ IntTy.max .i64
  · simp only [if_pos hA]
    have hAbound : IntTy.i64.min ≤ a ∧ a ≤ IntTy.i64.max := by
      change -(2 ^ 63 : Int) ≤ a ∧ a ≤ 2 ^ 63 - 1
      change a ≤ 2 ^ 63 - 1 at hA
      omega
    let a64 : JInt64 := ⟨a, hAbound⟩
    refine ⟨⟨itr, a64⟩, takeModel_native itr a64 ha, ?_⟩
    by_cases hB : b ≤ IntTy.max .i64
    · simp only [if_pos hB]
      have hBbound : IntTy.i64.min ≤ b ∧ b ≤ IntTy.i64.max := by
        change -(2 ^ 63 : Int) ≤ b ∧ b ≤ 2 ^ 63 - 1
        change b ≤ 2 ^ 63 - 1 at hB
        omega
      let b64 : JInt64 := ⟨b, hBbound⟩
      have hbconv : JInt.convert IntTy.i64.name .i64 b = .ok b64 := by
        exact jint_convert_i64_self b64
      by_cases hba : b ≤ a
      · have hnat : b.toNat ≤ a.toNat := by omega
        refine ⟨⟨itr, b64⟩, ?_, ?_⟩
        · simp [CountValue.takeTake, hbconv, a64, b64, hba, show ¬ b < 0 by omega,
            Bind.bind, Except.bind]
        · intro depth
          simpa [a64, b64, Nat.min_eq_right hnat] using
            observeTakePrefixFromState (fun xs st => xs.run st) ⟨itr, b64⟩ depth none hb
      · have hab : a ≤ b := by omega
        have hnat : a.toNat ≤ b.toNat := by omega
        refine ⟨⟨itr, a64⟩, ?_, ?_⟩
        · simp [CountValue.takeTake, hbconv, a64, b64, hba, show ¬ a < 0 by omega,
            Bind.bind, Except.bind]
        · intro depth
          simpa [a64, b64, Nat.min_eq_left hnat] using
            observeTakePrefixFromState (fun xs st => xs.run st) ⟨itr, a64⟩ depth none ha
    · simp only [if_neg hB]
      have hbig : 2 ^ 63 ≤ b := by
        change ¬ b ≤ 2 ^ 63 - 1 at hB
        omega
      simp [CountValue.takeTake, jint_convert_i64_out b (Or.inr hbig), Bind.bind, Except.bind]
  · simp only [if_neg hA]
    have hbig : 2 ^ 63 ≤ a := by
      change ¬ a ≤ 2 ^ 63 - 1 at hA
      omega
    exact takeModel_int_of_ge_max itr a hbig

theorem repeatedOutputs_proven : Round5.RepeatedOutputs := by
  constructor
  · intro α x depth
    exact observeRepeatedModel x depth none
  · intro α x n hn
    by_cases hfit : n ≤ IntTy.max .i64
    · simp only [if_pos hfit]
      have hbound : IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max := by
        change -(2 ^ 63 : Int) ≤ n ∧ n ≤ 2 ^ 63 - 1
        change n ≤ 2 ^ 63 - 1 at hfit
        omega
      let count : JInt64 := ⟨n, hbound⟩
      refine ⟨⟨repeatedModel x, count⟩, ?_, ?_⟩
      · simp [CountValue.repeated, count, JInt.convert, hbound, show ¬ n < 0 by omega]
      · intro depth
        have hprefix := observeTakePrefixFromState
          (fun rep st => pure (iterateRepeated rep st)) ⟨repeatedModel x, count⟩ depth none hn
        rw [hprefix]
        exact observeRepeatedModel x (min depth n.toNat) none
    · simp only [if_neg hfit]
      have hbig : 2 ^ 63 ≤ n := by
        change ¬ n ≤ 2 ^ 63 - 1 at hfit
        omega
      simpa [CountValue.repeated] using takeModel_int_of_ge_max (repeatedModel x) n hbig

theorem listGet_none_of_length_le {α : Type} (xs : List α) (i : Nat)
    (hi : xs.length ≤ i) : listGet xs i = none := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => simp at hi
    | succ i => simpa [listGet] using ih i (by simpa using hi)

private theorem vectorGetIndexInt_r6OrdinalList {α : Type}
    (xs : List α) (n : Int) :
    vectorGetIndexInt xs n = r6OrdinalList xs n := by
  by_cases hpos : 1 ≤ n
  · have hnonpos : ¬ n ≤ 0 := by omega
    by_cases hlen : n ≤ xs.length
    · cases hget : listGet xs (n.toNat - 1) <;>
        simp [vectorGetIndexInt, r6OrdinalList, hpos, hnonpos, hlen, hget]
    · have hnat : (n.toNat : Int) = n := Int.toNat_of_nonneg (by omega)
      have hidx : xs.length ≤ n.toNat - 1 := by omega
      have hget : listGet xs (n.toNat - 1) = none :=
        listGet_none_of_length_le xs _ hidx
      simp [vectorGetIndexInt, r6OrdinalList, hpos, hnonpos, hlen, hget]
  · have hnonpos : n ≤ 0 := by omega
    have hguard : ¬ (1 ≤ n ∧ n ≤ xs.length) := by simp [hpos]
    simp [vectorGetIndexInt, r6OrdinalList, hnonpos, hguard]

private theorem vectorGetIndex_r6OrdinalList {α : Type} {t : IntTy}
    (xs : List α) (n : JInt t) :
    vectorGetIndex xs n = r6OrdinalList xs n.val := by
  change vectorGetIndexInt xs n.val = r6OrdinalList xs n.val
  exact vectorGetIndexInt_r6OrdinalList xs n.val

private theorem vectorGetIndexIntegerArg_r6OrdinalList {α : Type}
    (xs : List α) (n : IntegerArg) :
    vectorGetIndexIntegerArg xs n = r6OrdinalList xs n.toInt := by
  cases n with
  | bool b =>
      simpa [vectorGetIndexIntegerArg, IntegerArg.toInt] using
        vectorGetIndexInt_r6OrdinalList xs (if b then 1 else 0)
  | bit t value =>
      simpa [vectorGetIndexIntegerArg, IntegerArg.toInt] using
        vectorGetIndex_r6OrdinalList xs value
  | big value =>
      exact vectorGetIndexInt_r6OrdinalList xs value

private theorem integerArgNthOffset_toInt (n : IntegerArg) :
    (IntegerArg.subOne
      (IntegerArg.add (.bit .i64 (JInt.lit .i64 1)) n)).toInt = n.toInt := by
  cases n with
  | bool b =>
      cases b <;> decide
  | bit t value =>
      let u := IntTy.promote .i64 t
      have hu : IntTy.promote u .i64 = u := by
        cases t <;> simp [u, IntTy.promote, IntTy.bits, IntTy.signed]
      have hrem (x : JInt u) : JInt.rem u x = x := by
        apply Subtype.ext
        change wrapInt u x.val = x.val
        exact wrapInt_of_inRange u x.val x.property
      change
        (JInt.rem (IntTy.promote u .i64)
          (JInt.rem u (JInt.lit .i64 1) + JInt.rem u value) -
          JInt.lit (IntTy.promote u .i64) 1).val = value.val
      rw [hu]
      have hsum :
          JInt.rem u (JInt.rem u (JInt.lit .i64 1) + JInt.rem u value) =
            JInt.rem u (JInt.lit .i64 1) + JInt.rem u value := hrem _
      rw [hsum]
      exact nthArray_index_val t value
  | big value =>
      simp [IntegerArg.add, IntegerArg.subOne, IntegerArg.toInt,
        JInt.lit, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits,
        IntTy.min, IntTy.max]
      omega

theorem nthVectorCorrect_proven : NthVectorCorrect := by
  intro α xs n
  change vectorGetIndexIntegerArg xs
    (IntegerArg.subOne (IntegerArg.add (.bit .i64 (JInt.lit .i64 1)) n)) =
      r6OrdinalList xs n.toInt
  rw [vectorGetIndexIntegerArg_r6OrdinalList]
  rw [integerArgNthOffset_toInt]


theorem dropLoop_list_refines {I α S : Type}
    (run : I → Option S → Jl (Option (α × S))) (itr : I) (range : List Nat) :
    ∀ remaining (rangeState : Option Nat) (value : Option (α × S)),
      range.length = rangeState.getD 0 + remaining →
      dropLoop (fun i s => liftJl (run i s))
        (fun r st => liftJl ((listIterator r).run st)) itr range rangeState value =
        liftJl (nthAdvance (run itr) remaining value) := by
  intro remaining
  induction remaining with
  | zero =>
    intro rangeState value hlength
    have hget : listGet range (rangeState.getD 0) = none :=
      listGet_none_of_length_le range _ (by omega)
    funext heap
    cases heap
    rw [dropLoop.eq_def]
    simp [liftJl, listIterator, hget, nthAdvance, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | succ remaining ih =>
    intro rangeState value hlength
    have hlt : rangeState.getD 0 < range.length := by omega
    obtain ⟨index, hget, _⟩ := listGet_take_last range (rangeState.getD 0) hlt
    cases value with
    | none =>
      funext heap
      cases heap
      rw [dropLoop.eq_def]
      simp [liftJl, listIterator, hget, nthAdvance, Bind.bind, Except.bind, Pure.pure, Except.pure]
    | some pair =>
      rcases pair with ⟨value, state⟩
      have hlength' : range.length = (some (rangeState.getD 0 + 1)).getD 0 + remaining := by
        simp only [Option.getD_some]
        omega
      cases hr : run itr (some state) with
      | error e =>
        funext heap
        cases heap
        rw [dropLoop.eq_def]
        simp [liftJl, listIterator, hget, nthAdvance, hr,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      | ok following =>
        have htail := congrFun (ih (some (rangeState.getD 0 + 1)) following hlength') ()
        funext heap
        cases heap
        rw [dropLoop.eq_def]
        simpa [liftJl, listIterator, hget, nthAdvance, hr,
          Bind.bind, Except.bind, Pure.pure, Except.pure] using htail

theorem nthAdvance_after_run {α S : Type}
    (run : Option S → Jl (Option (α × S))) :
    ∀ count initial,
      (do let value ← run initial; nthAdvance run count value) = dropAdvance run count initial := by
  intro count
  induction count with
  | zero => intro initial; cases hr : run initial <;>
      simp [nthAdvance, dropAdvance, hr, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | succ count ih =>
    intro initial
    cases hr : run initial with
    | error e => simp [nthAdvance, dropAdvance, hr, Bind.bind, Except.bind]
    | ok value =>
      cases value with
      | none => simp [nthAdvance, dropAdvance, hr, Bind.bind, Except.bind, Pure.pure, Except.pure]
      | some pair =>
        simpa [nthAdvance, dropAdvance, hr, Bind.bind, Except.bind, Pure.pure, Except.pure]
          using ih (some pair.2)

theorem dropStep_refines {I α S : Type}
    (run : I → Option S → Jl (Option (α × S))) (d : Drop I) (state : Option S) :
    dropStep run d state =
      observeJl (dropFromRun (run d.xs) d.n.val.toNat none state) := by
  cases state with
  | some state => rfl
  | none =>
    have hloop := dropLoop_list_refines run d.xs (List.range d.n.val.toNat)
      d.n.val.toNat none
    cases hr : run d.xs none with
    | error e =>
      have hpure := nthAdvance_after_run (run d.xs) d.n.val.toNat none
      rw [hr] at hpure
      simp only [err_bind] at hpure
      simp [dropStep, iterateDrop, observe, observeJl, liftJl, hr, dropFromRun,
        ← hpure, Bind.bind, Except.bind, Pure.pure, Except.pure, JuliaLean.base.iterators.bind, ret]
    | ok value =>
      have hloop' := hloop value (by simp)
      have hpure := nthAdvance_after_run (run d.xs) d.n.val.toNat none
      rw [hr] at hpure
      simp only [ok_bind] at hpure
      simp [dropStep, iterateDrop, observe, observeJl, liftJl, hr, hloop',
        dropFromRun, ← hpure, Bind.bind, Except.bind, Pure.pure, Except.pure,
        JuliaLean.base.iterators.bind, ret]

@[simp] theorem observeJl_ok {α : Type} (value : α) : observeJl (.ok value) = .ok value := rfl
@[simp] theorem observeJl_error {α : Type} (e : JlError) : observeJl (.error e : Jl α) = .error e := rfl

theorem observeLiftJl {α S : Type} (run : Option S → Jl (Option (α × S))) :
    ∀ depth state,
      Round5.observe (fun state => observeJl (run state)) depth state =
        observeJl (Round5.observe run depth state) := by
  intro depth
  induction depth with
  | zero => intro state; rfl
  | succ depth ih =>
    intro state
    cases hr : run state with
    | error e => simp [Round5.observe, hr, Bind.bind, Except.bind, Pure.pure, Except.pure]
    | ok value =>
      cases value with
      | none => simp [Round5.observe, hr, Bind.bind, Except.bind, Pure.pure, Except.pure]
      | some pair =>
        simp only [Round5.observe, hr, observeJl_ok, Bind.bind, Except.bind, Pure.pure, Except.pure]
        rw [ih]
        cases Round5.observe run depth (some pair.2) <;> rfl

theorem observeDrop_native {α S : Type} (itr : IteratorModel α S)
    (count : JInt64) (depth : Nat) :
    Round5.observe (dropStep (fun xs st => xs.run st) ⟨itr, count⟩) (depth + 1) none =
      observeJl ((Round5.observe itr.run (count.val.toNat + depth + 1) none).map
        (List.drop count.val.toNat)) := by
  have heq : dropStep (fun xs st => xs.run st) ⟨itr, count⟩ =
      (fun state => observeJl (dropFromRun itr.run count.val.toNat none state)) := by
    funext state
    exact dropStep_refines _ _ _
  rw [heq, observeLiftJl, observeDropFromRun]

theorem dropSuffix_proven : Round5.DropSuffix := by
  intro α S itr n hn
  by_cases hfit : n ≤ IntTy.max .i64
  · simp only [if_pos hfit]
    have hbound : IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max := by
      change -(2 ^ 63 : Int) ≤ n ∧ n ≤ 2 ^ 63 - 1
      change n ≤ 2 ^ 63 - 1 at hfit
      omega
    let count : JInt64 := ⟨n, hbound⟩
    refine ⟨⟨itr, count⟩, dropModel_native itr count hn, ?_⟩
    intro depth
    exact observeDrop_native itr count depth
  · simp only [if_neg hfit]
    have hbig : 2 ^ 63 ≤ n := by
      change ¬ n ≤ 2 ^ 63 - 1 at hfit
      omega
    simp [CountValue.drop, jint_convert_i64_out n (Or.inr hbig), Bind.bind, Except.bind]

theorem takeDropComplement_proven : Round5.TakeDropComplement := by
  refine ⟨takePrefix_proven, dropSuffix_proven, ?_⟩
  intro α S itr n hn
  by_cases hfit : n ≤ IntTy.max .i64
  · simp only [if_pos hfit]
    have hbound : IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max := by
      change -(2 ^ 63 : Int) ≤ n ∧ n ≤ 2 ^ 63 - 1
      change n ≤ 2 ^ 63 - 1 at hfit
      omega
    let count : JInt64 := ⟨n, hbound⟩
    refine ⟨⟨itr, count⟩, ⟨itr, count⟩,
      takeModel_native itr count hn, dropModel_native itr count hn, ?_⟩
    intro before after cut final hbefore hlen hafter
    constructor
    · have hprefix := observeTakePrefixFromState
        (fun xs st => xs.run st) ⟨itr, count⟩ before.length none hn
      have hmin : min before.length count.val.toNat = before.length := by
        change min before.length n.toNat = before.length
        rw [hlen, Nat.min_self]
      simpa [hmin, observeHistory itr.run hbefore] using hprefix
    · cases after with
      | nil => rfl
      | cons value rest =>
        have hjoined := historyAppendRound5 itr.run hbefore hafter
        have hfull : Round5.observe itr.run (n.toNat + rest.length + 1) none =
            .ok (before ++ value :: rest) := by
          rw [← hlen]
          simpa [List.length_append, List.length_cons, Nat.add_assoc] using
            (observeHistory itr.run hjoined)
        have hdrop := observeDrop_native itr count rest.length
        change Round5.observe
          (dropStep (fun xs st => xs.run st) ⟨itr, count⟩) (rest.length + 1) none = _
        rw [hdrop]
        change observeJl ((Round5.observe itr.run (n.toNat + rest.length + 1) none).map
          (List.drop n.toNat)) = .ok (value :: rest)
        rw [hfull, ← hlen]
        simp only [Except.map]
        rw [listDropAppendRound5]
        rfl
  · simp only [if_neg hfit]
    have hbig : 2 ^ 63 ≤ n := by
      change ¬ n ≤ 2 ^ 63 - 1 at hfit
      omega
    constructor
    · exact takeModel_int_of_ge_max itr n hbig
    · simp [CountValue.drop, jint_convert_i64_out n (Or.inr hbig), Bind.bind, Except.bind]

end JuliaLean.Proofs.base.iterators

section
/- Batch 4, group 5: completed targets and checked supporting results. -/

/- Supporting block: Queue01_06 -/
namespace JuliaLean.ChatGPT.Batch4.Group5
open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators

/-- A nonempty completion-aware iterator with zero elements requested. -/
theorem IteratorsTakeIsdoneZero_refuted : ¬ JuliaLean.Proofs.base.iterators.TakeIsemptyCorrect := by
  intro h
  exact nomatch (h [1] (JInt.lit .i64 0) (by decide)).mpr rfl

/-- The singleton completion protocol is realized by mapping the zero-factor product. -/
theorem IteratorsRestIsdoneState_refuted : ¬ JuliaLean.Proofs.base.iterators.PeelRestIsempty := by
  intro h
  exact nomatch (h [1] 1 ⟨listIterator [1], 1⟩ rfl).mpr rfl

/-- The cycle is lazy: its count does not require storage proportional to that count. -/
theorem IteratorsNthCycleOverflow_refuted : ¬ JuliaLean.Proofs.base.iterators.NthCycleCorrect := by
  intro h
  obtain ⟨cyc, hcyc, hnth⟩ := h [1, 2, 3] (2 ^ 62) 1 1
    (by decide) (by decide) (by decide) rfl
  cases hcyc
  exact nomatch hnth

/-- Three compact ranges have an empty product but overflow during length reduction. -/
theorem IteratorsProductLengthZero_refuted : ¬ JuliaLean.Proofs.base.iterators.ProductLengthExact := by
  intro h
  exact nomatch h checkedMulI64 (fun m vs init => checkedProductFold m init vs)
    (fun _ _ => rfl) (fun _ _ => rfl)
    [JInt.lit .i64 (2 ^ 32), JInt.lit .i64 (2 ^ 32), JInt.lit .i64 0]
    (by decide) (by decide) (by decide)

/-- Componentwise last returns a tuple even though one compact range is empty. -/
theorem IteratorsProductLastEmpty_refuted : ¬ JuliaLean.Proofs.base.iterators.ProductLastNonempty := by
  intro h
  have h0 := h [(JInt.lit .i64 1, JInt.lit .i64 2), (JInt.lit .i64 1, JInt.lit .i64 0)]
    [JInt.lit .i64 2, JInt.lit .i64 0] rfl
    (JInt.lit .i64 1, JInt.lit .i64 0) (by decide)
  revert h0
  decide

/-- Taking three elements of a cycle over an empty vector reports length three. -/
theorem IteratorsCycleEmptyLength_refuted : ¬ JuliaLean.Proofs.base.iterators.CycleFirstN := by
  intro h
  obtain ⟨t, ys, ht, hys, hlen⟩ := h [] 3 (by decide)
  cases ht
  cases hys
  exact nomatch hlen

end JuliaLean.ChatGPT.Batch4.Group5

/- Supporting block: Queue07_12 -/
namespace JuliaLean.ChatGPT.Batch4.Group5
open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators

/-- A one-element identity range suffices: all stored inputs are machine integers. -/
theorem IteratorsPartitionRangeOverflow_refuted :
    ¬ JuliaLean.Proofs.base.iterators.PartitionRangeChunks := by
  intro h
  have hbad := h
    (JInt.lit .i64 (2 ^ 63 - 1)) (JInt.lit .i64 (2 ^ 63 - 1)) 2 none
    (JInt.lit .i64 (2 ^ 63 - 1), JInt.lit .i64 (2 ^ 63 - 2))
    (JInt.lit .i64 (-(2 ^ 63) + 1)) (by decide) (by decide) (by rfl)
  have hordered := hbad.1
  revert hordered
  decide

/-- The tuple has three entries; only the scalar requested count is large. -/
theorem IteratorsPartitionGenericAlloc_refuted :
    ¬ JuliaLean.Proofs.base.iterators.PartitionFirstChunk := by
  intro h
  obtain ⟨_, h0⟩ := h [1, 2, 3] (2 ^ 62) (by decide) (by decide)
  exact nomatch h0

/-- A UInt64 count is constructible even when the public Int conversion rejects it. -/
theorem IteratorsTakeHugeCount_refuted :
    ¬ JuliaLean.Proofs.base.iterators.FirstNAnyInteger := by
  intro h
  obtain ⟨_, _, htake, _⟩ := h .u64 [1, 2, 3] (JInt.typemax .u64) (by decide)
  exact nomatch htake

/-- The frozen completion callback declares every initial state finished. -/
theorem productOneFactorDoneAtStart (xs : List Int)
    (isdoneAfter : Option Nat → Jl (Option Bool))
    (h : ∀ st, isdoneAfter st = .ok (some (xs.length ≤ st.getD xs.length))) :
    isdoneAfter none = .ok (some true) := by
  rw [h none]
  simp only [Option.getD_none, Nat.le_refl, decide_true]

/-- The first two outputs are Bool true and Int 2, despite the Bool element type. -/
theorem IteratorscovCountfromEltype_refuted :
    ¬ JuliaLean.Proofs.base.iterators.CountfromEltype := by
  intro h
  exact nomatch h (.inl true) 2 [.inl true, .inr (JInt.lit .i64 2)] rfl
    (.inr (JInt.lit .i64 2))
    (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))

/-- The broadcast specialization used below repeats the single left tuple field. -/
def productIntersectBroadcastSingleton
    (f : List Int → List Int → Jl (List Int))
    (left right : List (List Int)) : Jl (List (List Int)) :=
  match left with
  | [x] => right.mapM (f x)
  | _ => .error (.argumentError "singleton left tuple required")

/-- One-field versus two-field tuple broadcasting produces a nonempty two-factor product. -/
theorem IteratorscovProductIntersectArity_refuted :
    ¬ JuliaLean.Proofs.base.iterators.ProductIntersect := by
  intro h
  have hbad := h
    (fun xs ys => .ok (xs.filter fun x => ys.contains x))
    productIntersectBroadcastSingleton [[1]] [[1], [1]] (by decide) (by decide)
  exact nomatch hbad

end JuliaLean.ChatGPT.Batch4.Group5

/- Supporting block: Queue13_18 -/
namespace JuliaLean.ChatGPT.Batch4.Group5

open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators

theorem group5_nat_count_val (n : Nat) (hn : n < 2 ^ 63) :
    (JInt.lit .i64 (Int.ofNat n)).val = Int.ofNat n := by
  exact jint_lit_i64_val _ (by simp only [Int.ofNat_eq_natCast]; omega)
    (by simp only [Int.ofNat_eq_natCast]; omega)

theorem group5_collect_eq_observe {I α S : Type} {m : Type → Type}
    [Monad m] [CollectRun I α S m] (itr : I) (depth : Nat) (state : Option S) :
    JuliaLean.Proofs.base.iterators.collectPrefix itr depth state =
      Round5.observe (CollectRun.run itr) depth state := by
  induction depth generalizing state with
  | zero => rfl
  | succ depth ih =>
      simp only [JuliaLean.Proofs.base.iterators.collectPrefix, Round5.observe, ih]

theorem group5_action_observe {α : Type} (result : Jl α) :
    action (observeJl result) = liftJl result := by
  cases result <;> rfl

theorem group5_observe_total {α : Type} (run : Exec JlError Unit α)
    (h : (run ()).isSome) :
    observe run = observeJl ((run ()).get h).1 := by
  unfold observe
  generalize hr : run () = result at h ⊢
  cases result with
  | none => simp only [Option.isSome_none, Bool.false_eq_true] at h
  | some result =>
      rcases result with ⟨value, heap⟩
      cases heap
      cases value <;> rfl

theorem group5_take_run {α S : Type} (itr : IteratorModel α S) (n : JInt64)
    (state : Option (JInt64 × S)) :
    (takeObservation itr ⟨itr, n⟩).run state =
      observeJl (takeStep (fun it st => it.run st) ⟨itr, n⟩ state) := by
  simp only [takeObservation, AsObservation.view, group5_action_observe]
  unfold takeStep
  apply group5_observe_total

theorem group5_drop_run {α S : Type} (itr : IteratorModel α S) (n : JInt64)
    (state : Option S) :
    (dropObservation itr ⟨itr, n⟩).run state =
      dropStep (fun it st => it.run st) ⟨itr, n⟩ state := by
  simp only [dropObservation, AsObservation.view, group5_action_observe, dropStep]

theorem group5_take_run_function {α S : Type} (itr : IteratorModel α S) (n : JInt64) :
    (takeObservation itr ⟨itr, n⟩).run =
      fun state => observeJl (takeStep (fun it st => it.run st) ⟨itr, n⟩ state) := by
  funext state
  exact group5_take_run itr n state

theorem group5_drop_run_function {α S : Type} (itr : IteratorModel α S) (n : JInt64) :
    (dropObservation itr ⟨itr, n⟩).run =
      dropStep (fun it st => it.run st) ⟨itr, n⟩ := by
  funext state
  exact group5_drop_run itr n state

theorem group5_observe_list {α : Type} (xs : List α) (depth i : Nat) :
    Round5.observe (listIterator xs).run depth (some i) =
      .ok ((xs.drop i).take depth) := by
  induction depth generalizing i with
  | zero => rfl
  | succ depth ih =>
      rw [Round5.observe, listIterator_run_some]
      cases hd : xs.drop i with
      | nil => simp only [List.take_nil, ok_bind, pure_jl]
      | cons x rest =>
          have hnext : xs.drop (i + 1) = rest := by
            rw [← List.drop_drop, hd]
            rfl
          simp only [ok_bind]
          rw [ih, hnext]
          rfl

theorem group5_observe_list_initial {α : Type} (xs : List α) (depth : Nat) :
    Round5.observe (listIterator xs).run depth none = .ok (xs.take depth) := by
  cases depth with
  | zero => rfl
  | succ depth =>
      have h := group5_observe_list xs (depth + 1) 0
      simpa only [Round5.observe, listIterator_run_none, List.drop_zero] using h

theorem group5_observe_from_trace {α S : Type} (itr : IteratorModel α S)
    (xs : List α) : ∀ (state : Option S), followsFrom itr state xs →
      ∀ depth, Round5.observe itr.run depth state = .ok (xs.take depth) := by
  induction xs with
  | nil =>
      intro state h depth
      have hstop := followsFrom_nil itr state h
      cases depth with
      | zero => rfl
      | succ depth => simp only [Round5.observe, hstop, ok_bind, pure_jl, List.take_nil]
  | cons x rest ih =>
      intro state h depth
      cases depth with
      | zero => rfl
      | succ depth =>
          obtain ⟨next, hrun, htail⟩ := followsFrom_cons itr state x rest h
          simp only [Round5.observe, hrun, ok_bind]
          rw [ih (some next) htail depth]
          rfl

theorem group5_take_take_length {α : Type} (xs : List α) (n : Nat) :
    xs.take (min ((xs.take n).length + 1) n) = xs.take n := by
  rw [List.length_take]
  by_cases h : n ≤ xs.length
  · rw [Nat.min_eq_left h, Nat.min_eq_right (by omega)]
  · have hx : xs.length ≤ n := by omega
    rw [Nat.min_eq_right hx]
    rw [List.take_of_length_le hx]
    exact List.take_of_length_le (by omega)

theorem group5_take_emits_trace {α S : Type} (itr : IteratorModel α S)
    (xs : List α) (htrace : followsFrom itr none xs) (n : JInt64) (hn : 0 ≤ n.val) :
    emitsExactly (takeObservation itr ⟨itr, n⟩) (xs.take n.val.toNat) := by
  unfold emitsExactly
  rw [group5_collect_eq_observe]
  change Round5.observe (takeObservation itr ⟨itr, n⟩).run
    ((xs.take n.val.toNat).length + 1) none = .ok (xs.take n.val.toNat)
  rw [group5_take_run_function, observeLiftJl,
    observeTakePrefixFromState (fun (it : IteratorModel α S) st => it.run st)
      ⟨itr, n⟩ _ none hn]
  simp only [Option.map_none, Option.getD_none]
  rw [group5_observe_from_trace itr xs none htrace]
  simp only [observeJl_ok, group5_take_take_length]

theorem group5_drop_emits_trace {α S : Type} (itr : IteratorModel α S)
    (xs : List α) (htrace : followsFrom itr none xs) (n : JInt64) :
    emitsExactly (dropObservation itr ⟨itr, n⟩) (xs.drop n.val.toNat) := by
  unfold emitsExactly
  rw [group5_collect_eq_observe]
  change Round5.observe (dropObservation itr ⟨itr, n⟩).run
    ((xs.drop n.val.toNat).length + 1) none = .ok (xs.drop n.val.toNat)
  rw [group5_drop_run_function, observeDrop_native, group5_observe_from_trace itr xs none htrace]
  have hlen : xs.length ≤ n.val.toNat + (xs.drop n.val.toNat).length + 1 := by
    rw [List.length_drop]
    omega
  rw [List.take_of_length_le hlen]
  rfl

theorem group5_take_emits {α : Type} (xs : List α) (n : JInt64) (hn : 0 ≤ n.val) :
    emitsExactly (takeObservation (listIterator xs) ⟨listIterator xs, n⟩)
      (xs.take n.val.toNat) := by
  unfold emitsExactly
  rw [group5_collect_eq_observe]
  change Round5.observe
    (takeObservation (listIterator xs) ⟨listIterator xs, n⟩).run
    ((xs.take n.val.toNat).length + 1) none = .ok (xs.take n.val.toNat)
  rw [group5_take_run_function, observeLiftJl,
    observeTakePrefixFromState (fun (it : IteratorModel α Nat) st => it.run st)
      ⟨listIterator xs, n⟩ _ none hn]
  simp only [Option.map_none, Option.getD_none]
  rw [group5_observe_list_initial]
  simp only [observeJl_ok]
  congr 1
  rw [List.length_take]
  by_cases h : n.val.toNat ≤ xs.length
  · rw [Nat.min_eq_left h, Nat.min_eq_right (by omega)]
  · have hx : xs.length ≤ n.val.toNat := by omega
    rw [Nat.min_eq_right hx]
    rw [List.take_of_length_le hx]
    exact List.take_of_length_le (by omega)

theorem group5_drop_emits {α : Type} (xs : List α) (n : JInt64) :
    emitsExactly (dropObservation (listIterator xs) ⟨listIterator xs, n⟩)
      (xs.drop n.val.toNat) := by
  unfold emitsExactly
  rw [group5_collect_eq_observe]
  change Round5.observe
    (dropObservation (listIterator xs) ⟨listIterator xs, n⟩).run
    ((xs.drop n.val.toNat).length + 1) none = .ok (xs.drop n.val.toNat)
  rw [group5_drop_run_function, observeDrop_native, group5_observe_list_initial]
  have hlen : xs.length ≤ n.val.toNat + (xs.drop n.val.toNat).length + 1 := by
    rw [List.length_drop]
    omega
  rw [List.take_of_length_le hlen]
  rfl

theorem IteratorsTake_proven : JuliaLean.Proofs.base.iterators.TakeCorrect := by
  refine ⟨?_, ?_, ?_⟩
  · intro α xs n hn
    refine ⟨group5_take_emits xs n hn, ?_⟩
    simp only [takeObservation, AsObservation.view, takeLength, listIterator,
      minLengthFinite, pure_jl, ok_bind, Sum.elim_inr]
    rw [Nat.min_comm]
    rfl
  · intro I α S run it s
    constructor
    · rw [takeStep_equation]
      rfl
    · intro hn
      rw [takeStep_equation]
      simp only [Option.map_none, Option.getD_none, hn, Int.le_refl, if_true]
  · intro I trait len t m hm
    cases ht : trait t.xs <;>
      simp only [takeLength, ht, minLengthFinite, minLengthLeftInfinite,
        hm, pure_jl, ok_bind, Except.map, Sum.elim_inl, Sum.elim_inr]
    all_goals rfl

theorem IteratorsDrop_proven : JuliaLean.Proofs.base.iterators.DropCorrect := by
  refine ⟨?_, ?_, ?_⟩
  · intro α xs n hn
    refine ⟨group5_drop_emits xs n, ?_⟩
    simp only [dropObservation, AsObservation.view, dropLength, listIterator,
      diffLengthFinite, pure_jl, ok_bind]
    split <;> simp_all [pure_jl, ok_bind]
  · intro I α S run it s
    exact ⟨rfl, rfl⟩
  · intro I trait len d m hm
    cases ht : trait d.xs <;> by_cases hgt : m > d.n.val.toNat <;>
      simp [dropLength, ht, diffLengthFinite, diffLengthLeftInfinite,
        hm, pure_jl, ok_bind, Except.map, hgt]
    all_goals omega

end JuliaLean.ChatGPT.Batch4.Group5

/- Supporting block: Queue15_18 -/
namespace JuliaLean.ChatGPT.Batch4.Group5
open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators

set_option maxRecDepth 4096

 theorem group5_q15_actionJl {α : Type} (result : Jl α) :
    action (observeJl result) = liftJl result := by
  cases result <;> rfl

 theorem group5_q15_take_run {α S : Type} (itr : IteratorModel α S)
    (p : α → Bool) (st : Option S) :
    (takeWhileObservation itr p).run st = observeJl (do
      match ← itr.run st with
      | none => pure none
      | some y => if p y.1 then pure (some y) else pure none) := by
  change observe (takeWhile (fun i s => action (observeJl (i.run s)))
    (fun y => pure y.1) (fun pred x => pure (pred x)) ⟨p, itr⟩ st) = _
  simp only [group5_q15_actionJl]
  cases hr : itr.run st with
  | error e => simp only [takeWhile, hr, liftJl, Bind.bind, JuliaLean.base.iterators.bind,
      Pure.pure, ret, observe, observeJl, Except.bind, Except.pure]
  | ok value =>
      cases value with
      | none => simp only [takeWhile, hr, liftJl, Bind.bind, JuliaLean.base.iterators.bind,
          Pure.pure, ret, observe, observeJl, Except.bind, Except.pure]
      | some pair =>
          simp only [takeWhile, hr, liftJl, Bind.bind, JuliaLean.base.iterators.bind,
            Pure.pure, ret, observe, observeJl, Except.bind, Except.pure]
          all_goals (cases p pair.1 <;> rfl)

 theorem group5_q15_take_trace {α S : Type} (itr : IteratorModel α S)
    (p : α → Bool) (xs : List α) (st : Option S)
    (h : followsFrom itr st xs) :
    followsFrom (takeWhileObservation itr p) st (xs.takeWhile p) := by
  induction xs generalizing st with
  | nil =>
      have hs := followsFrom_nil itr st h
      change JuliaLean.Proofs.base.iterators.collectPrefix (takeWhileObservation itr p) 1 st = .ok []
      simp only [JuliaLean.Proofs.base.iterators.collectPrefix]
      change (do match ← (takeWhileObservation itr p).run st with
        | none => pure []
        | some (x, next) => pure (x :: (← JuliaLean.Proofs.base.iterators.collectPrefix (takeWhileObservation itr p) 0 (some next)))) = _
      rw [group5_q15_take_run, hs]
      all_goals rfl
  | cons x xs ih =>
      obtain ⟨next, hs, ht⟩ := followsFrom_cons itr st x xs h
      by_cases hp : p x = true
      · have htt := ih (some next) ht
        simp only [List.takeWhile_cons, hp, ↓reduceIte]
        change JuliaLean.Proofs.base.iterators.collectPrefix (takeWhileObservation itr p) ((xs.takeWhile p).length + 1 + 1) st = _
        rw [JuliaLean.Proofs.base.iterators.collectPrefix]
        change (do match ← (takeWhileObservation itr p).run st with
          | none => pure []
          | some (y, following) => pure (y :: (← JuliaLean.Proofs.base.iterators.collectPrefix (takeWhileObservation itr p)
              ((xs.takeWhile p).length + 1) (some following)))) = _
        rw [group5_q15_take_run, hs]
        simp only [ok_bind, hp, ↓reduceIte]
        change (do pure (x :: (← JuliaLean.Proofs.base.iterators.collectPrefix (takeWhileObservation itr p)
          ((xs.takeWhile p).length + 1) (some next)))) = _
        change JuliaLean.Proofs.base.iterators.collectPrefix (takeWhileObservation itr p) ((xs.takeWhile p).length + 1)
          (some next) = .ok (xs.takeWhile p) at htt
        rw [htt]
        all_goals rfl
      · have hf : p x = false := Bool.eq_false_iff.mpr hp
        simp only [List.takeWhile_cons, hf, Bool.false_eq_true, ↓reduceIte]
        change JuliaLean.Proofs.base.iterators.collectPrefix (takeWhileObservation itr p) 1 st = .ok []
        rw [JuliaLean.Proofs.base.iterators.collectPrefix]
        change (do match ← (takeWhileObservation itr p).run st with
          | none => pure []
          | some (y, following) => pure (y :: (← JuliaLean.Proofs.base.iterators.collectPrefix (takeWhileObservation itr p) 0 (some following)))) = _
        rw [group5_q15_take_run, hs]
        simp only [ok_bind, hf]
        all_goals rfl

 def group5_q15_scan {α S : Type} (itr : IteratorModel α S) (p : α → Bool)
    (st : Option S) : Exec JlError Unit (Option (α × S)) := do
  dropWhileScan (fun i s => liftJl (i.run s)) (fun y => pure y.1)
    (fun y => pure y.2) (fun pred x => pure (pred x)) ⟨p, itr⟩ (← liftJl (itr.run st))

 theorem group5_q15_scan_trace {α S : Type} (itr : IteratorModel α S)
    (p : α → Bool) (xs : List α) (st : Option S)
    (h : followsFrom itr st xs) :
    ∃ restState, group5_q15_scan itr p st = liftJl (itr.run restState) ∧
      followsFrom itr restState (xs.dropWhile p) := by
  induction xs generalizing st with
  | nil =>
      have hs := followsFrom_nil itr st h
      refine ⟨st, ?_, h⟩
      funext heap
      cases heap
      simp only [group5_q15_scan, hs, liftJl, Bind.bind, JuliaLean.base.iterators.bind]
      rw [dropWhileScan.eq_def]
  | cons x xs ih =>
      obtain ⟨next, hs, ht⟩ := followsFrom_cons itr st x xs h
      by_cases hp : p x = true
      · obtain ⟨restState, heq, hrest⟩ := ih (some next) ht
        refine ⟨restState, ?_, ?_⟩
        · rw [← heq]
          funext heap
          cases heap
          simp only [group5_q15_scan, hs, liftJl, Bind.bind, JuliaLean.base.iterators.bind]
          rw [dropWhileScan.eq_def]
          simp only [Pure.pure, ret, hp, liftJl]
          all_goals (cases itr.run (some next) <;> rfl)
        · simpa only [List.dropWhile_cons, hp, ↓reduceIte] using hrest
      · have hf : p x = false := Bool.eq_false_iff.mpr hp
        refine ⟨st, ?_, ?_⟩
        · funext heap
          cases heap
          simp only [group5_q15_scan, hs, liftJl, Bind.bind, JuliaLean.base.iterators.bind]
          rw [dropWhileScan.eq_def]
          simp only [Pure.pure, ret, hf]
        · simpa only [List.dropWhile_cons, hf, Bool.false_eq_true, ↓reduceIte] using h


 theorem group5_q15_drop_run_none {α S : Type} (itr : IteratorModel α S)
    (p : α → Bool) :
    (dropWhileObservation itr p).run none = observe (group5_q15_scan itr p none) := by
  change observe (dropWhile (fun i s => action (observeJl (i.run s)))
    (fun y => pure y.1) (fun y => pure y.2) (fun pred x => pure (pred x)) ⟨p, itr⟩) = _
  simp only [group5_q15_actionJl]
  all_goals rfl

 theorem group5_q15_drop_collect_some {α S : Type} (itr : IteratorModel α S)
    (p : α → Bool) (depth : Nat) (st : S) :
    JuliaLean.Proofs.base.iterators.collectPrefix (dropWhileObservation itr p) depth (some st) =
      observeJl (JuliaLean.Proofs.base.iterators.collectPrefix itr depth (some st)) := by
  induction depth generalizing st with
  | zero => rfl
  | succ depth ih =>
      rw [JuliaLean.Proofs.base.iterators.collectPrefix, JuliaLean.Proofs.base.iterators.collectPrefix]
      change (do match ← observeJl (itr.run (some st)) with
        | none => pure []
        | some (x, next) => pure (x :: (← JuliaLean.Proofs.base.iterators.collectPrefix (dropWhileObservation itr p)
          depth (some next)))) = observeJl (do
          match ← itr.run (some st) with
          | none => pure []
          | some (x, next) => pure (x :: (← JuliaLean.Proofs.base.iterators.collectPrefix itr depth (some next))))
      cases hr : itr.run (some st) with
      | error e => rfl
      | ok value =>
          cases value with
          | none => rfl
          | some pair =>
              change (do pure (pair.1 :: (← JuliaLean.Proofs.base.iterators.collectPrefix (dropWhileObservation itr p)
                depth (some pair.2)))) = observeJl (do
                  pure (pair.1 :: (← JuliaLean.Proofs.base.iterators.collectPrefix itr depth (some pair.2))))
              rw [ih]
              cases JuliaLean.Proofs.base.iterators.collectPrefix itr depth (some pair.2) <;> rfl

 theorem group5_q15_drop_emits {α S : Type} (itr : IteratorModel α S)
    (p : α → Bool) (xs : List α) (h : followsFrom itr none xs) :
    emitsExactly (dropWhileObservation itr p) (xs.dropWhile p) := by
  obtain ⟨restState, hscan, hrest⟩ := group5_q15_scan_trace itr p xs none h
  cases hd : xs.dropWhile p with
  | nil =>
      simp only [hd] at hrest
      have hstop := followsFrom_nil itr restState hrest
      change JuliaLean.Proofs.base.iterators.collectPrefix (dropWhileObservation itr p) 1 none = .ok []
      rw [JuliaLean.Proofs.base.iterators.collectPrefix]
      change (do match ← (dropWhileObservation itr p).run none with
        | none => pure []
        | some (x, next) => pure (x :: (← JuliaLean.Proofs.base.iterators.collectPrefix (dropWhileObservation itr p) 0 (some next)))) = _
      rw [group5_q15_drop_run_none, hscan, hstop]
      all_goals rfl
  | cons x tail =>
      simp only [hd] at hrest
      obtain ⟨next, hstep, htail⟩ := followsFrom_cons itr restState x tail hrest
      change JuliaLean.Proofs.base.iterators.collectPrefix (dropWhileObservation itr p) ((x :: tail).length + 1) none = .ok (x :: tail)
      rw [JuliaLean.Proofs.base.iterators.collectPrefix]
      change (do match ← (dropWhileObservation itr p).run none with
        | none => pure []
        | some (y, following) => pure (y :: (← JuliaLean.Proofs.base.iterators.collectPrefix (dropWhileObservation itr p)
            (tail.length + 1) (some following)))) = _
      rw [group5_q15_drop_run_none, hscan, hstep]
      change (do pure (x :: (← JuliaLean.Proofs.base.iterators.collectPrefix (dropWhileObservation itr p)
        (tail.length + 1) (some next)))) = _
      rw [group5_q15_drop_collect_some]
      change JuliaLean.Proofs.base.iterators.collectPrefix itr (tail.length + 1) (some next) = .ok tail at htail
      rw [htail]
      all_goals rfl

 theorem group5_q15_list_follows {α : Type} (xs : List α) :
    followsFrom (listIterator xs) none xs := by
  change JuliaLean.Proofs.base.iterators.collectPrefix (listIterator xs) (xs.length + 1) none = .ok xs
  rw [group5_collect_eq_observe]
  change Round5.observe (listIterator xs).run (xs.length + 1) none = .ok xs
  rw [group5_observe_list_initial]
  have ht : xs.take (xs.length + 1) = xs := List.take_of_length_le (by omega)
  rw [ht]

 theorem group5_q15_take_step {I P α S : Type} (apply : P → α → Bool)
    (run : I → Option S → Jl (Option (α × S))) (pred : P) (itr : I)
    (state : Option S) :
    takeWhileStep apply run (takewhileModel pred itr) state =
      (do match ← run itr state with
      | none => pure none
      | some y => if apply pred y.1 then pure (some y) else pure none) := by
  cases hr : run itr state with
  | error e =>
      simp only [takeWhileStep, takewhileModel, takeWhile, hr, liftJl, observe,
        Bind.bind, JuliaLean.base.iterators.bind, Pure.pure, ret]
      all_goals rfl
  | ok value =>
      cases value with
      | none =>
          simp only [takeWhileStep, takewhileModel, takeWhile, hr, liftJl, observe,
            Bind.bind, JuliaLean.base.iterators.bind, Pure.pure, ret]
          all_goals rfl
      | some pair =>
          cases hp : apply pred pair.1 <;>
            simp only [takeWhileStep, takewhileModel, takeWhile, hr, liftJl, observe,
              Bind.bind, JuliaLean.base.iterators.bind, Pure.pure, ret, hp,
              liftM, MonadLiftT.monadLift, MonadLift.monadLift, observeJl]
          all_goals rfl

 theorem IteratorsTakewhileDropwhile_proven : JuliaLean.Proofs.base.iterators.TakeWhileDropWhile := by
  refine ⟨?_, ?_, ?_⟩
  · intro α p xs
    refine ⟨group5_q15_take_trace (listIterator xs) p xs none (group5_q15_list_follows xs),
      group5_q15_drop_emits (listIterator xs) p xs (group5_q15_list_follows xs), ?_⟩
    exact List.takeWhile_append_dropWhile
  · intro I α S iterate isdone it xs p h
    exact ⟨group5_q15_take_trace (protocolIterator iterate isdone it) p xs none h,
      group5_q15_drop_emits (protocolIterator iterate isdone it) p xs h⟩
  · intro I P α S apply iterate pred xs state s
    exact ⟨rfl, rfl, rfl, group5_q15_take_step apply iterate pred xs state⟩


 theorem group5_q16_enumerate_from {α S : Type} (itr : IteratorModel α S)
    (xs : List α) (state : S) (counter : JInt64)
    (h : followsFrom itr (some state) xs) :
    followsFrom (enumerateAsIterator itr) (some (counter, state))
      (enumerateFrom counter xs) := by
  induction xs generalizing state counter with
  | nil =>
      have hs := followsFrom_nil itr (some state) h
      change JuliaLean.Proofs.base.iterators.collectPrefix (enumerateAsIterator itr) 1 (some (counter, state)) = .ok []
      rw [collectPrefix_succ]
      have hstop : (enumerateAsIterator itr).run (some (counter, state)) = .ok none := by
        simp only [enumerateAsIterator, iterateEnumerate, hs]
        all_goals rfl
      rw [hstop]
      all_goals rfl
  | cons x xs ih =>
      obtain ⟨next, hs, ht⟩ := followsFrom_cons itr (some state) x xs h
      change followsFrom (enumerateAsIterator itr) (some (counter, state))
        ((counter, x) :: enumerateFrom (counter + JInt.lit .i64 1) xs)
      apply followsFrom_cons_intro (enumerateAsIterator itr) (some (counter, state))
        (counter, x) (enumerateFrom (counter + JInt.lit .i64 1) xs)
        (counter + JInt.lit .i64 1, next)
      · simp only [enumerateAsIterator, iterateEnumerate, hs]
        all_goals rfl
      · exact ih next (counter + JInt.lit .i64 1) ht

 theorem group5_q16_enumerate_initial {α S : Type} (itr : IteratorModel α S)
    (xs : List α) (h : followsFrom itr none xs) :
    emitsExactly (enumerateAsIterator itr) (enumerateSpec xs) := by
  cases xs with
  | nil =>
      have hs := followsFrom_nil itr none h
      change JuliaLean.Proofs.base.iterators.collectPrefix (enumerateAsIterator itr) 1 none = .ok []
      rw [collectPrefix_succ]
      have hstop : (enumerateAsIterator itr).run none = .ok none := by
        simp only [enumerateAsIterator, iterateEnumerate, hs]
        all_goals rfl
      rw [hstop]
      all_goals rfl
  | cons x xs =>
      obtain ⟨next, hs, ht⟩ := followsFrom_cons itr none x xs h
      change followsFrom (enumerateAsIterator itr) none
        ((JInt.lit .i64 1, x) :: enumerateFrom (JInt.lit .i64 1 + JInt.lit .i64 1) xs)
      apply followsFrom_cons_intro (enumerateAsIterator itr) none
        (JInt.lit .i64 1, x) (enumerateFrom (JInt.lit .i64 1 + JInt.lit .i64 1) xs)
        (JInt.lit .i64 1 + JInt.lit .i64 1, next)
      · simp only [enumerateAsIterator, iterateEnumerate, hs]
        all_goals rfl
      · exact group5_q16_enumerate_from itr xs next _ ht

 theorem IteratorsEnumerate_proven : JuliaLean.Proofs.base.iterators.EnumerateCorrect := by
  refine ⟨?_, ?_, ?_⟩
  · intro α xs
    exact ⟨group5_q16_enumerate_initial (listIterator xs) xs (group5_q15_list_follows xs), rfl⟩
  · intro I α S iterate itr i s
    exact ⟨rfl, rfl, rfl⟩
  · intro I R α S r reverse length k ri st iterRi
    refine ⟨rfl, ?_⟩
    cases hr : iterRi ri st with
    | error e => simp [sourceMethod228, hr]
    | ok value =>
      cases value with
      | none => simp [sourceMethod228, hr]
      | some pair =>
        rcases pair with ⟨x, next⟩
        simp [sourceMethod228, hr]


 def group5_q17_state {α : Type} (xs ys : List α) (i : Nat) :
    TupleVals (fun _ : IteratorModel α Nat => Nat) (zipModel [listIterator xs, listIterator ys]).is :=
  .cons i (.cons i .nil)

 theorem group5_q17_zip_run {α : Type} (xs ys : List α) (i : Nat) :
    (zipListObservation xs ys).run (some (group5_q17_state xs ys i)) =
      match xs.drop i, ys.drop i with
      | x :: _, y :: _ => .ok (some ([x, y], group5_q17_state xs ys (i + 1)))
      | _, _ => .ok none := by
  cases hx : xs.drop i with
  | nil =>
      have hxi : xs.length ≤ i := List.drop_eq_nil_iff.mp hx
      simp [zipListObservation, zipObservation, zipModel, zipState, group5_q17_state,
        tupleOfList, tupleMap, zipIterateAll, zipDoneScan, listIterator, hxi, hx,
        tupleAllMissing, zipUnknown, zipRest, tupleValueList, observeJl, observe, liftJl]
  | cons x xt =>
      have hxi : ¬ xs.length ≤ i := by
        have hlen := congrArg List.length hx
        simp only [List.length_drop, List.length_cons] at hlen
        omega
      cases hy : ys.drop i with
      | nil =>
          have hyi : ys.length ≤ i := List.drop_eq_nil_iff.mp hy
          simp [zipListObservation, zipObservation, zipModel, zipState, group5_q17_state,
            tupleOfList, tupleMap, zipIterateAll, zipDoneScan, listIterator, hxi, hyi, hx, hy,
            tupleAllMissing, zipUnknown, zipRest, tupleValueList, observeJl, observe, liftJl]
      | cons y yt =>
          have hyi : ¬ ys.length ≤ i := by
            have hlen := congrArg List.length hy
            simp only [List.length_drop, List.length_cons] at hlen
            omega
          simp [zipListObservation, zipObservation, zipModel, zipState, group5_q17_state,
            tupleOfList, tupleMap, zipIterateAll, zipDoneScan, listIterator, hxi, hyi,
            listGet_eq_drop_head?, hx, hy, tupleAllMissing, zipUnknown, zipRest,
            tupleValueList, observeJl, observe, liftJl]

 theorem group5_q17_zip_initial {α : Type} (xs ys : List α) :
    (zipListObservation xs ys).run none =
      (zipListObservation xs ys).run (some (group5_q17_state xs ys 0)) := by
  all_goals rfl

 theorem group5_q17_zip_collect {α : Type} (xs ys : List α) (depth i : Nat) :
    JuliaLean.Proofs.base.iterators.collectPrefix (zipListObservation xs ys) depth (some (group5_q17_state xs ys i)) =
      .ok ((List.zipWith (fun x y => [x, y]) (xs.drop i) (ys.drop i)).take depth) := by
  induction depth generalizing i with
  | zero => rfl
  | succ depth ih =>
      simp only [JuliaLean.Proofs.base.iterators.collectPrefix, CollectRun.run]
      rw [group5_q17_zip_run]
      cases hx : xs.drop i with
      | nil => rfl
      | cons x xt =>
          cases hy : ys.drop i with
          | nil => rfl
          | cons y yt =>
              simp only [Bind.bind, Pure.pure]
              rw [ih]
              simp only [List.drop_add_one_eq_tail_drop, hx, hy, List.tail_cons]
              all_goals rfl

 theorem group5_q17_zip_emits {α : Type} (xs ys : List α) :
    emitsExactly (zipListObservation xs ys) (List.zipWith (fun x y => [x, y]) xs ys) := by
  have hi : ∀ depth, JuliaLean.Proofs.base.iterators.collectPrefix (zipListObservation xs ys) depth none =
      JuliaLean.Proofs.base.iterators.collectPrefix (zipListObservation xs ys) depth (some (group5_q17_state xs ys 0)) := by
    intro depth
    cases depth with
    | zero => rfl
    | succ depth =>
        simp only [JuliaLean.Proofs.base.iterators.collectPrefix, CollectRun.run]
        rw [group5_q17_zip_initial]
        all_goals rfl
  unfold emitsExactly
  rw [hi, group5_q17_zip_collect]
  simp only [List.drop_zero]
  have ht : (List.zipWith (fun x y => [x, y]) xs ys).take
      ((List.zipWith (fun x y => [x, y]) xs ys).length + 1) =
      List.zipWith (fun x y => [x, y]) xs ys := List.take_of_length_le (by omega)
  rw [ht]
  all_goals rfl

 theorem group5_q17_zip_length {α S : Type} (i1 i2 : IteratorModel α S) (m n : Nat)
    (h1 : (i1.iteratorSize == .isInfinite) = false)
    (h2 : (i2.iteratorSize == .isInfinite) = false)
    (hm : i1.length = .ok m) (hn : i2.length = .ok n) :
    homogeneousZipLength (zipModel [i1, i2]) = .ok (min m n) := by
  have hi1 : i1.iteratorSize ≠ .isInfinite := by
    intro heq
    rw [heq] at h1
    cases h1
  have hi2 : i2.iteratorSize ≠ .isInfinite := by
    intro heq
    rw [heq] at h2
    cases h2
  simp [homogeneousZipLength, zipLength, sourceMethod385, sourceMethod394,
    tupleOfList, zipModel, hi1, hi2, hm, hn, Nat.min_comm]

 theorem IteratorsZip_proven : JuliaLean.Proofs.base.iterators.ZipCorrect := by
  refine ⟨?_, ?_, ?_⟩
  · intro α xs ys
    exact ⟨group5_q17_zip_emits xs ys,
      group5_q17_zip_length (listIterator xs) (listIterator ys) _ _ rfl rfl rfl rfl⟩
  · intro α β xs ys
    refine ⟨?_, ?_⟩
    · rw [← zipWith_map_inl_inr]
      exact group5_q17_zip_emits _ _
    · have hlen := group5_q17_zip_length (listIterator (xs.map Sum.inl))
        (listIterator (ys.map Sum.inr)) _ _ rfl rfl rfl rfl
      change homogeneousZipLength (zipModel [listIterator (xs.map Sum.inl), listIterator (ys.map Sum.inr)]) = _
      simpa only [List.length_map] using hlen
  · exact group5_q17_zip_length

 theorem IteratorsZipReverse_proven : JuliaLean.Proofs.base.iterators.ZipReverse := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α xs ys hlen
    constructor
    · simp [reverseZipModel, zipLengthsFiniteEqualOn, listIterator, zipModel, hlen, List.mapM, List.mapM.loop]
    · rw [List.reverse_zipWith hlen]
      exact group5_q17_zip_emits xs.reverse ys.reverse
  · intro α xs ys hlen
    refine ⟨"Cannot reverse zipped iterators of unknown, infinite, or unequal lengths", ?_⟩
    have hrev : ys.length ≠ xs.length := Ne.symm hlen
    simp [reverseZipModel, zipLengthsFiniteEqualOn, listIterator, zipModel, hlen, hrev]
  · intro α β xs ys hlen
    rw [List.reverse_zipWith hlen, ← zipWith_map_inl_inr]
    exact group5_q17_zip_emits _ _
  · intro I R iteratorSize length reverseEach z same len h
    simp only [reverseZipModel, h, ok_bind]

end JuliaLean.ChatGPT.Batch4.Group5

/- Supporting block: Queue36_42_45 -/
namespace JuliaLean.ChatGPT.Batch4.Group5
open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators

set_option maxRecDepth 4096

 theorem group5_q36_promote_fallback {A : Type}
    (promoteShape : List A → List A → Jl (List A)) (a b : List A) :
    promoteTupleShape2 (fun _ => (none : Option Empty)) Empty.elim (fun e _ => pure e)
      (fun _ => (none : Option Empty)) Empty.elim (fun e _ => pure e) promoteShape a b =
        promoteShape a b := by
  cases a with
  | nil => rfl
  | cons x xs =>
      cases xs with
      | cons y ys => rfl
      | nil =>
          cases b with
          | nil => rfl
          | cons z zs => cases zs <;> rfl

 theorem IteratorscovZipMetadata_proven : JuliaLean.Proofs.base.iterators.ZipMetadata := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α xs ys
    constructor <;>
      simp [homogeneousZipMinimum, tupleOfList, sourceMethod385, sourceMethod394,
        listIterator, Nat.min_comm]
  · intro α β xs ys
    have h := group5_q17_zip_length (listIterator (xs.map Sum.inl))
      (listIterator (ys.map Sum.inr)) _ _ rfl rfl rfl rfl
    change homogeneousZipLength (zipModel [listIterator (xs.map Sum.inl), listIterator (ys.map Sum.inr)]) = _
    simpa only [List.length_map] using h
  · intro α xs ys
    constructor
    · by_cases hxy : xs.length = ys.length
      · simp [zipLengthsFiniteEqual, listIterator, hxy]
      · have hyx : ys.length ≠ xs.length := Ne.symm hxy
        simp [zipLengthsFiniteEqual, listIterator, hxy, hyx]
    · rfl
  · intro α xs ys zs
    simp [zipSizeValues, zipAxesValues, sourceMethod412, sourceMethod413, zipShape,
      zipModel, tupleMetadata, tupleOfList, sourceMethod417, sourceMethod418,
      listIterator, promoteSizeShape1D_single, promoteAxesShape1D, sourceMethod414]
    all_goals rfl
  · intro A promoteShape a b m n intersect mi ni
    refine ⟨rfl, rfl, rfl, ?_, rfl⟩
    simp only [sourceMethod417, sourceMethod418, pure_jl, ok_bind]
    exact group5_q36_promote_fallback promoteShape a b
  · intro Is T fieldTypes eltype tupleOrBottom z
    all_goals rfl
  · intro α xs ys
    have hlen := group5_q17_zip_length (listIterator xs) (listIterator ys) _ _ rfl rfl rfl rfl
    change (if 0 < min xs.length ys.length then
      ∃ x y, listGet xs (min xs.length ys.length - 1) = some x ∧
        listGet ys (min xs.length ys.length - 1) = some y ∧
        sourceMethod519 (zipModel [listIterator xs, listIterator ys])
          (fun z => Except.map Int.ofNat (homogeneousZipLength z))
          (fun z n => nthZipValues z.is n) = .ok [x, y]
      else sourceMethod519 (zipModel [listIterator xs, listIterator ys])
          (fun z => Except.map Int.ofNat (homogeneousZipLength z))
          (fun z n => nthZipValues z.is n) = .error .boundsError)
    simp only [sourceMethod519, hlen, Except.map, ok_bind]
    have hnth := nthZip_two_lists xs ys (Int.ofNat (min xs.length ys.length))
    by_cases hp : 0 < min xs.length ys.length
    · have hpn : (1 : Nat) ≤ min xs.length ys.length := by omega
      have hc : 1 ≤ Int.ofNat (min xs.length ys.length) ∧
          Int.ofNat (min xs.length ys.length) ≤ min xs.length ys.length :=
        ⟨Int.ofNat_le.mpr hpn, Int.le_refl _⟩
      rw [if_pos hc] at hnth
      simpa only [hp, ↓reduceIte, Int.toNat, zipModel] using hnth
    · have hz : min xs.length ys.length = 0 := Nat.eq_zero_of_not_pos hp
      simpa [hz, zipModel] using hnth

 theorem group5_q43_collect_same_run {I α S : Type} {m : Type → Type}
    [Monad m] [CollectRun I α S m] (itr : I) (state1 state2 : Option S)
    (hr : CollectRun.run itr state1 = CollectRun.run itr state2) (depth : Nat) :
    JuliaLean.Proofs.base.iterators.collectPrefix itr depth state1 = JuliaLean.Proofs.base.iterators.collectPrefix itr depth state2 := by
  cases depth with
  | zero => rfl
  | succ depth => simp only [JuliaLean.Proofs.base.iterators.collectPrefix, hr]

 theorem group5_q43_reverse_trace {α : Type} (xs : List α) (m : Nat)
    (hm : m ≤ xs.length) :
    followsFrom (reverseListAsIterator xs) (some (Int.ofNat m)) ((xs.take m).reverse) := by
  induction m with
  | zero =>
      change JuliaLean.Proofs.base.iterators.collectPrefix (reverseListAsIterator xs) 1 (some 0) = .ok []
      rw [collectPrefix_succ, reverseListAsIterator_run_zero]
      all_goals rfl
  | succ m ih =>
      obtain ⟨x, hx, hrev⟩ := listGet_take_last xs m (by omega)
      rw [hrev]
      apply followsFrom_cons_intro (reverseListAsIterator xs) (some (Int.ofNat (m + 1)))
        x ((xs.take m).reverse) (Int.ofNat m)
      · exact reverseListAsIterator_run_succ xs m x hx
      · exact ih (by omega)

 theorem group5_q43_reverse_emits {α : Type} (xs : List α) :
    emitsExactly (reverseListAsIterator xs) xs.reverse := by
  have h := group5_q43_reverse_trace xs xs.length (Nat.le_refl _)
  simp only [List.take_length] at h
  change JuliaLean.Proofs.base.iterators.collectPrefix (reverseListAsIterator xs) (xs.reverse.length + 1) none = .ok xs.reverse
  rw [group5_q43_collect_same_run (reverseListAsIterator xs) none
    (some (Int.ofNat xs.length)) (by rfl)]
  exact h

 theorem group5_q43_reverseArray_step {α : Type} (xs : List α) (indices : List Nat) (i : Nat) :
    (reverseArrayAsIterator xs).run (some (indices, i)) =
      (do match ← (listIterator indices).run (some i) with
        | none => pure none
        | some (idx, next) =>
            match listGet xs idx with
            | none => .error .boundsError
            | some x => .ok (some (x, (indices, next)))) := by
  simp only [reverseArrayAsIterator, sourceMethod136, pure_jl, ok_bind, reverseDefault]
  cases (listIterator indices).run (some i) with
  | error e => rfl
  | ok y =>
      cases y with
      | none => rfl
      | some pair =>
          rcases pair with ⟨idx, next⟩
          simp only [ok_bind]
          cases hget : listGet xs idx <;> rfl

 theorem group5_q43_reverseArray_trace {α : Type} (xs : List α) (m i : Nat)
    (hmi : m + i = xs.length) :
    followsFrom (reverseArrayAsIterator xs) (some ((List.range xs.length).reverse, i))
      ((xs.take m).reverse) := by
  induction m generalizing i with
  | zero =>
      have hi : i = xs.length := by omega
      subst i
      change JuliaLean.Proofs.base.iterators.collectPrefix (reverseArrayAsIterator xs) 1
        (some ((List.range xs.length).reverse, xs.length)) = .ok []
      rw [collectPrefix_succ, group5_q43_reverseArray_step, listIterator_run_some]
      have hdrop : (List.range xs.length).reverse.drop xs.length = [] := by
        exact List.drop_eq_nil_iff.mpr (by simpa only [List.length_reverse, List.length_range] using Nat.le_refl xs.length)
      rw [hdrop]
      all_goals rfl
  | succ m ih =>
      obtain ⟨x, hx, hrev⟩ := listGet_take_last xs m (by omega)
      rw [hrev]
      apply followsFrom_cons_intro (reverseArrayAsIterator xs)
        (some ((List.range xs.length).reverse, i)) x ((xs.take m).reverse)
        ((List.range xs.length).reverse, i + 1)
      · rw [group5_q43_reverseArray_step, listIterator_run_some,
          drop_reverse_range xs.length i (by omega)]
        have hd : xs.length - i = m + 1 := by omega
        rw [hd, List.range_succ, List.reverse_append]
        simp only [List.reverse_singleton, List.singleton_append, pure_jl, ok_bind, hx]
      · exact ih (i + 1) (by omega)

 theorem group5_q43_reverseArray_emits {α : Type} (xs : List α) :
    emitsExactly (reverseArrayAsIterator xs) xs.reverse := by
  have h := group5_q43_reverseArray_trace xs xs.length 0 (by omega)
  simp only [List.take_length] at h
  change JuliaLean.Proofs.base.iterators.collectPrefix (reverseArrayAsIterator xs) (xs.reverse.length + 1) none = .ok xs.reverse
  rw [group5_q43_collect_same_run (reverseArrayAsIterator xs) none
    (some ((List.range xs.length).reverse, 0)) (by rfl)]
  exact h

 theorem IteratorscovReverseYields_proven : JuliaLean.Proofs.base.iterators.ReverseYields := by
  intro α β N inst xs f n a b
  refine ⟨group5_q43_reverse_emits xs, group5_q43_reverseArray_emits xs,
    group5_q43_reverseArray_emits xs, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · simpa only [List.reverse_reverse] using group5_q43_reverse_emits xs.reverse
  · rw [← List.map_reverse]
    change JuliaLean.Proofs.base.iterators.collectPrefix (generatorAsIterator (fun f x => pure (f x)) ⟨f, listIterator xs.reverse⟩)
      ((xs.reverse.map f).length + 1) none = .ok (xs.reverse.map f)
    simp only [List.length_map]
    exact collectPrefix_generator f (listIterator xs.reverse) (xs.reverse.length + 1) none
      xs.reverse (group5_q15_list_follows xs.reverse)
  · intro s
    all_goals rfl

 theorem IteratorscovReverseTraits_proven : JuliaLean.Proofs.base.iterators.ReverseTraits := by
  constructor
  · intro α xs
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, reverseLast_eq_last_reverse xs, rfl, ?_⟩
    · simpa only [List.reverse_reverse] using group5_q43_reverse_emits xs.reverse
    · intro s
      all_goals rfl
  · intro I α N length size first isz iel itr
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩


 theorem group5_q42_reverse_enumerate_trace {α : Type} (xs : List α) (m : Nat)
    (hm : m ≤ xs.length) :
    followsFrom (reverseEnumerateAsIterator xs)
      (some (m, reverseListAsIterator xs, Int.ofNat m))
      (((enumerateNatFrom 1 (xs.take m)).reverse).map
        (fun (i, v) => (JInt.lit .i64 (Int.ofNat i), v))) := by
  induction m with
  | zero =>
      change JuliaLean.Proofs.base.iterators.collectPrefix (reverseEnumerateAsIterator xs) 1
        (some (0, reverseListAsIterator xs, 0)) = .ok []
      rw [collectPrefix_succ]
      have hstop : (reverseEnumerateAsIterator xs).run
          (some (0, reverseListAsIterator xs, 0)) = .ok none := by
        simp only [reverseEnumerateAsIterator, reverseEnumerateStep,
          reverseListAsIterator_run_zero, pure_jl, ok_bind]
      rw [hstop]
      all_goals rfl
  | succ m ih =>
      obtain ⟨x, hx, _⟩ := listGet_take_last xs m (by omega)
      have hrev := enumerateNatFrom_take_succ xs 1 m x hx (by omega)
      rw [Nat.add_comm 1 m] at hrev
      rw [hrev, List.map_cons]
      apply followsFrom_cons_intro (reverseEnumerateAsIterator xs)
        (some (m + 1, reverseListAsIterator xs, Int.ofNat (m + 1)))
        (JInt.lit .i64 (Int.ofNat (m + 1)), x)
        (((enumerateNatFrom 1 (xs.take m)).reverse).map
          (fun (i, v) => (JInt.lit .i64 (Int.ofNat i), v)))
        (m, reverseListAsIterator xs, Int.ofNat m)
      · have hs : (reverseListAsIterator xs).run (some (Int.ofNat (m + 1))) =
            .ok (some (x, Int.ofNat m)) := reverseListAsIterator_run_succ xs m x hx
        simp only [reverseEnumerateAsIterator, reverseEnumerateStep,
          pure_jl, Nat.add_sub_cancel]
        rw [hs]
        rfl
      · exact ih (by omega)

 theorem group5_q42_reverse_enumerate_emits {α : Type} (xs : List α) :
    emitsExactly (reverseEnumerateAsIterator xs)
      (((enumerateNatFrom 1 xs).reverse).map
        (fun (i, v) => (JInt.lit .i64 (Int.ofNat i), v))) := by
  have h := group5_q42_reverse_enumerate_trace xs xs.length (Nat.le_refl _)
  simp only [List.take_length] at h
  unfold emitsExactly
  rw [group5_q43_collect_same_run (reverseEnumerateAsIterator xs) none
    (some (xs.length, reverseListAsIterator xs, Int.ofNat xs.length)) (by rfl)]
  exact h

 theorem IteratorscovEnumerate_proven : JuliaLean.Proofs.base.iterators.EnumerateSound := by
  refine ⟨IteratorsEnumerate_proven, ?_, ?_⟩
  · intro α xs
    exact ⟨group5_q42_reverse_enumerate_emits xs, enumerateLast_eq xs,
      rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro I α N length size last isz iel itr
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩


 theorem group5_q45_any_cons {I S : Type} (done : I → Option S → Jl (Option Bool))
    (itr : I) (st : Option S) (rest : List (I × Option S)) :
    zipAnyDoneObservation done ((itr, st) :: rest) =
      (do let d ← done itr st
          if d = some true then pure d
          else pure (boolOrMissing d (← zipAnyDoneObservation done rest))) := by
  all_goals rfl

 theorem group5_q45_any_false {I S : Type} (done : I → Option S → Jl (Option Bool))
    (inputs : List (I × Option S))
    (h : ∀ c ∈ inputs, done c.1 c.2 = .ok (some false)) :
    zipAnyDoneObservation done inputs = .ok (some false) := by
  induction inputs with
  | nil => rfl
  | cons c rest ih =>
      rcases c with ⟨itr, st⟩
      rw [group5_q45_any_cons, h (itr, st) (List.mem_cons_self)]
      simp only [ok_bind, reduceCtorEq, ↓reduceIte]
      have hrest := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
      rw [hrest]
      all_goals rfl

 theorem group5_q45_scan_missing {K : Type} {I V S : K → Type}
    (ops : ZipCalls Jl I V S)
    (h : ∀ k i st, ops.done k i st = .ok none)
    {ks : List K} (is : TupleVals I ks) (ss : TupleVals (fun k => Option (S k)) ks) :
    zipDoneScan ops is ss =
      .ok (false, tupleMap (fun _ _ => (none : Option Bool)) is) := by
  induction is with
  | nil => cases ss; rfl
  | cons i is ih =>
      cases ss with
      | cons st ss =>
          simp only [zipDoneScan, h, ok_bind, ih ss, tupleMap]
          all_goals rfl

 theorem group5_q45_tuple_missing {K : Type} {I : K → Type}
    {ks : List K} (is : TupleVals I ks) :
    tupleAllMissing (tupleMap (fun _ _ => (none : Option Bool)) is) = true := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [tupleMap, tupleAllMissing, Option.isNone_none, Bool.true_and, ih]

 theorem group5_q45_tuple_constant {K A : Type} {I : K → Type}
    {ks : List K} (is : TupleVals I ks) (a : A) :
    tupleValueList (tupleMap (fun _ _ => a) is) = List.replicate ks.length a := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [tupleMap, tupleValueList, List.length_cons, List.replicate_succ, ih]

 theorem group5_q45_tuple_map {K A B : Type} {ks : List K}
    (f : A → B) (values : TupleVals (fun _ : K => A) ks) :
    tupleValueList (tupleMap (fun _ x => f x) values) = (tupleValueList values).map f := by
  induction values with
  | nil => rfl
  | cons x xs ih => simp only [tupleMap, tupleValueList, List.map_cons, ih]

 theorem group5_q45_all_missing {I S : Type} (done : I → Option S → Jl (Option Bool))
    (h : ∀ itr st, done itr st = .ok none) (inputs : List (I × Option S)) :
    zipDoneScanObservation done inputs = .ok (false, List.replicate inputs.length none) := by
  dsimp only [zipDoneScanObservation]
  rw [group5_q45_scan_missing _ (by intro k i st; exact h k.1 st)]
  simp only [ok_bind, group5_q45_tuple_constant]
  all_goals rfl

 theorem group5_q45_all_order {I α S : Type}
    (done : I → Option S → Jl (Option Bool)) (run : I → Option S → Jl (Option (α × S)))
    (h : ∀ itr st, done itr st = .ok none) (inputs : List (I × Option S)) :
    zipAllObservation done run inputs = zipOrderObservation run inputs := by
  unfold zipAllObservation zipOrderObservation
  simp only [zipIterateAll]
  rw [group5_q45_scan_missing _ (by intro k i st; exact h k.1 st)]
  simp only [ok_bind, Bool.false_eq_true, ↓reduceIte, group5_q45_tuple_missing]
  have heq : (fun (i : I × Option S) (_ : Unit) st => done i.1 st) =
      (fun _ _ _ => (pure none : Jl (Option Bool))) := by
    funext i u st
    exact h i.1 st
  rw [heq]
  cases hr : zipInOrder
      (⟨(fun (i : I × Option S) (_ : Unit) st => run i.1 st),
        (fun _ _ _ => pure none)⟩ :
        ZipCalls Jl (fun _ : I × Option S => Unit) (fun _ => α) (fun _ => S))
      (tupleOfList inputs) (tupleOptions inputs) with
  | error e => rfl
  | ok result =>
      cases result with
      | none => rfl
      | some values =>
          simp only [pure_jl, ok_bind, Option.map_some, group5_q45_tuple_map, List.map_map]
          all_goals rfl

 theorem group5_q45_replicate_missing (n : Nat) :
    allMissingObservation (List.replicate n none) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, allMissingObservation,
      tupleOfList, tupleMap, tupleAllMissing, Option.isNone_none, Bool.true_and] using ih

 theorem group5_q45_projection_state {α : Type} (xs ys : List α) (i j : Nat) :
    observeJl (zipAllObservation
      (fun (itr : IteratorModel α Nat) st => itr.isdone st)
      (fun (itr : IteratorModel α Nat) st => itr.run st)
      [(listIterator xs, some i), (listIterator ys, some j)]) =
      projectZipState ((zipListObservation xs ys).run (some (.cons i (.cons j .nil)))) := by
  by_cases hx : xs.length ≤ i <;> by_cases hy : ys.length ≤ j
  all_goals
    simp [zipAllObservation, zipListObservation, zipObservation, projectZipState,
      zipState, zipModel, tupleOfList, tupleOptions, tupleMap, zipIterateAll, zipDoneScan,
      tupleAllMissing, zipUnknown, zipRest, tupleValueList, listIterator,
      hx, hy, observeJl, observe, liftJl, Observation.map]
  all_goals (cases hgx : listGet xs i <;> cases hgy : listGet ys j <;> rfl)

 theorem group5_q45_projection_initial {α : Type} (xs ys : List α) :
    observeJl (zipAllObservation
      (fun (itr : IteratorModel α Nat) st => itr.isdone st)
      (fun (itr : IteratorModel α Nat) st => itr.run st)
      [(listIterator xs, none), (listIterator ys, none)]) =
      projectZipState ((zipListObservation xs ys).run none) := by
  by_cases hx : xs.length ≤ 0 <;> by_cases hy : ys.length ≤ 0
  all_goals
    simp [zipAllObservation, zipListObservation, zipObservation, projectZipState,
      zipStart, zipState, zipModel, tupleOfList, tupleOptions, tupleInitial, tupleMap, zipIterateAll, zipDoneScan,
      tupleAllMissing, zipUnknown, zipRest, tupleValueList, listIterator,
      hx, hy, observeJl, observe, liftJl, Observation.map]
  all_goals (cases hgx : listGet xs 0 <;> cases hgy : listGet ys 0 <;> rfl)

 theorem IteratorscovZipProtocol_proven : JuliaLean.Proofs.base.iterators.ZipProtocol := by
  refine ⟨group5_q45_any_false, ?_, ?_, ?_, ?_⟩
  · intro I S done itr state rest h
    rw [group5_q45_any_cons, h]
    all_goals rfl
  · intro I α S iterate
    all_goals rfl
  · intro α xs ys i j
    refine ⟨?_, ?_, ?_, group5_q45_projection_initial xs ys,
      group5_q45_projection_state xs ys i j, group5_q45_projection_state xs ys i j⟩
    · change zipAnyDoneObservation (fun (itr : IteratorModel α Nat) st => itr.isdone st)
        [(listIterator xs, none), (listIterator ys, none)] =
          .ok (some (decide (xs.length ≤ 0 ∨ ys.length ≤ 0)))
      by_cases hx : xs.length ≤ 0 <;> by_cases hy : ys.length ≤ 0 <;>
        simp [zipAnyDoneObservation, tupleOfList, tupleOptions, zipAnyDone,
          listIterator, boolOrMissing, hx, hy]
    · by_cases hx : xs.length ≤ i <;> by_cases hy : ys.length ≤ j <;>
        simp [zipAnyDoneObservation, List.map_cons, List.map_nil, tupleOfList, tupleOptions, zipAnyDone,
          listIterator, boolOrMissing, hx, hy]
    · by_cases hx : xs.length ≤ i <;> by_cases hy : ys.length ≤ j <;>
        simp [zipDoneScanObservation, tupleOfList, tupleOptions, zipDoneScan,
          tupleValueList, listIterator, hx, hy]
  · intro I α S is states done run hlen hdone
    refine ⟨?_, group5_q45_replicate_missing is.length, group5_q45_all_order done run hdone _⟩
    simpa only [List.length_zip, hlen, Nat.min_self] using group5_q45_all_missing done hdone (List.zip is states)

end JuliaLean.ChatGPT.Batch4.Group5

/- Supporting block: Queue19_24 -/
namespace JuliaLean.ChatGPT.Batch4.Group5
open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators

theorem finiteObservation_ok_bind {α β : Type} (x : α)
    (f : α → Observation JlError β) : (Observation.ok x >>= f) = f x := rfl

theorem finiteObservation_pure {α : Type} (x : α) :
    (pure x : Observation JlError α) = .ok x := rfl

/-- Pointwise correspondence between two finite lists. -/
inductive finiteRelatedLists {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : finiteRelatedLists R [] []
  | cons {x y xs ys} : R x y → finiteRelatedLists R xs ys →
      finiteRelatedLists R (x :: xs) (y :: ys)

/-- The two empty-product clauses do not require any iterator assumptions. -/
theorem productEmptyClauses :
    (∀ {α : Type}, iterateEmptyProduct (α := α) = ([], true)) ∧
    (∀ {α S : Type} (state : S), iterateEmptyProductState (α := α) state = none) := by
  exact ⟨fun {α} => rfl, fun {α S} state => rfl⟩

/-- At depth zero, every Cartesian product has the required empty prefix. -/
theorem productZeroDepth {α : Type} (factors : List (List α)) :
    let p := productModel (factors.map listIterator)
    let itr := productObservation p (fun item state => item.isdone state)
      (fun item state => item.run state) (fun _ => α) (fun _ value _ => pure value)
    observeRun itr.run 0 none = .ok ((r6CartesianRows factors).take 0) := rfl

/-- Tuple flattening uses checked multiplication of the fixed arity and outer length. -/
theorem IteratorsFlattenTupleLength_proven :
    JuliaLean.Proofs.base.iterators.FlattenTupleLength := by
  constructor
  · intro α k rows hrows
    have hlen : rows.flatten.length = k * rows.length := flatten_uniform_length k rows hrows
    change if k * rows.length < 2 ^ 63 then
      flattenTupleLength (fun it => it.length) checkedMulNatI64
        (flattenModel (listIterator rows)) k = .ok rows.flatten.length ∧
      sourceMethod1332 (fun it => it.length) (.fixedTuple k) checkedMulNatI64
        (flattenModel (listIterator rows)) = .ok rows.flatten.length
    else
      flattenTupleLength (fun it => it.length) checkedMulNatI64
        (flattenModel (listIterator rows)) k = .error (.overflowError "checked_mul") ∧
      sourceMethod1332 (fun it => it.length) (.fixedTuple k) checkedMulNatI64
        (flattenModel (listIterator rows)) = .error (.overflowError "checked_mul")
    rw [hlen]
    by_cases hfit : k * rows.length < 2 ^ 63
    · simp only [hfit, ↓reduceIte, sourceMethod1332, flattenTupleLength, flattenModel,
        listIterator_length, ok_bind, checkedMulNatI64, and_self]
    · simp only [hfit, ↓reduceIte, sourceMethod1332, flattenTupleLength, flattenModel,
        listIterator_length, ok_bind, checkedMulNatI64, and_self]
  · intro I length f k m hlength
    simp only [sourceMethod1332, flattenTupleLength, hlength, ok_bind, and_self]

/-- The generic partition-length clause delegates to the supplied ceiling division. -/
theorem partitionLengthDelegates {I : Type} (length : I → Jl Nat)
    (itr : PartitionIterator I) (l : Nat) (hlength : length itr.c = .ok l) :
    partitionLength length (fun l k => pure ((l + k.val.toNat - 1) / k.val.toNat)) itr =
      .ok ((l + itr.n.val.toNat - 1) / itr.n.val.toNat) := by
  simp only [partitionLength, hlength, ok_bind, pure_jl]


/-- Rewrapping a nonnegative machine count through Nat preserves it exactly. -/
theorem countNatRoundtrip (n : JInt64) (hn : 0 ≤ n.val) :
    JInt.lit .i64 (n.val.toNat : Int) = n := by
  apply Subtype.ext
  change wrapInt .i64 (n.val.toNat : Int) = n.val
  rw [Int.toNat_of_nonneg hn]
  exact wrapInt_of_inRange .i64 n.val n.property

/-- Finite repetition preserves its nonnegative native count. -/
theorem repeatedConstructorNonnegative {O : Type} (x : O) (n : JInt64)
    (hn : 0 ≤ n.val) : CountValue.repeated x n.val = .ok ⟨repeatedModel x, n⟩ := by
  simp only [CountValue.repeated, repeatedNModel, CountValue.toInt,
    jint_convert_i64_self, ok_bind, takeModel, CountValue.convert_native,
    CountValue.takeConstructor_eq, show ¬ n.val < 0 by omega, ↓reduceIte]

/-- Negative native counts fail the Take constructor after successful conversion. -/
theorem repeatedConstructorNegative {O : Type} (x : O) (n : JInt64)
    (hn : n.val < 0) : CountValue.repeated x n.val =
      .error (.argumentError "Take length must be non-negative") := by
  simp only [CountValue.repeated, repeatedNModel, CountValue.toInt,
    jint_convert_i64_self, ok_bind, takeModel, CountValue.convert_native,
    CountValue.takeConstructor_eq, hn, ↓reduceIte]

/-- Counts outside the signed native range fail before building the repetition. -/
theorem repeatedConstructorOutOfRange {O : Type} (x : O) (n : Int)
    (hn : n < -(2 ^ 63) ∨ 2 ^ 63 ≤ n) : CountValue.repeated x n =
      .error (.inexactError "Int64") := by
  simp only [CountValue.repeated, repeatedNModel, CountValue.toInt,
    jint_convert_i64_out n hn, err_bind]

/-- Repetition yields its requested finite prefix and reports exactly that length. -/
theorem IteratorsRepeatedN_proven : JuliaLean.Proofs.base.iterators.RepeatedNCorrect := by
  refine ⟨?_, ?_, ?_⟩
  · intro O x n hn
    refine ⟨⟨repeatedModel x, n⟩, repeatedConstructorNonnegative x n hn, ?_, ?_⟩
    · unfold repeatedListObservation emitsExactly
      rw [countNatRoundtrip n hn, group5_collect_eq_observe]
      change Round5.observe
        (takeObservation (repeatedAsIterator (repeatedModel x))
          ⟨repeatedAsIterator (repeatedModel x), n⟩).run
        ((List.replicate n.val.toNat x).length + 1) none =
          .ok (List.replicate n.val.toNat x)
      rw [group5_take_run_function]
      rw [observeLiftJl, observeTakePrefixFromState
        (fun it st => it.run st) ⟨repeatedAsIterator (repeatedModel x), n⟩
        ((List.replicate n.val.toNat x).length + 1) none hn]
      simp only [Option.map_none, Option.getD_none, List.length_replicate,
        Nat.min_eq_right (Nat.le_succ _)]
      change observeJl (Round5.observe
        (fun st => pure (iterateRepeated (repeatedModel x) st)) n.val.toNat none) =
          .ok (List.replicate n.val.toNat x)
      rw [observeRepeatedModel]
      rfl
    · unfold repeatedListObservation
      rw [countNatRoundtrip n hn]
      simp only [takeObservation, AsObservation.view, takeLength, repeatedAsIterator,
        repeatedIteratorSize, minLengthLeftInfinite, pure_jl, ok_bind, Sum.elim_inl, id_eq]
  · exact repeatedConstructorNegative
  · exact repeatedConstructorOutOfRange

/-- The native finite-cycle constructor preserves its input and count. -/
theorem cycleConstructorNonnegative {I : Type} (xs : I) (n : JInt64)
    (hn : 0 ≤ n.val) : CountValue.cycle xs n.val = .ok ⟨⟨repeatedModel xs, n⟩⟩ := by
  simp only [CountValue.cycle, cycleNModel, repeatedConstructorNonnegative xs n hn,
    ok_bind, pure_jl, flattenModel]

/-- The finite-cycle constructor propagates negative-count rejection. -/
theorem cycleConstructorNegative {I : Type} (xs : I) (n : JInt64)
    (hn : n.val < 0) : CountValue.cycle xs n.val =
      .error (.argumentError "Take length must be non-negative") := by
  simp only [CountValue.cycle, cycleNModel, repeatedConstructorNegative xs n hn, err_bind]

/-- The finite-cycle constructor propagates an out-of-range conversion error. -/
theorem cycleConstructorOutOfRange {I : Type} (xs : I) (n : Int)
    (hn : n < -(2 ^ 63) ∨ 2 ^ 63 ≤ n) : CountValue.cycle xs n =
      .error (.inexactError "Int64") := by
  simp only [CountValue.cycle, cycleNModel, repeatedConstructorOutOfRange xs n hn, err_bind]

/-- Flatten stops immediately if its outer iterator is empty. -/
theorem flattenStartEmpty {α O S : Type}
    (outer : IteratorModel (IteratorModel α S) O)
    (h : outer.run none = .ok none) : flattenStartStep outer = .ok none := by
  unfold flattenStartStep observe
  rw [flattenOuter.eq_def]
  simp only [flattenModel, liftJl, h]

/-- Flatten forwards the first value and both returned iteration states. -/
theorem flattenStartNonempty {α O S : Type}
    (outer : IteratorModel (IteratorModel α S) O) (inner : IteratorModel α S)
    (nextOuter : O) (value : α) (nextInner : S)
    (ho : outer.run none = .ok (some (inner, nextOuter)))
    (hi : inner.run none = .ok (some (value, nextInner))) :
    flattenStartStep outer = .ok (some (value, (nextOuter, inner, nextInner))) ∧
    (flattenObservation (flattenModel outer)).run none =
      .ok (some (value, (nextOuter, inner, nextInner))) := by
  have hstart : flattenStartStep outer = .ok (some (value, (nextOuter, inner, nextInner))) := by
    unfold flattenStartStep observe
    rw [flattenOuter.eq_def]
    simp only [flattenModel, liftJl, ho, hi]
  refine ⟨hstart, ?_⟩
  simpa only [flattenObservation, AsObservation.view, group5_action_observe,
    flattenStartStep] using hstart

/-- A live inner iterator advances without touching the outer iterator. -/
theorem flattenInnerNonempty {α O S : Type}
    (outer : IteratorModel (IteratorModel α S) O) (outerState : O)
    (inner : IteratorModel α S) (innerState : S) (value : α) (nextInner : S)
    (hi : inner.run (some innerState) = .ok (some (value, nextInner))) :
    flattenStateStep outer (outerState, inner, innerState) =
      .ok (some (value, (outerState, inner, nextInner))) := by
  simp only [flattenStateStep, flattenState, liftJl, hi, observe,
    Bind.bind, JuliaLean.base.iterators.bind, Pure.pure, ret]


/-- A finite successful collection includes a history followed by exhaustion. -/
theorem followsFromComplete {α S : Type} (itr : IteratorModel α S) :
    ∀ (xs : List α) (st : Option S), followsFrom itr st xs →
      ∃ final, Round4.History itr.run st xs final ∧ itr.run final = .ok none := by
  intro xs
  induction xs with
  | nil =>
      intro st h
      exact ⟨st, .nil st, followsFrom_nil itr st h⟩
  | cons x xs ih =>
      intro st h
      obtain ⟨next, hstep, htail⟩ := followsFrom_cons itr st x xs h
      obtain ⟨final, hhistory, hstop⟩ := ih (some next) htail
      exact ⟨final, .cons hstep hhistory, hstop⟩

/-- Reading exactly a recorded observation history recovers its values. -/
theorem observationHistoryReads {α S : Type}
    (run : Option S → Observation JlError (Option (α × S)))
    {st final : Option S} {xs : List α} (h : Round4.History run st xs final) :
    Round5.observe run xs.length st = .ok xs := by
  induction h with
  | nil st => rfl
  | @cons st x next xs final hstep htail ih =>
      rw [List.length_cons, Round5.observe, hstep]
      change (do pure (x :: (← Round5.observe run xs.length (some next)))) = .ok (x :: xs)
      rw [ih]
      rfl

/-- A restartable finite protocol produces any prescribed number of full cycles. -/
theorem cycleFiniteRounds {I α S : Type}
    (iterate : I → Option S → Jl (Option (α × S)))
    (isdone : I → Option S → Jl (Option Bool)) (it : I) (xs : List α)
    (cycles : Nat) (h : followsProtocol iterate isdone it xs) :
    JuliaLean.Proofs.base.iterators.collectPrefix (cycleObservation (cycleModel (protocolIterator iterate isdone it)))
      (cycles * xs.length) none = .ok ((List.replicate cycles xs).flatten) := by
  by_cases hempty : xs = []
  · subst xs
    simp only [List.length_nil, Nat.mul_zero, JuliaLean.Proofs.base.iterators.collectPrefix, List.flatten_replicate_nil]
    rfl
  · let itr := protocolIterator iterate isdone it
    have hcomplete : Round4.CompleteHistory itr.run xs := followsFromComplete itr xs none h
    have hrounds : ∀ round ∈ List.replicate cycles xs,
        round ≠ [] ∧ Round4.CompleteHistory itr.run round := by
      intro round hmem
      have heq : round = xs := (List.mem_replicate.mp hmem).2
      subst round
      exact ⟨hempty, hcomplete⟩
    have htail : Round4.History itr.run none [] none := .nil none
    have hdecomp : ∃ (rounds : List (List α)) (tailValues : List α) (final : Option S),
        (∀ round ∈ rounds, round ≠ [] ∧ Round4.CompleteHistory itr.run round) ∧
        Round4.History itr.run none tailValues final ∧
        (List.replicate cycles xs).flatten = rounds.flatten ++ tailValues :=
      ⟨List.replicate cycles xs, [], none, hrounds, htail, (List.append_nil _).symm⟩
    obtain ⟨final, hhistory⟩ :=
      (cycleOutputSemantics_proven.1 itr ((List.replicate cycles xs).flatten)).mpr hdecomp
    have hlen : (List.replicate cycles xs).flatten.length = cycles * xs.length := by
      have huniform : ∀ row ∈ List.replicate cycles xs, row.length = xs.length := by
        intro row hmem
        exact congrArg List.length (List.mem_replicate.mp hmem).2
      rw [flatten_uniform_length xs.length (List.replicate cycles xs) huniform,
        List.length_replicate, Nat.mul_comm]
    rw [group5_collect_eq_observe]
    rw [← hlen]
    exact observationHistoryReads _ hhistory


/-- A terminating observation trace, including its final exhaustion check. -/
inductive finiteObservationTrace {α S : Type}
    (run : Option S → Observation JlError (Option (α × S))) : Option S → List α → Prop where
  | stop {st} : run st = .ok none → finiteObservationTrace run st []
  | step {st x next xs} : run st = .ok (some (x, next)) →
      finiteObservationTrace run (some next) xs → finiteObservationTrace run st (x :: xs)

/-- A single already-computed observation followed by a terminating trace. -/
def finiteObservationStep {α S : Type}
    (run : Option S → Observation JlError (Option (α × S)))
    (step : Observation JlError (Option (α × S))) : List α → Prop
  | [] => step = .ok none
  | x :: xs => ∃ next, step = .ok (some (x, next)) ∧ finiteObservationTrace run (some next) xs

theorem finiteObservationStep_to_trace {α S : Type}
    (run : Option S → Observation JlError (Option (α × S)))
    (st : Option S) (xs : List α) (h : finiteObservationStep run (run st) xs) :
    finiteObservationTrace run st xs := by
  cases xs with
  | nil => exact .stop h
  | cons x xs => obtain ⟨next, hstep, htail⟩ := h; exact .step hstep htail

theorem finiteObservationTrace_reads {α S : Type}
    (run : Option S → Observation JlError (Option (α × S)))
    {st : Option S} {xs : List α} (h : finiteObservationTrace run st xs) :
    Round5.observe run (xs.length + 1) st = .ok xs := by
  induction h with
  | stop hstop =>
      rw [List.length_nil, Nat.zero_add, Round5.observe, hstop]
      rfl
  | @step st x next xs hstep htail ih =>
      rw [List.length_cons, Round5.observe, hstep]
      change (do pure (x :: (← Round5.observe run (xs.length + 1) (some next)))) = .ok (x :: xs)
      rw [ih]
      rfl

/-- Recover the individual successful steps from an exact finite observation. -/
theorem finiteObservationTrace_of_reads {α S : Type}
    (run : Option S → Observation JlError (Option (α × S))) :
    ∀ (xs : List α) (st : Option S),
      Round5.observe run (xs.length + 1) st = .ok xs → finiteObservationTrace run st xs := by
  intro xs
  induction xs with
  | nil =>
      intro st h
      rw [List.length_nil, Nat.zero_add, Round5.observe] at h
      cases hr : run st with
      | error e => rw [hr] at h; cases h
      | diverged => rw [hr] at h; cases h
      | ok y =>
          rw [hr] at h
          cases y with
          | none => exact .stop hr
          | some pair =>
              change Observation.ok [pair.1] = Observation.ok [] at h
              cases h
  | cons x xs ih =>
      intro st h
      rw [List.length_cons, Round5.observe] at h
      cases hr : run st with
      | error e => rw [hr] at h; cases h
      | diverged => rw [hr] at h; cases h
      | ok y =>
          rw [hr] at h
          cases y with
          | none =>
              change Observation.ok [] = Observation.ok (x :: xs) at h
              cases h
          | some pair =>
              change (do pure (pair.1 ::
                (← Round5.observe run (xs.length + 1) (some pair.2)))) = .ok (x :: xs) at h
              cases ht : Round5.observe run (xs.length + 1) (some pair.2) with
              | error e => rw [ht] at h; cases h
              | diverged => rw [ht] at h; cases h
              | ok tail =>
                  rw [ht] at h
                  have heq : pair.1 :: tail = x :: xs := by
                    exact Observation.ok.inj h
                  obtain ⟨hx, hxs⟩ := List.cons.inj heq
                  subst tail
                  exact .step (by
                    rw [hr]
                    exact congrArg (fun value : α × S => Observation.ok (some value)) (Prod.ext hx rfl))
                    (ih (some pair.2) ht)

/-- The current inner iterator either yields or continues with the outer scan. -/
def flattenCurrentStep {OI I α O S : Type}
    [AsObservation OI I O] [AsObservation I α S]
    (f : Flatten OI) (outerState : O) (inner : I) (innerState : Option S) :
    Observation JlError (Option (α × (O × I × S))) := do
  match ← (AsObservation.view inner).run innerState with
  | some (value, next) => pure (some (value, (outerState, inner, next)))
  | none => observe (flattenOuter
      (fun i s => action ((AsObservation.view i).run s))
      (fun i s => action ((AsObservation.view i).run s)) f (some outerState))

theorem flattenCurrentStep_state {OI I α O S : Type}
    [AsObservation OI I O] [AsObservation I α S]
    (f : Flatten OI) (outerState : O) (inner : I) (innerState : S) :
    (flattenObservation f).run (some (outerState, inner, innerState)) =
      flattenCurrentStep f outerState inner (some innerState) := by
  cases hi : (AsObservation.view inner).run (some innerState) with
  | error e =>
      simp only [flattenObservation, flattenState, flattenCurrentStep, hi,
        observe, action, Bind.bind, JuliaLean.base.iterators.bind]
  | diverged =>
      simp only [flattenObservation, flattenState, flattenCurrentStep, hi,
        observe, action, Bind.bind, JuliaLean.base.iterators.bind]
  | ok y =>
      cases y <;>
        simp only [flattenObservation, flattenState, flattenCurrentStep, hi,
          observe, action, Bind.bind, JuliaLean.base.iterators.bind, Pure.pure, ret]

theorem flattenOuterStep_empty {OI I α O S : Type}
    [AsObservation OI I O] [AsObservation I α S]
    (f : Flatten OI) (st : Option O)
    (ho : (AsObservation.view f.it).run st = .ok none) :
    observe (flattenOuter
      (fun i s => action ((AsObservation.view i).run s))
      (fun i s => action ((AsObservation.view i).run s)) f st) = .ok none := by
  unfold observe
  rw [flattenOuter.eq_def]
  simp only [ho, action]

theorem flattenOuterStep_nonempty {OI I α O S : Type}
    [AsObservation OI I O] [AsObservation I α S]
    (f : Flatten OI) (st : Option O) (inner : I) (nextOuter : O)
    (ho : (AsObservation.view f.it).run st = .ok (some (inner, nextOuter))) :
    observe (flattenOuter
      (fun i s => action ((AsObservation.view i).run s))
      (fun i s => action ((AsObservation.view i).run s)) f st) =
        flattenCurrentStep f nextOuter inner none := by
  unfold observe
  rw [flattenOuter.eq_def]
  cases hi : (AsObservation.view inner).run none with
  | error e => simp only [ho, hi, action, flattenCurrentStep, Bind.bind]
  | diverged => simp only [ho, hi, action, flattenCurrentStep, Bind.bind]
  | ok y =>
      cases y <;> simp only [ho, hi, action, flattenCurrentStep, observe,
        Bind.bind, Pure.pure]

/-- A finite inner trace is prepended to the already-established outer tail. -/
theorem flattenInnerTrace {OI I α O S : Type}
    [AsObservation OI I O] [AsObservation I α S]
    (f : Flatten OI) (outerState : O) (inner : I) (rest : List α)
    (hrest : finiteObservationStep (flattenObservation f).run
      (observe (flattenOuter
        (fun i s => action ((AsObservation.view i).run s))
        (fun i s => action ((AsObservation.view i).run s)) f (some outerState))) rest)
    {st : Option S} {xs : List α}
    (hinner : finiteObservationTrace (AsObservation.view inner).run st xs) :
    finiteObservationStep (flattenObservation f).run
      (flattenCurrentStep f outerState inner st) (xs ++ rest) := by
  induction hinner with
  | stop hstop =>
      simpa only [List.nil_append, flattenCurrentStep, hstop, finiteObservation_ok_bind] using hrest
  | @step st x next xs hstep htail ih =>
      change ∃ nextState,
        flattenCurrentStep f outerState inner st = .ok (some (x, nextState)) ∧
        finiteObservationTrace (flattenObservation f).run (some nextState) (xs ++ rest)
      refine ⟨(outerState, inner, next), ?_, ?_⟩
      · simp only [flattenCurrentStep, hstep, finiteObservation_ok_bind, finiteObservation_pure]
      · apply finiteObservationStep_to_trace
        rw [flattenCurrentStep_state]
        exact ih

/-- Flatten converts a finite outer trace and finite inner traces to one trace. -/
theorem flattenOuterTrace {OI I α O S : Type}
    [AsObservation OI I O] [AsObservation I α S]
    (f : Flatten OI) {st : Option O} {inners : List I}
    (houter : finiteObservationTrace (AsObservation.view f.it).run st inners) :
    ∀ (rows : List (List α)),
      finiteRelatedLists (fun inner row => finiteObservationTrace (AsObservation.view inner).run none row)
        inners rows →
      finiteObservationStep (flattenObservation f).run
        (observe (flattenOuter
          (fun i s => action ((AsObservation.view i).run s))
          (fun i s => action ((AsObservation.view i).run s)) f st)) rows.flatten := by
  induction houter with
  | stop hstop =>
      intro rows hrows
      cases hrows
      exact flattenOuterStep_empty f _ hstop
  | @step st inner next inners hstep htail ih =>
      intro rows hrows
      cases hrows with
      | cons hinner hrest =>
          rw [flattenOuterStep_nonempty f st inner next hstep]
          exact flattenInnerTrace f next inner _ (ih _ hrest) hinner

/-- A finite trace of each mapped list gives the corresponding list of rows. -/
theorem listIteratorFiniteTrace {α : Type} (xs : List α) :
    finiteObservationTrace (AsObservation.view (listIterator xs)).run none xs := by
  apply finiteObservationTrace_of_reads
  change Round5.observe (fun st => observeJl ((listIterator xs).run st))
    (xs.length + 1) none = .ok xs
  rw [observeLiftJl, group5_observe_list_initial, List.take_of_length_le (Nat.le_succ _)]
  rfl

theorem flattenFiniteTraces {OI I α O S : Type}
    [AsObservation OI I O] [AsObservation I α S]
    (f : Flatten OI) (inners : List I) (rows : List (List α))
    (houter : finiteObservationTrace (AsObservation.view f.it).run none inners)
    (hrows : finiteRelatedLists
      (fun inner row => finiteObservationTrace (AsObservation.view inner).run none row) inners rows) :
    emitsExactly (flattenObservation f) rows.flatten := by
  have hstep := flattenOuterTrace f houter rows hrows
  have htrace : finiteObservationTrace (flattenObservation f).run none rows.flatten :=
    finiteObservationStep_to_trace _ none rows.flatten hstep
  unfold emitsExactly
  rw [group5_collect_eq_observe]
  exact finiteObservationTrace_reads _ htrace

/-- Finite lists of finite lists are flattened without reordering any value. -/
theorem IteratorsFlatten_proven : JuliaLean.Proofs.base.iterators.FlattenCorrect := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α rows
    apply flattenFiniteTraces
      (flattenModel (listIterator (rows.map listIterator))) (rows.map listIterator) rows
      (listIteratorFiniteTrace _)
    induction rows with
    | nil => exact .nil
    | cons row rows ih => exact .cons (listIteratorFiniteTrace row) ih
  · exact flattenStartEmpty
  · exact flattenStartNonempty
  · exact flattenInnerNonempty

/-- Finite cycle observations flatten finite repetition of the same list iterator. -/
theorem finiteCycleEmits {α : Type} (xs : List α) (n : JInt64) (hn : 0 ≤ n.val) :
    emitsExactly (finiteCycleListObservation xs n.val.toNat)
      (List.replicate n.val.toNat xs).flatten := by
  have hrepeated := (IteratorsRepeatedN_proven.1 (listIterator xs) n hn)
  obtain ⟨repeated, _, hemits, _⟩ := hrepeated
  have houter : finiteObservationTrace
      (AsObservation.view (cycleOuterObservation xs n.val.toNat)).run none
      (List.replicate n.val.toNat (listIterator xs)) := by
    apply finiteObservationTrace_of_reads
    have hread := group5_collect_eq_observe (cycleOuterObservation xs n.val.toNat)
      ((List.replicate n.val.toNat (listIterator xs)).length + 1) none
    exact hread.symm.trans hemits
  apply flattenFiniteTraces (flattenModel (cycleOuterObservation xs n.val.toNat))
    (List.replicate n.val.toNat (listIterator xs)) (List.replicate n.val.toNat xs) houter
  induction n.val.toNat with
  | zero => exact .nil
  | succ k ih => exact .cons (listIteratorFiniteTrace xs) ih

theorem IteratorsCycleN_proven : JuliaLean.Proofs.base.iterators.CycleNCorrect := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro α xs n hn
    exact ⟨_, cycleConstructorNonnegative (listIterator xs) n hn, finiteCycleEmits xs n hn⟩
  · exact cycleConstructorNonnegative
  · exact cycleFiniteRounds
  · exact cycleConstructorNegative
  · exact cycleConstructorOutOfRange


/-- Homogeneous list-product calls, with exactly the conversions used by the property. -/
def listProductCalls (α : Type) :
    ProductCalls Jl (fun _ : IteratorModel α Nat => Unit) (fun _ => α)
      (fun _ => α) (fun _ => Nat) where
  run i _ st := i.run st
  done i _ st := i.isdone st
  convertStart _ _ x := pure x
  convertState _ _ x := pure x

abbrev listProductStates (α : Type) (rows : List (List α)) :=
  ProductStates (fun _ : IteratorModel α Nat => α) (fun _ => Nat) (rows.map listIterator)

def listProductCurrent {α : Type} {rows : List (List α)}
    (states : listProductStates α rows) : List α := productValueList (productValues states)

/-- Remaining Cartesian rows after an odometer state has been returned. -/
def listProductRemaining {α : Type} :
    (rows : List (List α)) → listProductStates α rows → List (List α)
  | [], .nil => []
  | xs :: rows, .cons (_, index) states =>
      (xs.drop index).map (fun x => x :: listProductCurrent states) ++
        (listProductRemaining rows states).flatMap (fun tail => xs.map (fun x => x :: tail))

/-- The pure odometer update on the same stored values and indices. -/
def listProductNext {α : Type} :
    (rows : List (List α)) → listProductStates α rows → Option (listProductStates α rows)
  | [], .nil => none
  | xs :: rows, .cons (_, index) states =>
      match xs.drop index with
      | x :: _ => some (.cons (x, index + 1) states)
      | [] =>
          match listProductNext rows states, xs with
          | some next, x :: _ => some (.cons (x, 1) next)
          | _, _ => none

theorem listProductRemaining_cons {α : Type} (xs : List α) (rows : List (List α))
    (value : α) (index : Nat) (states : listProductStates α rows) :
    listProductRemaining (xs :: rows) (.cons (value, index) states) =
      (xs.drop index).map (fun x => x :: listProductCurrent states) ++
        (listProductRemaining rows states).flatMap (fun tail => xs.map (fun x => x :: tail)) := rfl

theorem listProductNext_cons {α : Type} (xs : List α) (rows : List (List α))
    (value : α) (index : Nat) (states : listProductStates α rows) :
    listProductNext (xs :: rows) (.cons (value, index) states) =
      match xs.drop index with
      | x :: _ => some (.cons (x, index + 1) states)
      | [] => match listProductNext rows states, xs with
        | some next, x :: _ => some (.cons (x, 1) next)
        | _, _ => none := rfl

/-- The Cartesian suffix is either exhausted or begins with the next odometer state. -/
theorem listProductNext_spec {α : Type} :
    ∀ (rows : List (List α)) (states : listProductStates α rows),
      match listProductNext rows states with
      | none => listProductRemaining rows states = []
      | some next => listProductRemaining rows states =
          listProductCurrent next :: listProductRemaining rows next := by
  intro rows
  induction rows with
  | nil => intro states; cases states; rfl
  | cons xs rows ih =>
      intro states
      cases states with
      | cons pair states =>
          rcases pair with ⟨value, index⟩
          rw [listProductNext_cons]
          cases hd : xs.drop index with
          | cons x tail =>
              have hnext : xs.drop (index + 1) = tail := by
                rw [← List.drop_drop, hd]
                rfl
              simp only [listProductRemaining_cons, hd, hnext,
                List.map_cons, List.cons_append, listProductCurrent, productValues, productValueList]
          | nil =>
              cases hn : listProductNext rows states with
              | none =>
                  have hi : listProductRemaining rows states = [] := by
                    simpa only [hn] using ih states
                  simp only [listProductRemaining_cons, hd,
                    List.map_nil, List.nil_append, hi, List.flatMap_nil]
              | some next =>
                  have hi : listProductRemaining rows states =
                      listProductCurrent next :: listProductRemaining rows next := by
                    simpa only [hn] using ih states
                  cases xs with
                  | nil =>
                      simp only [listProductRemaining_cons, List.drop_nil,
                        List.map_nil, List.nil_append]
                      exact List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
                  | cons x tail =>
                      simp only [listProductRemaining_cons, hd,
                        List.map_nil, List.nil_append, hi, List.flatMap_cons,
                        List.map_cons, List.cons_append, List.drop_succ_cons,
                        List.drop_zero, listProductCurrent, productValues, productValueList]

/-- Initial product states for a list of nonempty factors. -/
def listProductInitial {α : Type} :
    (rows : List (List α)) → (∀ xs ∈ rows, xs ≠ []) → listProductStates α rows
  | [], _ => .nil
  | [] :: _, h => False.elim (h [] (List.mem_cons_self ..) rfl)
  | (x :: xs) :: rows, h => .cons (x, 1)
      (listProductInitial rows (fun ys hy => h ys (List.mem_cons_of_mem _ hy)))

theorem listProductInitial_spec {α : Type} :
    ∀ (rows : List (List α)) (h : ∀ xs ∈ rows, xs ≠ []),
      r6CartesianRows rows = listProductCurrent (listProductInitial rows h) ::
        listProductRemaining rows (listProductInitial rows h) := by
  intro rows
  induction rows with
  | nil => intro h; rfl
  | cons xs rows ih =>
      intro h
      cases xs with
      | nil => exact False.elim (h [] (List.mem_cons_self ..) rfl)
      | cons x xs =>
          have hrest : ∀ ys ∈ rows, ys ≠ [] := fun ys hy => h ys (List.mem_cons_of_mem _ hy)
          rw [r6CartesianRows, ih hrest]
          simp only [listProductInitial, listProductRemaining_cons, List.flatMap_cons,
            List.map_cons, List.cons_append, listProductCurrent, productValues,
            productValueList, List.drop_succ_cons, List.drop_zero]


def listProductObservation {α : Type} (rows : List (List α)) :=
  productObservation (productModel (rows.map listIterator))
    (fun item state => item.isdone state) (fun item state => item.run state)
    (fun _ => α) (fun _ value _ => pure value)

theorem listDoneNoneNonempty {α : Type} (xs : List α) (h : xs ≠ []) :
    (listIterator xs).isdone none = .ok (some false) := by
  cases xs with
  | nil => contradiction
  | cons x xs => rfl

theorem listProductDone_cons {α : Type} (xs : List α) (rows : List (List α)) :
    productIsdoneTyped (listProductCalls α)
      (productTupleOfList ((xs :: rows).map listIterator)) = (do
        let d ← (listIterator xs).isdone none
        if d = some true then pure d
        else pure (boolOrMissing d (← productIsdoneTyped (listProductCalls α)
          (productTupleOfList (rows.map listIterator))))) := rfl

theorem listProductPisdone_cons {α : Type} (xs : List α) (rows : List (List α))
    (pair : α × Nat) (states : listProductStates α rows) :
    pisdoneTyped (listProductCalls α)
      (productTupleOfList ((xs :: rows).map listIterator)) (.cons pair states) = (do
        let d ← (listIterator xs).isdone (some pair.2)
        if d != some true then pure d
        else do
          let d ← (listIterator xs).isdone none
          if d != some true then pure d
          else (pisdoneTyped (listProductCalls α)
            (productTupleOfList (rows.map listIterator)) states)) := rfl

theorem listProductStart_cons {α : Type} (xs : List α) (rows : List (List α)) :
    piterateTyped (listProductCalls α)
      (productTupleOfList ((xs :: rows).map listIterator)) = (do
        match ← (listProductCalls α).run (listIterator xs) () none with
        | none => pure none
        | some (x, st) =>
            match ← piterateTyped (listProductCalls α)
              (productTupleOfList (rows.map listIterator)) with
            | none => pure none
            | some rest => pure (some (.cons
                (← (listProductCalls α).convertStart (listIterator xs) () x, st) rest))) := by
  change piterateTyped (listProductCalls α)
    (.cons () (productTupleOfList (rows.map listIterator))) = _
  rw [piterateTyped.eq_2]
  apply congrArg (fun cont : Option (α × Nat) → Jl (Option (listProductStates α (xs :: rows))) =>
    (listProductCalls α).run (listIterator xs) () none >>= cont)
  funext first
  cases first with
  | none => rfl
  | some pair =>
      rcases pair with ⟨x, st⟩
      apply congrArg (fun cont : Option (listProductStates α rows) →
          Jl (Option (listProductStates α (xs :: rows))) =>
        piterateTyped (listProductCalls α) (productTupleOfList (rows.map listIterator)) >>= cont)
      funext rest
      cases rest <;> rfl

theorem listProductNextTyped_cons {α : Type} (xs : List α) (rows : List (List α))
    (pair : α × Nat) (states : listProductStates α rows) :
    piterate1Typed (listProductCalls α)
      (productTupleOfList ((xs :: rows).map listIterator)) (.cons pair states) = (do
        match ← (listProductCalls α).run (listIterator xs) () (some pair.2) with
        | some (x, st) => pure (some (.cons
            (← (listProductCalls α).convertState (listIterator xs) pair x, st) states))
        | none =>
            if (← (listProductCalls α).done (listIterator xs) () none) = some true then pure none
            else
              match ← piterate1Typed (listProductCalls α)
                (productTupleOfList (rows.map listIterator)) states with
              | none => pure none
              | some rest =>
                  match ← (listProductCalls α).run (listIterator xs) () none with
                  | none => pure none
                  | some (x, st) => pure (some (.cons
                      (← (listProductCalls α).convertState (listIterator xs) pair x, st) rest))) := by
  change piterate1Typed (listProductCalls α)
    (.cons () (productTupleOfList (rows.map listIterator))) (.cons pair states) = _
  rw [piterate1Typed.eq_2]
  apply congrArg (fun cont : Option (α × Nat) → Jl (Option (listProductStates α (xs :: rows))) =>
    (listProductCalls α).run (listIterator xs) () (some pair.2) >>= cont)
  funext first
  cases first with
  | some pair' => cases pair'; rfl
  | none =>
      apply congrArg (fun cont : Option Bool → Jl (Option (listProductStates α (xs :: rows))) =>
        (listProductCalls α).done (listIterator xs) () none >>= cont)
      funext done
      by_cases hd : done = some true
      · simp only [hd, ↓reduceIte]
      · simp only [hd, ↓reduceIte]
        apply congrArg (fun cont : Option (listProductStates α rows) →
            Jl (Option (listProductStates α (xs :: rows))) =>
          piterate1Typed (listProductCalls α)
            (productTupleOfList (rows.map listIterator)) states >>= cont)
        funext rest
        cases rest with
        | none => rfl
        | some rest =>
            apply congrArg (fun cont : Option (α × Nat) →
                Jl (Option (listProductStates α (xs :: rows))) =>
              (listProductCalls α).run (listIterator xs) () none >>= cont)
            funext first
            cases first with
            | none => rfl
            | some pair' => cases pair'; rfl

theorem listProductConvertStart {α : Type} (itr : IteratorModel α Nat) (x : α) :
    (listProductCalls α).convertStart itr () x = .ok x := rfl

theorem listProductConvertState {α : Type} (itr : IteratorModel α Nat) (pair : α × Nat) (x : α) :
    (listProductCalls α).convertState itr pair x = .ok x := rfl

theorem listProductRunCallback {α : Type} (itr : IteratorModel α Nat) (st : Option Nat) :
    (listProductCalls α).run itr () st = itr.run st := rfl

theorem listProductDoneCallback {α : Type} (itr : IteratorModel α Nat) (st : Option Nat) :
    (listProductCalls α).done itr () st = itr.isdone st := rfl

theorem listProductDoneInitial {α : Type} (rows : List (List α)) :
    productIsdoneTyped (listProductCalls α) (productTupleOfList (rows.map listIterator)) =
      .ok (some (rows.any List.isEmpty)) := by
  induction rows with
  | nil => rfl
  | cons xs rows ih =>
      cases xs with
      | nil => rfl
      | cons x xs =>
          simp only [listProductDone_cons, listDoneNoneNonempty _ (List.cons_ne_nil _ _),
            ok_bind, ih, List.any_cons, List.isEmpty_cons, Bool.false_or,
            pure_jl]
          cases rows.any List.isEmpty <;> rfl

theorem listProductPisdone {α : Type} (x : α) (xs : List α)
    (rows : List (List α)) (pair : α × Nat) (states : listProductStates α rows) :
    pisdoneTyped (listProductCalls α)
      (productTupleOfList (((x :: xs) :: rows).map listIterator)) (.cons pair states) =
        .ok (some false) := by
  cases pair with
  | mk value index =>
      by_cases hd : (x :: xs).length ≤ index
      · simp only [listProductPisdone_cons,
          listIterator_isdone_some, hd, decide_true, ok_bind,
          listDoneNoneNonempty _ (List.cons_ne_nil _ _), pure_jl]
        rfl
      · simp only [listProductPisdone_cons,
          listIterator_isdone_some, hd, decide_false, ok_bind, pure_jl]
        rfl

theorem listProductStart_eq {α : Type} :
    ∀ (rows : List (List α)) (h : ∀ xs ∈ rows, xs ≠ []),
      piterateTyped (listProductCalls α) (productTupleOfList (rows.map listIterator)) =
        .ok (some (listProductInitial rows h)) := by
  intro rows
  induction rows with
  | nil => intro h; rfl
  | cons xs rows ih =>
      intro h
      cases xs with
      | nil => exact False.elim (h [] (List.mem_cons_self ..) rfl)
      | cons x xs =>
          simp only [listProductStart_cons, listProductConvertStart, listProductRunCallback,
            listIterator_run_none, listIterator_run_some, List.drop_zero, ok_bind,
            ih (fun ys hy => h ys (List.mem_cons_of_mem _ hy)),
            pure_jl, listProductInitial]

theorem listProductNext_eq {α : Type} :
    ∀ (rows : List (List α)) (h : ∀ xs ∈ rows, xs ≠ [])
      (states : listProductStates α rows),
      piterate1Typed (listProductCalls α) (productTupleOfList (rows.map listIterator)) states =
        .ok (listProductNext rows states) := by
  intro rows
  induction rows with
  | nil => intro h states; cases states; rfl
  | cons xs rows ih =>
      intro h states
      cases xs with
      | nil => exact False.elim (h [] (List.mem_cons_self ..) rfl)
      | cons x xs =>
          cases states with
          | cons pair states =>
              rcases pair with ⟨value, index⟩
              have hrows : ∀ ys ∈ rows, ys ≠ [] :=
                fun ys hy => h ys (List.mem_cons_of_mem _ hy)
              cases hd : (x :: xs).drop index with
              | cons y tail =>
                  simp only [listProductNextTyped_cons, listProductConvertState, listProductRunCallback, listProductDoneCallback,
                    listIterator_run_some, hd, ok_bind, pure_jl,
                    listProductNext_cons]
              | nil =>
                  simp only [listProductNextTyped_cons, listProductConvertState, listProductRunCallback, listProductDoneCallback,
                    listIterator_run_some, hd, ok_bind,
                    listDoneNoneNonempty _ (List.cons_ne_nil _ _), pure_jl,
                    ih hrows states, listProductNext_cons]
                  cases listProductNext rows states <;> rfl

theorem listProductRunInitial {α : Type} (rows : List (List α))
    (h : ∀ xs ∈ rows, xs ≠ []) :
    (listProductObservation rows).run none =
      .ok (some (listProductCurrent (listProductInitial rows h), listProductInitial rows h)) := by
  have hany : rows.any List.isEmpty = false := by
    apply List.any_eq_false.mpr
    intro row hrow
    cases row with
    | nil => exact False.elim (h [] hrow rfl)
    | cons x xs => exact Bool.noConfusion
  cases rows with
  | nil => rfl
  | cons xs rows =>
      change observeJl (((do
        let next ← (do
          if (← productIsdoneTyped (listProductCalls α)
              (productTupleOfList ((xs :: rows).map listIterator))) = some true then pure none
          else (piterateTyped (listProductCalls α)
              (productTupleOfList ((xs :: rows).map listIterator))))
        pure (next.map fun st => (productValues st, st))) :
          Jl (Option (ProductValues (fun _ : IteratorModel α Nat => α)
            ((xs :: rows).map listIterator) × listProductStates α (xs :: rows)))).map
          (fun y => y.map fun (vs, st) => (productValueList vs, st))) = _
      rw [listProductDoneInitial, hany]
      simp only [ok_bind, listProductStart_eq _ h, pure_jl]
      rfl

theorem listProductRunState {α : Type} (rows : List (List α))
    (h : ∀ xs ∈ rows, xs ≠ []) (states : listProductStates α rows) :
    (listProductObservation rows).run (some states) =
      .ok ((listProductNext rows states).map fun next => (listProductCurrent next, next)) := by
  cases rows with
  | nil => cases states; rfl
  | cons xs rows =>
      cases xs with
      | nil => exact False.elim (h [] (List.mem_cons_self ..) rfl)
      | cons x xs =>
          cases states with
          | cons pair states =>
              change observeJl (((do
                let next ← (do
                  if (← pisdoneTyped (listProductCalls α)
                      (productTupleOfList (((x :: xs) :: rows).map listIterator))
                      (.cons pair states)) = some true then pure none
                  else (piterate1Typed (listProductCalls α)
                      (productTupleOfList (((x :: xs) :: rows).map listIterator))
                      (.cons pair states)))
                pure (next.map fun st => (productValues st, st))) :
                  Jl (Option (ProductValues (fun _ : IteratorModel α Nat => α)
                    (((x :: xs) :: rows).map listIterator) ×
                    listProductStates α ((x :: xs) :: rows)))).map
                  (fun y => y.map fun (vs, st) => (productValueList vs, st))) = _
              rw [listProductPisdone]
              simp only [ok_bind, listProductNext_eq _ h, pure_jl]
              cases listProductNext ((x :: xs) :: rows) (.cons pair states) <;> rfl

theorem listProductStateReads {α : Type} (rows : List (List α))
    (h : ∀ xs ∈ rows, xs ≠ []) :
    ∀ depth (states : listProductStates α rows),
      observeRun (listProductObservation rows).run depth (some states) =
        .ok ((listProductRemaining rows states).take depth) := by
  intro depth
  induction depth with
  | zero => intro states; rfl
  | succ depth ih =>
      intro states
      rw [observeRun, listProductRunState rows h states]
      cases hn : listProductNext rows states with
      | none =>
          have hspec : listProductRemaining rows states = [] := by
            simpa only [hn] using listProductNext_spec rows states
          rw [hspec]
          rfl
      | some next =>
          have hspec : listProductRemaining rows states =
              listProductCurrent next :: listProductRemaining rows next := by
            simpa only [hn] using listProductNext_spec rows states
          change (do pure (listProductCurrent next ::
            (← observeRun (listProductObservation rows).run depth (some next)))) = _
          rw [ih next, hspec]
          rfl

theorem listProductCartesianEmpty {α : Type} (rows : List (List α))
    (hempty : [] ∈ rows) : r6CartesianRows rows = [] := by
  induction rows with
  | nil => cases hempty
  | cons xs rows ih =>
      simp only [List.mem_cons] at hempty
      rcases hempty with hxs | hrest
      · subst xs
        simp only [r6CartesianRows, List.map_nil]
        exact List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
      · rw [r6CartesianRows, ih hrest]
        rfl

theorem listProductInitialReads {α : Type} (rows : List (List α)) (depth : Nat) :
    observeRun (listProductObservation rows).run depth none =
      .ok ((r6CartesianRows rows).take depth) := by
  classical
  by_cases hempty : [] ∈ rows
  · have hany : rows.any List.isEmpty = true :=
      List.any_eq_true.mpr ⟨[], hempty, rfl⟩
    have hnone : (listProductObservation rows).run none = .ok none := by
      cases rows with
      | nil => cases hempty
      | cons xs rows =>
          change observeJl (((do
            let next ← (do
              if (← productIsdoneTyped (listProductCalls α)
                  (productTupleOfList ((xs :: rows).map listIterator))) = some true then pure none
              else (piterateTyped (listProductCalls α)
                  (productTupleOfList ((xs :: rows).map listIterator))))
            pure (next.map fun st => (productValues st, st))) :
              Jl (Option (ProductValues (fun _ : IteratorModel α Nat => α)
                ((xs :: rows).map listIterator) × listProductStates α (xs :: rows)))).map
              (fun y => y.map fun (vs, st) => (productValueList vs, st))) = _
          rw [listProductDoneInitial, hany]
          rfl
    rw [listProductCartesianEmpty rows hempty]
    cases depth with
    | zero => rfl
    | succ depth => rw [observeRun, hnone]; rfl
  · have hnonempty : ∀ xs ∈ rows, xs ≠ [] := by
      intro xs hxs heq
      subst xs
      exact hempty hxs
    cases depth with
    | zero => rfl
    | succ depth =>
        rw [observeRun, listProductRunInitial rows hnonempty]
        change (do pure (listProductCurrent (listProductInitial rows hnonempty) ::
          (← observeRun (listProductObservation rows).run depth
            (some (listProductInitial rows hnonempty))))) = _
        rw [listProductStateReads rows hnonempty,
          listProductInitial_spec rows hnonempty]
        rfl

theorem IteratorsProduct_proven : JuliaLean.Proofs.base.iterators.ProductCorrect := by
  refine ⟨?_, productEmptyClauses.1, productEmptyClauses.2⟩
  intro α factors depth _
  exact listProductInitialReads factors depth


/-- A count outside the native domain is wrapped by the frozen direct-wrapper property. -/
theorem partitionWrappedCountLength :
    (partitionVectorObservation
      ⟨([1] : List Int), JInt.lit .i64 (Int.ofNat (2 ^ 63))⟩).length = .ok 0 := by
  decide

/-- The public constructor rejects that same mathematical count instead of wrapping it. -/
theorem partitionPublicCountRejects :
    partitionNativeConstruct ([1] : List Int) (2 ^ 63)
      (fun xs k => sourceMethod1447 xs (JInt.lit .i64 (Int.ofNat k))) =
        .error (.inexactError "Int64") := by
  rfl

/-- A pure generator maps a complete finite trace without changing its states. -/
theorem finiteObservationTrace_generator {I α β S : Type} [AsObservation I α S]
    (itr : I) (f : α → β) {st : Option S} {xs : List α}
    (h : finiteObservationTrace (AsObservation.view itr).run st xs) :
    finiteObservationTrace (generatorObservation ⟨f, itr⟩).run st (xs.map f) := by
  induction h with
  | stop hstop =>
      apply finiteObservationTrace.stop
      simp only [generatorObservation, JuliaLean.base.generator.iterateGenerator, hstop,
        finiteObservation_ok_bind, finiteObservation_pure]
  | @step st x next xs hstep htail ih =>
      apply finiteObservationTrace.step (next := next)
      · simp only [generatorObservation, JuliaLean.base.generator.iterateGenerator, hstep,
          finiteObservation_ok_bind, finiteObservation_pure]
      · exact ih

/-- The first observation of a terminating trace has the expected head or bounds error. -/
theorem firstObservation_trace {I α S : Type} [AsObservation I α S]
    (itr : I) (xs : List α)
    (h : finiteObservationTrace (AsObservation.view itr).run none xs) :
    firstObservation itr = observeJl ((xs.head?).elim (.error .boundsError) pure) := by
  cases h with
  | stop hstop =>
      simp only [firstObservation, hstop, firstIterModel, pure_jl, ok_bind,
        finiteObservation_ok_bind,
        List.head?_nil, Option.elim_none]
  | step hstep htail =>
      simp only [firstObservation, hstep, firstIterModel, pure_jl, ok_bind,
        finiteObservation_ok_bind,
        List.head?_cons, Option.elim_some]


end JuliaLean.ChatGPT.Batch4.Group5

/- Supporting block: Queue31_33 -/
namespace JuliaLean.ChatGPT.Batch4.Group5
open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators

/-- Reversing a flatten reverses both the outer row order and every inner row. -/
theorem reverseFlattenEmits {α : Type} (rows : List (List α)) :
    emitsExactly (reverseFlattenObservation rows) rows.flatten.reverse := by
  have hreverse : finiteObservationTrace
      (AsObservation.view (reverseListAsIterator rows)).run none rows.reverse := by
    apply finiteObservationTrace_of_reads
    change Round5.observe (fun st => observeJl ((reverseListAsIterator rows).run st))
      (rows.reverse.length + 1) none = .ok rows.reverse
    rw [observeLiftJl]
    have h := group5_q43_reverse_emits rows
    unfold emitsExactly at h
    rw [group5_collect_eq_observe] at h
    change Round5.observe (reverseListAsIterator rows).run (rows.reverse.length + 1) none = .ok rows.reverse at h
    rw [h]
    rfl
  have houter := finiteObservationTrace_generator (reverseListAsIterator rows)
    reverseListAsIterator hreverse
  have hinners : finiteRelatedLists
      (fun inner row => finiteObservationTrace (AsObservation.view inner).run none row)
      (rows.reverse.map reverseListAsIterator) (rows.reverse.map List.reverse) := by
    induction rows.reverse with
    | nil => exact .nil
    | cons row rest ih =>
        refine .cons ?_ ih
        apply finiteObservationTrace_of_reads
        change Round5.observe (fun st => observeJl ((reverseListAsIterator row).run st))
          (row.reverse.length + 1) none = .ok row.reverse
        rw [observeLiftJl]
        have h := group5_q43_reverse_emits row
        unfold emitsExactly at h
        rw [group5_collect_eq_observe] at h
        change Round5.observe (reverseListAsIterator row).run (row.reverse.length + 1) none = .ok row.reverse at h
        rw [h]
        rfl
  have hflat := flattenFiniteTraces
    (flattenModel (generatorObservation ⟨reverseListAsIterator, reverseListAsIterator rows⟩))
    (rows.reverse.map reverseListAsIterator) (rows.reverse.map List.reverse) houter hinners
  rw [flatten_reverse_map_reverse] at hflat
  exact hflat

/-- Mapping valid zero-based positions back through getD recovers the original list. -/
theorem mapRangeGetD {α : Type} (items : List α) (fallback : α) :
    (List.range items.length).map (fun k => items.getD k fallback) = items := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range, List.getD,
      List.getElem?_eq_getElem hj, Option.getD_some]

/-- Finite flatten metadata, reversal, and last all agree with the flattened values. -/
theorem IteratorscovFlattenMethods_proven : JuliaLean.Proofs.base.iterators.FlattenMethodSemantics := by
  refine ⟨IteratorsFlatten_proven, IteratorsFlattenTupleLength_proven, ?_,
    flatten_iteratorsize_iff, ?_, ?_, ?_, ?_⟩
  · intro α rows
    have hemits := reverseFlattenEmits rows
    refine ⟨hemits, ?_⟩
    have htrace : finiteObservationTrace
        (AsObservation.view (reverseFlattenObservation rows)).run none rows.flatten.reverse := by
      apply finiteObservationTrace_of_reads
      have hread := group5_collect_eq_observe (reverseFlattenObservation rows)
        (rows.flatten.reverse.length + 1) none
      exact hread.symm.trans hemits
    have hfirst := firstObservation_trace (reverseFlattenObservation rows) rows.flatten.reverse htrace
    rw [head_reverse_eq_listLastModel] at hfirst
    unfold lastFlattenObservation
    rw [hfirst]
    cases listLastModel rows.flatten <;>
      simp only [observeJl, observe, liftJl, lastFlatten, sourceMethod1379,
        pure_jl, ok_bind, Bind.bind]
    all_goals rfl
  · intro sz kind slurp
    rfl
  · intro α xs
    simp only [sourceMethod1332, flattenLengthBottom, flattenTupleLength,
      flattenLengthNumber, flattenModel, listIterator_length, checkedMulNatI64,
      Nat.zero_mul, sourceMethod1330, sourceMethod1325, flattenEmptyLength,
      pure_jl, ok_bind]
    all_goals decide
  · intro I outerTag innerTag it
    cases outerTag <;> cases innerTag <;>
      simp only [flattenIteratorEltype, flattenHasEltype, flattenUnknownEltype]
    all_goals decide
  · intro I elem nothing missing items it
    refine ⟨rfl, ?_, rfl⟩
    simp only [flattenTupleEltype, id_eq, Nat.add_sub_cancel,
      mapRangeGetD items .bottom]

/-- Nonpositive partition counts are rejected before conversion and construction. -/
theorem partitionRejectsNonpositive {I C : Type} (c : I) (n : Int)
    (construct : I → Nat → PartitionIterator C) (hn : n < 1) :
    partitionNativeConstruct c n construct =
      .error (.argumentError s!"cannot create partitions of length {n}") := by
  simp only [partitionNativeConstruct, partition, hn, decide_true,
    pure_jl, ok_bind, ↓reduceIte]
  rfl

theorem partitionArrayConstructs {A V : Type} (vec : A → V) (a : A)
    (n : JInt64) (hn : 1 ≤ n.val) :
    partitionNativeConstruct a n.val
      (fun x k => sourceMethod1447 (vec x) (JInt.lit .i64 (Int.ofNat k))) =
      .ok ⟨vec a, JInt.lit .i64 (Int.ofNat n.val.toNat)⟩ ∧
    partitionArray (m := Jl) (fun x => pure (vec x)) a n = .ok ⟨vec a, n⟩ := by
  have hnot : ¬ n.val < 1 := by omega
  simp only [partitionNativeConstruct, partition, hnot, decide_false,
    pure_jl, ok_bind, ↓reduceIte, jint_convert_i64_self, sourceMethod1447, partitionArray]
  exact ⟨rfl, rfl⟩

/-- The partition size and element-type clauses are independent of count-domain defects. -/
theorem partitionTraits {T : Type} (sz : IteratorSizeTag) (it : PartitionIterator T) :
    (sourceMethod1461 sz it = .hasLength ↔ (sz = .hasLength ∨ ∃ d, sz = .hasShape d)) ∧
    ((∀ d, sz ≠ .hasShape d) → sourceMethod1461 sz it = sz) ∧
    sourceMethod1455 .hasEltype it = .hasEltype ∧
    sourceMethod1456 it = .eltypeUnknown ∧
    sourceMethod1457 .hasEltype it = .hasEltype :=
  ⟨(partition_iteratorsize_iff sz it).1, (partition_iteratorsize_iff sz it).2, rfl, rfl, rfl⟩

/-- The vector constructor and declared view element types are forwarded exactly. -/
theorem partitionArrayTypes {A V : Type} (vec : A → V) (a : A) (v : V)
    (n : JInt64) (eltype : Type) :
    partitionArray (m := Jl) (fun x => pure (vec x)) a n = .ok ⟨vec a, n⟩ ∧
    sourceMethod1447 v n = ⟨v, n⟩ ∧
    sourceMethod1449 (Elem := Type) (fun _ => eltype) (sourceMethod1447 v n) = .vector eltype ∧
    sourceMethod1451 (Elem := Type) (fun _ => eltype) (sourceMethod1447 v n) = .abstractVector eltype ∧
    sourceMethod1453 (Elem := Type) (fun _ => eltype) (sourceMethod1447 v n) =
      .subArray eltype 1 v .unitRangeInt true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩


theorem collectEqObserveRun {I α S : Type} {m : Type → Type}
    [Monad m] [CollectRun I α S m] (itr : I) (depth : Nat) (state : Option S) :
    JuliaLean.Proofs.base.iterators.collectPrefix itr depth state = observeRun (CollectRun.run itr) depth state := by
  induction depth generalizing state with
  | zero => rfl
  | succ depth ih =>
      simp only [JuliaLean.Proofs.base.iterators.collectPrefix, observeRun, ih]
      apply congrArg (fun cont : Option (α × S) → m (List α) =>
        CollectRun.run itr state >>= cont)
      funext next
      cases next with
      | none => rfl
      | some pair => cases pair; rfl

/-- Cartesian enumeration of two factors has its first factor changing fastest. -/
theorem cartesianTwoLists {α : Type} (xs ys : List α) :
    r6CartesianRows [xs, ys] = ys.flatMap (fun y => xs.map (fun x => [x, y])) := by
  simp only [r6CartesianRows, List.flatMap_cons, List.flatMap_nil,
    List.map_nil, List.append_nil, List.flatMap_map]

/-- Componentwise reversal reverses the complete two-factor enumeration. -/
theorem cartesianTwoReverse {α : Type} (xs ys : List α) :
    r6CartesianRows [xs.reverse, ys.reverse] =
      (ys.flatMap (fun y => xs.map (fun x => [x, y]))).reverse := by
  rw [cartesianTwoLists, List.reverse_flatMap]
  apply congrArg (List.flatMap · ys.reverse)
  funext y
  exact List.map_reverse

/-- A nonempty list has a finite prefix followed by its last element. -/
theorem nonemptyListLastDecomp {α : Type} (xs : List α) (h : xs ≠ []) :
    ∃ before last, xs = before ++ [last] := by
  rcases List.eq_nil_or_concat xs with hnil | ⟨before, last, heq⟩
  · exact False.elim (h hnil)
  · exact ⟨before, last, by simpa only [List.concat_eq_append] using heq⟩

theorem productTwoLastNonempty {α : Type} (xs ys : List α)
    (hx : xs ≠ []) (hy : ys ≠ []) :
    productLastObservation listLastModel (productModel [xs, ys]) =
      listLastModel (ys.flatMap fun y => xs.map fun x => [x, y]) := by
  obtain ⟨xb, x, rfl⟩ := nonemptyListLastDecomp xs hx
  obtain ⟨yb, y, rfl⟩ := nonemptyListLastDecomp ys hy
  have hlast : listLastModel
      ((yb ++ [y]).flatMap fun v => (xb ++ [x]).map fun u => [u, v]) = .ok [x, y] := by
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.map_append, List.map_cons, List.map_nil, ← List.append_assoc]
    exact listLastModel_append_singleton _ _
  rw [hlast]
  simp only [productLastObservation, tupleLast, productModel, tupleOfList,
    tupleMetadata, listLastModel_append_singleton, pure_jl, ok_bind, tupleValueList]

theorem productTwoLastEmpty {α : Type} (xs ys : List α)
    (h : xs = [] ∨ ys = []) :
    productLastObservation listLastModel (productModel [xs, ys]) = .error .boundsError := by
  rcases h with rfl | rfl
  · rfl
  · cases hlast : listLastModel xs with
    | error e =>
        have heq := listLastModel_err xs e hlast
        subst e
        simp only [productLastObservation, tupleLast, productModel, tupleOfList,
          tupleMetadata, hlast, err_bind]
    | ok x =>
        simp only [productLastObservation, tupleLast, productModel, tupleOfList,
          tupleMetadata, hlast, listLastModel, ok_bind, err_bind]

/-- A nonempty tuple's computed element trait agrees with the fold of its fields. -/
theorem productEltypeFoldResult (tags : List IteratorEltypeTag) (hne : tags ≠ []) :
    ((if tags.any (fun tag => tag == .eltypeUnknown) then .ok .eltypeUnknown
      else match tags.getLast? with
        | some last => .ok last
        | none => .error .boundsError) : Jl IteratorEltypeTag) = .ok (productEltypeFold tags) := by
  induction tags with
  | nil => contradiction
  | cons tag tags ih =>
      cases tag with
      | eltypeUnknown => rfl
      | hasEltype =>
          cases tags with
          | nil => rfl
          | cons next tags =>
              change ((if (next :: tags).any (fun tag => tag == .eltypeUnknown) then
                .ok .eltypeUnknown else match (next :: tags).getLast? with
                  | some last => .ok last
                  | none => .error .boundsError) : Jl IteratorEltypeTag) =
                .ok (productEltypeFold (next :: tags))
              exact ih (List.cons_ne_nil _ _)

theorem productListEltype {α S : Type} (it : IteratorModel α S)
    (its : List (IteratorModel α S)) :
    productIteratorEltype (fun ts n => ts.getD (n - 1) it)
      (fun i : IteratorModel α S => i.iteratorEltype)
      (it :: its).length (productModel (it :: its)) =
      .ok (productEltypeFold ((it :: its).map fun i => i.iteratorEltype)) := by
  have hmap : (List.range (it :: its).length).map
      (fun k => ((it :: its).getD (k + 1 - 1) it).iteratorEltype) =
        (it :: its).map (fun i => i.iteratorEltype) := by
    simp only [Nat.add_sub_cancel]
    calc
      (List.range (it :: its).length).map
          (fun k => ((it :: its).getD k it).iteratorEltype) =
          ((List.range (it :: its).length).map (fun k => (it :: its).getD k it)).map
            (fun i => i.iteratorEltype) := by rw [List.map_map]; rfl
      _ = (it :: its).map (fun i => i.iteratorEltype) := by rw [mapRangeGetD]
  unfold productIteratorEltype
  change ((if ((List.range (it :: its).length).map
      (fun k => ((it :: its).getD (k + 1 - 1) it).iteratorEltype)).any
        (fun tag => tag == .eltypeUnknown) then .ok .eltypeUnknown
    else match ((List.range (it :: its).length).map
      (fun k => ((it :: its).getD (k + 1 - 1) it).iteratorEltype)).getLast? with
      | some last => .ok last
      | none => .error .boundsError) : Jl IteratorEltypeTag) = _
  rw [hmap]
  exact productEltypeFoldResult _ (List.cons_ne_nil _ _)

/-- Typed product initialization builds precisely the returned values and states. -/
theorem productStartExpected {I α β S : Type}
    (isdone : I → Option S → Jl (Option Bool))
    (iterate : I → Option S → Jl (Option (α × S)))
    (defaultEltype : I → Type) (typeassert : I → α → Type → Jl β)
    (value : I → α) (state : I → S) (converted : I → β) :
    ∀ (items : List I),
      (∀ i ∈ items, iterate i none = .ok (some (value i, state i)) ∧
        typeassert i (value i) (defaultEltype i) = .ok (converted i)) →
      piterateTyped
        (⟨(fun i _ st => iterate i st), (fun i _ st => isdone i st),
          (fun i _ x => typeassert i x (defaultEltype i)),
          (fun i _ x => typeassert i x β)⟩ :
          ProductCalls Jl (fun _ : I => Unit) (fun _ => α) (fun _ => β) (fun _ => S))
        (productTupleOfList items) = .ok (some (productExpectedStates items converted state)) := by
  intro items
  induction items with
  | nil => intro h; rfl
  | cons item items ih =>
      intro h
      have hitem := h item (List.mem_cons_self ..)
      have hrest := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
      simp only [productTupleOfList, piterateTyped, hitem.1, ok_bind, hrest,
        hitem.2, pure_jl, productExpectedStates]

theorem productExpectedValues {I V S : Type} (items : List I)
    (value : I → V) (state : I → S) :
    productValueList (productValues (productExpectedStates items value state)) = items.map value := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      simp only [productExpectedStates, productValues, productValueList, List.map_cons, ih]

/-- The Product initialization clause needs only its actual successful callbacks. -/
theorem productStartWhenLive {I α β S : Type}
    (isdone : I → Option S → Jl (Option Bool))
    (iterate : I → Option S → Jl (Option (α × S))) (p : ProductIterator (List I))
    (defaultEltype : I → Type) (typeassert : I → α → Type → Jl β)
    (value : I → α) (state : I → S) (converted : I → β)
    (hdone : (productObservation p isdone iterate defaultEltype typeassert).isdone none = .ok (some false))
    (h : ∀ i ∈ p.iterators, iterate i none = .ok (some (value i, state i)) ∧
      typeassert i (value i) (defaultEltype i) = .ok (converted i)) :
    (productObservation p isdone iterate defaultEltype typeassert).run none =
      .ok (some (p.iterators.map converted, productExpectedStates p.iterators converted state)) := by
  let ops : ProductCalls Jl (fun _ : I => Unit) (fun _ => α) (fun _ => β) (fun _ => S) :=
    ⟨(fun i _ st => iterate i st), (fun i _ st => isdone i st),
      (fun i _ x => typeassert i x (defaultEltype i)), (fun i _ x => typeassert i x β)⟩
  have hd : productIsdoneTyped ops (productTupleOfList p.iterators) = .ok (some false) := by
    change observeJl (productIsdoneTyped ops (productTupleOfList p.iterators)) = .ok (some false) at hdone
    cases hc : productIsdoneTyped ops (productTupleOfList p.iterators) with
    | error e =>
        simp only [hc, observeJl, observe, liftJl] at hdone
        cases hdone
    | ok result =>
        simp only [hc, observeJl, observe, liftJl, Observation.ok.injEq] at hdone
        rw [hdone]
  have hp := productStartExpected isdone iterate defaultEltype typeassert value state converted p.iterators h
  change piterateTyped ops (productTupleOfList p.iterators) =
    .ok (some (productExpectedStates p.iterators converted state)) at hp
  cases p with
  | mk items =>
      cases items with
      | nil => rfl
      | cons item items =>
          change observeJl (((do
            let next ← (do if (← productIsdoneTyped ops (productTupleOfList (item :: items))) = some true
              then pure none else piterateTyped ops (productTupleOfList (item :: items)))
            pure (next.map fun st => (productValues st, st))) :
              Jl (Option (ProductValues (fun _ : I => β) (item :: items) ×
                ProductStates (fun _ : I => β) (fun _ => S) (item :: items)))).map
              (fun y => y.map fun (values, st) => (productValueList values, st))) = _
          rw [hd]
          simp only [ok_bind, show (some false : Option Bool) ≠ some true by decide,
            ↓reduceIte, hp, pure_jl]
          change Observation.ok (some
            (productValueList (productValues (productExpectedStates (item :: items) converted state)),
              productExpectedStates (item :: items) converted state)) = _
          rw [productExpectedValues]

/-- Product iteration and metadata implement the frozen method contract. -/
theorem IteratorscovProductMethods_proven : JuliaLean.Proofs.base.iterators.ProductMethodSemantics := by
  refine ⟨IteratorsProduct_proven, rfl, productShapeFinite, productIelSpec_proven,
    ?_, ?_, ?_, ?_, productStartWhenLive⟩
  · intro α xs ys
    refine ⟨?_, productTwoLastEmpty xs ys, productTwoLastNonempty xs ys⟩
    have hrev : productReverseObservation (fun (l : List α) => pure l.reverse)
        (productModel [xs, ys]) = .ok (productModel [xs.reverse, ys.reverse]) := rfl
    rw [hrev]
    change JuliaLean.Proofs.base.iterators.collectPrefix (listProductObservation [xs.reverse, ys.reverse])
      (((ys.flatMap fun y => xs.map fun x => [x, y]).reverse).length + 1) none = _
    have hobs := listProductInitialReads [xs.reverse, ys.reverse]
      (((ys.flatMap fun y => xs.map fun x => [x, y]).reverse).length + 1)
    rw [cartesianTwoReverse, List.take_of_length_le (Nat.le_succ _)] at hobs
    rw [collectEqObserveRun]
    exact hobs
  · intro α xss
    refine ⟨sourceMethod1171_listIterators xss, sourceMethod1179_listIterators xss, ?_⟩
    simp only [sourceMethod1185, sourceMethod1177, sourceMethod1179_listIterators,
      productModel, ok_bind, pure_jl, List.length_map]
  · intro I a typeof sz
    exact ⟨rfl, rfl⟩
  · intro I α S s it its eltype tupleOrBottom items
    exact ⟨rfl, rfl, rfl, rfl, rfl, productListEltype it its, rfl, rfl⟩

end JuliaLean.ChatGPT.Batch4.Group5

/- Supporting block: Queue25_30 -/
namespace JuliaLean.ChatGPT.Batch4.Group5

open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators

theorem group5_plain_list_follows {α : Type} (xs : List α) : followsFrom (listIterator xs) none xs := by
  unfold followsFrom
  rw [group5_collect_eq_observe]
  change Round5.observe (listIterator xs).run (xs.length + 1) none = .ok xs
  rw [group5_observe_list_initial, List.take_of_length_le (Nat.le_succ _)]

theorem group5_collect_run_eq {α S : Type} (left right : IteratorModel α S)
    (hr : ∀ state, left.run state = right.run state) :
    ∀ depth state, JuliaLean.Proofs.base.iterators.collectPrefix left depth state =
      JuliaLean.Proofs.base.iterators.collectPrefix right depth state := by
  intro depth
  induction depth with
  | zero => intro state; rfl
  | succ depth ih =>
    intro state
    rw [collectPrefix_succ, collectPrefix_succ, hr]
    unfold collectAfterStep
    cases right.run state with
    | error error => rfl
    | ok step =>
      cases step with
      | none => rfl
      | some pair => simp only [ok_bind, ih]

theorem group5_snapshot_done {I VS Y : Type} (s : StatefulSnapshot I VS Y) :
    isdoneSnapshot s = .ok s.nextvalstate.isNone := by
  rfl

theorem group5_snapshot_peek {I VS α S β : Type}
    (s : StatefulSnapshot I VS (α × S)) (sentinel : β) :
    peekSnapshot s sentinel = .ok
      (match s.nextvalstate with | none => Sum.inr sentinel | some p => Sum.inl p.1) := by
  cases s with
  | mk itr pending cacheType assertValue cacheTypeOf =>
    cases pending <;> rfl

theorem group5_snapshot_pop_empty {I VS α S : Type}
    (run : I → Option S → Jl (Option (α × S)))
    (s : StatefulSnapshot I VS (α × S)) (h : s.nextvalstate = none) :
    popSnapshot run s = .error .eofError := by
  cases s with
  | mk itr pending cacheType assertValue cacheTypeOf =>
    cases h
    rfl

theorem group5_snapshot_iterate_empty {I VS α S : Type}
    (run : I → Option S → Jl (Option (α × S)))
    (s : StatefulSnapshot I VS (α × S)) (h : s.nextvalstate = none) :
    iterateSnapshot run s = .ok (none, s) := by
  cases s with
  | mk itr pending cacheType assertValue cacheTypeOf =>
    cases h
    rfl

theorem group5_snapshot_transition_checked {I VS α S : Type}
    (run : I → Option S → Jl (Option (α × S)))
    (s : StatefulSnapshot I VS (α × S)) (value : α) (state : S)
    (pending : Option (α × S))
    (hp : s.nextvalstate = some (value, state))
    (hr : run s.itr (some state) = .ok pending)
    (ha : s.assertValue pending s.cacheType = .ok pending) :
    popSnapshot run s = .ok (value, { s with nextvalstate := pending }) ∧
    iterateSnapshot run s = .ok (some (value, ()), { s with nextvalstate := pending }) := by
  cases s with
  | mk itr current cacheType assertValue cacheTypeOf =>
    cases hp
    change run itr (some state) = .ok pending at hr
    change assertValue pending cacheType = .ok pending at ha
    constructor
    · unfold popSnapshot snapshotOutcome popfirstStateful setCache
      simp only [snapshotOps, Bind.bind, JuliaLean.base.iterators.bind,
        Pure.pure, ret, hr, Except.mapError, ha]
    · unfold iterateSnapshot snapshotOutcome iterateStateful popfirstStateful setCache
      simp only [snapshotOps, Bind.bind, JuliaLean.base.iterators.bind,
        Pure.pure, ret, hr, Except.mapError, ha,
        Option.isNone_some, Bool.false_eq_true, ite_false]

theorem group5_snapshot_iterate_default {I VS α S : Type}
    (run : I → Option S → Jl (Option (α × S))) (itr : I)
    (value : α) (state : S) (pending : Option (α × S))
    (hr : run itr (some state) = .ok pending) :
    iterateSnapshot run ({ itr := itr, nextvalstate := some (value, state) } :
      StatefulSnapshot I VS (α × S)) =
      .ok (some (value, ()), { itr := itr, nextvalstate := pending }) := by
  exact (group5_snapshot_transition_checked run
    ({ itr := itr, nextvalstate := some (value, state) } : StatefulSnapshot I VS (α × S))
    value state pending rfl hr rfl).2

theorem group5_trace_run_success {I α S : Type}
    (run : I → Option S → Jl (Option (α × S)))
    (done : I → Option S → Jl (Option Bool)) (itr : I)
    (xs : List α) (state : Option S)
    (h : followsFrom (protocolIterator run done itr) state xs) :
    ∃ pending, run itr state = .ok pending := by
  cases xs with
  | nil => exact ⟨none, followsFrom_nil (protocolIterator run done itr) state h⟩
  | cons value rest =>
    obtain ⟨next, hr, _⟩ := followsFrom_cons (protocolIterator run done itr) state value rest h
    exact ⟨some (value, next), hr⟩

theorem group5_snapshot_collect_trace {I VS α S : Type}
    (run : I → Option S → Jl (Option (α × S)))
    (done : I → Option S → Jl (Option Bool)) (itr : I) :
    ∀ (xs : List α) (state : Option S) (pending : Option (α × S)),
      followsFrom (protocolIterator run done itr) state xs →
      run itr state = .ok pending →
      collectSnapshots run (xs.length + 1)
        ({ itr := itr, nextvalstate := pending } : StatefulSnapshot I VS (α × S)) =
        .ok (xs, { itr := itr, nextvalstate := none }) := by
  intro xs
  induction xs with
  | nil =>
    intro state pending ht hp
    have hr : run itr state = .ok none :=
      followsFrom_nil (protocolIterator run done itr) state ht
    rw [hr] at hp
    cases hp
    rfl
  | cons value xs ih =>
    intro state pending ht hp
    obtain ⟨next, hr, htail⟩ := followsFrom_cons (protocolIterator run done itr) state value xs ht
    change run itr state = .ok (some (value, next)) at hr
    rw [hr] at hp
    cases hp
    obtain ⟨pendingNext, hpNext⟩ := group5_trace_run_success run done itr xs (some next) htail
    rw [List.length_cons, collectSnapshots, group5_snapshot_iterate_default run itr value next pendingNext hpNext]
    change (do
      let (values, final) ← collectSnapshots run (xs.length + 1)
        ({ itr := itr, nextvalstate := pendingNext } : StatefulSnapshot I VS (α × S))
      pure (value :: values, final)) = _
    rw [ih (some next) pendingNext htail hpNext]
    rfl

theorem group5_stateful_constructor : StatefulConstructorSemantics := by
  refine ⟨?_, ?_, ?_⟩
  · intro I α S run typeof stateTuple inferIterate inferDoiterate assertValue cacheTypeOf itr result checked types hr ha
    simp only [statefulConstructorObservation, snapshotOutcome, stateful, snapshotOps,
      Bind.bind, JuliaLean.base.iterators.bind, Pure.pure, ret, hr, Except.mapError, ha, Observation.map]
  · intro I α S run typeof stateTuple inferIterate inferDoiterate assertValue cacheTypeOf itr result error types hr ha
    simp only [statefulConstructorObservation, snapshotOutcome, stateful, snapshotOps,
      Bind.bind, JuliaLean.base.iterators.bind, Pure.pure, ret, hr, Except.mapError, ha, Observation.map]
  · intro I α S run typeof stateTuple inferIterate inferDoiterate assertValue cacheTypeOf itr error types hr
    simp only [statefulConstructorObservation, snapshotOutcome, stateful, snapshotOps,
      Bind.bind, JuliaLean.base.iterators.bind, Pure.pure, ret, hr, Except.mapError, Observation.map]

theorem group5_exec_pure_bind {E H α β : Type} (value : α)
    (next : α → Exec E H β) : (pure value >>= next) = next value := rfl

theorem group5_exec_bind_assoc {E H α β γ : Type} (action : Exec E H α)
    (next : α → Exec E H β) (last : β → Exec E H γ) :
    ((action >>= next) >>= last) = (action >>= fun value => next value >>= last) := by
  funext heap
  cases ha : action heap with
  | none => simp only [Bind.bind, JuliaLean.base.iterators.bind, ha]
  | some result =>
    rcases result with ⟨result, heap'⟩
    cases result <;> simp only [Bind.bind, JuliaLean.base.iterators.bind, ha]

theorem group5_accumulate_state_step {I α β S H : Type}
    (run : I → Option S → Jl (Option (α × S)))
    (rf : JuliaLean.base.reduce.Reducer (Exec JlError H β) α)
    (init : JuliaLean.base.reduce.FoldInit (Exec JlError H β))
    (itr : I) (previous : JuliaLean.base.reduce.FoldInit β) (state next : S) (value : α)
    (hr : run itr (some state) = .ok (some (value, next))) :
    accumulateNativeStep (fun i st heap => some (run i st, heap))
      rf init itr (some (previous, state)) =
      (do
        let acc ← forceFoldInit (rf.step (liftFoldValue previous) value)
        pure (some (acc, (acc, next)))) := by
  unfold accumulateNativeStep accumulateState
  dsimp only
  rw [hr]
  rfl

theorem group5_accumulate_state_empty {I α β S H : Type}
    (run : I → Option S → Jl (Option (α × S)))
    (rf : JuliaLean.base.reduce.Reducer (Exec JlError H β) α)
    (init : JuliaLean.base.reduce.FoldInit (Exec JlError H β))
    (itr : I) (previous : JuliaLean.base.reduce.FoldInit β) (state : S)
    (hr : run itr (some state) = .ok none) :
    accumulateNativeStep (fun i st heap => some (run i st, heap))
      rf init itr (some (previous, state)) = pure none := by
  unfold accumulateNativeStep accumulateState
  dsimp only
  rw [hr]
  rfl

theorem group5_accumulate_start_step {I α β S H : Type}
    (run : I → Option S → Jl (Option (α × S)))
    (rf : JuliaLean.base.reduce.Reducer (Exec JlError H β) α)
    (init : JuliaLean.base.reduce.FoldInit (Exec JlError H β))
    (itr : I) (value : α) (next : S)
    (hr : run itr none = .ok (some (value, next))) :
    accumulateNativeStep (fun i st heap => some (run i st, heap)) rf init itr none =
      (do
        let acc ← forceFoldInit (match init with
          | .initial => JuliaLean.base.reduce.bottomRF_initial ⟨rf⟩ value
          | .value acc => JuliaLean.base.reduce.bottomRF_apply ⟨rf⟩ acc value)
        pure (some (acc, (acc, next)))) := by
  unfold accumulateNativeStep accumulateStart
  dsimp only
  rw [hr]
  cases init <;> rfl

theorem group5_accumulate_tail {I α β S H : Type}
    (run : I → Option S → Jl (Option (α × S)))
    (done : I → Option S → Jl (Option Bool))
    (rf : JuliaLean.base.reduce.Reducer (Exec JlError H β) α)
    (init : JuliaLean.base.reduce.FoldInit (Exec JlError H β)) (itr : I) :
    ∀ (depth : Nat) (previous : JuliaLean.base.reduce.FoldInit β) (state : S)
      (xs : List α), followsFrom (protocolIterator run done itr) (some state) xs →
      collectAccumulateNative (fun i st heap => some (run i st, heap))
        rf init itr depth (some (previous, state)) = callablePrefixScan rf depth previous xs := by
  intro depth
  induction depth with
  | zero => intro previous state xs h; rfl
  | succ depth ih =>
    intro previous state xs h
    cases xs with
    | nil =>
      have hr : run itr (some state) = .ok none :=
        followsFrom_nil (protocolIterator run done itr) (some state) h
      rw [collectAccumulateNative, group5_accumulate_state_empty run rf init itr previous state hr]
      rfl
    | cons value xs =>
      obtain ⟨next, hr, ht⟩ :=
        followsFrom_cons (protocolIterator run done itr) (some state) value xs h
      rw [collectAccumulateNative,
        group5_accumulate_state_step run rf init itr previous state next value hr,
        group5_exec_bind_assoc]
      change
        (forceFoldInit (rf.step (liftFoldValue previous) value) >>= fun acc => do
          pure (acc :: (← collectAccumulateNative
            (fun i st heap => some (run i st, heap)) rf init itr depth (some (acc, next))))) = _
      unfold callablePrefixScan
      apply congrArg (fun cont => forceFoldInit (rf.step (liftFoldValue previous) value) >>= cont)
      funext acc
      rw [ih acc next xs ht]

theorem group5_accumulate_trace {I α β S H : Type}
    (run : I → Option S → Jl (Option (α × S)))
    (done : I → Option S → Jl (Option Bool))
    (rf : JuliaLean.base.reduce.Reducer (Exec JlError H β) α)
    (init : JuliaLean.base.reduce.FoldInit (Exec JlError H β)) (itr : I)
    (xs : List α) (depth : Nat)
    (h : followsProtocol run done itr xs) :
    collectAccumulateNative (fun i st heap => some (run i st, heap))
      rf init itr depth none = accumulationPrefixSpec rf init xs depth := by
  cases depth with
  | zero => rfl
  | succ depth =>
    cases xs with
    | nil =>
      have hr : run itr none = .ok none :=
        followsFrom_nil (protocolIterator run done itr) none h
      unfold collectAccumulateNative accumulateNativeStep accumulateStart
      dsimp only
      rw [hr]
      rfl
    | cons value xs =>
      obtain ⟨next, hr, ht⟩ :=
        followsFrom_cons (protocolIterator run done itr) none value xs h
      change run itr none = .ok (some (value, next)) at hr
      rw [collectAccumulateNative, group5_accumulate_start_step run rf init itr value next hr,
        group5_exec_bind_assoc]
      change
        (forceFoldInit (match init with
            | .initial => JuliaLean.base.reduce.bottomRF_initial ⟨rf⟩ value
            | .value acc => JuliaLean.base.reduce.bottomRF_apply ⟨rf⟩ acc value) >>= fun acc => do
          pure (acc :: (← collectAccumulateNative
            (fun i st heap => some (run i st, heap)) rf init itr depth (some (acc, next))))) = _
      unfold accumulationPrefixSpec
      dsimp only
      cases init with
      | initial =>
        apply congrArg (fun cont => forceFoldInit (JuliaLean.base.reduce.bottomRF_initial ⟨rf⟩ value) >>= cont)
        funext acc
        rw [group5_accumulate_tail run done rf .initial itr depth acc next xs ht]
      | value initial =>
        apply congrArg (fun cont => forceFoldInit (JuliaLean.base.reduce.bottomRF_apply ⟨rf⟩ initial value) >>= cont)
        funext acc
        rw [group5_accumulate_tail run done rf (.value initial) itr depth acc next xs ht]

theorem group5_accumulate_tail_history {I α β S H : Type}
    (run : I → Option S → Jl (Option (α × S)))
    (rf : JuliaLean.base.reduce.Reducer (Exec JlError H β) α)
    (init : JuliaLean.base.reduce.FoldInit (Exec JlError H β)) (itr : I) :
    ∀ (xs : List α) (previous : JuliaLean.base.reduce.FoldInit β) (state : S)
      (final : Option S),
      Round4.History (fun st => run itr st) (some state) xs final →
      collectAccumulateNative (fun i st heap => some (run i st, heap))
        rf init itr xs.length (some (previous, state)) = callablePrefixScan rf xs.length previous xs := by
  intro xs
  induction xs with
  | nil => intro previous state final h; rfl
  | cons value xs ih =>
    intro previous state final h
    have hs : ∃ next, run itr (some state) = .ok (some (value, next)) ∧
        Round4.History (fun st => run itr st) (some next) xs final := by
      cases h with
      | cons hr ht => exact ⟨_, hr, ht⟩
    obtain ⟨next, hr, ht⟩ := hs
    rw [List.length_cons, collectAccumulateNative,
      group5_accumulate_state_step run rf init itr previous state next value hr,
      group5_exec_bind_assoc]
    change
      (forceFoldInit (rf.step (liftFoldValue previous) value) >>= fun acc => do
        pure (acc :: (← collectAccumulateNative
          (fun i st heap => some (run i st, heap)) rf init itr xs.length (some (acc, next))))) = _
    unfold callablePrefixScan
    apply congrArg (fun cont => forceFoldInit (rf.step (liftFoldValue previous) value) >>= cont)
    funext acc
    rw [ih acc next final ht]

theorem group5_accumulate_history {I α β S H : Type}
    (run : I → Option S → Jl (Option (α × S)))
    (rf : JuliaLean.base.reduce.Reducer (Exec JlError H β) α)
    (init : JuliaLean.base.reduce.FoldInit (Exec JlError H β)) (itr : I)
    (xs : List α) (final : Option S)
    (h : Round4.History (fun st => run itr st) none xs final) :
    collectAccumulateNative (fun i st heap => some (run i st, heap))
      rf init itr xs.length none = accumulationPrefixSpec rf init xs xs.length := by
  cases xs with
  | nil => rfl
  | cons value xs =>
    have hs : ∃ next, run itr none = .ok (some (value, next)) ∧
        Round4.History (fun st => run itr st) (some next) xs final := by
      cases h with
      | cons hr ht => exact ⟨_, hr, ht⟩
    obtain ⟨next, hr, ht⟩ := hs
    rw [List.length_cons, collectAccumulateNative,
      group5_accumulate_start_step run rf init itr value next hr, group5_exec_bind_assoc]
    change
      (forceFoldInit (match init with
          | .initial => JuliaLean.base.reduce.bottomRF_initial ⟨rf⟩ value
          | .value acc => JuliaLean.base.reduce.bottomRF_apply ⟨rf⟩ acc value) >>= fun acc => do
        pure (acc :: (← collectAccumulateNative
          (fun i st heap => some (run i st, heap)) rf init itr xs.length (some (acc, next))))) = _
    unfold accumulationPrefixSpec
    dsimp only
    cases init with
    | initial =>
      apply congrArg (fun cont => forceFoldInit (JuliaLean.base.reduce.bottomRF_initial ⟨rf⟩ value) >>= cont)
      funext acc
      rw [group5_accumulate_tail_history run rf .initial itr xs acc next final ht]
    | value initial =>
      apply congrArg (fun cont => forceFoldInit (JuliaLean.base.reduce.bottomRF_apply ⟨rf⟩ initial value) >>= cont)
      funext acc
      rw [group5_accumulate_tail_history run rf (.value initial) itr xs acc next final ht]

theorem group5_accumulate_sound_of_correct (hCorrect : AccumulateCorrect) : AccumulateSound := by
  refine ⟨hCorrect, ?_, ?_, ?_⟩
  · intro I T N F length size trait f itr init
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro I α β S H run rf init itr xs final heap h
    exact congrFun (group5_accumulate_history run rf init itr xs final h) heap
  · intro I α β S H run rf init itr previous state xs final heap h
    exact congrFun (group5_accumulate_tail_history run rf init itr xs previous state final h) heap

theorem IteratorsAccumulate_proven : JuliaLean.Proofs.base.iterators.AccumulateCorrect := by
  refine ⟨?_, ?_⟩
  · intro α β H rf init xs depth heap
    constructor
    · have h : followsProtocol (fun (ys : List α) st => (listIterator ys).run st)
          (fun ys st => (listIterator ys).isdone st) xs xs := by
        unfold followsProtocol followsFrom
        rw [group5_collect_run_eq
          (protocolIterator (fun (ys : List α) st => (listIterator ys).run st)
            (fun ys st => (listIterator ys).isdone st) xs) (listIterator xs) (fun _ => rfl)]
        exact group5_plain_list_follows xs
      exact congrFun (group5_accumulate_trace
        (fun (ys : List α) st => (listIterator ys).run st)
        (fun ys st => (listIterator ys).isdone st) rf init xs xs depth h) heap
    · rfl
  · intro I α β S H run done itr xs rf init depth heap h
    exact congrFun (group5_accumulate_trace run done rf init itr xs depth h) heap

theorem IteratorscovAccumulate_proven : JuliaLean.Proofs.base.iterators.AccumulateSound :=
  group5_accumulate_sound_of_correct IteratorsAccumulate_proven

theorem group5_count_prefix {T S : Type} (add : T → S → T) (it : Count T S) :
    ∀ (depth : Nat) (state : Option T),
      JuliaLean.Proofs.base.iterators.collectPrefix (countAsIterator add it) depth state =
        .ok (countChainGen add (state.getD it.start) it.step depth) := by
  intro depth
  induction depth with
  | zero => intro state; rfl
  | succ depth ih =>
    intro state
    rw [collectPrefix_succ]
    change (do
      let values ← JuliaLean.Proofs.base.iterators.collectPrefix (countAsIterator add it) depth
        (some (add (state.getD it.start) it.step))
      pure (state.getD it.start :: values)) = _
    rw [ih]
    rfl

theorem IteratorsCountfrom_proven : JuliaLean.Proofs.base.iterators.CountfromCorrect := by
  refine ⟨?_, ?_, ?_⟩
  · intro A S R add convertStart addNext start step k
    simpa only [countTyped, pure_jl, ok_bind, Option.getD_none] using
      group5_count_prefix addNext (⟨convertStart start, step⟩ : Count R S) k none
  · intro A B T promote add start step s d k hp
    simp only [countNumbers, hp, ok_bind, pure_jl]
    exact group5_count_prefix add (⟨s, d⟩ : Count T T) k none
  · intro t start step k
    constructor
    · simpa only [countTyped, pure_jl, ok_bind, Option.getD_none] using
        group5_count_prefix (fun (a b : JInt t) => a + b) ⟨start, step⟩ k none
    · simpa only [countNumbers, pure_jl, ok_bind, Option.getD_none] using
        group5_count_prefix (fun (a b : JInt t) => a + b) ⟨start, step⟩ k none

theorem group5_iterable_pairs_run {α : Type} (xs : List α) (i : Nat) :
    (iterablePairsObservation xs).run (some i) =
      match xs.drop i with
      | [] => .ok none
      | value :: _ => .ok (some ((i, value), i + 1)) := by
  simp only [iterablePairsObservation, iterateStatePairs, pairsStringModel,
    pure_jl, ok_bind, listIterator_run_some]
  cases xs.drop i <;> rfl

theorem group5_iterable_pairs_trace {α : Type} (xs : List α) :
    ∀ (ys : List α) (i : Nat), xs.drop i = ys →
      followsFrom (iterablePairsObservation xs) (some i) (enumerateNatFrom i ys) := by
  intro ys
  induction ys with
  | nil =>
    intro i hd
    change JuliaLean.Proofs.base.iterators.collectPrefix (iterablePairsObservation xs) 1 (some i) = .ok []
    rw [collectPrefix_succ, group5_iterable_pairs_run, hd]
    rfl
  | cons value ys ih =>
    intro i hd
    have hnext : xs.drop (i + 1) = ys := by
      have h := congrArg (List.drop 1) hd
      simpa only [List.drop_drop, List.drop_succ_cons, List.drop_zero] using h
    exact followsFrom_cons_intro (iterablePairsObservation xs) (some i)
      (i, value) (enumerateNatFrom (i + 1) ys) (i + 1)
      (by rw [group5_iterable_pairs_run, hd]) (ih (i + 1) hnext)

theorem group5_iterable_pairs_emits {α : Type} (xs : List α) :
    emitsExactly (iterablePairsObservation xs) (enumerateNatFrom 0 xs) := by
  exact group5_iterable_pairs_trace xs xs 0 (by rfl)

theorem group5_reverse_iterable_run_zero {α : Type} (xs : List α) :
    (reverseIterableStatePairsAsIterator xs).run (some (0 : Int)) = .ok none := rfl

theorem group5_reverse_iterable_run_succ {α : Type} (xs : List α) (m : Nat) (x : α)
    (hx : listGet xs m = some x) :
    (reverseIterableStatePairsAsIterator xs).run (some ((m + 1 : Nat) : Int)) =
      .ok (some (((m + 1 : Nat), x), (m : Int))) := by
  simp only [reverseIterableStatePairsAsIterator, iterateReverseIterableStatePairs,
    pairsStringModel, reverseDefault, pure_jl, ok_bind]
  rw [reverseListAsIterator_run_succ xs m x hx]
  rfl

theorem group5_reverse_iterable_trace {α : Type} (xs : List α) :
    ∀ (m : Nat), m ≤ xs.length →
      followsFrom (reverseIterableStatePairsAsIterator xs) (some (Int.ofNat m))
        (((enumerateNatFrom 1 (xs.take m)).reverse).map fun (i, value) => (Int.ofNat i, value)) := by
  intro m
  induction m with
  | zero =>
    intro hm
    change JuliaLean.Proofs.base.iterators.collectPrefix
      (reverseIterableStatePairsAsIterator xs) 1 (some (0 : Int)) = .ok []
    rw [collectPrefix_succ, group5_reverse_iterable_run_zero]
    rfl
  | succ m ih =>
    intro hm
    obtain ⟨x, hx, _⟩ := listGet_take_last xs m (by omega)
    rw [enumerateNatFrom_take_succ xs 1 m x hx (by omega), List.map_cons]
    apply followsFrom_cons_intro (reverseIterableStatePairsAsIterator xs)
      (some (Int.ofNat (m + 1))) (Int.ofNat (1 + m), x) _ (Int.ofNat m)
    · rw [show 1 + m = m + 1 by omega]
      exact group5_reverse_iterable_run_succ xs m x hx
    · exact ih (by omega)

theorem group5_reverse_iterable_emits {α : Type} (xs : List α) :
    emitsExactly (reverseIterableStatePairsAsIterator xs)
      (((enumerateNatFrom 1 xs).reverse).map fun (i, value) => (Int.ofNat i, value)) := by
  have h := group5_reverse_iterable_trace xs xs.length (Nat.le_refl _)
  rw [List.take_length] at h
  exact h

theorem IteratorscovIterableStatePairs_proven : JuliaLean.Proofs.base.iterators.IterableStatePairsSemantics := by
  refine ⟨?_, ?_, ?_⟩
  · intro α xs
    exact ⟨group5_iterable_pairs_emits xs, group5_reverse_iterable_emits xs⟩
  · intro T Keys V S keys firstKey lastKey iterate x ks k0 kLast state hkeys hfirst hlast
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [iterateStatePairs, hkeys, hfirst, ok_bind, pure_jl]
      cases iterate x.x (some k0) with
      | error error => rfl
      | ok step => cases step <;> rfl
    · simp only [iterateStatePairs, pure_jl, ok_bind]
      cases iterate x.x (some state) with
      | error error => rfl
      | ok step => cases step <;> rfl
    · simp only [iterateReverseIterableStatePairs, reverseDefault, hkeys, hlast, ok_bind]
      rfl
    · rfl
  · intro T α length x sz keyType eltype reverse
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end JuliaLean.ChatGPT.Batch4.Group5

/- Supporting block: Queue25_34Partial -/
namespace JuliaLean.ChatGPT.Batch4.Group5

open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators

theorem group5_snapshot_any_run {I α S : Type}
    (run : I → Option S → Jl (Option (α × S))) (itr : I)
    (pending : Option (α × S)) (hr : run itr none = .ok pending) :
    (statefulAnySnapshot run itr : Observation IteratorError _) =
      .ok ({ itr := itr, nextvalstate := pending } : StatefulSnapshot I AnyCache (α × S)) := by
  unfold statefulAnySnapshot snapshotOutcome statefulAny
  simp only [snapshotOps, Bind.bind, JuliaLean.base.iterators.bind,
    hr, Except.mapError, Observation.map]

theorem group5_snapshot_reset_default {I VS α S : Type}
    (run : I → Option S → Jl (Option (α × S))) (itr : I)
    (old pending : Option (α × S)) (hr : run itr none = .ok pending) :
    resetSnapshot run ({ itr := itr, nextvalstate := old } : StatefulSnapshot I VS (α × S)) =
      .ok ({ itr := itr, nextvalstate := pending } : StatefulSnapshot I VS (α × S)) := by
  unfold resetSnapshot snapshotOutcome resetStateful setCache
  simp only [snapshotOps, Bind.bind, JuliaLean.base.iterators.bind,
    Pure.pure, Except.pure, ret, hr, Except.mapError, Observation.map]

theorem group5_snapshot_reset_to_default {I VS α S : Type}
    (run : I → Option S → Jl (Option (α × S))) (oldItr itr : I)
    (old pending : Option (α × S)) (hr : run itr none = .ok pending) :
    resetSnapshotTo run ({ itr := oldItr, nextvalstate := old } : StatefulSnapshot I VS (α × S)) itr =
      .ok ({ itr := itr, nextvalstate := pending } : StatefulSnapshot I VS (α × S)) := by
  unfold resetSnapshotTo snapshotOutcome resetStatefulTo resetStateful setCache
  simp only [snapshotOps, Bind.bind, JuliaLean.base.iterators.bind,
    Pure.pure, Except.pure, ret, hr, Except.mapError, Observation.map]

theorem group5_snapshot_any_trace {I α S : Type}
    (run : I → Option S → Jl (Option (α × S)))
    (done : I → Option S → Jl (Option Bool)) (itr : I) (xs : List α)
    (ht : followsProtocol run done itr xs) :
    ∃ s0 : StatefulSnapshot I AnyCache (α × S),
      (statefulAnySnapshot run itr : Observation IteratorError _) = .ok s0 ∧
      collectSnapshots run (xs.length + 1) s0 =
        .ok (xs, ({ itr := itr, nextvalstate := none } : StatefulSnapshot I AnyCache (α × S))) := by
  obtain ⟨pending, hr⟩ := group5_trace_run_success run done itr xs none ht
  refine ⟨{ itr := itr, nextvalstate := pending }, group5_snapshot_any_run run itr pending hr, ?_⟩
  exact group5_snapshot_collect_trace run done itr xs none pending ht hr

theorem group5_snapshot_list_run {α : Type} (xs : List α) (pos : Nat) :
    (listIterator xs).run (some pos) = .ok (statefulCurAt xs pos) := by
  rw [listIterator_run_some]
  unfold statefulCurAt
  cases xs.drop pos <;> rfl

theorem group5_snapshot_list_initial {α : Type} (xs : List α) :
    (listIterator xs).run none = .ok (statefulCurAt xs 0) := by
  cases xs <;> rfl

theorem group5_snapshot_list_trace {α VS : Type} (xs : List α) (pos : Nat) :
    collectSnapshots (fun _ st => (listIterator xs).run st) ((xs.drop pos).length + 1)
      ({ itr := listIterator xs, nextvalstate := statefulCurAt xs pos } :
        StatefulSnapshot (IteratorModel α Nat) VS (α × Nat)) =
      .ok (xs.drop pos, { itr := listIterator xs, nextvalstate := none }) := by
  apply group5_snapshot_collect_trace
    (fun _ st => (listIterator xs).run st) (fun _ st => (listIterator xs).isdone st)
    (listIterator xs) (xs.drop pos) (some pos) (statefulCurAt xs pos)
  · unfold followsFrom
    rw [group5_collect_run_eq
      (protocolIterator (fun _ st => (listIterator xs).run st)
        (fun _ st => (listIterator xs).isdone st) (listIterator xs))
      (listIterator xs) (fun _ => rfl), group5_collect_eq_observe]
    change Round5.observe (listIterator xs).run ((xs.drop pos).length + 1) (some pos) = .ok (xs.drop pos)
    rw [group5_observe_list, List.take_of_length_le (Nat.le_succ _)]
  · exact group5_snapshot_list_run xs pos

theorem group5_snapshot_list_roundtrip {α : Type} (xs ys : List α) :
    (do
      let s0 ← (statefulAnySnapshot (fun _ st => (listIterator xs).run st) (listIterator xs) : Observation IteratorError _)
      let (out1, s1) ← collectSnapshots (fun _ st => (listIterator xs).run st) (xs.length + 1) s0
      let s2 ← (resetSnapshot (fun _ st => (listIterator xs).run st) s1 : Observation IteratorError _)
      let (out2, s3) ← collectSnapshots (fun _ st => (listIterator xs).run st) (xs.length + 1) s2
      let s4 ← (resetSnapshotTo (fun (it : IteratorModel α Nat) st => it.run st) s3 (listIterator ys) : Observation IteratorError _)
      let (out3, _) ← collectSnapshots (fun _ st => (listIterator ys).run st) (ys.length + 1) s4
      pure (out1, out2, out3)) = .ok (xs, xs, ys) := by
  have hx := group5_snapshot_list_trace (VS := AnyCache) xs 0
  have hy := group5_snapshot_list_trace (VS := AnyCache) ys 0
  simp only [List.drop_zero] at hx hy
  rw [group5_snapshot_any_run (fun _ st => (listIterator xs).run st) (listIterator xs) _ (group5_snapshot_list_initial xs)]
  change (do
    let (out1, s1) ← collectSnapshots (fun _ st => (listIterator xs).run st) (xs.length + 1)
      ({ itr := listIterator xs, nextvalstate := statefulCurAt xs 0 } :
        StatefulSnapshot (IteratorModel α Nat) AnyCache (α × Nat))
    let s2 ← resetSnapshot (fun _ st => (listIterator xs).run st) s1
    let (out2, s3) ← collectSnapshots (fun _ st => (listIterator xs).run st) (xs.length + 1) s2
    let s4 ← resetSnapshotTo (fun (it : IteratorModel α Nat) st => it.run st) s3 (listIterator ys)
    let (out3, _) ← collectSnapshots (fun _ st => (listIterator ys).run st) (ys.length + 1) s4
    pure (out1, out2, out3)) = _
  rw [hx]
  change (do
    let s2 ← resetSnapshot (fun _ st => (listIterator xs).run st)
      ({ itr := listIterator xs, nextvalstate := none } :
        StatefulSnapshot (IteratorModel α Nat) AnyCache (α × Nat))
    let (out2, s3) ← collectSnapshots (fun _ st => (listIterator xs).run st) (xs.length + 1) s2
    let s4 ← resetSnapshotTo (fun (it : IteratorModel α Nat) st => it.run st) s3 (listIterator ys)
    let (out3, _) ← collectSnapshots (fun _ st => (listIterator ys).run st) (ys.length + 1) s4
    pure (xs, out2, out3)) = _
  rw [group5_snapshot_reset_default (fun _ st => (listIterator xs).run st) _ _ _ (group5_snapshot_list_initial xs)]
  change (do
    let (out2, s3) ← collectSnapshots (fun _ st => (listIterator xs).run st) (xs.length + 1)
      ({ itr := listIterator xs, nextvalstate := statefulCurAt xs 0 } :
        StatefulSnapshot (IteratorModel α Nat) AnyCache (α × Nat))
    let s4 ← resetSnapshotTo (fun (it : IteratorModel α Nat) st => it.run st) s3 (listIterator ys)
    let (out3, _) ← collectSnapshots (fun _ st => (listIterator ys).run st) (ys.length + 1) s4
    pure (xs, out2, out3)) = _
  rw [hx]
  change (do
    let s4 ← resetSnapshotTo (fun (it : IteratorModel α Nat) st => it.run st)
      ({ itr := listIterator xs, nextvalstate := none } :
        StatefulSnapshot (IteratorModel α Nat) AnyCache (α × Nat)) (listIterator ys)
    let (out3, _) ← collectSnapshots (fun _ st => (listIterator ys).run st) (ys.length + 1) s4
    pure (xs, xs, out3)) = _
  rw [group5_snapshot_reset_to_default (fun (it : IteratorModel α Nat) st => it.run st) _ _ _ _ (group5_snapshot_list_initial ys)]
  change (do
    let (out3, _) ← collectSnapshots (fun _ st => (listIterator ys).run st) (ys.length + 1)
      ({ itr := listIterator ys, nextvalstate := statefulCurAt ys 0 } :
        StatefulSnapshot (IteratorModel α Nat) AnyCache (α × Nat))
    pure (xs, xs, out3)) = _
  rw [hy]
  rfl

theorem group5_snapshot_size (tag : IteratorSizeTag) :
    (sourceMethod1625 tag = .isInfinite ↔ tag = .isInfinite) ∧
      (tag ≠ .isInfinite → sourceMethod1625 tag = .sizeUnknown) := by
  cases tag <;> simp only [sourceMethod1625, BEq.beq, beq_iff_eq, Bool.false_eq_true,
    Bool.true_eq, decide_false, decide_true, ite_false, ite_true, false_iff, true_iff, reduceCtorEq, not_false_eq_true,
    forall_const, implies_true, true_and, and_self]
  all_goals exact fun h => h rfl

theorem group5_stateful_methods_of_consistent (h : StatefulConsistent) :
    StatefulMethodSemantics := by
  refine ⟨h, ?_, ?_, ?_, statefulApproximation, group5_stateful_constructor,
    group5_snapshot_size⟩
  · intro α xs ys
    exact group5_snapshot_list_roundtrip xs ys
  · intro α xs
    refine ⟨?_, rfl, rfl, rfl, rfl⟩
    exact group5_snapshot_any_run (fun _ st => (listIterator xs).run st)
      (listIterator xs) (statefulCurAt xs 0) (group5_snapshot_list_initial xs)
  · intro I α S run itr x state
    exact ⟨rfl, rfl⟩

end JuliaLean.ChatGPT.Batch4.Group5

/- Supporting block: Queue28 -/
namespace JuliaLean.ChatGPT.Batch4.Group5
open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators

theorem group5_listGet_getElem {α : Type} (xs : List α) (i : Nat) :
    listGet xs i = xs[i]? := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => cases i <;> simp only [listGet, List.getElem?_cons_zero,
      List.getElem?_cons_succ, ih]

theorem group5_listGet_range (n i : Nat) :
    listGet (List.range n) i = if i < n then some i else none := by
  by_cases hi : i < n
  · rw [if_pos hi, group5_listGet_getElem]
    exact List.getElem?_range hi
  · rw [if_neg hi]
    exact listGet_none_of_length_le _ _ (by simpa only [List.length_range] using Nat.le_of_not_gt hi)

theorem group5_pairs_run_eq {α : Type} (xs : List α) (state : Option Nat) :
    (pairsObservation xs).run state = (iterablePairsObservation xs).run state := by
  have hsome : ∀ i : Nat, (pairsObservation xs).run (some i) =
      (iterablePairsObservation xs).run (some i) := by
    intro i
    by_cases hi : i < xs.length
    · obtain ⟨x, hx, _⟩ := listGet_take_last xs i hi
      simp only [pairsObservation, iterablePairsObservation, pairsLinear, keysPairs,
        iteratePairs, pairsElement, iterateStatePairs, pairsStringModel, listIterator,
        Option.getD_some, group5_listGet_range, if_pos hi, hx, pure_jl, ok_bind,
        Option.elim_some, Option.map_some]
    · have hx := listGet_none_of_length_le xs i (Nat.le_of_not_gt hi)
      simp only [pairsObservation, iterablePairsObservation, pairsLinear, keysPairs,
        iteratePairs, pairsElement, iterateStatePairs, pairsStringModel, listIterator,
        Option.getD_some, group5_listGet_range, if_neg hi, hx, pure_jl, ok_bind,
        Option.map_none]
  cases state with
  | none => exact hsome 0
  | some i => exact hsome i

theorem group5_pairs_emits {α : Type} (xs : List α) :
    emitsExactly (pairsObservation xs) (enumerateNatFrom 0 xs) := by
  unfold emitsExactly
  rw [group5_collect_run_eq _ _ (group5_pairs_run_eq xs)]
  exact group5_iterable_pairs_emits xs

theorem group5_reverse_pairs_run {α : Type} (xs : List α) (keys : List Nat) (i : Nat) :
    (reversePairsObservation xs).run (some (keys, i)) =
      match listGet keys i with
      | none => .ok none
      | some key => (listGet xs key).elim (.error .boundsError)
          (fun value => .ok (some ((key, value), (keys, i + 1)))) := by
  unfold reversePairsObservation iterateReversePairs pairsElement
  simp only [pure_jl, ok_bind, listIterator, Option.getD_some, pairsLinear]
  cases listGet keys i with
  | none => rfl
  | some key =>
    simp only [ok_bind]
    cases listGet xs key <;> rfl

theorem group5_reverse_pairs_trace {α : Type} (xs : List α) :
    ∀ m, m ≤ xs.length →
      followsFrom (reversePairsObservation xs)
        (some ((List.range xs.length).reverse, xs.length - m))
        (enumerateNatFrom 0 (xs.take m)).reverse := by
  intro m
  induction m with
  | zero =>
    intro hm
    change JuliaLean.Proofs.base.iterators.collectPrefix (reversePairsObservation xs) 1
      (some ((List.range xs.length).reverse, xs.length - 0)) = .ok []
    rw [collectPrefix_succ, group5_reverse_pairs_run, listGet_eq_drop_head?,
      drop_reverse_range xs.length (xs.length - 0) (by omega)]
    simp only [Nat.sub_zero, Nat.sub_self, List.range_zero, List.reverse_nil, List.head?_nil]
    rfl
  | succ m ih =>
    intro hm
    obtain ⟨x, hx, _⟩ := listGet_take_last xs m (by omega)
    rw [enumerateNatFrom_take_succ xs 0 m x hx (by omega), Nat.zero_add]
    have hk : listGet (List.range xs.length).reverse (xs.length - (m + 1)) = some m := by
      rw [listGet_eq_drop_head?, drop_reverse_range xs.length (xs.length - (m + 1)) (by omega)]
      rw [show xs.length - (xs.length - (m + 1)) = m + 1 by omega,
        List.range_succ, List.reverse_append]
      rfl
    apply followsFrom_cons_intro (reversePairsObservation xs)
      (some ((List.range xs.length).reverse, xs.length - (m + 1))) (m, x) _
      ((List.range xs.length).reverse, xs.length - (m + 1) + 1)
    · rw [group5_reverse_pairs_run, hk]
      simp only [hx, Option.elim_some]
    · rw [show xs.length - (m + 1) + 1 = xs.length - m by omega]
      exact ih (by omega)

theorem group5_reverse_pairs_emits {α : Type} (xs : List α) :
    emitsExactly (reversePairsObservation xs) (enumerateNatFrom 0 xs).reverse := by
  have h := group5_reverse_pairs_trace xs xs.length (Nat.le_refl _)
  rw [List.take_length, Nat.sub_self] at h
  exact h

theorem group5_pairs_last {α : Type} (xs : List α) :
    lastPairs (fun ys : List α => pure (List.range ys.length)) listLastModel
      (fun ys i => (listGet ys i).elim (.error .boundsError) pure)
      (fun key value => pure (key, value))
      (pairsLinear (K := Nat) (V := α) (fun ys => List.range ys.length) xs) =
      listLastModel (enumerateNatFrom 0 xs) := by
  by_cases hnil : xs = []
  · subst xs; rfl
  · have hlen : 0 < xs.length := List.length_pos_iff.mpr hnil
    let m := xs.length - 1
    have hm : xs.length = m + 1 := by omega
    obtain ⟨x, hx, _⟩ := listGet_take_last xs m (by omega)
    have hrev := enumerateNatFrom_take_succ xs 0 m x hx (by omega)
    rw [Nat.zero_add, ← hm, List.take_length] at hrev
    have hlast : listLastModel (enumerateNatFrom 0 xs) = .ok (m, x) := by
      rw [← List.reverse_reverse (enumerateNatFrom 0 xs), hrev,
        List.reverse_cons, listLastModel_append_singleton]
    unfold lastPairs keysPairs pairsLinear getindexPairs valuesPairsModel
    simp only [pure_jl, ok_bind]
    rw [hm, List.range_succ, listLastModel_append_singleton]
    simp only [ok_bind, hx, Option.elim_some, pure_jl, hlast]

theorem group5_pairs_call {K V I D S : Type} (p : PairsModel K V I D)
    (keysData : D → Jl I) (run : I → Option S → Jl (Option (I × S)))
    (getindex : D → I → Jl V) (keys : I) (state : Option S)
    (hk : keysPairs keysData p = .ok keys) :
    iteratePairs keysData run getindex (fun key value => pure (key, value))
      ({ data := p.data, itr := p.itr } : PairsModel I V I D) state =
      (do
        match ← run keys state with
        | none => pure none
        | some (key, next) =>
          pure (some (← pairsElement getindex (fun key value => pure (key, value))
            ({ data := p.data, itr := p.itr } : PairsModel I V I D) key, next))) := by
  unfold iteratePairs
  have hk' : keysPairs keysData
      ({ data := p.data, itr := p.itr } : PairsModel I V I D) = .ok keys := hk
  rw [hk', ok_bind]
  cases hr : run keys state with
  | error error => simp only [err_bind]
  | ok step =>
    cases step with
    | none => rfl
    | some pair =>
      rcases pair with ⟨key, next⟩
      simp only [ok_bind, pairsElement]

theorem group5_pairs_protocol {K V I D S : Type} (p : PairsModel K V I D)
    (keysData : D → Jl I) (run : I → Option S → Jl (Option (I × S)))
    (done : I → Option S → Jl (Option Bool)) (getindex : D → I → Jl V)
    (keys : I) (hk : keysPairs keysData p = .ok keys) :
    ∀ (indices : List I) (state : Option S),
      followsFrom (protocolIterator run done keys) state indices →
      JuliaLean.Proofs.base.iterators.collectPrefix
        (protocolIterator
          (fun (_ : PairsModel K V I D) st => iteratePairs keysData run getindex
            (fun key value => pure (key, value))
            ({ data := p.data, itr := p.itr } : PairsModel I V I D) st)
          (fun _ _ => .ok none) p) (indices.length + 1) state =
        pairsValuesSpec
          (fun (q : PairsModel K V I D) key => pairsElement getindex
            (fun key value => pure (key, value))
            ({ data := q.data, itr := q.itr } : PairsModel I V I D) key) p indices := by
  intro indices
  induction indices with
  | nil =>
    intro state ht
    have hr : run keys state = .ok none :=
      followsFrom_nil (protocolIterator run done keys) state ht
    rw [collectPrefix_succ]
    change collectAfterStep _ 0
      (iteratePairs keysData run getindex (fun key value => pure (key, value))
        ({ data := p.data, itr := p.itr } : PairsModel I V I D) state) = _
    rw [group5_pairs_call p keysData run getindex keys state hk, hr]
    rfl
  | cons key indices ih =>
    intro state ht
    obtain ⟨next, hr, htail⟩ :=
      followsFrom_cons (protocolIterator run done keys) state key indices ht
    change run keys state = .ok (some (key, next)) at hr
    rw [List.length_cons, collectPrefix_succ]
    change collectAfterStep _ (indices.length + 1)
      (iteratePairs keysData run getindex (fun key value => pure (key, value))
        ({ data := p.data, itr := p.itr } : PairsModel I V I D) state) = _
    rw [group5_pairs_call p keysData run getindex keys state hk, hr]
    simp only [collectAfterStep, ok_bind, pairsValuesSpec, pairsElement]
    cases hg : getindex p.data key with
    | error error => simp only [hg, err_bind]
    | ok value =>
      simp only [ok_bind, pure_jl]
      simpa only [pairsElement, pure_jl] using congrArg
        (fun values : Jl (List (I × V)) => do
          let rest ← values
          (.ok ((key, value) :: rest) : Jl (List (I × V)))) (ih (some next) htail)

theorem IteratorscovPairsSemantics_proven : JuliaLean.Proofs.base.iterators.PairsSemantics := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α xs
    refine ⟨group5_pairs_emits xs, group5_reverse_pairs_emits xs, group5_pairs_last xs,
      ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
    · simp only [pairsObservation, pairsMetadata, pairsLinear, keysPairs, pure_jl,
        ok_bind, List.length_range]
    · simp only [pairsObservation, pairsMetadata, pairsLinear, keysPairs, pure_jl,
        ok_bind, List.length_range]
    · simp only [pairsMetadata, pairsLinear, keysPairs, pure_jl, ok_bind, List.length_range]
    · intro st
      simp only [pairsMetadata, pairsLinear, keysPairs, pure_jl, ok_bind,
        listIterator, List.length_range]
    · intro k
      simp only [pairsMetadata, pairsLinear, keysPairs, pure_jl, ok_bind, List.mem_range]
  · intro K V I D S p keysData run done getindex indices state
    dsimp only
    cases hk : keysPairs keysData p with
    | error error =>
      have hk' : keysPairs keysData
          ({ data := p.data, itr := p.itr } : PairsModel I V I D) = .error error := hk
      simp only [iteratePairs, hk', err_bind]
    | ok keys =>
      exact group5_pairs_protocol p keysData run done getindex keys hk indices state
  · intro K V I D data selected keysData idxFn
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
    rfl
  · intro K V I D R getindex p key
    rfl
  · intro K V I D R H setindex getindex p key value heap next hset
    constructor
    · simp only [setindexPairs, Bind.bind, JuliaLean.base.iterators.bind, hset, Pure.pure, ret]
    · simp only [setindexPairs, getindexPairs, valuesPairsModel,
        Bind.bind, JuliaLean.base.iterators.bind, hset, Pure.pure, ret]
  · intro K V I D R get p key default
    rfl
  · intro K V I D R F getFn f p key
    rfl

end JuliaLean.ChatGPT.Batch4.Group5

/- Supporting block: Queue29 -/
namespace JuliaLean.ChatGPT.Batch4.Group5
open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators

theorem group5_observation_trace_of_follows {α S : Type} (itr : IteratorModel α S) :
    ∀ (xs : List α) (state : Option S), followsFrom itr state xs →
      finiteObservationTrace (AsObservation.view itr).run state xs := by
  intro xs
  induction xs with
  | nil =>
    intro state h
    have hr := followsFrom_nil itr state h
    apply finiteObservationTrace.stop
    change observeJl (itr.run state) = .ok none
    rw [hr]
    rfl
  | cons value xs ih =>
    intro state h
    obtain ⟨next, hr, ht⟩ := followsFrom_cons itr state value xs h
    apply finiteObservationTrace.step (next := next)
    · change observeJl (itr.run state) = .ok (some (value, next))
      rw [hr]
      rfl
    · exact ih (some next) ht

theorem group5_filter_observation_stop {I α S : Type} [AsObservation I α S]
    (itr : I) (predicate : α → Bool) (state : Option S)
    (hr : (AsObservation.view itr).run state = .ok none) :
    (filterObservation itr predicate).run state = .ok none := by
  unfold filterObservation observe
  dsimp only
  rw [filterScan.eq_def]
  simp only [hr, action, Pure.pure, ret]

theorem group5_filter_observation_accept {I α S : Type} [AsObservation I α S]
    (itr : I) (predicate : α → Bool) (state : Option S) (value : α) (next : S)
    (hr : (AsObservation.view itr).run state = .ok (some (value, next)))
    (hp : predicate value = true) :
    (filterObservation itr predicate).run state = .ok (some (value, next)) := by
  unfold filterObservation observe
  dsimp only
  rw [filterScan.eq_def]
  simp only [hr, action, Pure.pure, ret, hp, if_true]

theorem group5_filter_observation_skip {I α S : Type} [AsObservation I α S]
    (itr : I) (predicate : α → Bool) (state : Option S) (value : α) (next : S)
    (hr : (AsObservation.view itr).run state = .ok (some (value, next)))
    (hp : predicate value = false) :
    (filterObservation itr predicate).run state = (filterObservation itr predicate).run (some next) := by
  unfold filterObservation observe
  dsimp only
  conv =>
    lhs
    rw [filterScan.eq_def]
  simp only [hr, action, Pure.pure, ret, hp, if_true]

theorem group5_observation_trace_restate {α S : Type}
    (run : Option S → Observation JlError (Option (α × S)))
    (state state' : Option S) (xs : List α) (hr : run state = run state')
    (ht : finiteObservationTrace run state' xs) : finiteObservationTrace run state xs := by
  cases ht with
  | stop hstop => exact .stop (hr.trans hstop)
  | step hstep htail => exact .step (hr.trans hstep) htail

theorem group5_filter_observation_trace {I α S : Type} [AsObservation I α S]
    (itr : I) (predicate : α → Bool) {state : Option S} {xs : List α}
    (h : finiteObservationTrace (AsObservation.view itr).run state xs) :
    finiteObservationTrace (filterObservation itr predicate).run state (xs.filter predicate) := by
  induction h with
  | stop hr => exact .stop (group5_filter_observation_stop itr predicate _ hr)
  | @step state value next xs hr ht ih =>
    cases hp : predicate value with
    | true =>
      rw [List.filter_cons, hp]
      exact .step (group5_filter_observation_accept itr predicate state value next hr hp) ih
    | false =>
      rw [List.filter_cons, hp]
      have hs := group5_filter_observation_skip itr predicate state value next hr hp
      exact group5_observation_trace_restate _ state (some next) _ hs ih

theorem group5_find_each_emits {K V S : Type} (itr : IteratorModel (K × V) S)
    (predicate : V → Bool) (xs : List (K × V))
    (h : followsFrom itr none xs) :
    emitsExactly
      (generatorObservation ⟨Prod.fst, filterObservation itr (fun pair => predicate pair.2)⟩)
      ((xs.filter fun pair => predicate pair.2).map Prod.fst) := by
  have hfilter := group5_filter_observation_trace itr (fun pair => predicate pair.2)
    (group5_observation_trace_of_follows itr xs none h)
  have hmap := finiteObservationTrace_generator (I := IteratorObservation (K × V) S)
    (α := K × V) (β := K) (S := S)
    (filterObservation itr (fun (pair : K × V) => predicate pair.2)) Prod.fst hfilter
  unfold emitsExactly
  rw [group5_collect_eq_observe]
  exact finiteObservationTrace_reads _ hmap

theorem group5_map_list_emits {α β : Type} (f : α → β) (xs : List α) :
    emitsExactly (mapGeneratorAsIterator (mapModel id f (listIterator xs) [])) (xs.map f) := by
  exact emitsExactly_generator f (listIterator xs) xs (group5_plain_list_follows xs)

theorem group5_flatmap_list_emits {α β : Type} (f : α → List β) (xs : List α) :
    let outer := mapGeneratorAsIterator (flatmapModel (m := Id)
      (fun f c => mapModel id f c []) (fun x => listIterator (f x)) (listIterator xs)).it
    emitsExactly (flattenObservation (flattenModel outer)) ((xs.map f).flatten) := by
  let outer := mapGeneratorAsIterator (mapModel id (fun x => listIterator (f x)) (listIterator xs) [])
  have houter : finiteObservationTrace (AsObservation.view outer).run none
      (xs.map fun x => listIterator (f x)) :=
    group5_observation_trace_of_follows outer _ none
      (group5_map_list_emits (fun x => listIterator (f x)) xs)
  have hrows : finiteRelatedLists
      (fun inner row => finiteObservationTrace (AsObservation.view inner).run none row)
      (xs.map fun x => listIterator (f x)) (xs.map f) := by
    clear houter outer
    induction xs with
    | nil => exact .nil
    | cons x xs ih => exact .cons (listIteratorFiniteTrace (f x)) ih
  exact flattenFiniteTraces (flattenModel outer) _ _ houter hrows

theorem group5_cycle_first_wrap {α : Type} (value : α) (rest : List α) :
    JuliaLean.Proofs.base.iterators.collectPrefix
      (cycleObservation (cycleModel (listIterator (value :: rest))))
      (rest.length + 2) none = .ok ((value :: rest) ++ [value]) := by
  let itr := listIterator (value :: rest)
  have hc : Round4.CompleteHistory itr.run (value :: rest) :=
    followsFromComplete itr (value :: rest) none (group5_plain_list_follows _)
  have hp : Round4.History itr.run none [value] (some 1) :=
    .cons rfl (.nil _)
  have hd : ∃ (rounds : List (List α)) (tailValues : List α) (final : Option Nat),
      (∀ round ∈ rounds, round ≠ [] ∧ Round4.CompleteHistory itr.run round) ∧
      Round4.History itr.run none tailValues final ∧
      (value :: rest) ++ [value] = rounds.flatten ++ tailValues := by
    refine ⟨[value :: rest], [value], some 1, ?_, hp, ?_⟩
    · intro round hmem
      have heq : round = value :: rest := List.mem_singleton.mp hmem
      subst round
      exact ⟨(by intro he; cases he), hc⟩
    · simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  obtain ⟨final, hh⟩ := (cycleOutputSemantics_proven.1 itr ((value :: rest) ++ [value])).mpr hd
  have hr := observationHistoryReads _ hh
  rw [group5_collect_eq_observe]
  change Round5.observe (cycleObservation (cycleModel itr)).run (rest.length + 2) none = _
  simpa only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.add_assoc, Nat.reduceAdd] using hr

theorem IteratorscovCycleRepeated_proven : JuliaLean.Proofs.base.iterators.CycleRepeatedSemantics := by
  refine ⟨?_, ?_, ?_, ?_, ?_, IteratorsCycleN_proven, IteratorsRepeatedN_proven, ?_, ?_⟩
  · intro α β f xs
    exact group5_map_list_emits f xs
  · intro α β f xs
    exact group5_flatmap_list_emits f xs
  · intro It K V pairsList predicate it
    exact group5_find_each_emits (listIterator (pairsList it)) predicate (pairsList it)
      (group5_plain_list_follows _)
  · intro It K pairsList it
    exact ⟨rfl, group5_find_each_emits (listIterator (pairsList it)) id (pairsList it)
      (group5_plain_list_follows _)⟩
  · intro It K V S pairs predicate it xs h
    exact group5_find_each_emits (pairs it) predicate xs h
  · intro α xs
    refine ⟨rfl, rfl, rfl, ?_, fun _ => rfl, rfl, rfl, ?_, ?_, ?_⟩
    · cases xs <;> rfl
    · change emitsExactly (reverseListAsIterator xs.reverse) xs
      simpa only [List.reverse_reverse] using group5_q43_reverse_emits xs.reverse
    · intro h
      subst xs
      rfl
    · intro value rest h
      subst xs
      exact group5_cycle_first_wrap value rest
  · intro O x k
    refine ⟨collectPrefix_repeatedInf x k none, ?_, rfl, rfl, rfl, rfl, rfl⟩
    exact collectPrefix_repeatedInf x k none

end JuliaLean.ChatGPT.Batch4.Group5

/- Supporting block: Queue35 -/
namespace JuliaLean.ChatGPT.Batch4.Group5
open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators

theorem group5_mod1_arithmetic (n k : Int) (hk : 0 < k) :
    (if n % k = 0 then k else n % k) = (n - 1) % k + 1 := by
  have hm0 : 0 ≤ (n - 1) % k := Int.emod_nonneg _ (by omega)
  have hmk : (n - 1) % k < k := Int.emod_lt_of_pos _ hk
  have hmod : ((n - 1) % k + 1) % k = n % k := by
    calc
      ((n - 1) % k + 1) % k = ((n - 1) + 1) % k := by
        rw [Int.add_emod, Int.emod_emod, ← Int.add_emod]
      _ = n % k := by congr 1; omega
  by_cases heq : (n - 1) % k + 1 = k
  · have hn0 : n % k = 0 := by rw [← hmod, heq, Int.emod_self]
    rw [if_pos hn0]
    exact heq.symm
  · have hlt : (n - 1) % k + 1 < k := by omega
    have hval : n % k = (n - 1) % k + 1 := by
      rw [← hmod, Int.emod_eq_of_lt (by omega) hlt]
    simp only [hval, if_neg (by omega : (n - 1) % k + 1 ≠ 0)]

theorem group5_mod1_index (n : Int) (k : Nat) (hn : 0 < n) :
    (n - 1) % Int.ofNat k + 1 = Int.ofNat ((n.toNat - 1) % k + 1) := by
  have hsub : n - 1 = Int.ofNat (n.toNat - 1) := by
    rw [← Int.toNat_sub' n 1]
    exact (Int.toNat_of_nonneg (by omega : 0 ≤ n - 1)).symm
  rw [hsub]
  rfl

theorem group5_value_mod1 (n k : Int) (hk : 0 < k) :
    valueMod1 n k = .ok ((n - 1) % k + 1) := by
  have hne : k ≠ 0 := by omega
  have hrem := Int.fmod_eq_emod_of_nonneg n (by omega : 0 ≤ k)
  have hformula : valueMod1 n k = .ok (if n % k = 0 then k else n % k) := by
    by_cases hz : n % k = 0 <;>
      simp [valueMod1, JuliaLean.base.operators.mod1, JuliaLean.base.number.iszero,
        hne, hrem, hz, Except.map]
  rw [hformula, group5_mod1_arithmetic n k hk]

theorem group5_nth_mod_index {α : Type} (xs : List α) (n : Int)
    (hx : 0 < xs.length) (hn : 0 < n) :
    ∃ x, listGet xs ((n.toNat - 1) % xs.length) = some x ∧
      nthIterator (listIterator xs) (Int.ofNat ((n.toNat - 1) % xs.length + 1)) = .ok x := by
  have hm : (n.toNat - 1) % xs.length < xs.length := Nat.mod_lt _ hx
  have hindex : 1 ≤ Int.ofNat ((n.toNat - 1) % xs.length + 1) ∧
      Int.ofNat ((n.toNat - 1) % xs.length + 1) ≤ xs.length := by
    constructor <;> simp only [Int.ofNat_eq_natCast] <;> omega
  have h := nthModel_listIterator_spec xs (Int.ofNat ((n.toNat - 1) % xs.length + 1))
  rw [if_pos hindex] at h
  obtain ⟨x, hget, hnth, _⟩ := h
  refine ⟨x, ?_, hnth⟩
  simpa only [Int.ofNat_eq_natCast, Int.toNat_natCast, Nat.add_sub_cancel] using hget

theorem group5_cycle_nth_pos {α : Type} (xs : List α) (n : Int)
    (hx : 0 < xs.length) (hn : 0 < n) :
    ∃ x, listGet xs ((n.toNat - 1) % xs.length) = some x ∧
      nthCycleValue (fun it => it.length) nthIterator (cycleModel (listIterator xs)) n = .ok x := by
  obtain ⟨x, hget, hnth⟩ := group5_nth_mod_index xs n hx hn
  refine ⟨x, hget, ?_⟩
  have hlen : xs.length ≠ 0 := by omega
  have hmod := group5_value_mod1 n (Int.ofNat xs.length)
    (by simp only [Int.ofNat_eq_natCast]; omega)
  rw [group5_mod1_index n xs.length hn] at hmod
  simp only [Int.ofNat_eq_natCast] at hmod hnth
  simp [nthCycleValue, sourceMethod1758, cycleModel, listIterator_length,
    hlen, hn, hmod, hnth, Except.map, -nthIterator_eq, -nthValue_eq,
    -Int.natCast_add]

theorem group5_cycle_nth_nonpos {α : Type} (xs : List α) (n : Int)
    (hx : 0 < xs.length) (hn : n ≤ 0) :
    nthCycleValue (fun it => it.length) nthIterator (cycleModel (listIterator xs)) n =
      .error .boundsError := by
  have hlen : xs.length ≠ 0 := by omega
  have hpos : ¬ 0 < n := by omega
  have hspec := nthModel_listIterator_spec xs n
  rw [if_neg (by omega)] at hspec
  simp [nthCycleValue, sourceMethod1758, cycleModel, listIterator_length,
    hlen, hpos, hspec.1, Except.map, -nthIterator_eq, -nthValue_eq]

theorem group5_finite_cycle_nth {α : Type} (xs : List α) (cycles : Nat) (n : Int)
    (hxfit : (xs.length : Int) < 2 ^ 63) (hcfit : (cycles : Int) < 2 ^ 63)
    (hpfit : (xs.length : Int) * (cycles : Int) < 2 ^ 63) :
    let ftr : Flatten (Take (Repeated (IteratorModel α Nat))) :=
      ⟨⟨repeatedModel (listIterator xs), JInt.lit .i64 cycles⟩⟩
    let call := nthFiniteCycleValue
      (fun o => Except.map (fun (l : Nat) => JInt.lit .i64 (Int.ofNat l)) o.length)
      (fun o idx => nthIterator o idx) ftr n
    if 0 < xs.length ∧ 1 ≤ n ∧ n ≤ (xs.length : Int) * (cycles : Int) then
      ∃ x, listGet xs ((n.toNat - 1) % xs.length) = some x ∧ call = .ok x
    else call = .error .boundsError := by
  have hxval := group5_nat_count_val xs.length (by omega)
  have hcval := group5_nat_count_val cycles (by omega)
  simp only [Int.ofNat_eq_natCast] at hxval hcval
  have hzero : (JInt.lit .i64 0).val = 0 := rfl
  have hprod : (JuliaLean.base.int.mul_int (JInt.lit .i64 xs.length)
      (JInt.lit .i64 cycles)).val = (xs.length : Int) * (cycles : Int) := by
    rw [JuliaLean.Proofs.base.int.mul_int_val, hxval, hcval]
    apply wrapInt_of_inRange
    have hnonneg : (0 : Int) ≤ (xs.length : Int) * (cycles : Int) :=
      Int.mul_nonneg (by omega) (by omega)
    change -(2 ^ 63 : Int) ≤ (xs.length : Int) * (cycles : Int) ∧
      (xs.length : Int) * (cycles : Int) ≤ 2 ^ 63 - 1
    constructor <;> omega
  dsimp only
  by_cases h : 0 < xs.length ∧ 1 ≤ n ∧ n ≤ (xs.length : Int) * (cycles : Int)
  · rw [if_pos h]
    obtain ⟨x, hget, hnth⟩ := group5_nth_mod_index xs n h.1 (by omega)
    have hmod := group5_value_mod1 n (Int.ofNat xs.length)
      (by simp only [Int.ofNat_eq_natCast]; omega)
    rw [group5_mod1_index n xs.length (by omega)] at hmod
    simp only [Int.ofNat_eq_natCast] at hmod hnth
    refine ⟨x, hget, ?_⟩
    have hxs : xs ≠ [] := by intro he; simp [he] at h
    simp [nthFiniteCycleValue, sourceMethod1767, repeatedModel, listIterator_length,
      Except.map, pure_jl, ok_bind, hprod, hxval, hzero, JuliaLean.Proofs.base.int.eq_eq,
      show ¬ (xs.length : Int) * (cycles : Int) < n by omega,
      show (xs.length : Int) ≠ 0 by omega, show 0 < n by omega, hmod, hnth,
      -nthIterator_eq, -nthValue_eq, -Int.natCast_add, hxs]
  · rw [if_neg h]
    by_cases hlarge : (xs.length : Int) * (cycles : Int) < n
    · simp [nthFiniteCycleValue, sourceMethod1767, repeatedModel, listIterator_length,
        Except.map, hprod, hlarge, -nthIterator_eq, -nthValue_eq]
    · by_cases hempty : xs.length = 0
      · simp [nthFiniteCycleValue, sourceMethod1767, repeatedModel, listIterator_length,
          Except.map, hprod, hlarge, hxval, hzero, hempty, JuliaLean.Proofs.base.int.eq_eq,
          -nthIterator_eq, -nthValue_eq]
      · have hn : n ≤ 0 := by omega
        have hspec := nthModel_listIterator_spec xs n
        rw [if_neg (by omega)] at hspec
        simp [nthFiniteCycleValue, sourceMethod1767, repeatedModel, listIterator_length,
          Except.map, hprod, hlarge, hxval, hzero, JuliaLean.Proofs.base.int.eq_eq,
          show (xs.length : Int) ≠ 0 by omega, show ¬ 0 < n by omega, hspec.1,
          -nthIterator_eq, -nthValue_eq]

theorem IteratorscovOnlyNthMethods_proven : JuliaLean.Proofs.base.iterators.OnlyNthMethodSemantics := by
  refine ⟨onlyCorrect, nthVectorCorrect_proven, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α xs
    rfl
  · intro α x rest
    constructor <;> simp [onlyValue_eq, listIterator, listGet]
  · intro K V Name α d xs k v
    refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, ?_⟩
    · intro hlen
      obtain ⟨kv, hkv⟩ := List.length_eq_one_iff.mp hlen
      refine ⟨kv, hkv, ?_, ?_⟩ <;>
        simp [onlyFirstValue, onlyDictValue, sourceMethod1680, sourceMethod1673, hkv, listLastModel]
    · intro hlen
      refine ⟨"Collection must contain exactly 1 element", ?_, ?_⟩ <;>
        simp [onlyFirstValue, onlyDictValue, sourceMethod1680, sourceMethod1673, hlen]
    · rfl
  · intro α xs n
    rfl
  · intro α S itr n
    rfl
  · exact nthGeneric_from_protocol
  · exact nthZip_two_lists
  · intro α xs cycles n hx hc hp
    simpa only [nthFiniteDispatchValue, sourceMethod1755, pure_jl, ok_bind] using
      group5_finite_cycle_nth xs cycles n hx hc hp
  · intro α xs n
    refine ⟨?_, ?_, ?_⟩
    · intro h
      subst xs
      rfl
    · intro hx hn
      exact group5_cycle_nth_nonpos xs n hx hn
    · intro hx hn
      exact group5_cycle_nth_pos xs n hx hn

end JuliaLean.ChatGPT.Batch4.Group5

/- Supporting block: Queue37_39 -/
namespace JuliaLean.ChatGPT.Batch4.Group5
open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators

theorem group5_lit_self (n : JInt64) : JInt.lit .i64 n.val = n := by
  apply Subtype.ext
  exact wrapInt_of_inRange .i64 n.val n.property

theorem group5_takeTake_native {I : Type} (xs : I) (a b : JInt64)
    (ha : 0 ≤ a.val) (hb : 0 ≤ b.val) :
    CountValue.takeTake ⟨xs, a⟩ b.val =
      .ok ⟨xs, JInt.lit .i64 (min a.val b.val)⟩ := by
  by_cases hba : b.val ≤ a.val
  · simp only [CountValue.takeTake, takeTakeModel, CountValue.toInt,
      jint_convert_i64_self, ok_bind, pure_jl, CountValue.native_min,
      if_pos hba, CountValue.takeConstructor_eq, if_neg (by omega : ¬ b.val < 0),
      Int.min_eq_right hba, group5_lit_self]
  · simp only [CountValue.takeTake, takeTakeModel, CountValue.toInt,
      jint_convert_i64_self, ok_bind, pure_jl, CountValue.native_min,
      if_neg hba, CountValue.takeConstructor_eq, if_neg (by omega : ¬ a.val < 0),
      Int.min_eq_left (by omega : a.val ≤ b.val), group5_lit_self]

theorem group5_takeTake_correct : JuliaLean.Proofs.base.iterators.TakeTakeCorrect := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α xs a b ha hb
    by_cases hba : b.val ≤ a.val
    · refine ⟨⟨listIterator xs, b⟩, ?_, ?_⟩
      · simpa only [Int.min_eq_right hba, group5_lit_self] using
          group5_takeTake_native (listIterator xs) a b ha hb
      · have hnat : b.val.toNat ≤ a.val.toNat := by omega
        rw [Nat.min_eq_right hnat]
        exact group5_take_emits xs b hb
    · refine ⟨⟨listIterator xs, a⟩, ?_, ?_⟩
      · simpa only [Int.min_eq_left (by omega : a.val ≤ b.val), group5_lit_self] using
          group5_takeTake_native (listIterator xs) a b ha hb
      · have hnat : a.val.toNat ≤ b.val.toNat := by omega
        rw [Nat.min_eq_left hnat]
        exact group5_take_emits xs a ha
  · exact fun xs a b ha hb => group5_takeTake_native xs a b ha hb
  · intro I xs a b ha hb
    have hba : b.val ≤ a.val := by omega
    simp only [CountValue.takeTake, takeTakeModel, CountValue.toInt,
      jint_convert_i64_self, ok_bind, pure_jl, CountValue.native_min,
      if_pos hba, CountValue.takeConstructor_eq, if_pos hb]
  · intro I xs a b hb
    simp only [CountValue.takeTake, takeTakeModel, CountValue.toInt,
      jint_convert_i64_out b hb, err_bind]

theorem group5_take_done_state {α : Type} (xs : List α) (n rem : JInt64)
    (i : Nat) (hrem : 0 ≤ rem.val) :
    (takeObservation (listIterator xs) ⟨listIterator xs, n⟩).isdone (some (rem, i)) =
      .ok (some (decide (rem.val = 0 ∨ xs.length ≤ i))) := by
  have hzero : rem.val ≤ 0 ↔ rem.val = 0 := by omega
  by_cases hz : rem.val = 0 <;> by_cases hi : xs.length ≤ i <;>
    simp [takeObservation, AsObservation.view, group5_action_observe, takeIsdoneState,
      listIterator, observe, action, liftJl, boolOrMissing, ret, Bind.bind,
      JuliaLean.base.iterators.bind, Pure.pure, Except.pure, hzero, hz, hi]

theorem group5_take_done_iff {α : Type} (xs : List α) (n rem : JInt64)
    (i : Nat) (hrem : 0 ≤ rem.val) :
    ((takeObservation (listIterator xs) ⟨listIterator xs, n⟩).isdone (some (rem, i)) =
      .ok (some true) ↔
     (takeObservation (listIterator xs) ⟨listIterator xs, n⟩).run (some (rem, i)) = .ok none) := by
  rw [group5_take_done_state xs n rem i hrem, group5_take_run, takeStep_equation]
  simp only [Option.map_some, Option.getD_some]
  by_cases hz : rem.val ≤ 0
  · have hz' : rem.val = 0 := by omega
    simp [hz, hz']
  · rw [if_neg hz, listIterator_run_some]
    cases hd : xs.drop i with
    | nil =>
        have hi : xs.length ≤ i := List.drop_eq_nil_iff.mp hd
        simp only [hi, or_true, decide_true, ok_bind, pure_jl, observeJl_ok]
    | cons x rest =>
        have hi : ¬ xs.length ≤ i := by
          intro h
          have hn := List.drop_eq_nil_iff.mpr h
          rw [hd] at hn
          cases hn
        have hz' : rem.val ≠ 0 := by omega
        simp only [hz', hi, false_or, decide_false, ok_bind, pure_jl, observeJl_ok]
        constructor <;> intro h <;> cases h

theorem IteratorscovTake_proven : JuliaLean.Proofs.base.iterators.TakeSound := by
  refine ⟨group5_takeTake_correct, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun xs n hn => group5_take_emits xs n hn
  · intro I α S run done it xs n hn ht
    exact group5_take_emits_trace (protocolIterator run done it) xs ht n hn
  · intro I xs n hn
    exact ⟨mkTake_native xs n hn, takeModel_native xs n hn⟩
  · intro I xs n
    constructor
    · intro hn
      simp only [CountValue.rawTake, mkTake, pure_jl, ok_bind, decide_eq_true hn, if_true]
    · intro hn
      have hnonneg : ¬ n < 0 := by omega
      constructor
      · simp only [CountValue.rawTake, mkTake, CountValue.toInt, pure_jl, ok_bind,
          decide_eq_false hnonneg, Bool.false_eq_true, if_false,
          jint_convert_i64_out n (Or.inr hn), err_bind]
      · exact takeModel_int_of_ge_max xs n hn
  · intro I tag eltype iel isz t
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
    · cases h : isz t.xs <;> simp only [takeIteratorSizeOf, h,
        takeIteratorSize, takeIteratorSizeUnknown, reduceCtorEq]
    · intro h
      cases heq : isz t.xs <;> simp only [takeIteratorSizeOf, heq,
        takeIteratorSize, takeIteratorSizeUnknown]
      exact False.elim (h heq)
  · intro α xs n rem i hn hrem
    exact ⟨group5_take_done_state xs n rem i hrem,
      group5_take_done_iff xs n rem i hrem⟩

theorem IteratorscovFilter_proven : JuliaLean.Proofs.base.iterators.FilterSound :=
  filterSound_proven

theorem group5_collect_congr {I J α S : Type} {m : Type → Type} [Monad m]
    [CollectRun I α S m] [CollectRun J α S m] (left : I) (right : J)
    (hrun : ∀ st, CollectRun.run left st = CollectRun.run right st)
    (depth : Nat) (state : Option S) :
    JuliaLean.Proofs.base.iterators.collectPrefix left depth state = JuliaLean.Proofs.base.iterators.collectPrefix right depth state := by
  induction depth generalizing state with
  | zero => rfl
  | succ depth ih => simp only [JuliaLean.Proofs.base.iterators.collectPrefix, hrun, ih]

theorem group5_take_observation_congr {I J α S : Type}
    [AsObservation I α S] [AsObservation J α S] (left : I) (right : J)
    (hrun : ∀ st, (AsObservation.view left).run st = (AsObservation.view right).run st)
    (n : JInt64) (state : Option (JInt64 × S)) :
    (takeObservation left ⟨left, n⟩).run state =
      (takeObservation right ⟨right, n⟩).run state := by
  cases state with
  | none => simp only [takeObservation, iterateTake, hrun]
  | some state => cases state; simp only [takeObservation, iterateTake, hrun]

def group5_drop_model {α S : Type} (itr : IteratorModel α S) (n : JInt64) :
    IteratorModel α S :=
  { itr with run := dropFromRun itr.run n.val.toNat none }

theorem group5_drop_model_trace {α : Type} (xs : List α) (n : JInt64) :
    followsFrom (group5_drop_model (listIterator xs) n) none (xs.drop n.val.toNat) := by
  unfold followsFrom
  rw [group5_collect_eq_observe]
  change Round5.observe (dropFromRun (listIterator xs).run n.val.toNat none)
    ((xs.drop n.val.toNat).length + 1) none = .ok (xs.drop n.val.toNat)
  rw [observeDropFromRun, group5_observe_list_initial]
  have hlen : xs.length ≤ n.val.toNat + (xs.drop n.val.toNat).length + 1 := by
    rw [List.length_drop]
    omega
  rw [List.take_of_length_le hlen]
  rfl

theorem group5_drop_take_emits {α : Type} (xs : List α) (dropCount takeCount : JInt64)
    (hn : 0 ≤ takeCount.val) :
    emitsExactly
      (dropTakeObservation (listIterator xs) ⟨⟨listIterator xs, dropCount⟩, takeCount⟩)
      ((xs.drop dropCount.val.toNat).take takeCount.val.toNat) := by
  let left := dropObservation (listIterator xs) ⟨listIterator xs, dropCount⟩
  let right := group5_drop_model (listIterator xs) dropCount
  have hrun : ∀ st, (AsObservation.view left).run st = (AsObservation.view right).run st := by
    intro st
    change (dropObservation (listIterator xs) ⟨listIterator xs, dropCount⟩).run st =
      observeJl (dropFromRun (listIterator xs).run dropCount.val.toNat none st)
    rw [group5_drop_run, dropStep_refines]
  have ht := group5_take_emits_trace right (xs.drop dropCount.val.toNat)
    (group5_drop_model_trace xs dropCount) takeCount hn
  unfold emitsExactly at ht ⊢
  change JuliaLean.Proofs.base.iterators.collectPrefix (takeObservation left ⟨left, takeCount⟩)
    (((xs.drop dropCount.val.toNat).take takeCount.val.toNat).length + 1) none = _
  rw [group5_collect_congr _ (takeObservation right ⟨right, takeCount⟩)
    (fun st => group5_take_observation_congr left right hrun takeCount st)]
  exact ht

theorem group5_dropTake_native_step {I D : Type} (xs : I)
    (count dropCount remaining : JInt64) (dropInner : I → Int → Jl D) (d : D)
    (hd : dropInner xs dropCount.val = .ok d)
    (hmax : JuliaLean.base.int.jmax (JInt.lit .i64 0)
      (JuliaLean.base.int.sub_int count dropCount) = remaining)
    (hremaining : 0 ≤ remaining.val) :
    CountValue.dropTake (JInt.convert IntTy.i64.name .i64)
      (fun it k => dropInner it k.val) ⟨xs, count⟩ dropCount.val = .ok ⟨d, remaining⟩ := by
  simp only [CountValue.dropTake, dropTakeModel, jint_convert_i64_self,
    ok_bind, hd, pure_jl, hmax, CountValue.takeConstructor_eq,
    if_neg (by omega : ¬ remaining.val < 0)]

theorem group5_dropTake_native {I D : Type} (xs : I) (a : Nat) (b : JInt64)
    (dropInner : I → Int → Jl D) (d : D) (ha : a < 2 ^ 63)
    (hb : 0 ≤ b.val) (hd : dropInner xs b.val = .ok d) :
    CountValue.dropTake (JInt.convert IntTy.i64.name .i64)
      (fun it k => dropInner it k.val) ⟨xs, JInt.lit .i64 a⟩ b.val =
      .ok ⟨d, JInt.lit .i64 (Int.ofNat (a - b.val.toNat))⟩ := by
  have hav := group5_nat_count_val a ha
  simp only [Int.ofNat_eq_natCast] at hav
  have hsub : (JuliaLean.base.int.sub_int (JInt.lit .i64 a) b).val = (a : Int) - b.val := by
    rw [JuliaLean.Proofs.base.int.sub_int_val, hav]
    apply wrapInt_of_inRange
    have hbmax := b.property.2
    change b.val ≤ 2 ^ 63 - 1 at hbmax
    change -(2 ^ 63 : Int) ≤ (a : Int) - b.val ∧ (a : Int) - b.val ≤ 2 ^ 63 - 1
    constructor <;> omega
  have hmax : max (0 : Int) ((a : Int) - b.val) = Int.ofNat (a - b.val.toNat) := by
    simp only [Int.ofNat_eq_natCast]
    omega
  have hzero : (JInt.lit .i64 0).val = 0 := rfl
  have hfit : a - b.val.toNat < 2 ^ 63 := by omega
  have hremaining := group5_nat_count_val (a - b.val.toNat) hfit
  have hmaximum := CountValue.native_max (JInt.lit .i64 0)
    (JuliaLean.base.int.sub_int (JInt.lit .i64 a) b)
  rw [hzero, hsub, hmax] at hmaximum
  apply group5_dropTake_native_step xs (JInt.lit .i64 a) b _ dropInner d hd hmaximum
  rw [hremaining]
  simp only [Int.ofNat_eq_natCast]
  omega

theorem group5_dropDrop_native_step {I : Type} (xs : I)
    (count extra total : JInt64)
    (hadd : JuliaLean.base.int.add_int extra count = total)
    (htotal : 0 ≤ total.val) :
    CountValue.dropDrop ⟨xs, count⟩ extra.val = .ok ⟨xs, total⟩ := by
  simp only [CountValue.dropDrop, dropDropModel, CountValue.toInt, jint_convert_i64_self,
    ok_bind, hadd, CountValue.dropConstructor_eq,
    if_neg (by omega : ¬ total.val < 0)]

theorem group5_dropDrop_native {I : Type} (xs : I) (a b : Nat)
    (hab : a + b < 2 ^ 63) :
    CountValue.dropDrop ⟨xs, JInt.lit .i64 a⟩ (Int.ofNat b) =
      .ok ⟨xs, JInt.lit .i64 (Int.ofNat (a + b))⟩ := by
  have ha : a < 2 ^ 63 := by omega
  have hb : b < 2 ^ 63 := by omega
  have hbval := group5_nat_count_val b hb
  have hav := group5_nat_count_val a ha
  simp only [Int.ofNat_eq_natCast] at hbval hav
  have hadd : JuliaLean.base.int.add_int (JInt.lit .i64 b) (JInt.lit .i64 a) =
      JInt.lit .i64 (Int.ofNat (a + b)) := by
    apply Subtype.ext
    rw [JuliaLean.Proofs.base.int.add_int_val, hbval, hav]
    change wrapInt .i64 ((b : Int) + (a : Int)) = wrapInt .i64 (Int.ofNat (a + b))
    apply congrArg (wrapInt .i64)
    simp only [Int.ofNat_eq_natCast]
    omega
  have htotal : 0 ≤ (JInt.lit .i64 (Int.ofNat (a + b))).val := by
    rw [group5_nat_count_val (a + b) hab]
    simp only [Int.ofNat_eq_natCast]
    omega
  have result := group5_dropDrop_native_step xs (JInt.lit .i64 a) (JInt.lit .i64 b)
    (JInt.lit .i64 (Int.ofNat (a + b))) hadd htotal
  rw [hbval] at result
  exact result

theorem group5_dropTake_model_error {I D N : Type}
    (toInt : N → Jl JInt64) (dropInner : I → JInt64 → Jl D)
    (maximum : JInt64 → JInt64 → Jl JInt64) (construct : D → JInt64 → Jl (Take D))
    (xs : Take I) (n : N) (count : JInt64) (error : JlError)
    (hn : toInt n = .ok count) (hd : dropInner xs.xs count = .error error) :
    dropTakeModel toInt dropInner maximum construct xs n = .error error := by
  unfold dropTakeModel
  rw [hn, ok_bind, hd, err_bind]

theorem group5_dropTake_native_error {I D : Type} (xs : I)
    (count dropCount : JInt64) (dropInner : I → Int → Jl D) (error : JlError)
    (hd : dropInner xs dropCount.val = .error error) :
    CountValue.dropTake (JInt.convert IntTy.i64.name .i64)
      (fun it k => dropInner it k.val) ⟨xs, count⟩ dropCount.val = .error error := by
  exact group5_dropTake_model_error (JInt.convert IntTy.i64.name .i64)
    (fun it k => dropInner it k.val) (fun a b => pure (JuliaLean.base.int.jmax a b))
    CountValue.takeConstructor ⟨xs, count⟩ dropCount.val dropCount error
    (jint_convert_i64_self dropCount) hd

theorem group5_dropTake_negative {I : Type} (xs : I) (count dropCount : JInt64)
    (hn : dropCount.val < 0) :
    CountValue.dropTake (JInt.convert IntTy.i64.name .i64)
      (fun it k => CountValue.drop it k.val) ⟨xs, count⟩ dropCount.val =
      .error (.argumentError "Drop length must be non-negative") := by
  have hdrop : CountValue.drop xs dropCount.val =
      .error (.argumentError "Drop length must be non-negative") := by
    simp only [CountValue.drop, dropModel, CountValue.toInt, jint_convert_i64_self,
      ok_bind, CountValue.dropConstructor_eq, if_pos hn]
  exact group5_dropTake_native_error xs count dropCount
    (fun it k => CountValue.drop it k) _ hdrop

theorem group5_dropTake_list {α : Type} (xs : List α) (a : Nat) (b : JInt64)
    (ha : a < 2 ^ 63) (hb : 0 ≤ b.val) :
    ∃ td, CountValue.dropTake (JInt.convert IntTy.i64.name .i64)
      (fun it k => CountValue.drop it k.val) ⟨listIterator xs, JInt.lit .i64 a⟩ b.val = .ok td ∧
      emitsExactly (dropTakeObservation (listIterator xs) td)
        ((xs.drop b.val.toNat).take (a - b.val.toNat)) := by
  let remaining := JInt.lit .i64 (Int.ofNat (a - b.val.toNat))
  have hremaining : remaining.val = Int.ofNat (a - b.val.toNat) :=
    group5_nat_count_val (a - b.val.toNat) (by omega)
  have hremainingNat : remaining.val.toNat = a - b.val.toNat := by
    rw [hremaining]
    rfl
  refine ⟨⟨⟨listIterator xs, b⟩, remaining⟩, ?_, ?_⟩
  · exact group5_dropTake_native (listIterator xs) a b (fun it k => CountValue.drop it k)
      ⟨listIterator xs, b⟩ ha hb (dropModel_native _ b hb)
  · have hnonnegative : 0 ≤ remaining.val := by
      rw [hremaining]
      exact Int.ofNat_zero_le _
    have h := group5_drop_take_emits xs b remaining hnonnegative
    rw [hremainingNat] at h
    exact h

theorem IteratorscovDrop_proven : JuliaLean.Proofs.base.iterators.DropSound := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun xs n _ => group5_drop_emits xs n
  · intro I α S run done it xs n hn ht
    exact group5_drop_emits_trace (protocolIterator run done it) xs ht n
  · intro I xs n hn
    exact ⟨mkDrop_native xs n hn, dropModel_native xs n hn⟩
  · intro I xs n
    constructor
    · intro hn
      simp only [CountValue.rawDrop, mkDrop, pure_jl, ok_bind, decide_eq_true hn, if_true]
    · intro hn
      have hnonneg : ¬ n < 0 := by omega
      constructor
      · simp only [CountValue.rawDrop, mkDrop, CountValue.toInt, pure_jl, ok_bind,
          decide_eq_false hnonneg, Bool.false_eq_true, if_false,
          jint_convert_i64_out n (Or.inr hn), err_bind]
      · simp only [CountValue.drop, dropModel, CountValue.toInt,
          jint_convert_i64_out n (Or.inr hn), err_bind]
  · exact group5_dropTake_list
  · exact group5_dropTake_native
  · intro I xs a b hb
    exact group5_dropTake_negative xs (JInt.lit .i64 a) b hb
  · exact group5_dropDrop_native
  · intro I S tag eltype iel isz done d s
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · cases h : isz d.xs <;> simp only [dropIteratorSizeOf, h,
        dropIteratorSizeFinite, dropIteratorSizeUnknown, dropIteratorSizeInfinite, reduceCtorEq]
    · cases h : isz d.xs <;> simp only [dropIteratorSizeOf, h,
        dropIteratorSizeFinite, dropIteratorSizeUnknown, dropIteratorSizeInfinite, reduceCtorEq]

end JuliaLean.ChatGPT.Batch4.Group5

/- Supporting block: Queue41 -/
namespace JuliaLean.ChatGPT.Batch4.Group5
open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators

theorem IteratorscovWhile_proven : JuliaLean.Proofs.base.iterators.WhileSound := by
  refine ⟨IteratorsTakewhileDropwhile_proven, ?_⟩
  intro I P pred xs eltype iel
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end JuliaLean.ChatGPT.Batch4.Group5

/- Supporting block: Queue24Bounded -/
namespace JuliaLean.ChatGPT.Batch4.Group5
open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators

abbrev group5_partition_nat (n : Nat) : JInt64 := JInt.lit .i64 (n : Int)

theorem group5_partition_nat_val (n : Nat) (hn : n < 2 ^ 63) :
    (group5_partition_nat n).val = (n : Int) := by
  simpa only [Int.ofNat_eq_natCast] using group5_nat_count_val n hn

theorem group5_partition_nat_add (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    group5_partition_nat a + group5_partition_nat b = group5_partition_nat (a + b) := by
  apply Subtype.ext
  change wrapInt .i64 ((group5_partition_nat a).val + (group5_partition_nat b).val) =
    wrapInt .i64 ((a + b : Nat) : Int)
  rw [group5_partition_nat_val a ha, group5_partition_nat_val b hb]
  simp only [Int.natCast_add]

theorem group5_partition_nat_sub_one (a : Nat) (ha : a < 2 ^ 63) (hpos : 0 < a) :
    group5_partition_nat a - group5_partition_nat 1 = group5_partition_nat (a - 1) := by
  apply Subtype.ext
  change wrapInt .i64 ((group5_partition_nat a).val - (group5_partition_nat 1).val) =
    wrapInt .i64 ((a - 1 : Nat) : Int)
  rw [group5_partition_nat_val a ha, group5_partition_nat_val 1 (by decide)]
  apply congrArg (wrapInt .i64)
  omega

/-- One native vector step, with the effectful plumbing evaluated once. -/
theorem group5_partition_vector_run {α : Type} (xs : List α) (n s : JInt64) :
    (partitionVectorObservation ⟨xs, n⟩).run (some s) =
      observeJl (if decide ((JInt.lit .i64 (xs.length : Int)).val < s.val) then .ok none else
        let stop0 := s + n - JInt.lit .i64 1
        let stop := if stop0.val ≤ (JInt.lit .i64 (xs.length : Int)).val then stop0
          else JInt.lit .i64 (xs.length : Int)
        .ok (some ((xs.drop (s.val - 1).toNat).take (stop.val - s.val + 1).toNat,
          stop + JInt.lit .i64 1))) := by
  rfl

theorem group5_partition_vector_stop_raw {α : Type} (xs : List α) (n s : JInt64)
    (hgt : (JInt.lit .i64 (xs.length : Int)).val < s.val) :
    (partitionVectorObservation ⟨xs, n⟩).run (some s) = .ok none := by
  rw [group5_partition_vector_run]
  simp only [hgt, decide_true, ↓reduceIte, observeJl, observe, liftJl]

theorem group5_partition_vector_live_raw {α : Type} (xs : List α) (n s : JInt64)
    (hgt : ¬ (JInt.lit .i64 (xs.length : Int)).val < s.val) :
    (partitionVectorObservation ⟨xs, n⟩).run (some s) =
      let stop0 := s + n - JInt.lit .i64 1
      let stop := if stop0.val ≤ (JInt.lit .i64 (xs.length : Int)).val then stop0
        else JInt.lit .i64 (xs.length : Int)
      .ok (some ((xs.drop (s.val - 1).toNat).take (stop.val - s.val + 1).toNat,
        stop + JInt.lit .i64 1)) := by
  rw [group5_partition_vector_run]
  simp only [hgt, decide_false, Bool.false_eq_true, ↓reduceIte, observeJl, observe, liftJl]

/-- The bounded vector protocol stops at the first index after the array. -/
theorem group5_partition_vector_stop {α : Type} (xs : List α) (n : Nat)
    (hn : 0 < n) (hbound : xs.length + n < 2 ^ 63) :
    (partitionVectorObservation ⟨xs, group5_partition_nat n⟩).run
      (some (group5_partition_nat (xs.length + 1))) = .ok none := by
  have hl := group5_partition_nat_val xs.length (by omega : xs.length < 2 ^ 63)
  have hs := group5_partition_nat_val (xs.length + 1) (by omega : xs.length + 1 < 2 ^ 63)
  have hgt : (group5_partition_nat xs.length).val <
      (group5_partition_nat (xs.length + 1)).val := by rw [hl, hs]; omega
  exact group5_partition_vector_stop_raw xs _ _ hgt

/-- A live bounded vector step yields one mathematical chunk and a representable next index. -/
theorem group5_partition_vector_step {α : Type} (xs : List α) (n a : Nat)
    (hn : 0 < n) (hbound : xs.length + n < 2 ^ 63) (ha : a < xs.length) :
    (partitionVectorObservation ⟨xs, group5_partition_nat n⟩).run
      (some (group5_partition_nat (a + 1))) =
      .ok (some ((xs.drop a).take n,
        group5_partition_nat (min (a + n) xs.length + 1))) := by
  have hl := group5_partition_nat_val xs.length (by omega : xs.length < 2 ^ 63)
  have hs := group5_partition_nat_val (a + 1) (by omega : a + 1 < 2 ^ 63)
  have he := group5_partition_nat_val (a + n) (by omega : a + n < 2 ^ 63)
  have hm := group5_partition_nat_val (min (a + n) xs.length)
    (by omega : min (a + n) xs.length < 2 ^ 63)
  have hgt : ¬ (group5_partition_nat xs.length).val <
      (group5_partition_nat (a + 1)).val := by rw [hl, hs]; omega
  have hadd : group5_partition_nat (a + 1) + group5_partition_nat n =
      group5_partition_nat (a + 1 + n) :=
    group5_partition_nat_add _ _ (by omega) (by omega)
  have hsub : group5_partition_nat (a + 1 + n) - JInt.lit .i64 1 =
      group5_partition_nat (a + n) := by
    change group5_partition_nat (a + 1 + n) - group5_partition_nat 1 = _
    rw [group5_partition_nat_sub_one _ (by omega) (by omega)]
    exact congrArg group5_partition_nat (by omega : a + 1 + n - 1 = a + n)
  have hminimum : (if (group5_partition_nat (a + n)).val ≤ (group5_partition_nat xs.length).val
      then group5_partition_nat (a + n) else group5_partition_nat xs.length) =
      group5_partition_nat (min (a + n) xs.length) := by
    rw [he, hl]
    by_cases hle : a + n ≤ xs.length
    · rw [if_pos (by omega), Nat.min_eq_left hle]
    · rw [if_neg (by omega), Nat.min_eq_right (by omega)]
  have haddOne : group5_partition_nat (min (a + n) xs.length) + JInt.lit .i64 1 =
      group5_partition_nat (min (a + n) xs.length + 1) :=
    group5_partition_nat_add _ _ (by omega) (by decide)
  have hdrop : ((group5_partition_nat (a + 1)).val - 1).toNat = a := by
    rw [hs]
    omega
  have htake : ((group5_partition_nat (min (a + n) xs.length)).val -
      (group5_partition_nat (a + 1)).val + 1).toNat = min (a + n) xs.length - a := by
    rw [hm, hs]
    omega
  rw [group5_partition_vector_live_raw xs _ _ hgt]
  simp only [hadd, hsub, hminimum, haddOne, hdrop, htake, partTake]

/-- A complete bounded trace follows the same ordinal sequence as chunksSpec. -/
theorem group5_partition_vector_trace_aux {α : Type} (xs : List α) (n : Nat)
    (hn : 0 < n) (hbound : xs.length + n < 2 ^ 63) :
    ∀ remaining i, i + remaining = (xs.length + n - 1) / n →
      finiteObservationTrace (partitionVectorObservation ⟨xs, group5_partition_nat n⟩).run
        (some (group5_partition_nat (min (i * n) xs.length + 1)))
        ((List.range' i remaining).map fun j => (xs.drop (j * n)).take n) := by
  intro remaining
  induction remaining with
  | zero =>
      intro i hi
      have hi' : ¬ i < (xs.length + n - 1) / n := by omega
      have hprod : xs.length ≤ i * n := by
        have hnot : ¬ i * n < xs.length := fun h => hi' ((partCount xs.length n i hn).mpr h)
        omega
      simp only [Nat.min_eq_right hprod, List.range'_zero, List.map_nil]
      exact .stop (group5_partition_vector_stop xs n hn hbound)
  | succ remaining ih =>
      intro i hi
      have hi' : i < (xs.length + n - 1) / n := by omega
      have hprod : i * n < xs.length := (partCount xs.length n i hn).mp hi'
      rw [List.range'_succ, List.map_cons]
      refine finiteObservationTrace.step
        (next := group5_partition_nat (min ((i + 1) * n) xs.length + 1)) ?_ ?_
      · rw [Nat.min_eq_left (Nat.le_of_lt hprod)]
        simpa only [Nat.add_mul, Nat.one_mul] using
          group5_partition_vector_step xs n (i * n) hn hbound hprod
      · exact ih (i + 1) (by omega)

theorem finiteObservationTrace_change_start {α S : Type}
    (run : Option S → Observation JlError (Option (α × S)))
    (st st' : Option S) (xs : List α) (heq : run st = run st')
    (h : finiteObservationTrace run st' xs) : finiteObservationTrace run st xs := by
  cases h with
  | stop hstop => exact .stop (heq.trans hstop)
  | step hstep htail => exact .step (heq.trans hstep) htail

/-- A separately bounded strengthening; the frozen universal target is unchanged. -/
theorem group5_partition_vector_bounded {α : Type} (xs : List α) (n : Nat)
    (hn : 0 < n) (hbound : xs.length + n < 2 ^ 63) :
    let itr := partitionVectorObservation ⟨xs, JInt.lit .i64 (Int.ofNat n)⟩
    emitsExactly itr (chunksSpec n xs) ∧ itr.length = .ok ((xs.length + n - 1) / n) := by
  have htrace := group5_partition_vector_trace_aux xs n hn hbound
    ((xs.length + n - 1) / n) 0 (by omega)
  simp only [Nat.zero_mul, Nat.min_eq_left (Nat.zero_le _), Nat.zero_add,
    ← List.range_eq_range'] at htrace
  have hchunks : chunksSpec n xs =
      (List.range ((xs.length + n - 1) / n)).map fun j => (xs.drop (j * n)).take n := by
    simp only [chunksSpec, Nat.ne_of_gt hn, ↓reduceIte]
  rw [← hchunks] at htrace
  have htrace0 := finiteObservationTrace_change_start
    (partitionVectorObservation ⟨xs, group5_partition_nat n⟩).run none
    (some (group5_partition_nat 1)) (chunksSpec n xs) rfl htrace
  constructor
  · unfold emitsExactly
    rw [group5_collect_eq_observe]
    exact finiteObservationTrace_reads _ htrace0
  · have hnval := group5_partition_nat_val n (by omega : n < 2 ^ 63)
    simp only [Int.ofNat_eq_natCast, partitionVectorObservation, partitionLength,
      pure_jl, ok_bind, hnval, Int.toNat_natCast]

end JuliaLean.ChatGPT.Batch4.Group5
end

section

namespace JuliaLean.ChatGPT.Batch5.Group5
open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators
open JuliaLean.ChatGPT.Batch4.Group5

/-- Dispatching through the iterator preserves its initial completion branch. -/
theorem b5_product_base_is_list (xs : List Int)
    (isdoneAfter : Option Nat → Jl (Option Bool))
    (h : ∀ st, isdoneAfter st = .ok (some (xs.length ≤ st.getD xs.length))) :
    ({ listIterator xs with isdone := fun st =>
      match st with | none => pure (some xs.isEmpty) | some s => isdoneAfter (some s) } :
      IteratorModel Int Nat) = listIterator xs := by
  have hdone : (fun st => match st with
      | none => pure (some xs.isEmpty)
      | some s => isdoneAfter (some s)) = (listIterator xs).isdone := by
    funext st
    cases st with
    | none => cases xs <;> rfl
    | some s => exact h (some s)
  rw [hdone]

/-- The one-factor emission clause holds when product uses the iterator's own
completion method, including its separately specified initial branch. -/
theorem b5_product_one_factor_dispatched (xs : List Int)
    (isdoneAfter : Option Nat → Jl (Option Bool))
    (h : ∀ st, isdoneAfter st = .ok (some (xs.length ≤ st.getD xs.length))) :
    let base := { listIterator xs with isdone := fun st =>
      match st with | none => pure (some xs.isEmpty) | some s => isdoneAfter (some s) }
    emitsExactly (productObservation (productModel [base])
      (fun itr state => itr.isdone state) (fun itr state => itr.run state)
      (fun _ => Int) (fun _ value _ => pure value))
      (xs.map fun x => [x]) := by
  dsimp only
  rw [b5_product_base_is_list xs isdoneAfter h]
  change emitsExactly (listProductObservation [xs]) (xs.map fun x => [x])
  unfold emitsExactly
  rw [collectEqObserveRun]
  change observeRun (listProductObservation [xs]).run
    ((xs.map fun x => [x]).length + 1) none = .ok (xs.map fun x => [x])
  rw [listProductInitialReads]
  simp only [r6CartesianRows, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.take_of_length_le (Nat.le_succ _)]

/-- Public native construction and the complete vector emission/length clause,
under the bound needed by native endpoint arithmetic. -/
theorem b5_partition_public_bounded {α : Type} (xs : List α) (n : JInt64)
    (hn : 1 ≤ n.val) (hbound : xs.length + n.val.toNat < 2 ^ 63) :
    ∃ p, partitionNativeConstruct xs n.val
      (fun v k => sourceMethod1447 v (JInt.lit .i64 (Int.ofNat k))) = .ok p ∧
      emitsExactly (partitionVectorObservation p) (chunksSpec n.val.toNat xs) ∧
      (partitionVectorObservation p).length =
        .ok ((xs.length + n.val.toNat - 1) / n.val.toNat) := by
  refine ⟨⟨xs, JInt.lit .i64 (Int.ofNat n.val.toNat)⟩, ?_, ?_⟩
  · exact (partitionArrayConstructs id xs n hn).1
  · exact group5_partition_vector_bounded xs n.val.toNat (by omega) hbound

/-- The read-only and exhaustion clauses hold for every stored cache policy. -/
theorem b5_snapshot_observation_and_exhaustion {I α S VS β : Type}
    (iterate : I → Option S → Jl (Option (α × S)))
    (s : StatefulSnapshot I VS (α × S)) (sentinel : β) :
    let isdoneFn : StatefulSnapshot I VS (α × S) → List (α × Unit) → Option Bool :=
      fun stf _ => match isdoneSnapshot stf with | .ok b => some b | _ => none
    let iterateFn : StatefulSnapshot I VS (α × S) → List (α × Unit) →
        Option ((α × Unit) × List (α × Unit)) :=
      fun stf _ => match iterateSnapshot iterate stf with
        | .ok (some step, _) => some (step, [])
        | _ => none
    JuliaLean.base.essentials.isempty isdoneFn iterateFn s = s.nextvalstate.isNone ∧
    isdoneSnapshot s = .ok s.nextvalstate.isNone ∧
    (s.nextvalstate = none →
      peekSnapshot s sentinel = .ok (Sum.inr sentinel) ∧
      popSnapshot iterate s = .error .eofError ∧
      iterateSnapshot iterate s = .ok (none, s)) := by
  refine ⟨rfl, rfl, ?_⟩
  intro hnone
  refine ⟨?_, group5_snapshot_pop_empty iterate s hnone,
    group5_snapshot_iterate_empty iterate s hnone⟩
  rw [group5_snapshot_peek, hnone]

/-- A live transition includes all observable clauses once the actual next
cache value is accepted unchanged by the stored assertion. -/
theorem b5_snapshot_live_checked {I α S VS β : Type}
    (iterate : I → Option S → Jl (Option (α × S)))
    (s : StatefulSnapshot I VS (α × S)) (sentinel : β) (value : α) (state : S)
    (hp : s.nextvalstate = some (value, state)) :
    isdoneSnapshot s = .ok false ∧
    peekSnapshot s sentinel = .ok (Sum.inl value) ∧
    (∀ next, iterate s.itr (some state) = .ok next →
      s.assertValue next s.cacheType = .ok next →
      popSnapshot iterate s = .ok (value, { s with nextvalstate := next }) ∧
      iterateSnapshot iterate s =
        .ok (some (value, ()), { s with nextvalstate := next })) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [group5_snapshot_done, hp]
    rfl
  · rw [group5_snapshot_peek, hp]
  · intro next hr ha
    exact group5_snapshot_transition_checked iterate s value state next hp hr ha

/-- Complete default-cache list behavior at an arbitrary consumed prefix. -/
theorem b5_snapshot_default_list {α : Type} (xs : List α) (pos : Nat) (sentinel : α) :
    let s : StatefulSnapshot (IteratorModel α Nat) (α × Nat) :=
      { itr := listIterator xs, nextvalstate := statefulCurAt xs pos }
    let isdoneFn : StatefulSnapshot (IteratorModel α Nat) (α × Nat) →
        List (α × Unit) → Option Bool :=
      fun stf _ => match isdoneSnapshot stf with | .ok b => some b | _ => none
    let iterateFn : StatefulSnapshot (IteratorModel α Nat) (α × Nat) →
        List (α × Unit) → Option ((α × Unit) × List (α × Unit)) :=
      fun stf _ => match iterateSnapshot (fun _ st => (listIterator xs).run st) stf with
        | .ok (some step, _) => some (step, [])
        | _ => none
    isdoneSnapshot s = .ok (xs.drop pos).isEmpty ∧
    JuliaLean.base.essentials.isempty isdoneFn iterateFn s = (xs.drop pos).isEmpty ∧
    peekSnapshot s sentinel =
      .ok (match xs.drop pos with | [] => Sum.inr sentinel | x :: _ => Sum.inl x) ∧
    collectSnapshots (fun _ st => (listIterator xs).run st) ((xs.drop pos).length + 1) s =
      .ok (xs.drop pos, { itr := listIterator xs, nextvalstate := none }) ∧
    (xs.drop pos = [] →
      popSnapshot (fun _ st => (listIterator xs).run st) s = .error .eofError) ∧
    (∀ x rest, xs.drop pos = x :: rest →
      ∃ sNext, popSnapshot (fun _ st => (listIterator xs).run st) s = .ok (x, sNext) ∧
        iterateSnapshot (fun _ st => (listIterator xs).run st) s =
          .ok (some (x, ()), sNext) ∧
        collectSnapshots (fun _ st => (listIterator xs).run st) (rest.length + 1) sNext =
          .ok (rest, { itr := listIterator xs, nextvalstate := none })) := by
  dsimp only
  refine ⟨?_, ?_, ?_, group5_snapshot_list_trace xs pos, ?_, ?_⟩
  · rw [group5_snapshot_done]
    unfold statefulCurAt
    cases xs.drop pos <;> rfl
  · change (statefulCurAt xs pos).isNone = (xs.drop pos).isEmpty
    unfold statefulCurAt
    cases xs.drop pos <;> rfl
  · rw [group5_snapshot_peek]
    unfold statefulCurAt
    cases xs.drop pos <;> rfl
  · intro hempty
    apply group5_snapshot_pop_empty
    simp only [statefulCurAt, hempty]
  · intro x rest hrest
    have hnext : xs.drop (pos + 1) = rest := by
      rw [← List.drop_drop, hrest]
      rfl
    let sNext : StatefulSnapshot (IteratorModel α Nat) (α × Nat) :=
      { itr := listIterator xs, nextvalstate := statefulCurAt xs (pos + 1) }
    have hp : statefulCurAt xs pos = some (x, pos + 1) := by
      simp only [statefulCurAt, hrest]
    have hr := group5_snapshot_list_run xs (pos + 1)
    have hstep := group5_snapshot_transition_checked
      (fun _ st => (listIterator xs).run st)
      ({ itr := listIterator xs, nextvalstate := statefulCurAt xs pos } :
        StatefulSnapshot (IteratorModel α Nat) (α × Nat))
      x (pos + 1) (statefulCurAt xs (pos + 1)) hp hr rfl
    refine ⟨sNext, hstep.1, hstep.2, ?_⟩
    have hc := group5_snapshot_list_trace (VS := α × Nat) xs (pos + 1)
    rw [hnext] at hc
    exact hc

/-- Full useful consistency contract. This differs from the frozen target only
by the explicit acceptance premise in its generic live transition. The target
itself is not asserted; proposed-repairs/REPAIRS.md identifies this review candidate. -/
theorem b5_stateful_consistency_checked :
  (∀ {α : Type} (xs : List α) (pos : Nat) (sentinel : α),
    let s : StatefulSnapshot (IteratorModel α Nat) (α × Nat) := { itr := listIterator xs, nextvalstate := statefulCurAt xs pos }
    let isdoneFn : StatefulSnapshot (IteratorModel α Nat) (α × Nat) → List (α × Unit) → Option Bool :=
      fun stf _ => match isdoneSnapshot stf with | .ok b => some b | _ => none
    let iterateFn : StatefulSnapshot (IteratorModel α Nat) (α × Nat) → List (α × Unit) → Option ((α × Unit) × List (α × Unit)) :=
      fun stf _ => match iterateSnapshot (fun _ st => (listIterator xs).run st) stf with
        | .ok (some step, _) => some (step, [])
        | _ => none
    isdoneSnapshot s = .ok (xs.drop pos).isEmpty ∧
    JuliaLean.base.essentials.isempty isdoneFn iterateFn s = (xs.drop pos).isEmpty ∧
    peekSnapshot s sentinel =
      .ok (match xs.drop pos with | [] => Sum.inr sentinel | x :: _ => Sum.inl x) ∧
    collectSnapshots (fun _ st => (listIterator xs).run st) ((xs.drop pos).length + 1) s =
      .ok (xs.drop pos, { itr := listIterator xs, nextvalstate := none }) ∧
    (xs.drop pos = [] →
      popSnapshot (fun _ st => (listIterator xs).run st) s = .error .eofError) ∧
    (∀ x rest, xs.drop pos = x :: rest →
      ∃ sNext, popSnapshot (fun _ st => (listIterator xs).run st) s = .ok (x, sNext) ∧
        iterateSnapshot (fun _ st => (listIterator xs).run st) s = .ok (some (x, ()), sNext) ∧
        collectSnapshots (fun _ st => (listIterator xs).run st) (rest.length + 1) sNext =
          .ok (rest, { itr := listIterator xs, nextvalstate := none }))) ∧
  (∀ {α : Type} (xs : List α),
    (do
      let s0 ← (statefulAnySnapshot (fun _ st => (listIterator xs).run st) (listIterator xs) : Observation IteratorError _)
      collectSnapshots (fun _ st => (listIterator xs).run st) (xs.length + 1) s0) =
    .ok (xs, ({ itr := listIterator xs, nextvalstate := none } :
      StatefulSnapshot (IteratorModel α Nat) AnyCache (α × Nat)))) ∧
  (∀ {I α S VS β : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (s : StatefulSnapshot I VS (α × S)) (sentinel : β),
    let isdoneFn : StatefulSnapshot I VS (α × S) → List (α × Unit) → Option Bool :=
      fun stf _ => match isdoneSnapshot stf with | .ok b => some b | _ => none
    let iterateFn : StatefulSnapshot I VS (α × S) → List (α × Unit) → Option ((α × Unit) × List (α × Unit)) :=
      fun stf _ => match iterateSnapshot iterate stf with
        | .ok (some step, _) => some (step, [])
        | _ => none
    JuliaLean.base.essentials.isempty isdoneFn iterateFn s = s.nextvalstate.isNone ∧
    isdoneSnapshot s = .ok s.nextvalstate.isNone ∧
    (s.nextvalstate = none →
      peekSnapshot s sentinel = .ok (Sum.inr sentinel) ∧
      popSnapshot iterate s = .error .eofError ∧
      iterateSnapshot iterate s = .ok (none, s))) ∧
  (∀ {I α S VS β : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (s : StatefulSnapshot I VS (α × S)) (sentinel : β) (value : α) (state : S),
    s.nextvalstate = some (value, state) →
    isdoneSnapshot s = .ok false ∧
    peekSnapshot s sentinel = .ok (Sum.inl value) ∧
    (∀ next, iterate s.itr (some state) = .ok next →
      s.assertValue next s.cacheType = .ok next →
      popSnapshot iterate s = .ok (value, { s with nextvalstate := next }) ∧
      iterateSnapshot iterate s =
        .ok (some (value, ()), { s with nextvalstate := next }))) ∧
  (∀ {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
      (isdone : I → Option S → Jl (Option Bool)) (itr : I) (xs : List α),
      followsProtocol iterate isdone itr xs →
      ∃ s0 : StatefulSnapshot I AnyCache (α × S),
        (statefulAnySnapshot iterate itr : Observation IteratorError _) = .ok s0 ∧
        collectSnapshots iterate (xs.length + 1) s0 =
          .ok (xs, ({ itr := itr, nextvalstate := none } : StatefulSnapshot I AnyCache (α × S)))) := by
  refine ⟨b5_snapshot_default_list, ?_, b5_snapshot_observation_and_exhaustion,
    b5_snapshot_live_checked, group5_snapshot_any_trace⟩
  intro α xs
  rw [group5_snapshot_any_run (fun _ st => (listIterator xs).run st)
    (listIterator xs) (statefulCurAt xs 0) (group5_snapshot_list_initial xs)]
  change collectSnapshots (fun _ st => (listIterator xs).run st) (xs.length + 1)
    ({ itr := listIterator xs, nextvalstate := statefulCurAt xs 0 } :
      StatefulSnapshot (IteratorModel α Nat) AnyCache (α × Nat)) = _
  simpa only [List.drop_zero] using
    group5_snapshot_list_trace (VS := AnyCache) xs 0

/-- Every method clause after StatefulConsistent is discharged independently.
This isolates the exact frozen target's remaining obstruction to its first
conjunct, without assuming that defective conjunct. -/
theorem b5_stateful_method_remainder :
  (∀ {α : Type} (xs ys : List α),
    (do
      let s0 ← (statefulAnySnapshot (fun _ st => (listIterator xs).run st) (listIterator xs) : Observation IteratorError _)
      let (out1, s1) ← collectSnapshots (fun _ st => (listIterator xs).run st) (xs.length + 1) s0
      let s2 ← (resetSnapshot (fun _ st => (listIterator xs).run st) s1 : Observation IteratorError _)
      let (out2, s3) ← collectSnapshots (fun _ st => (listIterator xs).run st) (xs.length + 1) s2
      let s4 ← (resetSnapshotTo (fun (it : IteratorModel α Nat) st => it.run st) s3 (listIterator ys) : Observation IteratorError _)
      let (out3, _) ← collectSnapshots (fun _ st => (listIterator ys).run st) (ys.length + 1) s4
      pure (out1, out2, out3)) = .ok (xs, xs, ys)) ∧
  (∀ {α : Type} (xs : List α),
    let s : StatefulSnapshot (IteratorModel α Nat) (α × Nat) := { itr := listIterator xs, nextvalstate := statefulCurAt xs 0 }
    statefulAnySnapshot (fun _ st => (listIterator xs).run st) (listIterator xs) =
      .ok ({ itr := listIterator xs, nextvalstate := statefulCurAt xs 0 } :
        StatefulSnapshot (IteratorModel α Nat) AnyCache (α × Nat)) ∧
    sourceMethod1605 s = s ∧
    sourceMethod1606 (statefulAnySnapshot (fun _ st => (listIterator xs).run st)) (listIterator xs) =
      statefulAnySnapshot (fun _ st => (listIterator xs).run st) (listIterator xs) ∧
    sourceMethod1626 α s = α ∧
    sourceMethod1627 .hasEltype s = .hasEltype) ∧
  (∀ {I α S : Type} (iterate : I → Option S → Jl (Option (α × S))) (itr : I) (x : α) (st : S),
    sourceMethod1592 iterate itr none = .ok none ∧
    sourceMethod1592 iterate itr (some (x, st)) = iterate itr (some st)) ∧
  StatefulApproximation ∧
  StatefulConstructorSemantics ∧
  (∀ (tag : IteratorSizeTag),
    (sourceMethod1625 tag = .isInfinite ↔ tag = .isInfinite) ∧
    (tag ≠ .isInfinite → sourceMethod1625 tag = .sizeUnknown)) := by
  refine ⟨group5_snapshot_list_roundtrip, ?_, ?_, statefulApproximation,
    group5_stateful_constructor, group5_snapshot_size⟩
  · intro α xs
    refine ⟨?_, rfl, rfl, rfl, rfl⟩
    exact group5_snapshot_any_run (fun _ st => (listIterator xs).run st)
      (listIterator xs) (statefulCurAt xs 0) (group5_snapshot_list_initial xs)
  · intro I α S run itr x state
    exact ⟨rfl, rfl⟩

/-- Exact live behavior exposes the cache assertion's result, including rejection
and successful transformation. This is a model equation, not a Julia refutation. -/
theorem b5_snapshot_live_result {I α S VS : Type}
    (iterate : I → Option S → Jl (Option (α × S)))
    (s : StatefulSnapshot I VS (α × S)) (value : α) (state : S)
    (next : Option (α × S)) (hp : s.nextvalstate = some (value, state))
    (hr : iterate s.itr (some state) = .ok next) :
    popSnapshot iterate s =
      (match s.assertValue next s.cacheType with
      | .error e => .error (.julia e)
      | .ok checked => .ok (value, { s with nextvalstate := checked })) ∧
    iterateSnapshot iterate s =
      (match s.assertValue next s.cacheType with
      | .error e => .error (.julia e)
      | .ok checked => .ok (some (value, ()), { s with nextvalstate := checked })) := by
  cases s with
  | mk itr current cacheType assertValue cacheTypeOf =>
    cases hp
    change iterate itr (some state) = .ok next at hr
    constructor
    · unfold popSnapshot snapshotOutcome popfirstStateful setCache
      simp only [snapshotOps, Bind.bind, JuliaLean.base.iterators.bind,
        Pure.pure, ret, hr, Except.mapError]
      cases assertValue next cacheType <;> rfl
    · unfold iterateSnapshot snapshotOutcome iterateStateful popfirstStateful setCache
      simp only [snapshotOps, Bind.bind, JuliaLean.base.iterators.bind,
        Pure.pure, ret, hr, Except.mapError,
        Option.isNone_some, Bool.false_eq_true, ite_false]
      cases assertValue next cacheType <;> rfl

/-- For a successful next iterator step, preservation of the exact next cache is
necessary as well as sufficient for the target's claimed pop transition. -/
theorem b5_snapshot_pop_iff_cache_accepts {I α S VS : Type}
    (iterate : I → Option S → Jl (Option (α × S)))
    (s : StatefulSnapshot I VS (α × S)) (value : α) (state : S)
    (next : Option (α × S)) (hp : s.nextvalstate = some (value, state))
    (hr : iterate s.itr (some state) = .ok next) :
    (popSnapshot iterate s = .ok (value, { s with nextvalstate := next })) ↔
      s.assertValue next s.cacheType = .ok next := by
  rw [(b5_snapshot_live_result iterate s value state next hp hr).1]
  cases ha : s.assertValue next s.cacheType with
  | error e => simp only [reduceCtorEq]
  | ok checked =>
      constructor
      · intro heq
        have hs : { s with nextvalstate := checked } = { s with nextvalstate := next } :=
          congrArg Prod.snd (Observation.ok.inj heq)
        have hc : checked = next := congrArg StatefulSnapshot.nextvalstate hs
        exact congrArg Except.ok hc
      · intro heq
        cases heq
        rfl

end JuliaLean.ChatGPT.Batch5.Group5


namespace JuliaLean.ChatGPT.Batch5.Group5
open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators
open JuliaLean.ChatGPT.Batch4.Group5

/-- The first vector-partition endpoint is the count, even when the intermediate addition wraps. -/
theorem partitionOneAddCountSubOne (n : JInt64) :
    JInt.lit .i64 1 + n - JInt.lit .i64 1 = n := by
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 ((JInt.lit .i64 1).val + n.val) -
    (JInt.lit .i64 1).val) = n.val
  have hone : (JInt.lit .i64 1).val = 1 := by decide
  rw [hone, JuliaLean.Proofs.base.int.wrapInt_sub_left]
  have heq : 1 + n.val - 1 = n.val := by omega
  rw [heq]
  exact wrapInt_of_inRange .i64 n.val n.property

/-- A nonempty vector shorter than its positive native count gives one complete first chunk. -/
theorem partitionLargeCountFirst {α : Type} (xs : List α) (n : Nat)
    (hpos : 0 < xs.length) (hle : xs.length ≤ n) (hn : n < 2 ^ 63)
    (hindex : xs.length + 1 < 2 ^ 63) :
    (partitionVectorObservation ⟨xs, group5_partition_nat n⟩).run none =
      .ok (some (xs, group5_partition_nat (xs.length + 1))) := by
  have hlen := group5_partition_nat_val xs.length (by omega : xs.length < 2 ^ 63)
  have hnval := group5_partition_nat_val n hn
  have hone : (group5_partition_nat 1).val = 1 := by decide
  have hlive : ¬ (JInt.lit .i64 (xs.length : Int)).val < (group5_partition_nat 1).val := by
    rw [hlen, hone]
    omega
  have hminimum : (if (group5_partition_nat n).val ≤ (group5_partition_nat xs.length).val
      then group5_partition_nat n else group5_partition_nat xs.length) =
      group5_partition_nat xs.length := by
    rw [hnval, hlen]
    split
    · have he : n = xs.length := by omega
      rw [he]
    · rfl
  change (partitionVectorObservation ⟨xs, group5_partition_nat n⟩).run
      (some (group5_partition_nat 1)) = _
  rw [group5_partition_vector_live_raw xs _ _ hlive]
  dsimp only
  have hcancel : group5_partition_nat 1 + group5_partition_nat n - JInt.lit .i64 1 =
      group5_partition_nat n := partitionOneAddCountSubOne (group5_partition_nat n)
  rw [hcancel]
  rw [hminimum, hone, hlen]
  have htake : ((xs.length : Int) - 1 + 1).toNat = xs.length := by omega
  have hnext : group5_partition_nat xs.length + JInt.lit .i64 1 =
      group5_partition_nat (xs.length + 1) :=
    group5_partition_nat_add _ _ (by omega) (by decide)
  simp only [Int.sub_self, Int.toNat_zero, List.drop_zero, htake, List.take_length, hnext]

/-- The terminal index fits even when the count is the largest signed native integer. -/
theorem partitionStopAfterLargeCount {α : Type} (xs : List α) (n : Nat)
    (hindex : xs.length + 1 < 2 ^ 63) :
    (partitionVectorObservation ⟨xs, group5_partition_nat n⟩).run
      (some (group5_partition_nat (xs.length + 1))) = .ok none := by
  apply group5_partition_vector_stop_raw
  rw [group5_partition_nat_val xs.length (by omega),
    group5_partition_nat_val (xs.length + 1) hindex]
  omega

/-- Counts at least the nonzero vector length yield exactly one mathematical chunk. -/
theorem partitionChunksLargeCount {α : Type} (xs : List α) (n : Nat)
    (hpos : 0 < xs.length) (hle : xs.length ≤ n) :
    chunksSpec n xs = [xs] ∧ (xs.length + n - 1) / n = 1 := by
  have hn : 0 < n := by omega
  have hzero : 0 < (xs.length + n - 1) / n :=
    (partCount xs.length n 0 hn).mpr (by simpa only [Nat.zero_mul] using hpos)
  have hnot : ¬ 1 < (xs.length + n - 1) / n := by
    intro h
    have hmul := (partCount xs.length n 1 hn).mp h
    simp only [Nat.one_mul] at hmul
    omega
  have hcount : (xs.length + n - 1) / n = 1 := by omega
  refine ⟨?_, hcount⟩
  simp only [chunksSpec, Nat.ne_of_gt hn, ↓reduceIte, hcount, List.range_succ,
    List.range_zero, List.nil_append, List.map_cons, List.map_nil, Nat.zero_mul,
    List.drop_zero, List.take_of_length_le hle]

/-- Large representable counts are valid for a short vector without a length-plus-count bound. -/
theorem partitionVectorLargeCount {α : Type} (xs : List α) (n : Nat)
    (hpos : 0 < xs.length) (hle : xs.length ≤ n) (hn : n < 2 ^ 63)
    (hindex : xs.length + 1 < 2 ^ 63) :
    let itr := partitionVectorObservation ⟨xs, JInt.lit .i64 (Int.ofNat n)⟩
    emitsExactly itr (chunksSpec n xs) ∧ itr.length = .ok ((xs.length + n - 1) / n) := by
  have hfirst := partitionLargeCountFirst xs n hpos hle hn hindex
  have hstop := partitionStopAfterLargeCount xs n hindex
  have hchunks := (partitionChunksLargeCount xs n hpos hle).1
  have htrace : finiteObservationTrace
      (partitionVectorObservation ⟨xs, group5_partition_nat n⟩).run none [xs] :=
    .step hfirst (.stop hstop)
  constructor
  · rw [hchunks]
    unfold emitsExactly
    rw [group5_collect_eq_observe]
    exact finiteObservationTrace_reads _ htrace
  · have hnval := group5_partition_nat_val n hn
    simp only [Int.ofNat_eq_natCast, partitionVectorObservation, partitionLength,
      pure_jl, ok_bind, hnval, Int.toNat_natCast]

/-- A sufficient endpoint bound that uses only the smaller of the count and vector length. -/
theorem partitionVectorMinBound {α : Type} (xs : List α) (n : Nat)
    (hn : 0 < n) (hn64 : n < 2 ^ 63)
    (hbound : xs.length + min n xs.length < 2 ^ 63) :
    let itr := partitionVectorObservation ⟨xs, JInt.lit .i64 (Int.ofNat n)⟩
    emitsExactly itr (chunksSpec n xs) ∧ itr.length = .ok ((xs.length + n - 1) / n) := by
  by_cases he : xs = []
  · subst xs
    exact group5_partition_vector_bounded [] n hn (by simpa only [List.length_nil, Nat.zero_add] using hn64)
  · have hpos : 0 < xs.length := List.length_pos_iff.mpr he
    by_cases hle : xs.length ≤ n
    · have hindex : xs.length + 1 < 2 ^ 63 := by
        rw [Nat.min_eq_right hle] at hbound
        omega
      exact partitionVectorLargeCount xs n hpos hle hn64 hindex
    · have hsmall : n ≤ xs.length := by omega
      rw [Nat.min_eq_left hsmall] at hbound
      exact group5_partition_vector_bounded xs n hn hbound

/-- Every positive native count works for vectors whose length is below half the signed range. -/
theorem partitionVectorNativeCount {α : Type} (xs : List α) (n : Nat)
    (hn : 0 < n) (hn64 : n < 2 ^ 63) (hlen : xs.length < 2 ^ 62) :
    let itr := partitionVectorObservation ⟨xs, JInt.lit .i64 (Int.ofNat n)⟩
    emitsExactly itr (chunksSpec n xs) ∧ itr.length = .ok ((xs.length + n - 1) / n) := by
  apply partitionVectorMinBound xs n hn hn64
  have hmin : min n xs.length ≤ xs.length := Nat.min_le_right _ _
  omega

/-- Successful public construction connects every positive native count to the full vector contract. -/
theorem partitionPublicNativeCount {α : Type} (xs : List α) (n : JInt64)
    (hn : 1 ≤ n.val) (hlen : xs.length < 2 ^ 62) :
    ∃ p, partitionNativeConstruct xs n.val
      (fun v k => sourceMethod1447 v (JInt.lit .i64 (Int.ofNat k))) = .ok p ∧
      emitsExactly (partitionVectorObservation p) (chunksSpec n.val.toNat xs) ∧
      (partitionVectorObservation p).length =
        .ok ((xs.length + n.val.toNat - 1) / n.val.toNat) := by
  refine ⟨⟨xs, JInt.lit .i64 (Int.ofNat n.val.toNat)⟩, ?_, ?_⟩
  · exact (partitionArrayConstructs id xs n hn).1
  · have hmax := n.property.2
    change n.val ≤ (2 ^ 63 : Int) - 1 at hmax
    exact partitionVectorNativeCount xs n.val.toNat (by omega) (by omega) hlen

end JuliaLean.ChatGPT.Batch5.Group5


/-! Independent range and array method clauses for the frozen partition target.
The integer-index clauses require a representable native count. The native-index
clause keeps exactly the arithmetic premises from the frozen statement. -/

namespace JuliaLean.ChatGPT.Batch5.Group5

open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators

/-- The mathematical-index wrapper performs its exact native-count arithmetic. -/
theorem partitionIntIndexEquation {C Chunk : Type}
    (firstindex lastindex : C → Int) (slice : C → Int → Int → Chunk)
    (c : C) (n : JInt64) (st : Option Int) :
    partitionIndexed (m := Jl) (fun x => pure (firstindex x))
      (fun x => pure (lastindex x)) (fun x y => pure (decide (x > y)))
      (fun x y => pure (x + y.val)) (fun x y => pure (x - y.val))
      (fun x y => pure (min x y)) (fun x y => pure (x, y))
      (fun x (lo, hi) => pure (slice x lo hi)) (fun x y => pure (x + y.val))
      ⟨c, n⟩ st =
      if decide (st.getD (firstindex c) > lastindex c) then .ok none else
        let stop := min (st.getD (firstindex c) + n.val - 1) (lastindex c)
        .ok (some (slice c (st.getD (firstindex c)) stop, stop + 1)) := by
  cases st <;> rfl

/-- All mathematical-index vector clauses, with only the missing count bound added. -/
theorem partitionIntVectorMethods_of_countBound
    {A View : Type} (firstindex lastindex : A → Int)
    (view : A → Int → Int → View) (c : A) (s : Int) (n : Nat)
    (hn : n < 2 ^ 63) :
    let a := firstindex c
    let b := lastindex c
    let runVec := fun st =>
      partitionIndexed (m := Jl) (fun x => pure (firstindex x))
        (fun x => pure (lastindex x)) (fun x y => pure (decide (x > y)))
        (fun x y => pure (x + y.val)) (fun x y => pure (x - y.val))
        (fun x y => pure (min x y)) (fun x y => pure (x, y))
        (fun x (lo, hi) => pure (view x lo hi)) (fun x y => pure (x + y.val))
        ⟨c, JInt.lit .i64 (Int.ofNat n)⟩ st
    (s > b → runVec (some s) = .ok none) ∧
    (a > b → runVec none = .ok none) ∧
    (s ≤ b →
      let r := min (s + Int.ofNat n - 1) b
      runVec (some s) = .ok (some (view c s r, r + 1))) := by
  have hnval := JuliaLean.ChatGPT.Batch4.Group5.group5_nat_count_val n hn
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [partitionIntIndexEquation]
    simp only [Option.getD_some, h, decide_true, ite_true]
  · intro h
    rw [partitionIntIndexEquation]
    simp only [Option.getD_none, h, decide_true, ite_true]
  · intro h
    rw [partitionIntIndexEquation]
    have hnot : ¬ s > lastindex c := by omega
    simp only [Option.getD_some, hnot, decide_false, Bool.false_eq_true, ite_false, hnval]

/-- The mathematical-index range method has the same bounded-count step. -/
theorem partitionIntRangeMethod_of_countBound
    {R Slice : Type} (firstindex lastindex : R → Int)
    (getSlice : R → Int → Int → Slice) (c : R) (s : Int) (n : Nat)
    (hn : n < 2 ^ 63) (hs : s ≤ lastindex c) :
    let r := min (s + Int.ofNat n - 1) (lastindex c)
    partitionIndexed (m := Jl) (fun x => pure (firstindex x))
      (fun x => pure (lastindex x)) (fun x y => pure (decide (x > y)))
      (fun x y => pure (x + y.val)) (fun x y => pure (x - y.val))
      (fun x y => pure (min x y)) (fun x y => pure (x, y))
      (fun x (lo, hi) => pure (getSlice x lo hi)) (fun x y => pure (x + y.val))
      ⟨c, JInt.lit .i64 (Int.ofNat n)⟩ (some s) =
      .ok (some (getSlice c s r, r + 1)) := by
  exact (partitionIntVectorMethods_of_countBound firstindex lastindex getSlice c s n hn).2.2 hs

/-- One native-index step, retaining every native operation of the frozen wrapper. -/
theorem partitionNativeIndexEquation {C Chunk : Type}
    (firstindex lastindex : C → JInt64) (slice : C → JInt64 → JInt64 → Chunk)
    (c : C) (n : JInt64) (st : Option JInt64) :
    partitionIndexed (m := Jl) (fun x => pure (firstindex x))
      (fun x => pure (lastindex x)) (fun x y => pure (decide (x.val > y.val)))
      (fun x y => pure (x + y)) (fun x y => pure (x - y))
      (fun x y => pure (if y < x then y else x)) (fun x y => pure (x, y))
      (fun x (lo, hi) => pure (slice x lo hi)) (fun x y => pure (x + y))
      ⟨c, n⟩ st =
      if decide ((st.getD (firstindex c)).val > (lastindex c).val) then .ok none else
        let stop0 := st.getD (firstindex c) + n - JInt.lit .i64 1
        let stop := if lastindex c < stop0 then lastindex c else stop0
        .ok (some (slice c (st.getD (firstindex c)) stop, stop + JInt.lit .i64 1)) := by
  cases st <;> rfl

/-- The native range method's live branch, with its frozen premises unchanged. -/
theorem partitionNativeRangeLive
    {R Slice : Type} (firstindex lastindex : R → JInt64)
    (getSlice : R → JInt64 → JInt64 → Slice) (c : R) (s : JInt64) (n : Nat)
    (hs : s.val ≤ (lastindex c).val) (hnpos : 0 < n)
    (hn : (n : Int) < 2 ^ 63) (hslo : -(2 ^ 63) < s.val)
    (hsum : s.val + (n : Int) < 2 ^ 63) (hb : (lastindex c).val < 2 ^ 63 - 1) :
    ∃ r r1 : JInt64,
      r.val = min (s.val + (n : Int) - 1) (lastindex c).val ∧
      r1.val = r.val + 1 ∧
      partitionIndexed (m := Jl) (fun x => pure (firstindex x))
        (fun x => pure (lastindex x)) (fun x y => pure (decide (x.val > y.val)))
        (fun x y => pure (x + y)) (fun x y => pure (x - y))
        (fun x y => pure (if y < x then y else x)) (fun x y => pure (x, y))
        (fun x (lo, hi) => pure (getSlice x lo hi)) (fun x y => pure (x + y))
        ⟨c, JInt.lit .i64 (Int.ofNat n)⟩ (some s) =
        .ok (some (getSlice c s r, r1)) := by
  let count := JInt.lit .i64 (Int.ofNat n)
  let stop0 := s + count - JInt.lit .i64 1
  let stop := if lastindex c < stop0 then lastindex c else stop0
  have hcount : count.val = (n : Int) :=
    JuliaLean.ChatGPT.Batch4.Group5.group5_nat_count_val n (by omega)
  have hone : (JInt.lit .i64 1).val = 1 := by decide
  have hsumval : (s + count).val = s.val + (n : Int) := by
    rw [jint_add_val, hcount]
    apply wrapInt_of_inRange
    constructor <;> simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, ite_true] <;> omega
  have hstop0 : stop0.val = s.val + (n : Int) - 1 := by
    change (s + count - JInt.lit .i64 1).val = _
    rw [jint_sub_val, hsumval, hone]
    apply wrapInt_of_inRange
    constructor <;> simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, ite_true] <;> omega
  have hstop : stop.val = min (s.val + (n : Int) - 1) (lastindex c).val := by
    change (if (lastindex c).val < stop0.val then lastindex c else stop0).val = _
    by_cases hlt : (lastindex c).val < stop0.val
    · rw [ite_eq_left hlt, Int.min_eq_right (by omega)]
    · rw [ite_eq_right hlt, hstop0, Int.min_eq_left (by omega)]
  have hstopBound : stop.val ≤ (lastindex c).val := by
    rw [hstop]
    exact Int.min_le_right _ _
  have hnext : (stop + JInt.lit .i64 1).val = stop.val + 1 := by
    rw [jint_add_val, hone]
    apply wrapInt_of_inRange
    have hlow := stop.property.1
    constructor <;> simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, ite_true] at hlow ⊢ <;> omega
  refine ⟨stop, stop + JInt.lit .i64 1, hstop, hnext, ?_⟩
  rw [partitionNativeIndexEquation]
  have hnot : ¬ s.val > (lastindex c).val := by omega
  simp only [Option.getD_some, hnot, decide_false, Bool.false_eq_true, ite_false]
  rfl

/-- Complete native range clause from PartitionMethodSemantics, unchanged. -/
theorem partitionNativeRangeMethods
    {R Slice : Type} (firstindex lastindex : R → JInt64)
    (getSlice : R → JInt64 → JInt64 → Slice) (c : R) (s : JInt64) (n : Nat) :
    let a := firstindex c
    let b := lastindex c
    let runRange := fun st =>
      partitionIndexed (m := Jl) (fun x => pure (firstindex x))
        (fun x => pure (lastindex x)) (fun x y => pure (decide (x.val > y.val)))
        (fun x y => pure (x + y)) (fun x y => pure (x - y))
        (fun x y => pure (if y < x then y else x)) (fun x y => pure (x, y))
        (fun x (lo, hi) => pure (getSlice x lo hi)) (fun x y => pure (x + y))
        ⟨c, JInt.lit .i64 (Int.ofNat n)⟩ st
    (s.val > b.val → runRange (some s) = .ok none) ∧
    (a.val > b.val → runRange none = .ok none) ∧
    (s.val ≤ b.val → 0 < n → (n : Int) < 2 ^ 63 → -(2 ^ 63) < s.val →
      s.val + (n : Int) < 2 ^ 63 → b.val < 2 ^ 63 - 1 →
      ∃ r r1 : JInt64,
        r.val = min (s.val + (n : Int) - 1) b.val ∧
        r1.val = r.val + 1 ∧
        runRange (some s) = .ok (some (getSlice c s r, r1))) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [partitionNativeIndexEquation]
    simp only [Option.getD_some, h, decide_true, ite_true]
  · intro h
    rw [partitionNativeIndexEquation]
    simp only [Option.getD_none, h, decide_true, ite_true]
  · intro hs hnpos hn hslo hsum hb
    exact partitionNativeRangeLive firstindex lastindex getSlice c s n hs hnpos hn hslo hsum hb

end JuliaLean.ChatGPT.Batch5.Group5


/-! The public Julia witness uses Vector{Nothing}(undef, 2^62 + 5).
Nothing has zero storage size, so the vector is constructible without storage
proportional to its length. Lean's Unit list describes the same constant values.
Only two iterator steps and symbolic list-length facts are used below. -/

namespace JuliaLean.ChatGPT.Batch5.Group5

open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators
open JuliaLean.ChatGPT.Batch4.Group5

def partitionBugLength : Nat := 2 ^ 62 + 5
def partitionBugCount : Nat := 2 ^ 62 + 3
def partitionBugFirstNext : JInt64 := JInt.lit .i64 (partitionBugCount + 1 : Nat)
def partitionBugSecondNext : JInt64 := JInt.lit .i64 (-(2 ^ 63) + 7)

/-- The witness count and vector length are both valid native nonnegative values. -/
theorem partitionBugNativeBounds :
    0 < partitionBugCount ∧ partitionBugCount < partitionBugLength ∧
    partitionBugLength < 2 ^ 63 ∧ partitionBugCount < 2 ^ 63 := by
  decide

/-- The first step returns the expected large view and a positive next index. -/
theorem partitionBugFirstStep {α : Type} (xs : List α)
    (hlen : xs.length = partitionBugLength) :
    (partitionVectorObservation ⟨xs, JInt.lit .i64 (Int.ofNat partitionBugCount)⟩).run none =
      .ok (some (xs.take partitionBugCount, partitionBugFirstNext)) := by
  have hlive : ¬ (JInt.lit .i64 (xs.length : Int)).val < (JInt.lit .i64 1).val := by
    rw [hlen]
    decide
  change (partitionVectorObservation ⟨xs, JInt.lit .i64 (Int.ofNat partitionBugCount)⟩).run
    (some (JInt.lit .i64 1)) = _
  rw [group5_partition_vector_live_raw xs _ _ hlive]
  dsimp only
  have hcancel : JInt.lit .i64 1 + JInt.lit .i64 (Int.ofNat partitionBugCount) -
      JInt.lit .i64 1 = JInt.lit .i64 (Int.ofNat partitionBugCount) := by decide
  have hmin : (if (JInt.lit .i64 (Int.ofNat partitionBugCount)).val ≤
      (JInt.lit .i64 (partitionBugLength : Int)).val then
        JInt.lit .i64 (Int.ofNat partitionBugCount) else
        JInt.lit .i64 (partitionBugLength : Int)) =
      JInt.lit .i64 (Int.ofNat partitionBugCount) := by decide
  have hdrop : ((JInt.lit .i64 1).val - 1).toNat = 0 := by decide
  have htake : ((JInt.lit .i64 (Int.ofNat partitionBugCount)).val -
      (JInt.lit .i64 1).val + 1).toNat = partitionBugCount := by decide
  have hnext : JInt.lit .i64 (Int.ofNat partitionBugCount) + JInt.lit .i64 1 =
      partitionBugFirstNext := by decide
  rw [hcancel, hlen, hmin, hdrop, List.drop_zero, htake, hnext]

/-- On the second step the endpoint arithmetic wraps, producing an empty view. -/
theorem partitionBugSecondStep {α : Type} (xs : List α)
    (hlen : xs.length = partitionBugLength) :
    (partitionVectorObservation ⟨xs, JInt.lit .i64 (Int.ofNat partitionBugCount)⟩).run
      (some partitionBugFirstNext) = .ok (some ([], partitionBugSecondNext)) := by
  have hlive : ¬ (JInt.lit .i64 (xs.length : Int)).val < partitionBugFirstNext.val := by
    rw [hlen]
    decide
  rw [group5_partition_vector_live_raw xs _ _ hlive]
  dsimp only
  have hend : partitionBugFirstNext + JInt.lit .i64 (Int.ofNat partitionBugCount) -
      JInt.lit .i64 1 = JInt.lit .i64 (-(2 ^ 63) + 6) := by decide
  have hmin : (if (JInt.lit .i64 (-(2 ^ 63) + 6)).val ≤
      (JInt.lit .i64 (partitionBugLength : Int)).val then
        JInt.lit .i64 (-(2 ^ 63) + 6) else
        JInt.lit .i64 (partitionBugLength : Int)) =
      JInt.lit .i64 (-(2 ^ 63) + 6) := by decide
  have htake : ((JInt.lit .i64 (-(2 ^ 63) + 6)).val -
      partitionBugFirstNext.val + 1).toNat = 0 := by decide
  have hnext : JInt.lit .i64 (-(2 ^ 63) + 6) + JInt.lit .i64 1 =
      partitionBugSecondNext := by decide
  rw [hend, hlen, hmin, htake, List.take_zero, hnext]

/-- The mathematical chunk specification has exactly two chunks for this input. -/
theorem partitionBugExpectedChunks {α : Type} (xs : List α)
    (hlen : xs.length = partitionBugLength) :
    chunksSpec partitionBugCount xs =
      [xs.take partitionBugCount, (xs.drop partitionBugCount).take partitionBugCount] := by
  unfold chunksSpec
  have hn : partitionBugCount ≠ 0 := by decide
  rw [ite_eq_right hn, hlen]
  have hcount : (partitionBugLength + partitionBugCount - 1) / partitionBugCount = 2 := by
    decide
  rw [hcount]
  change [(xs.drop 0).take partitionBugCount,
    (xs.drop partitionBugCount).take partitionBugCount] = _
  rw [List.drop_zero]

/-- The expected second chunk contains two values, established without unfolding xs. -/
theorem partitionBugExpectedSecondLength {α : Type} (xs : List α)
    (hlen : xs.length = partitionBugLength) :
    ((xs.drop partitionBugCount).take partitionBugCount).length = 2 := by
  rw [List.length_take, List.length_drop, hlen]
  decide

/-- A trace of two chunks fixes the second observation after its first next-state. -/
theorem partitionTraceSecond {α S : Type}
    (run : Option S → Observation JlError (Option (α × S)))
    (first second : α) (next : S)
    (htrace : finiteObservationTrace run none [first, second])
    (hfirst : run none = .ok (some (first, next))) :
    ∃ after, run (some next) = .ok (some (second, after)) := by
  cases htrace with
  | @step _ _ actualNext _ hstep htail =>
    have heq : actualNext = next :=
      congrArg Prod.snd (Option.some.inj (Observation.ok.inj (hstep.symm.trans hfirst)))
    subst actualNext
    cases htail with
    | step hsecond _ => exact ⟨_, hsecond⟩

/-- The two-step discrepancy contradicts exact mathematical chunk emission.
The proof keeps xs abstract so no long list is normalized by elaboration. -/
theorem partitionBugNotEmits {α : Type} (xs : List α)
    (hlen : xs.length = partitionBugLength) :
    ¬ emitsExactly
      (partitionVectorObservation ⟨xs, JInt.lit .i64 (Int.ofNat partitionBugCount)⟩)
      (chunksSpec partitionBugCount xs) := by
  intro hemits
  rw [partitionBugExpectedChunks xs hlen] at hemits
  unfold emitsExactly at hemits
  rw [group5_collect_eq_observe] at hemits
  have htrace := finiteObservationTrace_of_reads
    (partitionVectorObservation ⟨xs, JInt.lit .i64 (Int.ofNat partitionBugCount)⟩).run
    [xs.take partitionBugCount, (xs.drop partitionBugCount).take partitionBugCount]
    none hemits
  obtain ⟨after, hsecond⟩ := partitionTraceSecond _ _ _ partitionBugFirstNext htrace
    (partitionBugFirstStep xs hlen)
  have hchunk : ([] : List α) = (xs.drop partitionBugCount).take partitionBugCount :=
    congrArg Prod.fst (Option.some.inj
      (Observation.ok.inj ((partitionBugSecondStep xs hlen).symm.trans hsecond)))
  have hlength := congrArg List.length hchunk
  rw [List.length_nil, partitionBugExpectedSecondLength xs hlen] at hlength
  omega

/-- iterators-partition-vector: a constructible zero-storage vector witnesses overflow. -/
theorem IteratorsPartitionVector_refuted :
    ¬ JuliaLean.Proofs.base.iterators.PartitionVectorCorrect := by
  intro h
  let xs : List Unit := List.replicate partitionBugLength ()
  have hlen : xs.length = partitionBugLength := List.length_replicate
  exact partitionBugNotEmits xs hlen
    (h.1 xs partitionBugCount partitionBugNativeBounds.1).1

/-- iteratorscov-partition-methods includes the refuted vector contract. -/
theorem IteratorscovPartitionMethods_refuted :
    ¬ JuliaLean.Proofs.base.iterators.PartitionMethodSemantics := by
  intro h
  exact IteratorsPartitionVector_refuted h.1

end JuliaLean.ChatGPT.Batch5.Group5


namespace JuliaLean.ChatGPT.Batch5.Group5
open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators

/-- Removing a positive first chunk decreases the rounded-up chunk count by one. -/
theorem b5_chunk_count_step (len n : Nat) (hn : 0 < n) (hlen : 0 < len) :
    (len + n - 1) / n = (len - n + n - 1) / n + 1 := by
  by_cases hnl : n ≤ len
  · have heq : len + n - 1 = (len - n + n - 1) + n := by omega
    rw [heq, Nat.add_div_right _ hn]
  · have hsub : len - n = 0 := by omega
    have heq : len + n - 1 = (len - 1) + n := by omega
    rw [heq, Nat.add_div_right _ hn, Nat.div_eq_of_lt (by omega : len - 1 < n), hsub]
    simp only [Nat.zero_add, Nat.div_eq_of_lt (by omega : n - 1 < n)]

/-- No chunks are emitted by the empty list, independently of the chunk size. -/
theorem b5_chunks_nil {α : Type} (n : Nat) : chunksSpec n ([] : List α) = [] := by
  by_cases hn : n = 0
  · simp only [chunksSpec, hn, ↓reduceIte]
  · have hcount : (0 + n - 1) / n = 0 := Nat.div_eq_of_lt (by omega)
    simp only [chunksSpec, hn, ↓reduceIte, List.length_nil, hcount,
      List.range_zero, List.map_nil]

/-- The range-based chunk specification has the usual take/drop recursion. -/
theorem b5_chunks_take_drop {α : Type} (xs : List α) (n : Nat)
    (hn : 0 < n) (hxs : xs ≠ []) :
    chunksSpec n xs = xs.take n :: chunksSpec n (xs.drop n) := by
  have hlen : 0 < xs.length := by
    cases xs with
    | nil => exact False.elim (hxs rfl)
    | cons x rest => exact Nat.zero_lt_succ _
  have hc := b5_chunk_count_step xs.length n hn hlen
  simp only [chunksSpec, Nat.ne_of_gt hn, ↓reduceIte, List.length_drop]
  rw [hc, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.zero_mul, List.drop_zero]
  congr 1
  apply congrArg (fun f : Nat → List α =>
    (List.range ((xs.length - n + n - 1) / n)).map f)
  funext i
  simp only [Function.comp_apply, Nat.succ_mul, List.drop_drop, Nat.add_comm]

/-- A nonempty list shorter than one chunk is emitted as a single final chunk. -/
theorem b5_chunks_singleton_of_length_le {α : Type} (xs : List α) (n : Nat)
    (hn : 0 < n) (hxs : xs ≠ []) (hlen : xs.length ≤ n) :
    chunksSpec n xs = [xs] := by
  rw [b5_chunks_take_drop xs n hn hxs, List.take_of_length_le hlen,
    List.drop_eq_nil_of_le hlen, b5_chunks_nil]

/-- Each recursive nonempty chunk consumes at least one source element. -/
theorem b5_chunks_drop_length_lt {α : Type} (xs : List α) (n : Nat)
    (hn : 0 < n) (hxs : xs ≠ []) : (xs.drop n).length < xs.length := by
  have hlen : 0 < xs.length := by
    cases xs with
    | nil => exact False.elim (hxs rfl)
    | cons x rest => exact Nat.zero_lt_succ _
  rw [List.length_drop]
  omega

end JuliaLean.ChatGPT.Batch5.Group5


namespace JuliaLean.ChatGPT.Batch5.Group5
open JuliaLean JuliaLean.base.iterators JuliaLean.Proofs.base.iterators
open JuliaLean.ChatGPT.Batch4.Group5

/-- A finite mathematical description of one pending partition chunk. -/
def b5_pendingChunk {I α S : Type}
    (run : I → Option S → Jl (Option (α × S))) (itr : I) :
    Nat → Option (α × S) → Jl (List α × Option (α × S))
  | 0, y => .ok ([], y)
  | _ + 1, none => .ok ([], none)
  | k + 1, some (value, state) =>
      if k = 0 then .ok ([value], some (value, state))
      else do
        let pending ← run itr (some state)
        let (values, final) ← b5_pendingChunk run itr k pending
        pure (value :: values, final)

theorem b5_native_increment (i : Nat) (hi : i < 2 ^ 63) :
    JuliaLean.base.int.add_int (JInt.lit .i64 (i : Int)) (JInt.lit .i64 1) =
      JInt.lit .i64 ((i + 1 : Nat) : Int) := by
  apply Subtype.ext
  rw [JuliaLean.Proofs.base.int.add_int_val]
  change wrapInt .i64 ((JInt.lit .i64 (i : Int)).val + (JInt.lit .i64 1).val) =
    wrapInt .i64 ((i + 1 : Nat) : Int)
  rw [group5_partition_nat_val i hi]
  rfl

/-- The heap loop performs exactly the finite pending-chunk computation.
The counter stays within its positive native count, so no counter wrap occurs. -/
theorem b5_partitionLoop_pending {I α S : Type}
    (run : I → Option S → Jl (Option (α × S))) (itr : I) (n : Nat)
    (hn : n < 2 ^ 63) :
    ∀ (k i : Nat) (pending final : Option (α × S)) (values heap : List α),
      0 < k → i + k = n →
      b5_pendingChunk run itr k pending = .ok (values, final) →
      partitionLoop
        (fun (i : I) (st : Option S) (heap : List α) => some (run i st, heap))
        (fun (_ : Unit) (value : α) (_ : JInt64) (heap : List α) =>
          some ((.ok () : Except JlError Unit), heap ++ [value]))
        ⟨itr, JInt.lit .i64 (n : Int)⟩ () (JInt.lit .i64 (i : Int)) pending heap =
        some (.ok (JInt.lit .i64 ((i + values.length : Nat) : Int), final), heap ++ values) := by
  intro k
  induction k with
  | zero => intro i pending final values heap hk; omega
  | succ k ih =>
    intro i pending final values heap hk hik hchunk
    cases pending with
    | none =>
      simp only [b5_pendingChunk, Except.ok.injEq, Prod.mk.injEq] at hchunk
      rcases hchunk with ⟨hvalues, hfinal⟩
      subst values
      subst final
      rw [partitionLoop.eq_def]
      simp only [List.length_nil, Nat.add_zero, List.append_nil]
    | some pair =>
      rcases pair with ⟨value, state⟩
      have hi : i < 2 ^ 63 := by omega
      have hip : i + 1 < 2 ^ 63 := by omega
      have hincr := b5_native_increment i hi
      have hiv := group5_partition_nat_val (i + 1) hip
      have hnv := group5_partition_nat_val n hn
      cases k with
      | zero =>
        change (Except.ok ([value], some (value, state)) : Jl _) =
          .ok (values, final) at hchunk
        cases hchunk
        rw [partitionLoop.eq_def]
        simp only [hincr, hiv, hnv]
        rw [ite_eq_left (by omega)]
        rfl
      | succ k =>
        simp only [b5_pendingChunk, Nat.succ_ne_zero, ↓reduceIte] at hchunk
        cases hr : run itr (some state) with
        | error e =>
          rw [hr] at hchunk
          cases hchunk
        | ok next =>
          rw [hr, ok_bind] at hchunk
          cases hc : b5_pendingChunk run itr (k + 1) next with
          | error e =>
            rw [hc] at hchunk
            cases hchunk
          | ok result =>
            rcases result with ⟨tail, last⟩
            rw [hc, ok_bind] at hchunk
            cases hchunk
            rw [partitionLoop.eq_def]
            simp only [hincr, hiv, hnv]
            rw [ite_eq_right (by omega)]
            simp only [hr]
            have hrec := ih (i + 1) next last tail (heap ++ [value])
              (by omega) (by omega) hc
            rw [hrec]
            have hcount : i + 1 + tail.length = i + (tail.length + 1) := by omega
            simp only [List.length_cons, List.append_assoc, List.cons_append,
              List.nil_append, hcount]

/-- A successful finite chunk never stores more than its requested count. -/
theorem b5_pendingChunk_length {I α S : Type}
    (run : I → Option S → Jl (Option (α × S))) (itr : I) :
    ∀ (k : Nat) (pending : Option (α × S)) (values : List α)
      (final : Option (α × S)),
      b5_pendingChunk run itr k pending = .ok (values, final) → values.length ≤ k := by
  intro k
  induction k with
  | zero =>
    intro pending values final h
    change (Except.ok ([], pending) : Jl _) = .ok (values, final) at h
    cases h
    exact Nat.le_refl 0
  | succ k ih =>
    intro pending values final h
    cases pending with
    | none =>
      change (Except.ok ([], none) : Jl _) = .ok (values, final) at h
      cases h
      exact Nat.zero_le _
    | some pair =>
      rcases pair with ⟨value, state⟩
      cases k with
      | zero =>
        change (Except.ok ([value], some (value, state)) : Jl _) = .ok (values, final) at h
        cases h
        exact Nat.le_refl 1
      | succ k =>
        simp only [b5_pendingChunk, Nat.succ_ne_zero, ↓reduceIte] at h
        cases hr : run itr (some state) with
        | error e => rw [hr] at h; cases h
        | ok next =>
          rw [hr, ok_bind] at h
          cases hc : b5_pendingChunk run itr (k + 1) next with
          | error e => rw [hc] at h; cases h
          | ok result =>
            rcases result with ⟨tail, last⟩
            rw [hc, ok_bind] at h
            cases h
            exact Nat.succ_le_succ (ih next tail last hc)

/-- Pending chunks agree with the existing mathematical chunk collector,
including the distinction between an exact-size and a short final chunk. -/
theorem b5_pendingChunk_collect {I α S : Type}
    (run : I → Option S → Jl (Option (α × S))) (itr : I) :
    ∀ (k : Nat) (state : Option S) (pending : Option (α × S))
      (values : List α) (final : Option (α × S)),
      0 < k → run itr state = .ok pending →
      b5_pendingChunk run itr k pending = .ok (values, final) →
      collectPartitionChunk run itr k state = .ok (values, final.map Prod.snd) := by
  intro k
  induction k with
  | zero => intro state pending values final hk; omega
  | succ k ih =>
    intro state pending values final hk hr h
    cases pending with
    | none =>
      change (Except.ok ([], none) : Jl _) = .ok (values, final) at h
      cases h
      rw [collectPartitionChunk, hr]
      rfl
    | some pair =>
      rcases pair with ⟨value, nextState⟩
      cases k with
      | zero =>
        change (Except.ok ([value], some (value, nextState)) : Jl _) = .ok (values, final) at h
        cases h
        rw [collectPartitionChunk, hr]
        rfl
      | succ k =>
        simp only [b5_pendingChunk, Nat.succ_ne_zero, ↓reduceIte] at h
        cases hn : run itr (some nextState) with
        | error e => rw [hn] at h; cases h
        | ok next =>
          rw [hn, ok_bind] at h
          cases hc : b5_pendingChunk run itr (k + 1) next with
          | error e => rw [hc] at h; cases h
          | ok result =>
            rcases result with ⟨tail, last⟩
            rw [hc, ok_bind] at h
            cases h
            rw [collectPartitionChunk, hr, ok_bind]
            dsimp only
            rw [ih (some nextState) next tail last (by omega) hn hc]
            rfl

/-- Every finite input protocol has a successful finite pending chunk. -/
theorem b5_pendingChunk_from_trace {I α S : Type}
    (run : I → Option S → Jl (Option (α × S)))
    (done : I → Option S → Jl (Option Bool)) (itr : I) :
    ∀ (k : Nat) (state : Option S) (xs : List α), 0 < k →
      followsFrom (protocolIterator run done itr) state xs →
      ∃ pending final, run itr state = .ok pending ∧
        b5_pendingChunk run itr k pending = .ok (xs.take k, final) := by
  intro k
  induction k with
  | zero => intro state xs hk; omega
  | succ k ih =>
    intro state xs hk ht
    cases xs with
    | nil =>
      refine ⟨none, none, followsFrom_nil (protocolIterator run done itr) state ht, ?_⟩
      rfl
    | cons value rest =>
      obtain ⟨nextState, hr, htail⟩ :=
        followsFrom_cons (protocolIterator run done itr) state value rest ht
      change run itr state = .ok (some (value, nextState)) at hr
      cases k with
      | zero => exact ⟨some (value, nextState), some (value, nextState), hr, rfl⟩
      | succ k =>
        obtain ⟨pending, final, hn, hc⟩ := ih (some nextState) rest (by omega) htail
        refine ⟨some (value, nextState), final, hr, ?_⟩
        simp only [b5_pendingChunk, Nat.succ_ne_zero, ↓reduceIte, hn, ok_bind, hc,
          List.take_succ_cons, pure_jl]

/-- The fixed allocation model accepts every requested native count below 2^60. -/
theorem b5_allocPartitionList_bounded {α : Type} (n : Nat) (hn : n < 2 ^ 60) :
    allocPartitionList (α := α) α (JInt.lit .i64 (n : Int)) = .ok [] := by
  have hnv := group5_partition_nat_val n (by omega : n < 2 ^ 63)
  unfold allocPartitionList
  rw [hnv]
  have hbad : ¬ ((n : Int) < 0 ∨ (n : Int) ≥ 2 ^ 63 - 2 ∨
      (n : Int) * 8 ≥ 2 ^ 63 - 2) := by omega
  rw [ite_eq_right hbad]
  rfl

/-- Convert a pending value-state pair to the generic partition continuation. -/
def b5_partitionMarker {α S : Type} : Option (α × S) → PartitionState S
  | none => .cutShort
  | some (_, st) => .at (some st)

/-- The finite generic wrapper uses one allocation, one initial iterator call,
and its loop result. The loop remains an abstract application in this proof. -/
theorem b5_partitionGeneric_loop_result {E H I α S Ty Vec : Type}
    (eltype : I → Ty) (allocate : Ty → JInt64 → Exec E H Vec)
    (store : Vec → α → JInt64 → Exec E H Unit)
    (resize : Vec → JInt64 → Exec E H Vec)
    (run : I → Option S → Exec E H (Option (α × S)))
    (p : PartitionIterator I) (state : Option S)
    (before afterAllocate afterRun afterLoop : H)
    (v resized : Vec) (i : JInt64) (pending final : Option (α × S))
    (ha : allocate (eltype p.c) p.n before = some (.ok v, afterAllocate))
    (hr : run p.c state afterAllocate = some (.ok pending, afterRun))
    (hl : partitionLoop run store p v (JInt.lit .i64 0) pending afterRun =
      some (.ok (i, final), afterLoop))
    (hs : resize v i afterLoop = some (.ok resized, afterLoop)) :
    partitionGeneric eltype allocate store resize run p (.at state) before =
      some (.ok (if i.val = 0 then none else
        some (resized, b5_partitionMarker final)), afterLoop) := by
  unfold partitionGeneric
  dsimp only
  simp only [Bind.bind, JuliaLean.base.iterators.bind, ha, hr, hl]
  by_cases hz : i.val = 0
  · simp only [hz, ↓reduceIte]
    rfl
  · simp only [hz, ↓reduceIte, JuliaLean.base.iterators.bind, hs]
    cases final <;> rfl

/-- Normalize only the finite result of the zero-counter loop invocation. -/
theorem b5_partitionLoop_initial {I α S : Type}
    (run : I → Option S → Jl (Option (α × S))) (itr : I) (n : Nat)
    (hn : 0 < n) (hbound : n < 2 ^ 63)
    (pending final : Option (α × S)) (values : List α)
    (hc : b5_pendingChunk run itr n pending = .ok (values, final)) :
    partitionLoop
      (fun (i : I) (st : Option S) (heap : List α) => some (run i st, heap))
      (fun (_ : Unit) (value : α) (_ : JInt64) (heap : List α) =>
        some ((.ok () : Except JlError Unit), heap ++ [value]))
      ⟨itr, JInt.lit .i64 (n : Int)⟩ () (JInt.lit .i64 0) pending [] =
      some (.ok (JInt.lit .i64 (values.length : Int), final), values) := by
  have hloopRaw := b5_partitionLoop_pending run itr n hbound
    n 0 pending final values [] hn (by omega) hc
  have hresult :
      (some (.ok (JInt.lit .i64 ((0 + values.length : Nat) : Int), final), [] ++ values) :
        Option (Except JlError (JInt64 × Option (α × S)) × List α)) =
      some (.ok (JInt.lit .i64 (values.length : Int), final), values) := by
    rw [Nat.zero_add, List.nil_append]
  exact hloopRaw.trans hresult

/-- The frozen list wrapper transports a successful loop result without
reducing the recursive loop or its native count. -/
theorem b5_partitionListStep_loop_result {I α S : Type}
    (run : I → Option S → Jl (Option (α × S)))
    (p : PartitionIterator I) (state : Option S)
    (pending final : Option (α × S)) (values : List α) (i : JInt64)
    (ha : allocPartitionList (α := α) α p.n = .ok [])
    (hr : run p.c state = .ok pending)
    (hl : partitionLoop
      (fun (itr : I) (st : Option S) (heap : List α) => some (run itr st, heap))
      (fun (_ : Unit) (value : α) (_ : JInt64) (heap : List α) =>
        some ((.ok () : Except JlError Unit), heap ++ [value]))
      p () (JInt.lit .i64 0) pending [] = some (.ok (i, final), values)) :
    partitionListStep run p (.at state) =
      .ok (if i.val = 0 then none else some (values, b5_partitionMarker final)) := by
  unfold partitionListStep
  dsimp only
  rw [b5_partitionGeneric_loop_result
    (afterAllocate := []) (afterRun := []) (afterLoop := values)
    (v := ()) (resized := ()) (i := i) (pending := pending) (final := final)]
  · by_cases hz : i.val = 0
    · simp only [hz, ↓reduceIte]
      rfl
    · simp only [hz, ↓reduceIte]
      rfl
  · rw [ha]
  · rw [hr]
  · exact hl
  · rfl

/-- One generic partition step agrees with the finite pending-chunk result,
including no output on exhaustion and the exact continuation tag. -/
theorem b5_partitionListStep_pending {I α S : Type}
    (run : I → Option S → Jl (Option (α × S))) (itr : I)
    (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 60)
    (state : Option S) (pending final : Option (α × S)) (values : List α)
    (hr : run itr state = .ok pending)
    (hc : b5_pendingChunk run itr n pending = .ok (values, final)) :
    partitionListStep run ⟨itr, JInt.lit .i64 (n : Int)⟩ (.at state) =
      .ok (if values.isEmpty then none else some (values, b5_partitionMarker final)) := by
  have hlen := b5_pendingChunk_length run itr n pending values final hc
  have hv := group5_partition_nat_val values.length (by omega : values.length < 2 ^ 63)
  have halloc := b5_allocPartitionList_bounded (α := α) n hbound
  have hloop := b5_partitionLoop_initial run itr n hn (by omega) pending final values hc
  have hstep :
      partitionListStep run ⟨itr, JInt.lit .i64 (n : Int)⟩ (.at state) =
      .ok (if (JInt.lit .i64 (values.length : Int)).val = 0 then none else
        some (values, b5_partitionMarker final)) := by
    refine b5_partitionListStep_loop_result run ⟨itr, JInt.lit .i64 (n : Int)⟩ state
      pending final values (JInt.lit .i64 (values.length : Int)) ?_ ?_ ?_
    · dsimp only
      exact halloc
    · dsimp only
      exact hr
    · exact hloop
  rw [hstep]
  simp only [hv]
  cases values with
  | nil => rfl
  | cons x rest =>
    have hnonzero : ¬ ((x :: rest).length : Int) = 0 := by
      simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
      omega
    rw [ite_eq_right hnonzero]
    rfl

/-- A finished short partition never allocates or queries its underlying iterator again. -/
theorem b5_partitionListStep_cutShort {I α S : Type}
    (run : I → Option S → Jl (Option (α × S))) (itr : I) (n : JInt64) :
    partitionListStep run ⟨itr, n⟩ .cutShort = .ok none := by
  rfl

/-- Exact first-chunk protocol clause of PartitionMethodSemantics. -/
theorem b5_partition_first_chunk_protocol {I α S : Type}
    (iterate : I → Option S → Jl (Option (α × S)))
    (isdone : I → Option S → Jl (Option Bool)) (it : I) (xs : List α) (n : Nat)
    (hn : 0 < n) (hbound : n < 2 ^ 60)
    (ht : followsProtocol iterate isdone it xs) :
    let p : PartitionIterator I := ⟨it, JInt.lit .i64 (Int.ofNat n)⟩
    (xs = [] → partitionListStep iterate p (.at none) = .ok none) ∧
    (xs ≠ [] → ∃ finalState,
      collectPartitionChunk iterate it n none = .ok (xs.take n, finalState) ∧
      partitionListStep iterate p (.at none) =
        .ok (some (xs.take n, match finalState with
          | none => .cutShort
          | some state => .at (some state)))) := by
  obtain ⟨pending, final, hr, hc⟩ :=
    b5_pendingChunk_from_trace iterate isdone it n none xs hn ht
  have hstep := b5_partitionListStep_pending iterate it n hn hbound none
    pending final (xs.take n) hr hc
  have hcollect := b5_pendingChunk_collect iterate it n none pending
    (xs.take n) final hn hr hc
  dsimp only
  simp only [Int.ofNat_eq_natCast]
  constructor
  · intro hempty
    subst xs
    simpa only [List.take_nil, List.isEmpty_nil, ↓reduceIte] using hstep
  · intro hne
    refine ⟨final.map Prod.snd, hcollect, ?_⟩
    have hnonempty : (xs.take n).isEmpty = false := by
      cases xs with
      | nil => exact False.elim (hne rfl)
      | cons x rest => cases n with
        | zero => omega
        | succ n => rfl
    rw [hnonempty] at hstep
    cases final <;> exact hstep

/-- A list protocol follows its remaining suffix at every natural state. -/
theorem b5_list_protocol_suffix {α : Type} (xs : List α) (pos : Nat) :
    followsFrom
      (protocolIterator (fun (itr : IteratorModel α Nat) st => itr.run st)
        (fun itr st => itr.isdone st) (listIterator xs)) (some pos) (xs.drop pos) := by
  unfold followsFrom
  rw [group5_collect_run_eq
    (protocolIterator (fun (itr : IteratorModel α Nat) st => itr.run st)
      (fun itr st => itr.isdone st) (listIterator xs))
    (listIterator xs) (fun _ => rfl), group5_collect_eq_observe]
  change Round5.observe (listIterator xs).run ((xs.drop pos).length + 1) (some pos) =
    .ok (xs.drop pos)
  rw [group5_observe_list, List.take_of_length_le (Nat.le_succ _)]

/-- A generic list partition step yields the next take and the exact continuation.
Only a strictly short final chunk has the cut-short marker. -/
theorem b5_partitionListStep_list {α : Type} (xs : List α) (pos n : Nat)
    (hn : 0 < n) (hbound : n < 2 ^ 60) :
    partitionListStep (fun (itr : IteratorModel α Nat) st => itr.run st)
      ⟨listIterator xs, JInt.lit .i64 (n : Int)⟩ (.at (some pos)) =
      .ok (if (xs.drop pos).isEmpty then none else
        some ((xs.drop pos).take n,
          if (xs.drop pos).length < n then .cutShort else .at (some (pos + n)))) := by
  obtain ⟨pending, final, hr, hc⟩ :=
    b5_pendingChunk_from_trace (fun (itr : IteratorModel α Nat) st => itr.run st)
      (fun itr st => itr.isdone st) (listIterator xs) n (some pos) (xs.drop pos) hn
      (b5_list_protocol_suffix xs pos)
  have hstep := b5_partitionListStep_pending
    (fun (itr : IteratorModel α Nat) st => itr.run st) (listIterator xs) n hn hbound
    (some pos) pending final ((xs.drop pos).take n) hr hc
  have hcollect := b5_pendingChunk_collect
    (fun (itr : IteratorModel α Nat) st => itr.run st) (listIterator xs)
    n (some pos) pending ((xs.drop pos).take n) final hn hr hc
  have hexact := collectPartitionChunk_listIterator xs n pos
  have hfinal : final.map Prod.snd =
      (if (xs.drop pos).length < n then none else some (pos + n)) :=
    congrArg Prod.snd (Except.ok.inj (hcollect.symm.trans hexact))
  have hmarker : b5_partitionMarker final =
      (if (xs.drop pos).length < n then .cutShort else .at (some (pos + n))) := by
    have hm : b5_partitionMarker final =
        (match final.map Prod.snd with | none => .cutShort | some st => .at (some st)) := by
      cases final <;> rfl
    rw [hm, hfinal]
    by_cases hshort : (xs.drop pos).length < n
    · simp only [hshort, ↓reduceIte]
    · simp only [hshort, ↓reduceIte]
  have hempty : ((xs.drop pos).take n).isEmpty = (xs.drop pos).isEmpty := by
    cases hdrop : xs.drop pos with
    | nil => simp only [List.take_nil]
    | cons x rest => cases n with
      | zero => omega
      | succ n => rfl
  rw [hempty, hmarker] at hstep
  exact hstep

/-- Changing the first underlying call preserves the generic monadic program.
The partial loop and the monad's bind operation remain abstract here. -/
theorem b5_partitionGeneric_at_congr {E H I α S Ty Vec : Type}
    (eltype : I → Ty) (allocate : Ty → JInt64 → Exec E H Vec)
    (store : Vec → α → JInt64 → Exec E H Unit)
    (resize : Vec → JInt64 → Exec E H Vec)
    (run : I → Option S → Exec E H (Option (α × S)))
    (p : PartitionIterator I) (left right : Option S)
    (h : run p.c left = run p.c right) :
    partitionGeneric eltype allocate store resize run p (.at left) =
      partitionGeneric eltype allocate store resize run p (.at right) := by
  unfold partitionGeneric
  dsimp only
  rw [h]

/-- The generic wrapper's initial state changes only the first iterator call. -/
theorem b5_partitionListStep_state_congr {I α S : Type}
    (run : I → Option S → Jl (Option (α × S))) (itr : I) (n : JInt64)
    (left right : Option S) (h : run itr left = run itr right) :
    partitionListStep run ⟨itr, n⟩ (.at left) =
      partitionListStep run ⟨itr, n⟩ (.at right) := by
  unfold partitionListStep
  dsimp only
  rw [b5_partitionGeneric_at_congr (left := left) (right := right)]
  funext heap
  exact congrArg (fun value => some (value, heap)) h

/-- Expose a generic list observation without reducing its partial heap loop. -/
theorem b5_partition_generic_run_at {α : Type} (xs : List α) (n pos : Nat) :
    (partitionGenericObservation xs n).run (some (.at (some pos))) =
      partitionListStep (fun (itr : IteratorModel α Nat) st => itr.run st)
        ⟨listIterator xs, JInt.lit .i64 (n : Int)⟩ (.at (some pos)) := by
  simp only [partitionGenericObservation, Option.getD_some]

/-- The initial generic list wrapper agrees with its zero-index continuation. -/
theorem b5_partition_generic_initial {α : Type} (xs : List α) (n : Nat) :
    (partitionGenericObservation xs n).run none =
      (partitionGenericObservation xs n).run (some (.at (some 0))) := by
  simp only [partitionGenericObservation, Option.getD_none, Option.getD_some]
  exact b5_partitionListStep_state_congr
    (fun (itr : IteratorModel α Nat) st => itr.run st) (listIterator xs)
    (JInt.lit .i64 (n : Int)) none (some 0) rfl

/-- Every positive bounded generic partition follows the complete suffix chunk
trace. Exact-size final chunks perform one subsequent exhaustion query. -/
theorem b5_partition_generic_trace_aux {α : Type} (xs : List α) (n : Nat)
    (hn : 0 < n) (hbound : n < 2 ^ 60) :
    ∀ remaining pos, (xs.drop pos).length = remaining →
      finiteObservationTrace (partitionGenericObservation xs n).run
        (some (.at (some pos))) (chunksSpec n (xs.drop pos)) := by
  intro remaining
  induction remaining using Nat.strongRecOn with
  | ind remaining ih =>
    intro pos hremaining
    by_cases hnil : xs.drop pos = []
    · rw [hnil, b5_chunks_nil]
      apply finiteObservationTrace.stop
      rw [b5_partition_generic_run_at, b5_partitionListStep_list xs pos n hn hbound]
      simp only [hnil, List.isEmpty_nil, ↓reduceIte]
    · have hempty : (xs.drop pos).isEmpty = false := List.isEmpty_eq_false_iff.mpr hnil
      rw [b5_chunks_take_drop (xs.drop pos) n hn hnil]
      by_cases hshort : (xs.drop pos).length < n
      · rw [List.drop_eq_nil_of_le (Nat.le_of_lt hshort), b5_chunks_nil]
        refine finiteObservationTrace.step (next := .cutShort) ?_ ?_
        · rw [b5_partition_generic_run_at, b5_partitionListStep_list xs pos n hn hbound]
          simp only [hempty, hshort, Bool.false_eq_true, ↓reduceIte]
        · exact .stop (b5_partitionListStep_cutShort
            (fun (itr : IteratorModel α Nat) st => itr.run st) (listIterator xs)
            (JInt.lit .i64 (n : Int)))
      · refine finiteObservationTrace.step (next := .at (some (pos + n))) ?_ ?_
        · rw [b5_partition_generic_run_at, b5_partitionListStep_list xs pos n hn hbound]
          simp only [hempty, hshort, Bool.false_eq_true, ↓reduceIte]
        · have hlt : (xs.drop (pos + n)).length < remaining := by
            rw [← List.drop_drop]
            rw [← hremaining]
            exact b5_chunks_drop_length_lt (xs.drop pos) n hn hnil
          rw [List.drop_drop]
          exact ih (xs.drop (pos + n)).length hlt (pos + n) rfl

/-- Exact generic-emission clause of PartitionMethodSemantics, for every list
and the frozen model's stated positive count and allocation arithmetic bound. -/
theorem b5_partition_generic_emits {α : Type} (xs : List α) (n : Nat)
    (hn : 0 < n) (hbound : n < 2 ^ 60) :
    emitsExactly (partitionGenericObservation xs n) (chunksSpec n xs) := by
  have htrace := b5_partition_generic_trace_aux xs n hn hbound xs.length 0
    (by rw [List.drop_zero])
  simp only [List.drop_zero] at htrace
  have htrace0 := finiteObservationTrace_change_start
    (partitionGenericObservation xs n).run none (some (.at (some 0))) (chunksSpec n xs)
    (b5_partition_generic_initial xs n) htrace
  unfold emitsExactly
  rw [group5_collect_eq_observe]
  exact finiteObservationTrace_reads _ htrace0

end JuliaLean.ChatGPT.Batch5.Group5

end

namespace JuliaLean.Proofs.base.iterators
/-- Registry for the source-backed iterator properties. -/
def entries : List JuliaLean.Registry.Entry := [
  { id := "iterators-take-isdone-zero", juliaFile := "base/iterators.jl", juliaFns := ["isdone(::Take)", "isempty(::Take)", "zip"],
    statement := "isempty(take(itr, n)) is true exactly when take(itr, n) yields nothing, for itr a vector or an Iterators.StatefulSnapshot.", source := "base/essentials.jl:1204-1206 (isempty docstring), 1574-1587 (isdone docstring)", status := .refuted,
    prop := ``TakeIsemptyCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsTakeIsdoneZero_refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64151, #28497, #64340, #63733; see bugs/iterators-take-isdone-zero.yaml",
    notes := "isdone(t::Take) = isdone(t.xs) ignores t.n: isempty(take(StatefulSnapshot([1,2,3]), 0)) is false, and zip advances other stateful iterators." },
  { id := "iterators-rest-isdone-state", juliaFile := "base/iterators.jl", juliaFns := ["isdone(::Rest)", "isempty(::Rest)", "peel"],
    statement := "For (x, r) = Iterators.peel(itr), isempty(r) is true exactly when r yields nothing.", source := "base/iterators.jl:700-704 (peel docstring), base/essentials.jl:1204 (isempty)", status := .refuted,
    prop := ``PeelRestIsempty, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsRestIsdoneState_refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64152, #64314; see bugs/iterators-rest-isdone-state.yaml",
    notes := "isdone(i::Rest, st...) = isdone(i.itr, st...) asks the wrapped iterator about its start instead of i.st; counterexample peel(take(StatefulSnapshot([1,2,3]), 1))." },
  { id := "iterators-drop-drop-overflow", juliaFile := "base/iterators.jl", juliaFns := ["drop(::Drop, n)", "drop(::Take, n)"],
    statement := "drop(drop(v, a), b) of a vector succeeds for all a, b >= 0 and yields all but the first a + b elements. Both drop optimizations use their actual returned objects; arbitrary protocols and every nonnegative count, with no combined-count fit premise.", source := "base/iterators.jl:849 (drop docstring)", status := .refuted,
    prop := ``Round4.DropDropCorrect, thm := some ``dropDropCorrect_refuted,
    issue := "gh search issues/prs --repo JuliaLang/julia --limit 100 'Iterators.drop nested overflow typemax' -> []; related issues #39079 (reverse Take/Drop arithmetic), #50486 (integer overflow RFC).",
    notes := "Int(n) + xs.n wraps: drop(drop([1,2,3], typemax(Int)), 1) throws ArgumentError." },
  { id := "iterators-nth-cycle-overflow", juliaFile := "base/iterators.jl", juliaFns := ["nth(::Flatten{Take{Repeated}}, n)", "cycle(xs, n)"],
    statement := "nth(cycle(v, m), k) is v[mod1(k, length(v))] for every 1 <= k <= length(v) * m.", source := "base/iterators.jl:1730 (nth docstring), 1031 (cycle docstring)", status := .refuted,
    prop := ``NthCycleCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsNthCycleOverflow_refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64311, #56580; see bugs/iterators-nth-cycle-overflow.yaml",
    notes := "k*cycles wraps: nth(cycle([1,2,3], 2^62), 1) throws BoundsError." },
  { id := "iterators-nth-zip-empty", juliaFile := "base/iterators.jl", juliaFns := ["nth(::Zip, n)"],
    statement := "nth(zip(vs...), n) throws BoundsError for n <= 0.", source := "base/iterators.jl:1730 (nth docstring: throw a BoundsError if not existing)", status := .refuted,
    prop := ``Round4.NthZipNonpositive, thm := some ``nthZipNonpositive_refuted,
    issue := "gh search issues/prs --repo JuliaLang/julia --limit 100 'Iterators.nth zip empty BoundsError' -> []; related PR #56580 (nth API), issues #46173 (collect(zip())), #43821 (zip() infinite), #54454 (nth API discussion).",
    notes := "_nth(::IteratorSize, z::Zip, n) = map(nth(n), z.is) never checks n; for zip() it returns ()." },
  { id := "iterators-nth-unsigned-offset", juliaFile := "base/iterators.jl", juliaFns := ["nth(::AbstractArray, n)"],
    statement := "nth(A, n) returns the n-th element of A = IdentityUnitRange(fi:li) for every in-range n of every integer type.", source := "base/iterators.jl:1730 (nth docstring)", status := .refuted,
    prop := ``NthAnyIntegerType, thm := some ``nthAnyIntegerType_refuted,
    issue := "none found (queries: gh search issues 'Iterators.nth unsigned' --repo JuliaLang/julia; gh search issues 'IdentityUnitRange nth' --repo JuliaLang/julia; gh search prs 'Iterators.nth offset' --repo JuliaLang/julia)",
    notes := "begin + n - 1 is computed in UInt64 when n::UInt64; a negative firstindex wraps to a huge index." },
  { id := "iterators-product-length-zero", juliaFile := "base/iterators.jl", juliaFns := ["length(::ProductIterator)"],
    statement := "length(product(1:l1, ..., 1:lk)) is l1*...*lk whenever that count fits in an Int.", source := "invariant (length is the number of elements; collect and isempty agree)", status := .refuted,
    prop := ``ProductLengthExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsProductLengthZero_refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #43422, #43429; see bugs/iterators-product-length-zero.yaml",
    notes := "reduce(checked_mul, size(P); init=1) folds left: length(product(1:2^32, 1:2^32, 1:0)) throws OverflowError." },
  { id := "iterators-product-last-empty", juliaFile := "base/iterators.jl", juliaFns := ["last(::ProductIterator)"],
    statement := "last(product(1:l1, ..., 1:lk)) returns only when the product is nonempty.", source := "base/abstractarray.jl:513-520 (last docstring: the last element of an ordered collection)", status := .refuted,
    prop := ``ProductLastNonempty, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsProductLastEmpty_refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #52195, #22989; see bugs/iterators-product-last-empty.yaml",
    notes := "last(p) = map(last, p.iterators) inherits last(1:0) == 0: last(product(1:2, 1:0)) == (2, 0). Possibly intended." },
  { id := "iterators-cycle-empty-length", juliaFile := "base/iterators.jl", juliaFns := ["cycle", "IteratorSize(::Type{Cycle})", "take", "length(::Take)"],
    statement := "length(take(cycle(v), n)) equals the number of elements that take(cycle(v), n) yields, which is 0 when v is empty.", source := "base/iterators.jl:1028-1032 (cycle docstring: when iter is empty, so is cycle(iter)), 823 (length(::Take))", status := .refuted,
    prop := ``CycleFirstN, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsCycleEmptyLength_refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #53169, #43235, #54187; see bugs/iterators-cycle-empty-length.yaml",
    notes := "IteratorSize(Cycle) is IsInfinite even for empty v (the XXX comment at base/iterators.jl:1063), so length(take(cycle(Int[]), 3)) == 3 and collect returns 3 uninitialised slots." },
  { id := "iterators-partition-range-overflow", juliaFile := "base/iterators.jl", juliaFns := ["iterate(::PartitionIterator{<:AbstractRange})", "collect"],
    statement := "partition(r, n) of r = IdentityUnitRange(fi:li) yields the chunks of n consecutive elements of r.", source := "base/iterators.jl:1426 (partition docstring)", status := .refuted,
    prop := ``PartitionRangeChunks, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsPartitionRangeOverflow_refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #40830; see bugs/iterators-partition-range-overflow.yaml",
    notes := "state + itr.n - 1 wraps near typemax(Int): the second chunk is empty, iteration never ends, and collect stores past the end (segfault)." },
  { id := "iterators-partition-generic-alloc", juliaFile := "base/iterators.jl", juliaFns := ["iterate(::PartitionIterator)"],
    statement := "The first chunk of partition(itr, n) of a nonempty tuple holds its first min(n, length) elements, for every n >= 1.", source := "base/iterators.jl:1426 (partition docstring)", status := .refuted,
    prop := ``PartitionFirstChunk, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsPartitionGenericAlloc_refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #45768; see bugs/iterators-partition-generic-alloc.yaml",
    notes := "The generic method allocates Vector(undef, n) per chunk: ArgumentError for n = typemax(Int), 800 MB for n = 10^8." },
  { id := "iterators-take-huge-count", juliaFile := "base/iterators.jl", juliaFns := ["take(xs, n)", "Take(xs, n::Integer)", "drop(xs, n)"],
    statement := "take(v, n) yields the first min(n, length(v)) elements and drop(v, n) yields the remaining elements for every nonnegative n of every Integer type.", source := "base/iterators.jl:790 (take docstring), 849 (drop docstring)", status := .refuted,
    prop := ``FirstNAnyInteger, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsTakeHugeCount_refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #19214, #19294; see bugs/iterators-take-huge-count.yaml",
    notes := "take(xs, n) = Take(xs, Int(n)) throws InexactError for n > typemax(Int); first(::AbstractVector, n) accepts it." },
  { id := "iterators-product-stateful-done", juliaFile := "base/iterators.jl", juliaFns := ["isdone(::ProductIterator, states)", "_pisdone"],
    statement := "product(itr) yields the 1-tuples of the elements of itr, for itr a vector or an Iterators.StatefulSnapshot.", source := "base/iterators.jl:1131-1133 (product docstring)", status := .todo,
    prop := ``ProductOneFactor, thm := none,
    issue := "none found (queries: product StatefulSnapshot, product eachline, tuple must be non-empty product; related closed #28753)",
    notes := "Statement defect: the completion callback ignores the iterator and invokes isdoneAfter at the initial none state, where the premise forces completion even for [1]. Dispatch through itr.isdone is required for the prose emission claim. This is a model adapter defect, not a Julia refutation." },
  { id := "iterators-take", juliaFile := "base/iterators.jl", juliaFns := ["take", "length(::Take)"],
    statement := "take(v, n) of a vector yields its first n elements and length(take(v, n)) == min(n, length(v)).", source := "base/iterators.jl:790 (take docstring)", status := .proven,
    prop := ``TakeCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsTake_proven, issue := "", notes := "" },
  { id := "iterators-take-take", juliaFile := "base/iterators.jl", juliaFns := ["take(::Take, n)"],
    statement := "Nested take uses each returned constructor result; representable counts preserve every prefix depth, and either oversized public Int conversion fails before iteration.", source := "take docstring; base/iterators.jl:790-833", status := .proven,
    prop := ``Round5.TakeTakeCorrect, thm := some ``takeTakeCorrect_proven, issue := "", notes := "" },
  { id := "iterators-drop", juliaFile := "base/iterators.jl", juliaFns := ["drop", "length(::Drop)"],
    statement := "drop(v, n) of a vector yields all but its first n elements and its length agrees.", source := "base/iterators.jl:849 (drop docstring)", status := .proven,
    prop := ``DropCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsDrop_proven, issue := "", notes := "" },
  { id := "iterators-take-drop-complement", juliaFile := "base/iterators.jl", juliaFns := ["take", "drop"],
    statement := "Take and Drop preserve both prefix and suffix observations across every finite reached source history; counts above Int64 fail at both public constructors.", source := "take/drop docstrings; base/iterators.jl:790-892", status := .proven,
    prop := ``Round5.TakeDropComplement, thm := some ``takeDropComplement_proven, issue := "", notes := "" },
  { id := "iterators-takewhile-dropwhile", juliaFile := "base/iterators.jl", juliaFns := ["takewhile", "dropwhile"],
    statement := "takewhile(p, v) yields the longest prefix satisfying p and dropwhile(p, v) the rest.", source := "base/iterators.jl:905, 952 (docstrings)", status := .proven,
    prop := ``TakeWhileDropWhile, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsTakewhileDropwhile_proven, issue := "", notes := "" },
  { id := "iterators-enumerate", juliaFile := "base/iterators.jl", juliaFns := ["enumerate", "length(::Enumerate)", "reverse(::Enumerate)"],
    statement := "enumerate(itr) numbers yielded elements starting at 1, preserves length(itr), and Iterators.reverse(enumerate(v)) yields the numbered pairs backwards.", source := "base/iterators.jl:173 (enumerate docstring)", status := .proven,
    prop := ``EnumerateCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsEnumerate_proven, issue := "", notes := "" },
  { id := "iterators-zip", juliaFile := "base/iterators.jl", juliaFns := ["zip", "length(::Zip)"],
    statement := "zip(a, b) of vectors yields the pairs up to the shorter length, which is its length.", source := "base/iterators.jl:343 (zip docstring)", status := .proven,
    prop := ``ZipCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsZip_proven, issue := "", notes := "" },
  { id := "iterators-zip-reverse", juliaFile := "base/iterators.jl", juliaFns := ["reverse(::Zip)"],
    statement := "Iterators.reverse(zip(a, b)) yields the pairs backwards for equal lengths and throws ArgumentError otherwise.", source := "base/iterators.jl:521-526", status := .proven,
    prop := ``ZipReverse, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsZipReverse_proven, issue := "", notes := "" },
  { id := "iterators-product", juliaFile := "base/iterators.jl", juliaFns := ["product", "size(::ProductIterator)"],
    statement := "product(a, b) of vectors yields all pairs with the first iterator changing fastest, and size is (length(a), length(b)).", source := "base/iterators.jl:1131-1133 (product docstring)", status := .proven,
    prop := ``ProductCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsProduct_proven, issue := "", notes := "" },
  { id := "iterators-flatten", juliaFile := "base/iterators.jl", juliaFns := ["flatten"],
    statement := "flatten(vs) of a vector of vectors yields their concatenation.", source := "base/iterators.jl:1268-1270 (flatten docstring)", status := .proven,
    prop := ``FlattenCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsFlatten_proven, issue := "", notes := "" },
  { id := "iterators-flatten-tuple-length", juliaFile := "base/iterators.jl", juliaFns := ["length(::Flatten)"],
    statement := "length(flatten(v)) for a vector of k-tuples is k * length(v), or OverflowError when that does not fit.", source := "invariant (length is the number of elements)", status := .proven,
    prop := ``FlattenTupleLength, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsFlattenTupleLength_proven, issue := "",
    notes := "Holds on master (checked_mul at base/iterators.jl:1327); 1.13.2 uses N * length(f.it), which wraps: length(cycle((1,2), 2^62)) == typemin(Int)." },
  { id := "iterators-cycle-n", juliaFile := "base/iterators.jl", juliaFns := ["cycle(xs, n)"],
    statement := "cycle(v, m) yields v m times.", source := "base/iterators.jl:1031-1035 (cycle docstring)", status := .proven,
    prop := ``CycleNCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsCycleN_proven, issue := "", notes := "" },
  { id := "iterators-repeated-n", juliaFile := "base/iterators.jl", juliaFns := ["repeated(x, n)"],
    statement := "repeated(x, n) yields x n times and has length n.", source := "base/iterators.jl:1088-1089 (repeated docstring)", status := .proven,
    prop := ``RepeatedNCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsRepeatedN_proven, issue := "", notes := "" },
  { id := "iterators-partition-vector", juliaFile := "base/iterators.jl", juliaFns := ["partition", "length(::PartitionIterator)"],
    statement := "partition(v, n) of a vector yields chunks of n elements, the last possibly shorter, and length is the number of chunks.", source := "base/iterators.jl:1426 (partition docstring)", status := .refuted,
    prop := ``PartitionVectorCorrect, thm := some ``JuliaLean.ChatGPT.Batch5.Group5.IteratorsPartitionVector_refuted, issue := "see bugs/iterators-partition-vector.yaml", notes := "" },
  { id := "iterators-stateful", juliaFile := "base/iterators.jl", juliaFns := ["StatefulSnapshot", "isdone(::StatefulSnapshot)", "peek", "popfirst!"],
    statement := "A StatefulSnapshot that has produced pos elements: isdone/isempty say whether elements remain, peek/popfirst! return the next one (or sentinel / EOFError when none remain), and collect returns the rest.", source := "base/iterators.jl:1505-1560 (StatefulSnapshot docstring)", status := .todo,
    prop := ``StatefulConsistent, thm := none, issue := "",
    notes := "Statement defect: the live transition requires a successful unchanged cache update for arbitrary assertValue callbacks, including callbacks that reject or transform the value. A faithful reachable-snapshot invariant or an explicit cache-acceptance premise is required; public Julia Stateful exposes no such arbitrary callback. No Julia bug is claimed." },
  { id := "iterators-only", juliaFile := "base/iterators.jl", juliaFns := ["only"],
    statement := "only(v) returns the element of a one-element vector and throws ArgumentError otherwise. All protocols, finite or infinite, with empty/singleton/multiple cardinality and first/second-step errors determined by observations, not callee-answer hypotheses.", source := "base/iterators.jl:1632-1633 (only docstring)", status := .proven,
    prop := ``Round4.OnlyCorrect, thm := some ``onlyCorrect_proven, issue := "", notes := "" },
  { id := "iterators-accumulate", juliaFile := "base/iterators.jl", juliaFns := ["Iterators.accumulate"],
    statement := "Iterators.accumulate(f, v; init) yields the running reductions and has length(v) elements.", source := "base/iterators.jl:612-616 (accumulate docstring)", status := .proven,
    prop := ``AccumulateCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsAccumulate_proven, issue := "", notes := "" },
  { id := "iterators-nth-vector", juliaFile := "base/iterators.jl", juliaFns := ["nth(::AbstractArray, n)"],
    statement := "nth(v, n) of a vector is v[n] for 1 <= n <= length(v) and BoundsError otherwise, for n of every integer type.", source := "base/iterators.jl:1730 (nth docstring)", status := .proven,
    prop := ``NthVectorCorrect, thm := some ``nthVectorCorrect_proven, issue := "", notes := "" },
  { id := "iterators-countfrom", juliaFile := "base/iterators.jl", juliaFns := ["countfrom"],
    statement := "countfrom(s, d) yields s, s + d, s + 2d, ... with Int wraparound.", source := "base/iterators.jl:751 (countfrom docstring)", status := .proven,
    prop := ``CountfromCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorsCountfrom_proven, issue := "", notes := "" },
  { id := "iteratorscov-pairs-semantics", juliaFile := "base/iterators.jl", juliaFns := ["pairs", "_pairs_elt", "iterate(::Pairs)", "iterate(::Reverse{<:Pairs})", "length(::Pairs)", "axes(::Pairs)", "size(::Pairs)", "isdone(::Pairs)", "last(::Pairs)", "haskey(::Pairs)", "keys(::Pairs)", "values(::Pairs)", "getindex(::Pairs)", "setindex!(::Pairs)", "get(::Pairs)"],
    statement := "Pairs retains the selected keys and data, iterates corresponding key-value pairs in order, delegates metadata and lookup, and reverse iteration reverses those pairs.", source := "pairs docstring and dictionary invariants; base/iterators.jl:281-332", status := .proven,
    prop := ``PairsSemantics, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorscovPairsSemantics_proven, issue := "", notes := "" },
  { id := "iteratorscov-cycle-repeated", juliaFile := "base/iterators.jl", juliaFns := ["map", "findeach", "cycle", "repeated", "iterate(::Cycle)", "iterate(::Repeated)", "reverse(::Cycle)", "reverse(::Repeated)", "last(::Cycle)", "last(::Repeated)", "flatmap"],
    statement := "Iterator map builds a Generator, findeach returns matching keys, finite cycle and repeated return their documented repetitions, and flatmap concatenates mapped collections.", source := "map, findeach, cycle, repeated and flatmap docstrings; base/iterators.jl:56,995-1121,1421", status := .proven,
    prop := ``CycleRepeatedSemantics, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorscovCycleRepeated_proven, issue := "", notes := "" },
  { id := "iteratorscov-iterable-state-pairs", juliaFile := "base/iterators.jl", juliaFns := ["IterableStatePairs", "iterate(::IterableStatePairs)", "reverse(::IterableStatePairs)", "pairs(::AbstractString)"],
    statement := "IterableStatePairs pairs each iteration state with its value, preserves length and element order, and reverse pairs reverse both sequences.", source := "IterableStatePairs invariant; base/iterators.jl:1693-1725", status := .proven,
    prop := ``IterableStatePairsSemantics, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorscovIterableStatePairs_proven, issue := "", notes := "" },
  { id := "iteratorscov-product-methods", juliaFile := "base/iterators.jl", juliaFns := ["product", "size(::ProductIterator)", "axes(::ProductIterator)", "ndims(::ProductIterator)", "length(::ProductIterator)", "IteratorEltype(::ProductIterator)", "eltype(::ProductIterator)", "iterate(::ProductIterator)", "_piterate", "_piterate1", "reverse(::ProductIterator)", "last(::ProductIterator)"],
    statement := "ProductIterator implements Cartesian-product order, truthful finite metadata, empty-product and odometer iteration, componentwise reverse, and componentwise last.", source := "product docstring and collection invariants; base/iterators.jl:1148-1256", status := .proven,
    prop := ``ProductMethodSemantics, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorscovProductMethods_proven, issue := "", notes := "" },
  { id := "iteratorscov-flatten-methods", juliaFile := "base/iterators.jl", juliaFns := ["flatten", "eltype(::Flatten)", "IteratorEltype(::Flatten)", "IteratorSize(::Flatten)", "flatten_length", "length(::Flatten)", "iterate(::Flatten)", "reverse(::Flatten)", "last(::Flatten)"],
    statement := "Flatten concatenates inner iterators and implements its documented type, size, length, reverse and last behavior.", source := "flatten docstring and invariants; base/iterators.jl:1268-1380", status := .proven,
    prop := ``FlattenMethodSemantics, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorscovFlattenMethods_proven, issue := "", notes := "" },
  { id := "iteratorscov-partition-methods", juliaFile := "base/iterators.jl", juliaFns := ["partition", "PartitionIterator", "eltype(::PartitionIterator)", "IteratorEltype(::PartitionIterator)", "IteratorSize(::PartitionIterator)", "length(::PartitionIterator)", "iterate(::PartitionIterator)"],
    statement := "Partition rejects nonpositive counts, yields consecutive chunks with a shorter final chunk, and computes its element type, size trait and number of chunks.", source := "partition docstring; base/iterators.jl:1426-1502", status := .refuted,
    prop := ``PartitionMethodSemantics, thm := some ``JuliaLean.ChatGPT.Batch5.Group5.IteratorscovPartitionMethods_refuted, issue := "see bugs/iteratorscov-partition-methods.yaml", notes := "" },
  { id := "iteratorscov-stateful-methods", juliaFile := "base/iterators.jl", juliaFns := ["StatefulSnapshot", "reset!", "approx_iter_type", "doiterate", "_approx_iter_type", "convert(::Type{StatefulSnapshot})", "isdone(::StatefulSnapshot)", "popfirst!(::StatefulSnapshot)", "peek(::StatefulSnapshot)", "iterate(::StatefulSnapshot)", "IteratorSize(::StatefulSnapshot)", "eltype(::StatefulSnapshot)", "IteratorEltype(::StatefulSnapshot)"],
    statement := "StatefulSnapshot stores the next value-state pair, resumes destructively, resets to the first pair, reports exhaustion consistently, and uses the documented conservative type approximation.", source := "StatefulSnapshot docstring and invariants; base/iterators.jl:1505-1627", status := .todo,
    prop := ``StatefulMethodSemantics, thm := none, issue := "", notes := "Statement defect: the live transition requires a successful unchanged cache update for arbitrary assertValue callbacks, including callbacks that reject or transform the value. A faithful reachable-snapshot invariant or an explicit cache-acceptance premise is required; public Julia Stateful exposes no such arbitrary callback. No Julia bug is claimed." },
  { id := "iteratorscov-only-nth-methods", juliaFile := "base/iterators.jl", juliaFns := ["only", "_only", "nth", "_nth"],
    statement := "only returns exactly one element and rejects other cardinalities; nth returns the requested element or BoundsError and its curried form delegates to nth.", source := "only and nth docstrings; base/iterators.jl:1632-1690,1730-1810", status := .proven,
    prop := ``OnlyNthMethodSemantics, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorscovOnlyNthMethods_proven, issue := "", notes := "" },
  { id := "iteratorscov-zip-metadata", juliaFile := "base/iterators.jl", juliaFns := ["length(::Zip)", "_zip_min_length", "_zip_lengths_finite_equal", "size(::Zip)", "axes(::Zip)", "_promote_tuple_shape", "eltype(::Zip)", "last(::Zip)"],
    statement := "Zip computes the shortest finite length, promotes compatible shapes, constructs its tuple eltype and returns the component values at the last shared index.", source := "zip docstring and invariants; base/iterators.jl:380-425,519", status := .proven,
    prop := ``ZipMetadata, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorscovZipMetadata_proven, issue := "", notes := "" },
  { id := "iteratorscov-zip-traits", juliaFile := "base/iterators.jl", juliaFns := ["zip_iteratorsize", "zip_iteratoreltype", "IteratorSize(::Type{Zip})", "IteratorEltype(::Type{Zip})"],
    statement := "Zip's size trait agrees with the shortest component and its eltype trait is known exactly when every component's is known. Source-dispatched trait composition for arbitrary arity, independent mathematical shortest-component count, exact shape information and known-eltype condition.", source := "zip docstring and invariant; base/iterators.jl:503-517", status := .proven,
    prop := ``Round4.ZipTraitsSound, thm := some ``zipTraitsSound_proven, issue := "", notes := "" },
  { id := "iteratorscov-product-empty-infinite", juliaFile := "base/iterators.jl", juliaFns := ["prod_iteratorsize", "IteratorSize(::Type{ProductIterator})"],
    statement := "The public ProductIterator size query agrees with independent factor cardinality for arbitrary reflected traits, including empty tuples and zero times infinity.", source := "product size trait; base/iterators.jl:1148-1170", status := .refuted,
    prop := ``Round5.ProductSizeQuerySound, thm := some ``productEmptyInfiniteQuery_refuted, issue := "bugs/iteratorscov-product-empty-infinite.yaml; related issue #53169 (Iterators.cycle, IteratorSize).", notes := "" },
  { id := "iteratorscov-product-shape-finite", juliaFile := "base/iterators.jl", juliaFns := ["prod_iteratorsize", "IteratorSize(::Type{ProductIterator})"],
    statement := "The public ProductIterator query agrees with factor cardinality when no factor is infinite, retains unknown-size factors in the count claim, and sums known dimensions.", source := "product size trait; base/iterators.jl:1148-1170", status := .proven,
    prop := ``Round5.ProductFiniteQuerySound, thm := some ``productFiniteQuerySound_proven, issue := "", notes := "" },
  { id := "iteratorscov-product-eltype-trait", juliaFile := "base/iterators.jl", juliaFns := ["IteratorEltype(::Type{ProductIterator})"],
    statement := "ProductIterator reports HasEltype exactly when every factor reports HasEltype.", source := "invariant; base/iterators.jl:1188-1195", status := .proven,
    prop := ``ProductIelSpec, thm := some ``productIelSpec_proven, issue := "", notes := "" },
  { id := "iteratorscov-take", juliaFile := "base/iterators.jl", juliaFns := ["Take", "take", "iterate(::Take)", "IteratorSize(::Type{Take})", "length(::Take)", "isdone(::Take)"],
    statement := "Take rejects negative Int counts, yields the requested prefix, and preserves truthful size, eltype and isdone information.", source := "take docstring; base/iterators.jl:790-833", status := .proven,
    prop := ``TakeSound, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorscovTake_proven, issue := "", notes := "" },
  { id := "iteratorscov-drop", juliaFile := "base/iterators.jl", juliaFns := ["Drop", "drop", "iterate(::Drop)", "IteratorSize(::Type{Drop})", "length(::Drop)", "isdone(::Drop)"],
    statement := "Drop rejects negative Int counts, yields the suffix after the count, and preserves truthful size, eltype and isdone information.", source := "drop docstring; base/iterators.jl:849-892", status := .proven,
    prop := ``DropSound, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorscovDrop_proven, issue := "", notes := "" },
  { id := "iteratorscov-countfrom-eltype", juliaFile := "base/iterators.jl", juliaFns := ["countfrom(start::Number, step::Number)", "countfrom(start)", "eltype(::Type{Count})", "iterate(::Count)"],
    statement := "The declared eltype of countfrom contains every value that its iterate methods yield.", source := "eltype docstring; countfrom docstring at base/iterators.jl:748-751", status := .refuted,
    prop := ``CountfromEltype, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorscovCountfromEltype_refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #37747; see bugs/iteratorscov-countfrom-eltype.yaml",
    notes := "countfrom(true) reports Bool but yields 2::Int64 on its second step." },
  { id := "iteratorscov-countfrom-integers", juliaFile := "base/iterators.jl", juliaFns := ["countfrom", "iterate(::Count)"],
    statement := "For Int inputs, countfrom yields the wrapped additive chain with the declared Int element type.", source := "countfrom docstring; base/iterators.jl:748-772", status := .proven,
    prop := ``CountfromInts, thm := some ``countfromInts_proven, issue := "", notes := "" },
  { id := "iteratorscov-filter", juliaFile := "base/iterators.jl", juliaFns := ["filter", "iterate(::Filter)", "last(::Filter)", "IteratorSize(::Type{Filter})"],
    statement := "Filter yields exactly the elements satisfying its predicate in order, with a truthful eltype and last result.", source := "filter docstring; base/iterators.jl:536-599", status := .proven,
    prop := ``FilterSound, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorscovFilter_proven, issue := "", notes := "" },
  { id := "iteratorscov-accumulate", juliaFile := "base/iterators.jl", juliaFns := ["accumulate", "iterate(::Accumulate)", "length(::Accumulate)", "size(::Accumulate)"],
    statement := "Accumulate yields the documented running reductions and preserves the wrapped iterator's finite length and size.", source := "accumulate docstring; base/iterators.jl:612-665", status := .proven,
    prop := ``AccumulateSound, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorscovAccumulate_proven, issue := "", notes := "" },
  { id := "iteratorscov-rest", juliaFile := "base/iterators.jl", juliaFns := ["rest", "iterate(::Rest)", "eltype(::Type{Rest})", "IteratorEltype(::Type{Rest})", "IteratorSize(::Type{Rest})"],
    statement := "Rest starts from a state reached by a nonempty history, resumes the exact suffix at every depth, composes with the newest state, and forwards element-type and size traits.", source := "rest docstring and trait methods; base/iterators.jl:677-739", status := .proven,
    prop := ``Round5.RestSound, thm := some ``restSound_proven, issue := "", notes := "" },
  { id := "iteratorscov-while", juliaFile := "base/iterators.jl", juliaFns := ["takewhile", "dropwhile", "iterate(::TakeWhile)", "iterate(::DropWhile)"],
    statement := "TakeWhile yields the longest satisfying prefix and DropWhile yields the remaining suffix, both with truthful eltypes.", source := "takewhile and dropwhile docstrings; base/iterators.jl:895-990", status := .proven,
    prop := ``WhileSound, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorscovWhile_proven, issue := "", notes := "" },
  { id := "iteratorscov-enumerate", juliaFile := "base/iterators.jl", juliaFns := ["enumerate", "iterate(::Enumerate)", "length(::Enumerate)", "size(::Enumerate)", "last(::Enumerate)", "reverse(::Enumerate)"],
    statement := "Enumerate numbers yielded elements from one, preserves size and eltype facts, computes last, and reverses the numbered pairs.", source := "enumerate docstring; base/iterators.jl:173-213", status := .proven,
    prop := ``EnumerateSound, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorscovEnumerate_proven, issue := "", notes := "" },
  { id := "iteratorscov-reverse-yields", juliaFile := "base/iterators.jl", juliaFns := ["reverse", "iterate(::Reverse)", "reverse(::Pair)", "reverse(::Generator)"],
    statement := "The covered Reverse methods yield exactly the wrapped elements backwards, and reversing twice restores the elements.", source := "reverse docstring; base/iterators.jl:81-162", status := .proven,
    prop := ``ReverseYields, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorscovReverseYields_proven, issue := "", notes := "" },
  { id := "iteratorscov-reverse-traits", juliaFile := "base/iterators.jl", juliaFns := ["eltype(::Type{Reverse})", "length(::Reverse)", "size(::Reverse)", "IteratorSize(::Type{Reverse})", "IteratorEltype(::Type{Reverse})", "last(::Reverse)"],
    statement := "Reverse preserves array and tuple traits and last(Reverse(A)) is first(A); reversing Bottom throws ArgumentError.", source := "invariant; base/iterators.jl:128-154", status := .proven,
    prop := ``ReverseTraits, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorscovReverseTraits_proven, issue := "", notes := "" },
  { id := "iteratorscov-zip-protocol", juliaFile := "base/iterators.jl", juliaFns := ["_zip_isdone", "_zip_iterate_in_order", "_zip_iterate_all", "_zip_any_isdone", "iterate(::Zip)", "isdone(::Zip)"],
    statement := "Zip steps live components in order, preserves an all-false isdone answer, and stops its isdone scan at the first true answer.", source := "zip docstring and invariant; base/iterators.jl:430-501", status := .proven,
    prop := ``ZipProtocol, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorscovZipProtocol_proven, issue := "", notes := "" },
  { id := "iteratorscov-product-intersect-arity", juliaFile := "base/iterators.jl", juliaFns := ["intersect(::ProductIterator, ::ProductIterator)"],
    statement := "The intersection of two products with different tuple arities is empty because tuples of different arity cannot be equal.", source := "intersect docstring; base/iterators.jl:1257", status := .refuted,
    prop := ``ProductIntersect, thm := some ``JuliaLean.ChatGPT.Batch4.Group5.IteratorscovProductIntersectArity_refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #39943, #39949; see bugs/iteratorscov-product-intersect-arity.yaml",
    notes := "Tuple broadcasting repeats a one-factor product against a two-factor product and returns four two-tuples." },
  { id := "iteratorsr4-count-default-progression", juliaFile := "base/iterators.jl", juliaFns := ["countfrom()", "iterate(::Count)"],
    statement := "The actual zero-argument countfromDefault constructor emits the wrapped Int sequence 1,2,3,... at every observation depth through installed iterateCountState and int.add_int.", source := "countfrom docstring; base/iterators.jl:748-772", status := .proven,
    prop := ``Round4.CountDefaultProgression, thm := some ``countDefaultProgression_proven, issue := "", notes := "" },
  { id := "iteratorsr4-cycle-output", juliaFile := "base/iterators.jl", juliaFns := ["cycle", "iterate(::Cycle)"],
    statement := "Every finite output observation consists of complete nonempty source rounds and a possibly unfinished source prefix; infinite sources need no terminating round, and an initially empty source yields no values at every depth.", source := "cycle docstring; base/iterators.jl:1028-1121", status := .proven,
    prop := ``Round4.CycleOutputSemantics, thm := some ``cycleOutputSemantics_proven, issue := "", notes := "" },
  { id := "iteratorsr4-drop-suffix", juliaFile := "base/iterators.jl", juliaFns := ["drop", "iterate(::Drop)"],
    statement := "Drop yields the requested suffix for each representable nonnegative Int count, preserving skipped errors and early exhaustion; larger counts fail before iteration.", source := "drop docstring; base/iterators.jl:840-892", status := .proven,
    prop := ``Round5.DropSuffix, thm := some ``dropSuffix_proven, issue := "", notes := "" },
  { id := "iteratorsr4-empty-zip-infinite", juliaFile := "base/iterators.jl", juliaFns := ["zip", "iterate(::Zip)"],
    statement := "Actual zero-factor Zip iteration yields an empty tuple at every observation depth, including depths beyond any finite prefix.", source := "zip iteration and docstring; base/iterators.jl:430-517", status := .proven,
    prop := ``Round4.EmptyZipInfinite, thm := some ``emptyZipInfinite_proven, issue := "", notes := "" },
  { id := "iteratorsr4-enumerate-forward", juliaFile := "base/iterators.jl", juliaFns := ["enumerate", "iterate(::Enumerate)"],
    statement := "Every output value retains its source position and source Int counter at every depth for an arbitrary protocol.", source := "enumerate docstring; base/iterators.jl:173-213", status := .proven,
    prop := ``Round4.EnumerateForward, thm := some ``enumerateForward_proven, issue := "", notes := "" },
  { id := "iteratorsr4-enumerate-reverse-state", juliaFile := "base/iterators.jl", juliaFns := ["iterate(::Reverse{<:Enumerate})"],
    statement := "The actual installed sourceMethod228 decrements native counters while preserving every observed suffix value of an arbitrary reverse-iterator extension.", source := "reverse(enumerate) iteration; base/iterators.jl:224-229", status := .proven,
    prop := ``Round4.EnumerateReverseState, thm := some ``enumerateReverseState_proven, issue := "", notes := "" },
  { id := "iteratorsr4-nth-protocol", juliaFile := "base/iterators.jl", juliaFns := ["nth", "_nth"],
    statement := "Installed nthModel returns the requested observed ordinal, BoundsError for nonpositive/missing positions and the source error for failed iteration.", source := "nth docstring; base/iterators.jl:1730-1810", status := .proven,
    prop := ``Round4.NthProtocol, thm := some ``nthProtocol_proven, issue := "", notes := "" },
  { id := "iteratorsr4-partition-native-length", juliaFile := "base/iterators.jl", juliaFns := ["partition", "length(::PartitionIterator)"],
    statement := "Installed partitionLengthInt/cld computes the least covering number of chunks for every nonnegative native length and positive native count, and propagates division by zero.", source := "partition docstring; base/iterators.jl:1426-1479", status := .proven,
    prop := ``Round4.PartitionNativeLength, thm := some ``partitionNativeLength_proven, issue := "", notes := "" },
  { id := "iteratorsr4-peel-reconstructs", juliaFile := "base/iterators.jl", juliaFns := ["peel", "iterate(::Rest)"],
    statement := "The actual returned Rest reconstructs every finite observation of the original protocol, without source termination assumptions.", source := "peel docstring; base/iterators.jl:700-704", status := .proven,
    prop := ``Round4.PeelReconstructs, thm := some ``peelReconstructs_proven, issue := "", notes := "" },
  { id := "iteratorsr4-product-trait-cardinality", juliaFile := "base/iterators.jl", juliaFns := ["prod_iteratorsize", "IteratorSize(::Type{ProductIterator})"],
    statement := "Installed recursive prod_iteratorsize dispatch agrees with independent mathematical product cardinality for every compatible input tag/count, including empty finite times infinite.", source := "product size trait; base/iterators.jl:1148-1167", status := .refuted,
    prop := ``Round4.ProductSizeSound, thm := some ``productTraitCardinality_refuted, issue := "gh search issues/prs --repo JuliaLang/julia --limit 100 'product empty infinite IteratorSize' -> []; 'IteratorSize product empty countfrom' -> []; 'product empty countfrom' -> []; related issue #53169 (same class, different iterator; OPEN, `Iterators.cycle`, `IteratorSize`: infinite but empty iterator).",
    notes := "product(1:0, countfrom()) is empty but reports IsInfinite(). possible out-of-bounds read: take on empty product returns uninitialized values (1.13.2)." },
  { id := "iteratorsr4-repeated-outputs", juliaFile := "base/iterators.jl", juliaFns := ["repeated", "iterate(::Repeated)", "take"],
    statement := "Repeated yields the same element at every depth; finite repetition observes its returned Take for representable counts and reports Int64 conversion errors otherwise.", source := "repeated docstring; base/iterators.jl:1085-1121", status := .proven,
    prop := ``Round5.RepeatedOutputs, thm := some ``repeatedOutputs_proven, issue := "", notes := "" },
  { id := "iteratorsr4-take-prefix", juliaFile := "base/iterators.jl", juliaFns := ["take", "iterate(::Take)"],
    statement := "Take yields the requested prefix for each representable nonnegative Int count and every depth; counts above Int64 fail before iteration.", source := "take docstring; base/iterators.jl:790-833", status := .proven,
    prop := ``Round5.TakePrefix, thm := some ``takePrefix_proven, issue := "", notes := "" },
]

/-- Julia methods and the source-backed properties that cover them. -/
def methodPropertyTable : List (String × List String) := [
  ("map@56", ["iteratorscov-cycle-repeated"]),
  ("_min_length@58", ["iteratorscov-length-helpers"]),
  ("_min_length@59", ["iteratorscov-length-helpers"]),
  ("_min_length@60", ["iteratorscov-length-helpers"]),
  ("_min_length@61", ["iteratorscov-length-helpers"]),
  ("_diff_length@63", ["iteratorscov-length-helpers"]),
  ("_diff_length@64", ["iteratorscov-length-helpers"]),
  ("_diff_length@65", ["iteratorscov-length-helpers"]),
  ("_diff_length@66", ["iteratorscov-length-helpers"]),
  ("and_iteratorsize@71", ["iteratorscov-trait-composition"]),
  ("and_iteratorsize@72", ["iteratorscov-trait-composition"]),
  ("and_iteratorsize@73", ["iteratorscov-trait-composition"]),
  ("and_iteratorsize@74", ["iteratorscov-trait-composition"]),
  ("and_iteratorsize@75", ["iteratorscov-trait-composition"]),
  ("and_iteratorsize@76", ["iteratorscov-trait-composition"]),
  ("and_iteratoreltype@78", ["iteratorscov-trait-composition"]),
  ("and_iteratoreltype@79", ["iteratorscov-trait-composition"]),
  ("reverse@113", ["iteratorscov-reverse-yields"]),
  ("eltype@128", ["iteratorscov-reverse-traits"]),
  ("length@129", ["iteratorscov-reverse-traits"]),
  ("size@130", ["iteratorscov-reverse-traits"]),
  ("IteratorSize@131", ["iteratorscov-reverse-traits"]),
  ("IteratorEltype@132", ["iteratorscov-reverse-traits"]),
  ("last@133", ["iteratorscov-reverse-traits"]),
  ("iterate@136", ["iteratorscov-reverse-yields"]),
  ("iterate@145", ["iteratorscov-reverse-yields"]),
  ("iterate@153", ["iteratorscov-reverse-yields", "iteratorscov-reverse-traits"]),
  ("iterate@154", ["iteratorscov-reverse-yields", "iteratorscov-reverse-traits"]),
  ("reverse@156", ["iteratorscov-reverse-yields"]),
  ("reverse@157", ["iteratorscov-reverse-yields"]),
  ("reverse@158", ["iteratorscov-reverse-yields"]),
  ("reverse@159", ["iteratorscov-reverse-yields"]),
  ("reverse@160", ["iteratorscov-reverse-yields"]),
  ("iterate@162", ["iteratorscov-reverse-yields"]),
  ("enumerate@207", ["iterators-enumerate"]),
  ("length@209", ["iterators-enumerate"]),
  ("size@210", ["iteratorscov-enumerate"]),
  ("iterate@211", ["iteratorscov-enumerate"]),
  ("last@217", ["iteratorscov-enumerate"]),
  ("eltype@219", ["iteratorscov-enumerate"]),
  ("IteratorSize@221", ["iteratorscov-enumerate"]),
  ("IteratorEltype@222", ["iteratorscov-enumerate"]),
  ("iterate@224", ["iteratorscov-enumerate"]),
  ("iterate@228", ["iteratorscov-enumerate"]),
  ("pairs@281", ["iteratorscov-pairs-semantics"]),
  ("pairs@285", ["iteratorscov-pairs-semantics"]),
  ("pairs@286", ["iteratorscov-pairs-semantics"]),
  ("pairs@287", ["iteratorscov-pairs-semantics"]),
  ("pairs@288", ["iteratorscov-pairs-semantics"]),
  ("pairs@291", ["iteratorscov-pairs-semantics"]),
  ("pairs@292", ["iteratorscov-pairs-semantics"]),
  ("length@294", ["iteratorscov-pairs-semantics"]),
  ("axes@295", ["iteratorscov-pairs-semantics"]),
  ("size@296", ["iteratorscov-pairs-semantics"]),
  ("_pairs_elt@298", ["iteratorscov-pairs-semantics"]),
  ("iterate@302", ["iteratorscov-pairs-semantics"]),
  ("iterate@309", ["iteratorscov-pairs-semantics"]),
  ("isdone@316", ["iteratorscov-pairs-semantics"]),
  ("IteratorSize@318", ["iteratorscov-pairs-semantics"]),
  ("IteratorSize@319", ["iteratorscov-pairs-semantics"]),
  ("last@321", ["iteratorscov-pairs-semantics"]),
  ("haskey@326", ["iteratorscov-pairs-semantics"]),
  ("keys@327", ["iteratorscov-pairs-semantics"]),
  ("values@328", ["iteratorscov-pairs-semantics"]),
  ("getindex@329", ["iteratorscov-pairs-semantics"]),
  ("setindex!@330", ["iteratorscov-pairs-semantics"]),
  ("get@331", ["iteratorscov-pairs-semantics"]),
  ("get@332", ["iteratorscov-pairs-semantics"]),
  ("zip@379", ["iterators-take-isdone-zero", "iterators-zip"]),
  ("length@380", ["iterators-zip"]),
  ("_zip_min_length@385", ["iteratorscov-zip-metadata"]),
  ("_zip_min_length@394", ["iteratorscov-zip-metadata"]),
  ("_zip_lengths_finite_equal@401", ["iteratorscov-zip-metadata"]),
  ("_zip_lengths_finite_equal@411", ["iteratorscov-zip-metadata"]),
  ("size@412", ["iteratorscov-zip-metadata"]),
  ("axes@413", ["iteratorscov-zip-metadata"]),
  ("_promote_tuple_shape@414", ["iteratorscov-zip-metadata"]),
  ("_promote_tuple_shape@415", ["iteratorscov-zip-metadata"]),
  ("_promote_tuple_shape@416", ["iteratorscov-zip-metadata"]),
  ("_promote_tuple_shape@417", ["iteratorscov-zip-metadata"]),
  ("_promote_tuple_shape@418", ["iteratorscov-zip-metadata"]),
  ("eltype@425", ["iteratorscov-zip-metadata"]),
  ("isdone@430", ["iteratorscov-zip-protocol"]),
  ("isdone@431", ["iteratorscov-zip-protocol"]),
  ("_zip_any_isdone@433", ["iteratorscov-zip-protocol"]),
  ("_zip_any_isdone@438", ["iteratorscov-zip-protocol"]),
  ("iterate@440", ["iteratorscov-zip-protocol"]),
  ("iterate@441", ["iteratorscov-zip-protocol"]),
  ("_zip_iterate_all@448", ["iteratorscov-zip-protocol"]),
  ("_zip_all_missing@462", ["iteratorscov-zip-protocol"]),
  ("_zip_all_missing@463", ["iteratorscov-zip-protocol"]),
  ("_zip_iterate_in_order@465", ["iteratorscov-zip-protocol"]),
  ("_zip_iterate_in_order@472", ["iteratorscov-zip-protocol"]),
  ("_zip_iterate_unknown@478", ["iteratorscov-zip-protocol"]),
  ("_zip_iterate_unknown@485", ["iteratorscov-zip-protocol"]),
  ("_zip_iterate_rest@487", ["iteratorscov-zip-protocol"]),
  ("_zip_iterate_rest@494", ["iteratorscov-zip-protocol"]),
  ("_zip_isdone@496", ["iteratorscov-zip-protocol"]),
  ("_zip_isdone@501", ["iteratorscov-zip-protocol"]),
  ("IteratorSize@503", ["iteratorscov-zip-traits"]),
  ("IteratorEltype@504", ["iteratorscov-zip-traits"]),
  ("zip_iteratorsize@506", ["iteratorscov-zip-traits"]),
  ("zip_iteratorsize@507", ["iteratorscov-zip-traits"]),
  ("zip_iteratorsize@508", ["iteratorscov-zip-traits"]),
  ("zip_iteratorsize@509", ["iteratorscov-zip-traits"]),
  ("zip_iteratorsize@510", ["iteratorscov-zip-traits"]),
  ("zip_iteratorsize@511", ["iteratorscov-zip-traits"]),
  ("zip_iteratorsize@512", ["iteratorscov-zip-traits"]),
  ("zip_iteratorsize@513", ["iteratorscov-zip-traits"]),
  ("zip_iteratoreltype@515", ["iteratorscov-zip-traits"]),
  ("zip_iteratoreltype@516", ["iteratorscov-zip-traits"]),
  ("zip_iteratoreltype@517", ["iteratorscov-zip-traits"]),
  ("last@519", ["iteratorscov-zip-metadata"]),
  ("reverse@521", ["iterators-zip-reverse"]),
  ("filter@576", ["iteratorscov-filter"]),
  ("iterate@578", ["iteratorscov-filter"]),
  ("eltype@594", ["iteratorscov-filter"]),
  ("IteratorEltype@595", ["iteratorscov-filter"]),
  ("IteratorSize@596", ["iteratorscov-filter"]),
  ("reverse@598", ["iteratorscov-filter"]),
  ("last@599", ["iteratorscov-filter"]),
  ("accumulate@641", ["iterators-accumulate"]),
  ("iterate@643", ["iteratorscov-accumulate"]),
  ("iterate@652", ["iteratorscov-accumulate"]),
  ("length@661", ["iteratorscov-accumulate"]),
  ("size@662", ["iteratorscov-accumulate"]),
  ("IteratorSize@664", ["iteratorscov-accumulate"]),
  ("IteratorEltype@665", ["iteratorscov-accumulate"]),
  ("rest@696", ["iteratorscov-rest"]),
  ("rest@697", ["iteratorscov-rest"]),
  ("rest@698", ["iteratorscov-rest"]),
  ("peel@725", ["iterators-rest-isdone-state"]),
  ("iterate@732", ["iteratorscov-rest"]),
  ("isdone@733", ["iterators-rest-isdone-state"]),
  ("eltype@735", ["iteratorscov-rest"]),
  ("IteratorEltype@736", ["iteratorscov-rest"]),
  ("rest_iteratorsize@737", ["iteratorscov-rest"]),
  ("rest_iteratorsize@738", ["iteratorscov-rest"]),
  ("IteratorSize@739", ["iteratorscov-rest"]),
  ("countfrom@764", ["iteratorscov-countfrom-eltype"]),
  ("countfrom@765", ["iteratorscov-countfrom-eltype"]),
  ("countfrom@766", ["iteratorscov-countfrom-eltype"]),
  ("countfrom@767", ["iteratorscov-countfrom-eltype"]),
  ("eltype@770", ["iteratorscov-countfrom-eltype"]),
  ("iterate@772", ["iteratorscov-countfrom-eltype"]),
  ("IteratorSize@774", ["iteratorscov-countfrom-eltype"]),
  ("Take@781", ["iteratorscov-take"]),
  ("take@815", ["iteratorscov-take"]),
  ("take@816", ["iteratorscov-take"]),
  ("eltype@818", ["iteratorscov-take"]),
  ("IteratorEltype@819", ["iteratorscov-take"]),
  ("take_iteratorsize@820", ["iteratorscov-take"]),
  ("take_iteratorsize@821", ["iteratorscov-take"]),
  ("IteratorSize@822", ["iteratorscov-take"]),
  ("length@823", ["iterators-cycle-empty-length", "iterators-take"]),
  ("isdone@824", ["iteratorscov-take"]),
  ("isdone@825", ["iteratorscov-take"]),
  ("iterate@827", ["iteratorscov-take"]),
  ("Drop@840", ["iteratorscov-drop"]),
  ("drop@871", ["iteratorscov-drop"]),
  ("drop@872", ["iteratorscov-drop"]),
  ("drop@873", ["iteratorscov-drop"]),
  ("eltype@875", ["iteratorscov-drop"]),
  ("IteratorEltype@876", ["iteratorscov-drop"]),
  ("drop_iteratorsize@877", ["iteratorscov-drop"]),
  ("drop_iteratorsize@878", ["iteratorscov-drop"]),
  ("drop_iteratorsize@879", ["iteratorscov-drop"]),
  ("IteratorSize@880", ["iteratorscov-drop"]),
  ("length@881", ["iterators-drop"]),
  ("iterate@883", ["iteratorscov-drop"]),
  ("iterate@891", ["iteratorscov-drop"]),
  ("isdone@892", ["iteratorscov-drop"]),
  ("takewhile@928", ["iterators-takewhile-dropwhile"]),
  ("iterate@930", ["iteratorscov-while"]),
  ("IteratorSize@937", ["iteratorscov-while"]),
  ("eltype@938", ["iteratorscov-while"]),
  ("IteratorEltype@939", ["iteratorscov-while"]),
  ("dropwhile@976", ["iterators-takewhile-dropwhile"]),
  ("iterate@978", ["iteratorscov-while"]),
  ("iterate@979", ["iteratorscov-while"]),
  ("IteratorSize@988", ["iteratorscov-while"]),
  ("eltype@989", ["iteratorscov-while"]),
  ("IteratorEltype@990", ["iteratorscov-while"]),
  ("findeach@1016", ["iteratorscov-cycle-repeated"]),
  ("findeach@1018", ["iteratorscov-cycle-repeated"]),
  ("cycle@1058", ["iterators-cycle-n", "iterators-nth-cycle-overflow"]),
  ("cycle@1059", ["iteratorscov-cycle-repeated"]),
  ("eltype@1061", ["iteratorscov-cycle-repeated"]),
  ("IteratorEltype@1062", ["iteratorscov-cycle-repeated"]),
  ("IteratorSize@1063", ["iteratorscov-cycle-repeated"]),
  ("iterate@1065", ["iteratorscov-cycle-repeated"]),
  ("isdone@1066", ["iteratorscov-cycle-repeated"]),
  ("isdone@1067", ["iteratorscov-cycle-repeated"]),
  ("iterate@1068", ["iteratorscov-cycle-repeated"]),
  ("reverse@1074", ["iteratorscov-cycle-repeated"]),
  ("last@1075", ["iteratorscov-cycle-repeated"]),
  ("repeated@1083", ["iterators-repeated-n"]),
  ("repeated@1111", ["iteratorscov-cycle-repeated"]),
  ("eltype@1113", ["iteratorscov-cycle-repeated"]),
  ("iterate@1115", ["iteratorscov-cycle-repeated"]),
  ("IteratorSize@1117", ["iteratorscov-cycle-repeated"]),
  ("IteratorEltype@1118", ["iteratorscov-cycle-repeated"]),
  ("reverse@1120", ["iteratorscov-cycle-repeated"]),
  ("last@1121", ["iteratorscov-cycle-repeated"]),
  ("product@1148", ["iterators-product"]),
  ("IteratorSize@1150", ["iteratorscov-product-empty-infinite"]),
  ("IteratorSize@1151", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1154", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1155", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1157", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1158", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1159", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1160", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1163", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1164", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1165", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1166", ["iteratorscov-product-empty-infinite"]),
  ("prod_iteratorsize@1167", ["iteratorscov-product-empty-infinite"]),
  ("size@1169", ["iterators-product"]),
  ("_prod_size@1170", ["iteratorscov-product-methods"]),
  ("_prod_size@1171", ["iteratorscov-product-methods"]),
  ("_prod_size1@1172", ["iteratorscov-product-methods"]),
  ("_prod_size1@1173", ["iteratorscov-product-methods"]),
  ("_prod_size1@1174", ["iteratorscov-product-methods"]),
  ("axes@1177", ["iteratorscov-product-methods"]),
  ("_prod_indices@1178", ["iteratorscov-product-methods"]),
  ("_prod_indices@1179", ["iteratorscov-product-methods"]),
  ("_prod_axes1@1180", ["iteratorscov-product-methods"]),
  ("_prod_axes1@1181", ["iteratorscov-product-methods"]),
  ("_prod_axes1@1182", ["iteratorscov-product-methods"]),
  ("ndims@1185", ["iteratorscov-product-methods"]),
  ("length@1186", ["iterators-product-length-zero"]),
  ("IteratorEltype@1188", ["iteratorscov-product-methods"]),
  ("IteratorEltype@1189", ["iteratorscov-product-methods"]),
  ("IteratorEltype@1191", ["iteratorscov-product-methods"]),
  ("eltype@1197", ["iteratorscov-product-methods"]),
  ("_prod_eltype@1198", ["iteratorscov-product-methods"]),
  ("_prod_eltype@1199", ["iteratorscov-product-methods"]),
  ("iterate@1201", ["iteratorscov-product-methods"]),
  ("iterate@1202", ["iteratorscov-product-methods"]),
  ("isdone@1204", ["iteratorscov-product-methods"]),
  ("_pisdone@1205", ["iterators-product-stateful-done"]),
  ("isdone@1213", ["iteratorscov-product-methods"]),
  ("isdone@1214", ["iteratorscov-product-methods"]),
  ("_piterate@1216", ["iteratorscov-product-methods"]),
  ("_piterate@1217", ["iteratorscov-product-methods"]),
  ("iterate@1226", ["iteratorscov-product-methods"]),
  ("_piterate1@1233", ["iteratorscov-product-methods"]),
  ("_piterate1@1234", ["iteratorscov-product-methods"]),
  ("iterate@1248", ["iteratorscov-product-methods"]),
  ("reverse@1255", ["iteratorscov-product-methods"]),
  ("last@1256", ["iterators-product-last-empty"]),
  ("intersect@1257", ["iteratorscov-product-intersect-arity"]),
  ("flatten@1291", ["iterators-flatten"]),
  ("eltype@1293", ["iteratorscov-flatten-methods"]),
  ("eltype@1298", ["iteratorscov-flatten-methods"]),
  ("eltype@1301", ["iteratorscov-flatten-methods"]),
  ("IteratorEltype@1305", ["iteratorscov-flatten-methods"]),
  ("IteratorEltype@1306", ["iteratorscov-flatten-methods"]),
  ("_flatteneltype@1307", ["iteratorscov-flatten-methods"]),
  ("_flatteneltype@1308", ["iteratorscov-flatten-methods"]),
  ("flatten_iteratorsize@1310", ["iteratorscov-flatten-methods"]),
  ("flatten_iteratorsize@1311", ["iteratorscov-flatten-methods"]),
  ("flatten_iteratorsize@1313", ["iteratorscov-flatten-methods"]),
  ("flatten_iteratorsize@1314", ["iteratorscov-flatten-methods"]),
  ("flatten_iteratorsize@1315", ["iteratorscov-flatten-methods"]),
  ("flatten_iteratorsize@1316", ["iteratorscov-flatten-methods"]),
  ("_flatten_iteratorsize@1318", ["iteratorscov-flatten-methods"]),
  ("_flatten_iteratorsize@1319", ["iteratorscov-flatten-methods"]),
  ("_flatten_iteratorsize@1320", ["iteratorscov-flatten-methods"]),
  ("IteratorSize@1322", ["iteratorscov-flatten-methods"]),
  ("flatten_length@1324", ["iteratorscov-flatten-methods"]),
  ("flatten_length@1325", ["iteratorscov-flatten-methods"]),
  ("flatten_length@1326", ["iteratorscov-flatten-methods"]),
  ("flatten_length@1329", ["iteratorscov-flatten-methods"]),
  ("flatten_length@1330", ["iteratorscov-flatten-methods"]),
  ("length@1332", ["iteratorscov-flatten-methods"]),
  ("length@1333", ["iteratorscov-flatten-methods"]),
  ("iterate@1335", ["iteratorscov-flatten-methods"]),
  ("iterate@1354", ["iteratorscov-flatten-methods"]),
  ("reverse@1379", ["iteratorscov-flatten-methods"]),
  ("last@1380", ["iteratorscov-flatten-methods"]),
  ("flatmap@1421", ["iteratorscov-cycle-repeated"]),
  ("partition@1436", ["iterators-partition-vector"]),
  ("PartitionIterator@1446", ["iteratorscov-partition-methods"]),
  ("PartitionIterator@1447", ["iteratorscov-partition-methods"]),
  ("eltype@1449", ["iteratorscov-partition-methods"]),
  ("eltype@1451", ["iteratorscov-partition-methods"]),
  ("eltype@1453", ["iteratorscov-partition-methods"]),
  ("IteratorEltype@1455", ["iteratorscov-partition-methods"]),
  ("IteratorEltype@1456", ["iteratorscov-partition-methods"]),
  ("IteratorEltype@1457", ["iteratorscov-partition-methods"]),
  ("partition_iteratorsize@1459", ["iteratorscov-partition-methods"]),
  ("partition_iteratorsize@1460", ["iteratorscov-partition-methods"]),
  ("IteratorSize@1461", ["iteratorscov-partition-methods"]),
  ("length@1465", ["iterators-partition-vector"]),
  ("iterate@1470", ["iterators-partition-range-overflow", "iteratorscov-partition-methods"]),
  ("iterate@1476", ["iteratorscov-partition-methods"]),
  ("iterate@1484", ["iterators-partition-generic-alloc", "iteratorscov-partition-methods"]),
  ("StatefulSnapshot{<:Any, Any}@1566", ["iteratorscov-stateful-methods"]),
  ("StatefulSnapshot@1569", ["iteratorscov-stateful-methods"]),
  ("reset!@1575", ["iteratorscov-stateful-methods"]),
  ("reset!@1579", ["iteratorscov-stateful-methods"]),
  ("approx_iter_type@1589", ["iteratorscov-stateful-methods"]),
  ("doiterate@1592", ["iteratorscov-stateful-methods"]),
  ("_approx_iter_type@1597", ["iteratorscov-stateful-methods"]),
  ("StatefulSnapshot@1605", ["iteratorscov-stateful-methods"]),
  ("convert@1606", ["iteratorscov-stateful-methods"]),
  ("isdone@1607", ["iterators-stateful"]),
  ("popfirst!@1609", ["iterators-stateful"]),
  ("peek@1620", ["iterators-stateful"]),
  ("iterate@1624", ["iteratorscov-stateful-methods"]),
  ("IteratorSize@1625", ["iteratorscov-stateful-methods"]),
  ("eltype@1626", ["iteratorscov-stateful-methods"]),
  ("IteratorEltype@1627", ["iteratorscov-stateful-methods"]),
  ("only@1659", ["iteratorscov-only-nth-methods"]),
  ("_only@1661", ["iteratorscov-only-nth-methods"]),
  ("_only@1673", ["iteratorscov-only-nth-methods"]),
  ("only@1680", ["iteratorscov-only-nth-methods"]),
  ("only@1683", ["iteratorscov-only-nth-methods"]),
  ("only@1684", ["iteratorscov-only-nth-methods"]),
  ("only@1687", ["iteratorscov-only-nth-methods"]),
  ("only@1688", ["iteratorscov-only-nth-methods"]),
  ("IteratorSize@1704", ["iteratorscov-iterable-state-pairs"]),
  ("length@1705", ["iteratorscov-iterable-state-pairs"]),
  ("Base.eltype@1706", ["iteratorscov-iterable-state-pairs"]),
  ("iterate@1708", ["iteratorscov-iterable-state-pairs"]),
  ("reverse@1714", ["iteratorscov-iterable-state-pairs"]),
  ("reverse@1715", ["iteratorscov-iterable-state-pairs"]),
  ("iterate@1717", ["iteratorscov-iterable-state-pairs"]),
  ("pairs@1725", ["iteratorscov-iterable-state-pairs"]),
  ("nth@1753", ["iteratorscov-only-nth-methods"]),
  ("nth@1754", ["iterators-nth-cycle-overflow", "iteratorscov-only-nth-methods"]),
  ("nth@1755", ["iterators-nth-cycle-overflow", "iteratorscov-only-nth-methods"]),
  ("nth@1756", ["iterators-nth-vector", "iterators-nth-unsigned-offset"]),
  ("_nth@1758", ["iterators-nth-cycle-overflow", "iteratorscov-only-nth-methods"]),
  ("_nth@1767", ["iterators-nth-cycle-overflow", "iteratorscov-only-nth-methods"]),
  ("_nth@1777", ["iteratorscov-only-nth-methods"]),
  ("_nth@1789", ["iterators-nth-zip-empty", "iteratorscov-only-nth-methods"]),
  ("nth@1810", ["iteratorscov-only-nth-methods"])
]

end JuliaLean.Proofs.base.iterators
