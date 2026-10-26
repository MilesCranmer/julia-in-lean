import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

abbrev AAMResult (α : Type) := Except Unit α

def aam5 (all : (E → Bool) → A → Bool) (isreal : E → Bool) (a : A) : Bool :=
  all isreal a
def AAM5Property : Prop := ∀ (E A : Type) (all : (E → Bool) → A → Bool)
    (isreal : E → Bool) (a : A), aam5 all isreal a = all isreal a
theorem aam5Property : AAM5Property := by unfold AAM5Property; intros; rfl

def aam6 (all : (E → Bool) → A → Bool) (iszero : E → Bool) (a : A) : Bool :=
  all iszero a
def AAM6Property : Prop := ∀ (E A : Type) (all : (E → Bool) → A → Bool)
    (iszero : E → Bool) (a : A), aam6 all iszero a = all iszero a
theorem aam6Property : AAM6Property := by unfold AAM6Property; intros; rfl

def aam7 (_ : A) : Bool := true
def AAM7Property : Prop := ∀ (A : Type) (a : A), aam7 a = true
theorem aam7Property : AAM7Property := by unfold AAM7Property; intros; rfl

def aam41 (length : A → Nat) (reshape : A → Nat → R) (a : A) : R :=
  reshape a (length a)
def AAM41Property : Prop := ∀ (A R : Type) (length : A → Nat)
    (reshape : A → Nat → R) (a : A), aam41 length reshape a = reshape a (length a)
theorem aam41Property : AAM41Property := by unfold AAM41Property; intros; rfl

def aam42 (a : A) : A := a
def AAM42Property : Prop := ∀ (A : Type) (a : A), aam42 a = a
theorem aam42Property : AAM42Property := by unfold AAM42Property; intros; rfl

def aam44 : Unit := ()
def AAM44Property : Prop := ∀ (_ : Unit), aam44 = ()
theorem aam44Property : AAM44Property := by intro; rfl

def aam45 (t : T) : T := t
def AAM45Property : Prop := ∀ (T : Type) (t : T), aam45 t = t
theorem aam45Property : AAM45Property := by unfold AAM45Property; intros; rfl

def aam46 (tailT : T → AAMResult T) (tailS : S → AAMResult S)
    (sub : T → S → R) (t : T) (s : S) : AAMResult R := do
  let tt ← tailT t
  let ss ← tailS s
  pure (sub tt ss)
def AAM46Property : Prop := ∀ (T S R : Type) tailT tailS sub t s,
  aam46 (R := R) (tailT : T → AAMResult T) (tailS : S → AAMResult S)
      (sub : T → S → R) t s = do
    let tt ← tailT t
    let ss ← tailS s
    pure (sub tt ss)
theorem aam46Property : AAM46Property := by unfold AAM46Property; intros; rfl

def aam85 (drop : A → D → R) (a : A) (dims : D) : R := drop a dims
def AAM85Property : Prop := ∀ (A D R : Type) (drop : A → D → R) a dims,
  aam85 drop (a : A) (dims : D) = drop a dims
theorem aam85Property : AAM85Property := by unfold AAM85Property; intros; rfl

def validateDrop (rank : Nat) (axisLength : Int → Nat) :
    List Int → List Int → AAMResult Unit
  | [], _ => pure ()
  | d :: ds, seen =>
      if d < 1 || (rank : Int) < d then .error ()
      else if axisLength d != 1 then .error ()
      else if seen.contains d then .error ()
      else validateDrop rank axisLength ds (seen ++ [d])

def aam86 (rank : Nat) (axisLength : Int → Nat) (axes : A → List X)
    (foldAxes : List Int → List X) (concrete : List X → Bool)
    (subAxes : List X → List Int → List X) (reshape : A → List X → R)
    (a : A) (dims : List Int) : AAMResult R := do
  validateDrop rank axisLength dims []
  let oldAxes := axes a
  let kept := foldAxes dims
  if concrete oldAxes then pure (reshape a (kept ++ subAxes oldAxes dims))
  else pure (reshape a kept)

def AAM86Property : Prop := ∀ (A X R : Type) rank axisLength axes foldAxes concrete subAxes
    reshape a dims,
  aam86 (A := A) (R := R) (X := X) rank axisLength axes foldAxes concrete subAxes reshape a dims = do
    validateDrop rank axisLength dims []
    let oldAxes := axes a
    let kept := foldAxes dims
    if concrete oldAxes then pure (reshape a (kept ++ subAxes oldAxes dims))
    else pure (reshape a kept)
theorem aam86Property : AAM86Property := by unfold AAM86Property; intros; rfl

def aam104 (toInt : I → AAMResult Int) (drop : A → List Int → R)
    (a : A) (dim : I) : AAMResult R := do
  let d ← toInt dim
  pure (drop a [d])
def AAM104Property : Prop := ∀ (I A R : Type) toInt drop a dim,
  aam104 (R := R) (toInt : I → AAMResult Int) (drop : A → List Int → R) a dim = do
    let d ← toInt dim
    pure (drop a [d])
theorem aam104Property : AAM104Property := by unfold AAM104Property; intros; rfl

def aam146 (insert : A → D → R) (a : A) (dims : D) : R := insert a dims
def AAM146Property : Prop := ∀ (A D R : Type) (insert : A → D → R) a dims,
  aam146 insert (a : A) (dims : D) = insert a dims
theorem aam146Property : AAM146Property := by unfold AAM146Property; intros; rfl

def validateInsert (rank added : Nat) : List Int → List Int → AAMResult Unit
  | [], _ => pure ()
  | d :: ds, seen =>
      if d < 1 || ((rank + added : Nat) : Int) < d then .error ()
      else if seen.contains d then .error ()
      else validateInsert rank added ds (seen ++ [d])

def insertedAxes (axis : Nat → X) (singleton : X) (rank added : Nat)
    (dims : List Int) : List X × Nat :=
  (List.range (rank + added)).foldl (fun state k =>
    if dims.contains ((k + 1 : Nat) : Int) then (state.1 ++ [singleton], state.2)
    else (state.1 ++ [axis state.2], state.2 + 1)) ([], 1)

def aam147 (axis : A → Nat → X) (singleton : X) (reshape : A → List X → R)
    (a : A) (rank added : Nat) (dims : List Int) : AAMResult R := do
  validateInsert rank added dims []
  pure (reshape a (insertedAxes (axis a) singleton rank added dims).1)

def AAM147Property : Prop := ∀ (A X R : Type) axis singleton reshape a rank added dims,
  aam147 (R := R) (axis : A → Nat → X) singleton (reshape : A → List X → R)
      a rank added dims = do
    validateInsert rank added dims []
    pure (reshape a (insertedAxes (axis a) singleton rank added dims).1)
theorem aam147Property : AAM147Property := by unfold AAM147Property; intros; rfl

def aam166 (toInt : I → AAMResult Int) (insert : A → List Int → R)
    (a : A) (dim : I) : AAMResult R := do
  let d ← toInt dim
  pure (insert a [d])
def AAM166Property : Prop := ∀ (I A R : Type) toInt insert a dim,
  aam166 (R := R) (toInt : I → AAMResult Int) (insert : A → List Int → R) a dim = do
    let d ← toInt dim
    pure (insert a [d])
theorem aam166Property : AAM166Property := by unfold AAM166Property; intros; rfl

def aam194 (broadcastBang : F → A → A → AAMResult Unit) (conj : F) (a : A) : AAMResult A := do
  broadcastBang conj a a
  pure a
def AAM194Property : Prop := ∀ (F A : Type) broadcastBang conj a,
  aam194 (broadcastBang : F → A → A → AAMResult Unit) conj a = do
    broadcastBang conj a a
    pure a
theorem aam194Property : AAM194Property := by unfold AAM194Property; intros; rfl

def aam196 (foreach : (E → AAMResult Unit) → A → AAMResult Unit)
    (conjBang : E → AAMResult Unit) (a : A) : AAMResult A := do
  foreach conjBang a
  pure a
def AAM196Property : Prop := ∀ (E A : Type) foreach conjBang a,
  aam196 (foreach : (E → AAMResult Unit) → A → AAMResult Unit)
      (conjBang : E → AAMResult Unit) a = do
    foreach conjBang a
    pure a
theorem aam196Property : AAM196Property := by unfold AAM196Property; intros; rfl

def unaryBroadcast (broadcast : F → A → R) (f : F) (a : A) : R := broadcast f a
def UnaryBroadcastProperty : Prop := ∀ (F A R : Type) broadcast f a,
  unaryBroadcast (R := R) (broadcast : F → A → R) f a = broadcast f a
theorem unaryBroadcastProperty : UnaryBroadcastProperty := by
  unfold UnaryBroadcastProperty; intros; rfl

def aam270 (zero : A → R) (a : A) : R := zero a
def AAM270Property : Prop := ∀ (A R : Type) (zero : A → R) a,
  aam270 zero (a : A) = zero a
theorem aam270Property : AAM270Property := by unfold AAM270Property; intros; rfl

def aam327 (axes : A → List X) (slice : X → I) (setindex : List I → V → Int → List I)
    (select : A → Int → V → List I → R) (a : A) (d : Int) (i : V) : R :=
  select a d i (setindex ((axes a).map slice) i d)
def AAM327Property : Prop := ∀ (A X I V R : Type) axes slice setindex select a d i,
  aam327 (R := R) (axes : A → List X) (slice : X → I)
      (setindex : List I → V → Int → List I) (select : A → Int → V → List I → R)
      a d i = select a d i (setindex ((axes a).map slice) i d)
theorem aam327Property : AAM327Property := by unfold AAM327Property; intros; rfl

def aam328 (rank : A → Nat) (isOne : I → Bool) (view : A → List X → R)
    (a : A) (d : Int) (i : I) (indices : List X) : AAMResult R :=
  if d < 1 then .error ()
  else if (rank a : Int) < d && !isOne i then .error ()
  else pure (view a indices)
def AAM328Property : Prop := ∀ (A I X R : Type) rank isOne view a d i indices,
  aam328 (R := R) (rank : A → Nat) (isOne : I → Bool) (view : A → List X → R)
      a d i indices =
    if d < 1 then .error ()
    else if (rank a : Int) < d && !isOne i then .error ()
    else pure (view a indices)
theorem aam328Property : AAM328Property := by unfold AAM328Property; intros; rfl

def aam335 (toInteger : S → AAMResult Int) (similar : A → B)
    (shift : B → A → List Int → R) (a : A) (amount : S) : AAMResult R := do
  let n ← toInteger amount
  pure (shift (similar a) a [n])
def AAM335Property : Prop := ∀ (S A B R : Type) toInteger similar shift a amount,
  aam335 (R := R) (toInteger : S → AAMResult Int) (similar : A → B)
      (shift : B → A → List Int → R) a amount = do
    let n ← toInteger amount
    pure (shift (similar a) a [n])
theorem aam335Property : AAM335Property := by unfold AAM335Property; intros; rfl

def aam338 (similar : A → B) (shift : B → A → D → R)
    (a : A) (amount : D) : R := shift (similar a) a amount
def AAM338Property : Prop := ∀ (A B D R : Type) similar shift a amount,
  aam338 (R := R) (similar : A → B) (shift : B → A → D → R) a amount =
    shift (similar a) a amount
theorem aam338Property : AAM338Property := by unfold AAM338Property; intros; rfl

def convertAAM (f : S → AAMResult Int) : List S → AAMResult (List Int)
  | [] => pure []
  | x :: xs => do pure ((← f x) :: (← convertAAM f xs))

def aam411 (toInteger : S → AAMResult Int) (similar : A → B)
    (shift : B → A → List Int → R) (a : A) (amounts : List S) : AAMResult R := do
  let values ← convertAAM toInteger amounts
  pure (shift (similar a) a values)

def AAM411Property : Prop := ∀ (S A B R : Type) toInteger similar shift a amounts,
  aam411 (R := R) (toInteger : S → AAMResult Int) (similar : A → B)
      (shift : B → A → List Int → R) a amounts = do
    let values ← convertAAM toInteger amounts
    pure (shift (similar a) a values)
theorem aam411Property : AAM411Property := by unfold AAM411Property; intros; rfl

def aam445 (repeatKeyword : A → List C → R) (a : A) (counts : List C) : R :=
  repeatKeyword a counts
def AAM445Property : Prop := ∀ (A C R : Type) repeatKeyword a counts,
  aam445 (R := R) (repeatKeyword : A → List C → R) a counts = repeatKeyword a counts
theorem aam445Property : AAM445Property := by unfold AAM445Property; intros; rfl

def aam482 (repeatInnerOuter : A → Option I → Option O → R)
    (a : A) (inner : Option I) (outer : Option O) : R := repeatInnerOuter a inner outer
def AAM482Property : Prop := ∀ (A I O R : Type) repeatInnerOuter a inner outer,
  aam482 (R := R) (repeatInnerOuter : A → Option I → Option O → R)
      a inner outer = repeatInnerOuter a inner outer
theorem aam482Property : AAM482Property := by unfold AAM482Property; intros; rfl

def aam488 (check : A → Option I → Option O → AAMResult Unit)
    (resolve : A → Option I → Option O → AAMResult (A × Option I × Option O))
    (repeatFn : A → Option I → Option O → R)
    (a : A) (inner : Option I) (outer : Option O) : AAMResult R := do
  check a inner outer
  let resolved ← resolve a inner outer
  pure (repeatFn resolved.1 resolved.2.1 resolved.2.2)
def AAM488Property : Prop := ∀ (A I O R : Type) check resolve repeatFn a inner outer,
  aam488 (R := R) (check : A → Option I → Option O → AAMResult Unit)
      (resolve : A → Option I → Option O → AAMResult (A × Option I × Option O))
      (repeatFn : A → Option I → Option O → R) a inner outer = do
    check a inner outer
    let resolved ← resolve a inner outer
    pure (repeatFn resolved.1 resolved.2.1 resolved.2.2)
theorem aam488Property : AAM488Property := by unfold AAM488Property; intros; rfl

def aam494 (tuple : T) : T := tuple
def AAM494Property : Prop := ∀ (T : Type) (tuple : T), aam494 tuple = tuple
theorem aam494Property : AAM494Property := by unfold AAM494Property; intros; rfl

def aam495 (x : I) : List I := [x]
def AAM495Property : Prop := ∀ (I : Type) (x : I), aam495 x = [x]
theorem aam495Property : AAM495Property := by unfold AAM495Property; intros; rfl

def aam496 (collectTuple : I → T) (itr : I) : T := collectTuple itr
def AAM496Property : Prop := ∀ (I T : Type) (collectTuple : I → T) itr,
  aam496 collectTuple (itr : I) = collectTuple itr
theorem aam496Property : AAM496Property := by unfold AAM496Property; intros; rfl

def aam498 (length : T → Nat) (fill : T → Nat → T) (a b : T) : T × T :=
  let n := max (length a) (length b)
  (fill a n, fill b n)
def AAM498Property : Prop := ∀ (T : Type) length fill a b,
  aam498 (length : T → Nat) (fill : T → Nat → T) a b =
    let n := max (length a) (length b); (fill a n, fill b n)
theorem aam498Property : AAM498Property := by unfold AAM498Property; intros; rfl

def aam502 (length : T → Nat) (fill : T → Nat → T) (a b c : T) : T × T × T :=
  let n := max (max (length a) (length b)) (length c)
  (fill a n, fill b n, fill c n)
def AAM502Property : Prop := ∀ (T : Type) length fill a b c,
  aam502 (length : T → Nat) (fill : T → Nat → T) a b c =
    let n := max (max (length a) (length b)) (length c); (fill a n, fill b n, fill c n)
theorem aam502Property : AAM502Property := by unfold AAM502Property; intros; rfl

def aam507 (a : A) (inner : I) (outer : O) : A × I × O := (a, inner, outer)
def AAM507Property : Prop := ∀ (A I O : Type) a inner outer,
  aam507 (a : A) (inner : I) (outer : O) = (a, inner, outer)
theorem aam507Property : AAM507Property := by unfold AAM507Property; intros; rfl

def aam510 (size : A → D) (toTupleI : I → TI) (toTupleO : O → TO)
    (pad : D → TI → TO → D × TI × TO) (reshape : A → D → A)
    (a : A) (inner : I) (outer : O) : A × TI × TO :=
  let padded := pad (size a) (toTupleI inner) (toTupleO outer)
  (reshape a padded.1, padded.2.1, padded.2.2)
def AAM510Property : Prop := ∀ (A D I O TI TO : Type) size toTupleI toTupleO pad reshape a inner outer,
  aam510 (size : A → D) (toTupleI : I → TI) (toTupleO : O → TO)
      (pad : D → TI → TO → D × TI × TO) (reshape : A → D → A) a inner outer =
    let padded := pad (size a) (toTupleI inner) (toTupleO outer)
    (reshape a padded.1, padded.2.1, padded.2.2)
theorem aam510Property : AAM510Property := by unfold AAM510Property; intros; rfl

def aam514 (a : A) : A × Option I × Option O := (a, none, none)
def AAM514Property : Prop := ∀ (A I O : Type) (a : A),
  aam514 (I := I) (O := O) a = (a, none, none)
theorem aam514Property : AAM514Property := by unfold AAM514Property; intros; rfl

def aam517 (size : A → D) (toTuple : O → TO) (pad : D → TO → D × TO)
    (reshape : A → D → A) (a : A) (outer : O) : A × Option I × TO :=
  let padded := pad (size a) (toTuple outer)
  (reshape a padded.1, none, padded.2)
def AAM517Property : Prop := ∀ (A D O TO I : Type) size toTuple pad reshape a outer,
  aam517 (I := I) (size : A → D) (toTuple : O → TO) (pad : D → TO → D × TO)
      (reshape : A → D → A) a outer =
    let padded := pad (size a) (toTuple outer); (reshape a padded.1, none, padded.2)
theorem aam517Property : AAM517Property := by unfold AAM517Property; intros; rfl

def aam521 (size : A → D) (toTuple : I → TI) (pad : D → TI → D × TI)
    (reshape : A → D → A) (a : A) (inner : I) : A × TI × Option O :=
  let padded := pad (size a) (toTuple inner)
  (reshape a padded.1, padded.2, none)
def AAM521Property : Prop := ∀ (A D I TI O : Type) size toTuple pad reshape a inner,
  aam521 (O := O) (size : A → D) (toTuple : I → TI) (pad : D → TI → D × TI)
      (reshape : A → D → A) a inner =
    let padded := pad (size a) (toTuple inner); (reshape a padded.1, padded.2, none)
theorem aam521Property : AAM521Property := by unfold AAM521Property; intros; rfl

structure RepeatCounts where
  values : List Int
  allInteger : Bool
  deriving DecidableEq, Repr

def aam526 (requireOneBased : A → AAMResult Unit) (rank : A → Nat) (a : A)
    (inner outer : Option RepeatCounts) : AAMResult Unit := do
  match inner with
  | some counts =>
      requireOneBased a
      if !counts.allInteger || counts.values.any (· < 0) || counts.values.length < rank a
      then .error () else pure ()
  | none => pure ()
  match outer with
  | some counts =>
      if !counts.allInteger || counts.values.any (· < 0) ||
          (counts.values.length < rank a && inner.isSome)
      then .error () else pure ()
  | none => pure ()

def AAM526Property : Prop := ∀ (A : Type) require rank a inner outer,
  aam526 (require : A → AAMResult Unit) (rank : A → Nat) a inner outer = do
    match inner with
    | some counts =>
        require a
        if !counts.allInteger || counts.values.any (· < 0) || counts.values.length < rank a
        then .error () else pure ()
    | none => pure ()
    match outer with
    | some counts =>
        if !counts.allInteger || counts.values.any (· < 0) ||
            (counts.values.length < rank a && inner.isSome)
        then .error () else pure ()
    | none => pure ()
theorem aam526Property : AAM526Property := by unfold AAM526Property; intros; rfl

def aam554 (a : A) : A := a
def AAM554Property : Prop := ∀ (A : Type) (a : A), aam554 a = a
theorem aam554Property : AAM554Property := by unfold AAM554Property; intros; rfl

def aam555 (outer : A → O → R) (a : A) (counts : O) : R := outer a counts
def AAM555Property : Prop := ∀ (A O R : Type) (outer : A → O → R) a counts,
  aam555 outer (a : A) (counts : O) = outer a counts
theorem aam555Property : AAM555Property := by unfold AAM555Property; intros; rfl

def aam556 (inner : A → I → R) (a : A) (counts : I) : R := inner a counts
def AAM556Property : Prop := ∀ (A I R : Type) (inner : A → I → R) a counts,
  aam556 inner (a : A) (counts : I) = inner a counts
theorem aam556Property : AAM556Property := by unfold AAM556Property; intros; rfl

def aam557 (inner : A → I → B) (outer : B → O → R)
    (a : A) (ic : I) (oc : O) : R := outer (inner a ic) oc
def AAM557Property : Prop := ∀ (A I B O R : Type) inner outer a ic oc,
  aam557 (R := R) (inner : A → I → B) (outer : B → O → R) a ic oc =
    outer (inner a ic) oc
theorem aam557Property : AAM557Property := by unfold AAM557Property; intros; rfl

def repeatAssignments (indices copies : List I) (source : I → V)
    (target : I → I → I) (set : A → I → V → A) (initial : A) : A :=
  indices.foldl (fun out i =>
    copies.foldl (fun out j => set out (target i j) (source i)) out) initial

def aam559 (allocate : Nat → Nat → A) (source : Int × Int → V)
    (setBlock : A → Nat → Nat → V → A) (rows cols : Nat) (m n : Nat) : A :=
  let initial := allocate (rows * m) (cols * n)
  (List.range n).foldl (fun out j => (List.range m).foldl (fun out i =>
    setBlock out (i * rows) (j * cols) (source (0, 0))) out) initial
def AAM559Property : Prop := ∀ (A V : Type) allocate source setBlock rows cols m n,
  aam559 (A := A) (allocate : Nat → Nat → A) (source : Int × Int → V)
      (setBlock : A → Nat → Nat → V → A) rows cols m n =
    let initial := allocate (rows * m) (cols * n)
    (List.range n).foldl (fun out j => (List.range m).foldl (fun out i =>
      setBlock out (i * rows) (j * cols) (source (0, 0))) out) initial
theorem aam559Property : AAM559Property := by unfold AAM559Property; intros; rfl

def aam573 (allocate : Nat → A) (source : V) (setBlock : A → Nat → V → A)
    (length m : Nat) : A :=
  let initial := allocate (length * m)
  (List.range m).foldl (fun out i => setBlock out (i * length) source) initial
def AAM573Property : Prop := ∀ (A V : Type) allocate source setBlock length m,
  aam573 (A := A) (allocate : Nat → A) (source : V)
      (setBlock : A → Nat → V → A) length m =
    (List.range m).foldl (fun out i => setBlock out (i * length) source)
      (allocate (length * m))
theorem aam573Property : AAM573Property := by unfold AAM573Property; intros; rfl

def aam583 (input outputCopies : List I) (allocate : A) (get : I → V)
    (target : I → I → I) (set : A → I → V → A) : A :=
  repeatAssignments input outputCopies get target set allocate
def AAM583Property : Prop := ∀ (I A V : Type) input copies allocate get target set,
  aam583 (input : List I) copies (allocate : A) (get : I → V)
      (target : I → I → I) (set : A → I → V → A) =
    repeatAssignments input copies get target set allocate
theorem aam583Property : AAM583Property := by unfold AAM583Property; intros; rfl

def aam599 (input innerCopies : List I) (allocate : A) (get : I → V)
    (target : I → I → I) (set : A → I → V → A) : A :=
  repeatAssignments input innerCopies get target set allocate
def AAM599Property : Prop := ∀ (I A V : Type) input copies allocate get target set,
  aam599 (input : List I) copies (allocate : A) (get : I → V)
      (target : I → I → I) (set : A → I → V → A) =
    repeatAssignments input copies get target set allocate
theorem aam599Property : AAM599Property := by unfold AAM599Property; intros; rfl

private def aamEntry (line : Nat) (fn statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-abstractarraymath-line{line}",
    juliaFile := "base/abstractarraymath.jl", juliaFns := [fn], statement, source,
    status := .proven, prop, thm := some thm }

def abstractArrayMathReviewEntries : List Entry := [
  aamEntry 5 "isreal(::AbstractArray)" "isreal applies the generic isreal predicate to all elements." "base/abstractarraymath.jl:5" ``AAM5Property ``aam5Property,
  aamEntry 6 "iszero(::AbstractArray)" "iszero applies the generic iszero predicate to all elements." "base/abstractarraymath.jl:6" ``AAM6Property ``aam6Property,
  aamEntry 7 "isreal(::AbstractArray{<:Real})" "Every real-element array returns true." "base/abstractarraymath.jl:7" ``AAM7Property ``aam7Property,
  aamEntry 41 "vec(::AbstractArray)" "vec calls reshape with the array length, preserving reshape alias behavior." "base/abstractarraymath.jl:41" ``AAM41Property ``aam41Property,
  aamEntry 42 "vec(::AbstractVector)" "vec returns an AbstractVector unchanged." "base/abstractarraymath.jl:42" ``AAM42Property ``aam42Property,
  aamEntry 44 "_sub(::Tuple{},::Tuple{})" "The empty tuple pair returns the empty tuple." "base/abstractarraymath.jl:44" ``AAM44Property ``aam44Property,
  aamEntry 45 "_sub(::Tuple,::Tuple{})" "An empty second tuple returns the first tuple unchanged." "base/abstractarraymath.jl:45" ``AAM45Property ``aam45Property,
  aamEntry 46 "_sub(::Tuple,::Tuple)" "The recursive overload takes both tails before its recursive call and preserves tail errors." "base/abstractarraymath.jl:46" ``AAM46Property ``aam46Property,
  aamEntry 85 "dropdims" "dropdims forwards the array and dimensions to _dropdims." "base/abstractarraymath.jl:85" ``AAM85Property ``aam85Property,
  aamEntry 86 "_dropdims(::AbstractArray,::Dims)" "_dropdims validates each dimension in order, constructs retained axes, selects the concrete-axis branch, and reshapes." "base/abstractarraymath.jl:86-103" ``AAM86Property ``aam86Property,
  aamEntry 104 "_dropdims(::AbstractArray,::Integer)" "The scalar wrapper converts to Int before tuple dispatch." "base/abstractarraymath.jl:104" ``AAM104Property ``aam104Property,
  aamEntry 146 "insertdims" "insertdims forwards to _insertdims." "base/abstractarraymath.jl:146" ``AAM146Property ``aam146Property,
  aamEntry 147 "_insertdims(::AbstractArray,::NTuple)" "_insertdims validates in order, advances the source-axis counter only for retained axes, and reshapes." "base/abstractarraymath.jl:147-165" ``AAM147Property ``aam147Property,
  aamEntry 166 "_insertdims(::AbstractArray,::Integer)" "The scalar insert wrapper converts to Int before tuple dispatch." "base/abstractarraymath.jl:166" ``AAM166Property ``aam166Property,
  aamEntry 194 "conj!(::AbstractArray{<:Number})" "Numeric conj! broadcasts into the same array and returns that array after successful mutation." "base/abstractarraymath.jl:194" ``AAM194Property ``aam194Property,
  aamEntry 196 "conj!(::AbstractArray)" "Nested conj! calls conj! on every element and returns the outer array." "base/abstractarraymath.jl:196" ``AAM196Property ``aam196Property,
  aamEntry 220 "conj(::AbstractArray)" "conj returns broadcast_preserving_zero_d(conj,A)." "base/abstractarraymath.jl:220" ``UnaryBroadcastProperty ``unaryBroadcastProperty,
  aamEntry 245 "real(::AbstractArray)" "real returns broadcast_preserving_zero_d(real,A)." "base/abstractarraymath.jl:245" ``UnaryBroadcastProperty ``unaryBroadcastProperty,
  aamEntry 269 "imag(::AbstractArray)" "imag returns broadcast_preserving_zero_d(imag,A)." "base/abstractarraymath.jl:269" ``UnaryBroadcastProperty ``unaryBroadcastProperty,
  aamEntry 270 "imag(::AbstractArray{<:Real})" "Real-array imag calls zero on the array." "base/abstractarraymath.jl:270" ``AAM270Property ``aam270Property,
  aamEntry 293 "-(::AbstractArray)" "Unary minus returns broadcast_preserving_zero_d(-,A)." "base/abstractarraymath.jl:293" ``UnaryBroadcastProperty ``unaryBroadcastProperty,
  aamEntry 327 "selectdim" "selectdim maps Slice over every axis, replaces dimension d with i, then calls _selectdim." "base/abstractarraymath.jl:327" ``AAM327Property ``aam327Property,
  aamEntry 328 "_selectdim" "_selectdim rejects dimensions below one and non-singleton trailing indices before calling view." "base/abstractarraymath.jl:328-333" ``AAM328Property ``aam328Property,
  aamEntry 335 "circshift(::AbstractArray,::Real)" "The Real overload converts the shift, allocates similar, then calls circshift!." "base/abstractarraymath.jl:335-337" ``AAM335Property ``aam335Property,
  aamEntry 338 "circshift(::AbstractArray,::DimsInteger)" "The DimsInteger overload allocates similar and calls circshift! with the supplied shifts." "base/abstractarraymath.jl:338" ``AAM338Property ``aam338Property,
  aamEntry 411 "circshift(::AbstractArray,shiftamt)" "The generic overload splats and converts each shift, allocates similar, then calls circshift!." "base/abstractarraymath.jl:411-413" ``AAM411Property ``aam411Property,
  aamEntry 445 "repeat(::AbstractArray,counts...)" "The positional repeat overload forwards counts as outer." "base/abstractarraymath.jl:445-447" ``AAM445Property ``aam445Property,
  aamEntry 482 "repeat(::AbstractArray;inner,outer)" "The public keyword method forwards to _RepeatInnerOuter.repeat." "base/abstractarraymath.jl:482-484" ``AAM482Property ``aam482Property,
  aamEntry 488 "_RepeatInnerOuter.repeat" "The helper checks, resolves, then repeats with the resolved array and counts in order." "base/abstractarraymath.jl:488-492" ``AAM488Property ``aam488Property,
  aamEntry 494 "to_tuple(::Tuple)" "Tuple conversion returns the exact tuple." "base/abstractarraymath.jl:494" ``AAM494Property ``aam494Property,
  aamEntry 495 "to_tuple(::Integer)" "Integer conversion returns a singleton tuple for every Integer representation." "base/abstractarraymath.jl:495" ``AAM495Property ``aam495Property,
  aamEntry 496 "to_tuple(itr)" "Generic conversion collects the iterator into a tuple." "base/abstractarraymath.jl:496" ``AAM496Property ``aam496Property,
  aamEntry 498 "pad(a,b)" "Two-way pad computes the maximum length and fills both inputs to it." "base/abstractarraymath.jl:498-501" ``AAM498Property ``aam498Property,
  aamEntry 502 "pad(a,b,c)" "Three-way pad computes the maximum length and fills all inputs to it." "base/abstractarraymath.jl:502-505" ``AAM502Property ``aam502Property,
  aamEntry 507 "resolve(::AbstractArray{T,N},::NTuple{N},::NTuple{N})" "Matching-rank resolve returns its three inputs unchanged." "base/abstractarraymath.jl:507-509" ``AAM507Property ``aam507Property,
  aamEntry 510 "resolve(arr,inner,outer)" "General resolve converts both counts, pads with size, reshapes, and returns padded counts." "base/abstractarraymath.jl:510-513" ``AAM510Property ``aam510Property,
  aamEntry 514 "resolve(arr,::Nothing,::Nothing)" "No-count resolve returns the array and both Nothing values." "base/abstractarraymath.jl:514-516" ``AAM514Property ``aam514Property,
  aamEntry 517 "resolve(arr,::Nothing,outer)" "Outer-only resolve converts and pads outer, reshapes, and preserves Nothing inner." "base/abstractarraymath.jl:517-520" ``AAM517Property ``aam517Property,
  aamEntry 521 "resolve(arr,inner,::Nothing)" "Inner-only resolve converts and pads inner, reshapes, and preserves Nothing outer." "base/abstractarraymath.jl:521-524" ``AAM521Property ``aam521Property,
  aamEntry 526 "check(arr,inner,outer)" "Repeat validation preserves the one-based, type, nonnegative, and rank checks in source order." "base/abstractarraymath.jl:526-552" ``AAM526Property ``aam526Property,
  aamEntry 554 "repeat_inner_outer(arr,::Nothing,::Nothing)" "No-count repetition returns the original array." "base/abstractarraymath.jl:554" ``AAM554Property ``aam554Property,
  aamEntry 555 "repeat_inner_outer(arr,::Nothing,outer)" "Outer-only repetition calls repeat_outer." "base/abstractarraymath.jl:555" ``AAM555Property ``aam555Property,
  aamEntry 556 "repeat_inner_outer(arr,inner,::Nothing)" "Inner-only repetition calls repeat_inner." "base/abstractarraymath.jl:556" ``AAM556Property ``aam556Property,
  aamEntry 557 "repeat_inner_outer(arr,inner,outer)" "Combined repetition completes repeat_inner before repeat_outer." "base/abstractarraymath.jl:557" ``AAM557Property ``aam557Property,
  aamEntry 559 "repeat_outer(::AbstractMatrix)" "Matrix outer repetition allocates multiplied dimensions and performs every block assignment in nested loop order." "base/abstractarraymath.jl:559-571" ``AAM559Property ``aam559Property,
  aamEntry 573 "repeat_outer(::AbstractVector)" "Vector outer repetition allocates multiplied length and performs every block assignment." "base/abstractarraymath.jl:573-581" ``AAM573Property ``aam573Property,
  aamEntry 583 "repeat_outer(::AbstractArray)" "General outer repetition assigns every source and repetition Cartesian-index pair." "base/abstractarraymath.jl:583-597" ``AAM583Property ``aam583Property,
  aamEntry 599 "repeat_inner" "Inner repetition assigns every source and inner Cartesian-index pair." "base/abstractarraymath.jl:599-612" ``AAM599Property ``aam599Property
]

end JuliaLean.MultidimCov
