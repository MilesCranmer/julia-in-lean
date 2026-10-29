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

def aam327 (axes : A → List X) (colon : I) (setindex : List I → V → Int → List I)
    (select : A → Int → V → List I → R) (a : A) (d : Int) (i : V) : R :=
  select a d i (setindex ((axes a).map fun _ => colon) i d)
def AAM327Property : Prop := ∀ (A X I V R : Type) axes colon setindex select a d i,
  aam327 (R := R) (axes : A → List X) (colon : I)
      (setindex : List I → V → Int → List I) (select : A → Int → V → List I → R)
      a d i = select a d i (setindex (List.replicate (axes a).length colon) i d)
theorem aam327Property : AAM327Property := by
  unfold AAM327Property aam327
  intro A X I V R axes colon setindex select a d i
  have hm : ∀ xs : List X, xs.map (fun _ => colon) = List.replicate xs.length colon := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa [List.replicate] using congrArg (List.cons colon) ih
  rw [hm]

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

def abstractArrayMathReviewEntries : List Entry := []

end JuliaLean.MultidimCov
