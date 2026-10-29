import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

abbrev PDResult (α : Type) := Except Unit α

structure PDView (P : Type) where
  parent : P

def pd48 (a : PDView P) : P := a.parent
def PD48Property : Prop := ∀ (P : Type) (a : PDView P), pd48 a = a.parent
theorem pd48Property : PD48Property := by unfold PD48Property; intros; rfl

def permuteList (xs : List X) (perm : List Nat) : List X :=
  perm.filterMap fun d => xs[d - 1]?

def pd49 (size : P → List X) (perm : List Nat) (a : PDView P) : List X :=
  permuteList (size (pd48 a)) perm
def PD49Property : Prop := ∀ (P X : Type) size perm a,
  pd49 (size : P → List X) perm a = permuteList (size a.parent) perm
theorem pd49Property : PD49Property := by unfold PD49Property; intros; rfl

def pd50 (axes : P → List X) (perm : List Nat) (a : PDView P) : List X :=
  permuteList (axes (pd48 a)) perm
def PD50Property : Prop := ∀ (P X : Type) axes perm a,
  pd50 (axes : P → List X) perm a = permuteList (axes a.parent) perm
theorem pd50Property : PD50Property := by unfold PD50Property; intros; rfl

def pd51 (hasOffset : P → Bool) (a : PDView P) : Bool := hasOffset a.parent
def PD51Property : Prop := ∀ (P : Type) hasOffset a,
  pd51 (hasOffset : P → Bool) (a : PDView P) = hasOffset a.parent
theorem pd51Property : PD51Property := by unfold PD51Property; intros; rfl

def pd52 (similar : P → T → D → R) (a : PDView P) (t : T) (dims : D) : R :=
  similar (pd48 a) t dims
def PD52Property : Prop := ∀ (P T D R : Type) similar a t dims,
  pd52 (R := R) (similar : P → T → D → R) (a : PDView P) t dims =
    similar a.parent t dims
theorem pd52Property : PD52Property := by unfold PD52Property; intros; rfl

def pd53 (dataids : P → R) (a : PDView P) : R := dataids (pd48 a)
def PD53Property : Prop := ∀ (P R : Type) dataids a,
  pd53 (R := R) (dataids : P → R) (a : PDView P) = dataids a.parent
theorem pd53Property : PD53Property := by unfold PD53Property; intros; rfl

def pd54 (copy : P → Q) (construct : Q → R) (a : PDView P) : R :=
  construct (copy (pd48 a))
def PD54Property : Prop := ∀ (P Q R : Type) copy construct a,
  pd54 (R := R) (copy : P → Q) (construct : Q → R) (a : PDView P) =
    construct (copy a.parent)
theorem pd54Property : PD54Property := by unfold PD54Property; intros; rfl

def pd55 (cconvert : P → R) (a : PDView P) : R := cconvert (pd48 a)
def PD55Property : Prop := ∀ (P R : Type) cconvert a,
  pd55 (R := R) (cconvert : P → R) (a : PDView P) = cconvert a.parent
theorem pd55Property : PD55Property := by unfold PD55Property; intros; rfl

def pd64 (strides : P → List X) (perm : List Nat) (a : PDView P) : List X :=
  permuteList (strides (pd48 a)) perm
def PD64Property : Prop := ∀ (P X : Type) strides perm a,
  pd64 (strides : P → List X) perm (a : PDView P) =
    permuteList (strides a.parent) perm
theorem pd64Property : PD64Property := by unfold PD64Property; intros; rfl

def pd68 (elsize : P → R) (parentType : P) : R := elsize parentType
def PD68Property : Prop := ∀ (P R : Type) elsize parentType,
  pd68 (R := R) (elsize : P → R) parentType = elsize parentType
theorem pd68Property : PD68Property := by unfold PD68Property; intros; rfl

def pd70 (checkbounds : A → List Int → PDResult Unit)
    (get : P → List Int → V) (iperm : List Nat) (a : A) (parent : P)
    (indices : List Int) : PDResult V := do
  checkbounds a indices
  pure (get parent (permuteList indices iperm))
def PD70Property : Prop := ∀ (A P V : Type) checkbounds get iperm a parent indices,
  pd70 (checkbounds : A → List Int → PDResult Unit) (get : P → List Int → V)
      iperm a parent indices = do
    checkbounds a indices
    pure (get parent (permuteList indices iperm))
theorem pd70Property : PD70Property := by unfold PD70Property; intros; rfl

def pd75 (checkbounds : A → List Int → PDResult Unit)
    (set : P → V → List Int → PDResult Unit) (iperm : List Nat) (a : A)
    (parent : P) (value : V) (indices : List Int) : PDResult V := do
  checkbounds a indices
  set parent value (permuteList indices iperm)
  pure value
def PD75Property : Prop := ∀ (A P V : Type) checkbounds set iperm a parent value indices,
  pd75 (checkbounds : A → List Int → PDResult Unit)
      (set : P → V → List Int → PDResult Unit) iperm a parent value indices = do
    checkbounds a indices
    set parent value (permuteList indices iperm)
    pure value
theorem pd75Property : PD75Property := by unfold PD75Property; intros; rfl

def pd81 (checkbounds : A → List Int → Bool) (assigned : P → List Int → Bool)
    (iperm : List Nat) (a : A) (parent : P) (indices : List Int) : Bool :=
  if !checkbounds a indices then false else assigned parent (permuteList indices iperm)
def PD81Property : Prop := ∀ (A P : Type) checkbounds assigned iperm a parent indices,
  pd81 (checkbounds : A → List Int → Bool) (assigned : P → List Int → Bool)
      iperm a parent indices =
    if !checkbounds a indices then false else assigned parent (permuteList indices iperm)
theorem pd81Property : PD81Property := by unfold PD81Property; intros; rfl

def pd87 (get : I → Nat → X) (input : I) (perm : List Nat) : List X :=
  (List.range perm.length).map fun d => get input (perm.getD d 0)
def PD87Property : Prop := ∀ (I X : Type) get input perm,
  pd87 (get : I → Nat → X) input perm =
    (List.range perm.length).map fun d => get input (perm.getD d 0)
theorem pd87Property : PD87Property := by unfold PD87Property; intros; rfl

def pd88 (toTuple : List Int → T) (tupleGenperm : I → T → R)
    (input : I) (perm : List Int) : R := tupleGenperm input (toTuple perm)
def PD88Property : Prop := ∀ (I T R : Type) toTuple tupleGenperm input perm,
  pd88 (R := R) (toTuple : List Int → T) (tupleGenperm : I → T → R) input perm =
    tupleGenperm input (toTuple perm)
theorem pd88Property : PD88Property := by unfold PD88Property; intros; rfl

def pd198 (axes : A → X) (genperm : X → P → D) (similar : A → D → B)
    (permutedimsBang : B → A → P → R) (a : A) (perm : P) : R :=
  let dest := similar a (genperm (axes a) perm)
  permutedimsBang dest a perm
def PD198Property : Prop := ∀ (A X P D B R : Type) axes genperm similar permute a perm,
  pd198 (R := R) (axes : A → X) (genperm : X → P → D) (similar : A → D → B)
      (permute : B → A → P → R) a perm =
    let dest := similar a (genperm (axes a) perm); permute dest a perm
theorem pd198Property : PD198Property := by unfold PD198Property; intros; rfl

def pd203 (permutedims : A → List Int → R) (a : A) : R := permutedims a [2, 1]
def PD203Property : Prop := ∀ (A R : Type) permutedims a,
  pd203 (R := R) (permutedims : A → List Int → R) a = permutedims a [2, 1]
theorem pd203Property : PD203Property := by unfold PD203Property; intros; rfl

def pd273 (length : A → Nat) (reshape : A → Nat → Nat → R) (a : A) : R :=
  reshape a 1 (length a)
def PD273Property : Prop := ∀ (A R : Type) length reshape a,
  pd273 (R := R) (length : A → Nat) (reshape : A → Nat → Nat → R) a =
    reshape a 1 (length a)
theorem pd273Property : PD273Property := by unfold PD273Property; intros; rfl

def pd286 (checkdims : D → S → P → PDResult Unit) (invperm : P → IP)
    (view : B → IP → V) (copy : V → A → PDResult Unit)
    (dest : B) (src : A) (destAxes : D) (srcAxes : S) (perm : P) : PDResult B := do
  checkdims destAxes srcAxes perm
  let target := view dest (invperm perm)
  copy target src
  pure dest
def PD286Property : Prop := ∀ (D S P IP B V A : Type) checkdims invperm view copy dest src da sa perm,
  pd286 (checkdims : D → S → P → PDResult Unit) (invperm : P → IP)
      (view : B → IP → V) (copy : V → A → PDResult Unit) dest src da sa perm = do
    checkdims da sa perm
    let target := view dest (invperm perm)
    copy target src
    pure dest
theorem pd286Property : PD286Property := by unfold PD286Property; intros; rfl

def pd293 (empty : S → Bool) (checkbounds : D → X → PDResult Unit)
    (axes : S → X) (unalias : D → S → S) (copy : D → S → PDResult Unit)
    (dest : D) (src : S) : PDResult D :=
  if empty src then pure dest else do
    checkbounds dest (axes src)
    let source := unalias dest src
    copy dest source
    pure dest
def PD293Property : Prop := ∀ (D S X : Type) empty check axes unalias copy dest src,
  pd293 (empty : S → Bool) (check : D → X → PDResult Unit) (axes : S → X)
      (unalias : D → S → S) (copy : D → S → PDResult Unit) dest src =
    if empty src then pure dest else do
      check dest (axes src)
      let source := unalias dest src
      copy dest source
      pure dest
theorem pd293Property : PD293Property := by unfold PD293Property; intros; rfl

def prefixFixedGo : List Nat → Nat → Nat
  | [], d => d
  | p :: ps, d => if p = d + 1 then prefixFixedGo ps (d + 1) else d

def prefixFixed (perm : List Nat) : Nat := prefixFixedGo perm 0

def pd300 (rank : S → Nat) (parent : P → D) (copyto : D → S → PDResult Unit)
    (ranges : S → Nat → RR) (findDest : Nat → List Nat → Nat)
    (kernel : P → S → RR → RR → RR → Nat → Nat → PDResult Unit)
    (p : P) (src : S) (perm : List Nat) : PDResult P := do
  let d := prefixFixed perm
  if d = rank src then copyto (parent p) src
  else
    let d1 := findDest (d + 1) perm
    kernel p src (ranges src d) (ranges src (d1 - d - 2)) (ranges src (rank src - d1))
      (d + 1) d1
  pure p
def PD300Property : Prop := ∀ (S P D RR : Type) rank parent copyto ranges findDest kernel p src perm,
  pd300 (rank : S → Nat) (parent : P → D) (copyto : D → S → PDResult Unit)
      (ranges : S → Nat → RR) (findDest : Nat → List Nat → Nat)
      (kernel : P → S → RR → RR → RR → Nat → Nat → PDResult Unit) p src perm = do
    let d := prefixFixed perm
    if d = rank src then copyto (parent p) src
    else
      let d1 := findDest (d + 1) perm
      kernel p src (ranges src d) (ranges src (d1 - d - 2)) (ranges src (rank src - d1))
        (d + 1) d1
    pure p
theorem pd300Property : PD300Property := by unfold PD300Property; intros; rfl

def kernelAssignments (r1 r2 r3 rows cols : List I) (get : List I → V)
    (set : A → List I → V → A) (initial : A) : A :=
  rows.foldl (fun out i =>
    cols.foldl (fun out j =>
      r3.foldl (fun out i3 =>
        r2.foldl (fun out i2 =>
          r1.foldl (fun out i1 =>
            set out [i1, i, i2, j, i3] (get [i1, i, i2, j, i3])) out) out) out) out) initial

def pd319 [Inhabited I] (r2 r3 rows cols : List I) (get : List I → V)
    (set : A → List I → V → A) (initial : A) : A :=
  kernelAssignments [default] r2 r3 rows cols get set initial

def PD319Property : Prop := ∀ (I A V : Type) [Inhabited I] r2 r3 rows cols get set initial,
  pd319 (r2 : List I) r3 rows cols (get : List I → V) (set : A → List I → V → A) initial =
    kernelAssignments [default] r2 r3 rows cols get set initial
theorem pd319Property : PD319Property := by unfold PD319Property; intros; rfl

def pd333 (r1 r2 r3 rows cols : List I) (get : List I → V)
    (set : A → List I → V → A) (initial : A) : A :=
  kernelAssignments r1 r2 r3 rows cols get set initial
def PD333Property : Prop := ∀ (I A V : Type) r1 r2 r3 rows cols get set initial,
  pd333 (r1 : List I) r2 r3 rows cols (get : List I → V)
      (set : A → List I → V → A) initial =
    kernelAssignments r1 r2 r3 rows cols get set initial
theorem pd333Property : PD333Property := by unfold PD333Property; intros; rfl

def pd351 (reduce : F → Op → Init → P → D → R) (parent : A → P)
    (f : F) (op : Op) (init : Init) (a : A) (dims : D) : R :=
  reduce f op init (parent a) dims
def PD351Property : Prop := ∀ (F Op Init P D R A : Type) reduce parent f op init a dims,
  pd351 (R := R) (reduce : F → Op → Init → P → D → R) (parent : A → P)
      f op init a dims = reduce f op init (parent a) dims
theorem pd351Property : PD351Property := by unfold PD351Property; intros; rfl

def pd354 (reduce : F → Op → Init → P → D → R) (parent : A → P)
    (f : F) (op : Op) (init : Init) (a : A) (dims : D) : R :=
  reduce f op init (parent a) dims
def PD354Property : Prop := ∀ (F Op Init P D R A : Type) reduce parent f op init a dims,
  pd354 (R := R) (reduce : F → Op → Init → P → D → R) (parent : A → P)
      f op init a dims = reduce f op init (parent a) dims
theorem pd354Property : PD354Property := by unfold PD354Property; intros; rfl

def pd358 (inverseView : B → C) (parent : A → P)
    (reduce : F → Op → C → P → PDResult Unit) (f : F) (op : Op)
    (b : B) (a : A) : PDResult B := do
  reduce f op (inverseView b) (parent a)
  pure b
def PD358Property : Prop := ∀ (B C A P F Op : Type) inverse parent reduce f op b a,
  pd358 (inverse : B → C) (parent : A → P)
      (reduce : F → Op → C → P → PDResult Unit) f op b a = do
    reduce f op (inverse b) (parent a)
    pure b
theorem pd358Property : PD358Property := by unfold PD358Property; intros; rfl

def pd363 (inverseView : B → C) (parent : A → P)
    (reduce : F → Op → C → P → PDResult Unit) (f : F) (op : Op)
    (b : B) (a : A) : PDResult B := do
  reduce f op (inverseView b) (parent a)
  pure b
def PD363Property : Prop := ∀ (B C A P F Op : Type) inverse parent reduce f op b a,
  pd363 (inverse : B → C) (parent : A → P)
      (reduce : F → Op → C → P → PDResult Unit) f op b a = do
    reduce f op (inverse b) (parent a)
    pure b
theorem pd363Property : PD363Property := by unfold PD363Property; intros; rfl

def pd369 (showParent : P → String) (showPerm : List Nat → String)
    (showEltype : A → String) (a : A) (parent : P) (perm : List Nat)
    (toplevel : Bool) : List String :=
  ["PermutedDimsArray(", showParent parent, ", ", showPerm perm, ")"] ++
    if toplevel then [" with eltype ", showEltype a] else []
def PD369Property : Prop := ∀ (P A : Type) showParent showPerm showEltype a parent perm top,
  pd369 (showParent : P → String) (showPerm : List Nat → String)
      (showEltype : A → String) a parent perm top =
    ["PermutedDimsArray(", showParent parent, ", ", showPerm perm, ")"] ++
      if top then [" with eltype ", showEltype a] else []
theorem pd369Property : PD369Property := by unfold PD369Property; intros; rfl

private def pdEntry (line : Nat) (fn statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-permuteddimsarray-line{line}",
    juliaFile := "base/permuteddimsarray.jl", juliaFns := [fn], statement, source,
    status := .proven, prop, thm := some thm }

def permutedDimsReviewEntries : List Entry := []

end JuliaLean.MultidimCov
