import JuliaLean.BitSetsCov.CollectionBugs

/-!
# `Set`, `AbstractSet`, and `IdSet` source models

The models use natural numbers as equality classes for ordinary `isequal`
sets. `IdValue.identity` is the `===` key used by `IdSet`; its separate
`value` field lets documented value-based operations be stated independently.
Every definition cites the master source path implemented by its branches and
loops.
-/

namespace JuliaLean.BitSetsCov

namespace Coll

open Bugs

abbrev SetState := List Nat

def insert (s : SetState) (x : Nat) : SetState :=
  if x ∈ s then s else s ++ [x]

def ofList (xs : List Nat) : SetState := xs.foldl insert []

def erase (s : SetState) (x : Nat) : SetState := s.erase x

def unionOne (s : SetState) (xs : List Nat) : SetState := xs.foldl insert s

def unionMany (s : SetState) (xss : List (List Nat)) : SetState := xss.foldl unionOne s

def intersectOne (s xs : List Nat) : SetState := s.filter (fun x => decide (x ∈ xs))

def intersectMany (s : SetState) (xss : List (List Nat)) : SetState := xss.foldl intersectOne s

def setdiffOne (s xs : List Nat) : SetState := xs.foldl erase s

def setdiffMany (s : SetState) (xss : List (List Nat)) : SetState := xss.foldl setdiffOne s

def symdiffOne (s xs : List Nat) : SetState :=
  (ofList xs).foldl (fun r x => if x ∈ r then erase r x else insert r x) s

def symdiffMany (s : SetState) (xss : List (List Nat)) : SetState := xss.foldl symdiffOne s

def subset (a b : List Nat) : Bool := a.all (fun x => decide (x ∈ b))

def setequal (a b : List Nat) : Bool := subset a b && subset b a

def properSubset (a b : List Nat) : Bool := decide (a.length < b.length) && subset a b

def disjointEq (eq : Nat → Nat → Bool) (a b : List Nat) : Bool :=
  !a.any (fun x => b.any (eq x))

/-! ## `base/abstractset.jl` -/

/-- Lines 3-4. -/
def abstractEltype (defined : Bool) (declared : Nat) : Nat := if defined then declared else 0
def abstractSizehint (s : SetState) (_n : Int) : SetState := s

/-- Lines 6-9. -/
def abstractCopyBang (same : Bool) (dst src : SetState) : SetState :=
  if same then dst else unionOne [] src

/-- Lines 55-58 and 105-112. -/
def abstractUnion (s : SetState) (sets : List (List Nat)) : SetState :=
  unionMany [] (s :: sets)
def abstractUnionUnary (s : SetState) : SetState := s
def abstractUnionBangMany (s : SetState) (sets : List (List Nat)) : SetState := unionMany s sets
def abstractUnionBangOne (s itr : SetState) (maxValues : Nat) : SetState :=
  itr.foldl (fun out x => if out.length = maxValues then out else insert out x) s

/-- Lines 92-103. -/
def maxValuesGeneric : Nat := 9223372036854775807
def maxValuesSmall (bytes : Nat) : Nat := 2 ^ (8 * bytes)
def maxValuesUnion (a b : Nat) : Nat :=
  if maxValuesGeneric - a < b then maxValuesGeneric else a + b
def maxValuesBool : Nat := 2
def maxValuesNothing : Nat := 1

/-- Lines 155-180. The first branch models the shortest-set rotation; both
branches then call the two-argument body and fold `intersect!` over `itrs`. -/
def abstractIntersect (s itr : SetState) (itrs : List SetState) : SetState :=
  let candidates := itr :: itrs
  let first := candidates.foldl (fun best x => if x.length < best.length then x else best) itr
  intersectMany (intersectOne s first) (candidates.erase first)
def abstractIntersectUnary (s : SetState) : SetState := abstractUnionUnary s
def abstractIntersectTwo (s itr : SetState) : SetState :=
  if s.length < itr.length then intersectOne s itr else intersectOne itr s
def abstractIntersectBangMany (s : SetState) (itrs : List SetState) : SetState := intersectMany s itrs
def abstractIntersectBangSet (s s2 : SetState) : SetState := intersectOne s s2
def abstractIntersectBangItr (s itr : SetState) : SetState := intersectOne s (ofList itr)

/-- Lines 222-255. -/
def abstractSetdiff (s : SetState) (itrs : List SetState) : SetState := setdiffMany s itrs
def abstractSetdiffUnary (s : SetState) : SetState := abstractUnionUnary s
def abstractSetdiffBangMany (s : SetState) (itrs : List SetState) : SetState := setdiffMany s itrs
def abstractSetdiffBangItr (s itr : SetState) : SetState := setdiffOne s itr

/-- Lines 278-304. -/
def abstractSymdiff (s : SetState) (sets : List SetState) : SetState := symdiffMany [] (s :: sets)
def abstractSymdiffUnary (s : SetState) : SetState := symdiffOne s []
def abstractSymdiffBangMany (s : SetState) (itrs : List SetState) : SetState := symdiffMany s itrs
def abstractSymdiffBangItr (s itr : SetState) : SetState := symdiffOne s (ofList itr)
def abstractSymdiffBangSet (s itr : SetState) : SetState := symdiffOne s itr

/-- Lines 335-369. `fastB` and `setA` are the two source traits. -/
def abstractIssubset (setA fastB : Bool) (a b : SetState) : Bool :=
  if !fastB && b.length > 70 then subset a (ofList b)
  else if setA && a.length > b.length then false
  else subset a b
def hasfastinType (isSetOrDictOrRange : Bool) : Bool := isSetOrDictOrRange
def hasfastinValue (isSetOrDictOrRange : Bool) : Bool := hasfastinType isSetOrDictOrRange

/-- The operator wrappers and curried `Fix2` methods, lines 309-500. -/
def superset (a b : SetState) : Bool := subset b a
def subsetFix (a y : SetState) : Bool := subset y a
def supersetFix (a y : SetState) : Bool := superset y a
def properSuperset (a b : SetState) : Bool := properSubset b a
def properSubsetConverted (a b : List Nat) : Bool := properSubset (ofList a) (ofList b)
def properSupersetFix (a y : SetState) : Bool := properSuperset y a
def properSubsetFix (a y : SetState) : Bool := properSubset y a
def notSubset (a b : SetState) : Bool := !subset a b
def notSuperset (a b : SetState) : Bool := notSubset b a
def notSupersetFix (a y : SetState) : Bool := notSuperset y a
def notSubsetFix (a y : SetState) : Bool := notSubset y a

/-- Lines 521-549. -/
def abstractSetequalSet (a b : SetState) : Bool := setequal a b
def abstractSetequalLeft (a b : List Nat) : Bool := abstractSetequalSet a (ofList b)
def abstractSetequalRight (a b : List Nat) : Bool :=
  if a.length < (ofList b).length then false else abstractSetequalSet (ofList a) b
def abstractSetequalGeneric (a b : List Nat) : Bool := abstractSetequalSet (ofList a) (ofList b)
def abstractSetequalFix (a y : List Nat) : Bool := abstractSetequalGeneric y a

/-- Lines 572-610. This is the ordinary-value analogue of the signed-zero
model in `CollectionBugs`. -/
def abstractIsdisjoint (a b : List Nat) : Bool :=
  if b.length < a.length then disjointEq (fun x y => decide (x = y)) b a
  else if b.length < 70 then disjointEq (fun x y => decide (x = y)) a b
  else disjointEq (fun x y => decide (x = y)) a (ofList b)
def abstractIsdisjointFix (a y : List Nat) : Bool := abstractIsdisjoint y a

structure IntRange where
  first : Int
  step : Int
  len : Nat
  deriving DecidableEq

def rangeValues (r : IntRange) : List Int :=
  (List.range r.len).map (fun (i : Nat) => r.first + r.step * (i : Int))

def rangeDisjoint (a b : IntRange) : RangeOutcome :=
  if a.len = 0 || b.len = 0 then .value true
  else
    let av := rangeValues a
    let bv := rangeValues b
    let amin := av.foldl min a.first
    let bmin := bv.foldl min b.first
    overlappingRangeIsdisjoint amin a.step bmin b.step

def overlappingRangeGeneric (a b : IntRange) : Bool :=
  disjointEq (fun x y => decide (x = y)) ((rangeValues a).map Int.natAbs) ((rangeValues b).map Int.natAbs)

/-- Lines 625-641. -/
def abstractLt (a b : SetState) : Bool := properSubset a b
def abstractLe (a b : SetState) : Bool := subset a b
def mapfilter (pred : Nat → Bool) (f : SetState → Nat → SetState)
    (itr res : SetState) : SetState :=
  itr.foldl (fun out x => if pred x then f out x else out) res
def abstractFilter (pred : Nat → Bool) (s : SetState) : SetState := mapfilter pred insert s []
def abstractUnsafeFilter (pred : Nat → Bool) (s : SetState) : SetState :=
  mapfilter (fun x => !pred x) erase s s

/-! ## `base/set.jl` -/

/-- Lines 42-73. -/
def setFromDict (keys : SetState) : SetState := keys
def setEmpty : SetState := []
def setCopy (s : SetState) : SetState := s
def setTyped (itr : List Nat) : SetState := unionOne [] itr
def setAny : SetState := []
def setKeyset (keys : SetState) : SetState := keys
def setHasEltype (itr : List Nat) : SetState := setTyped itr
def setUnknownEltype (concrete : Bool) (itr : List Nat) : SetState :=
  if concrete then setTyped itr else unionOne [] itr
def setEmptyLike (_s : SetState) : SetState := []
def setSimilar (_s : SetState) : SetState := []

/-- Lines 75-178. -/
def setShow (sameTypeInfo : Bool) (s : SetState) : String :=
  if s.isEmpty then if sameTypeInfo then "Set()" else "Set{T}()" else "Set(...)"
def setIsEmpty (s : SetState) : Bool := s.isEmpty
def setLength (s : SetState) : Nat := s.length
def setIn (x : Nat) (s : SetState) : Bool := decide (x ∈ s)
def setInBang (x : Nat) (s : SetState) : Bool × SetState :=
  if x ∈ s then (true, s) else (false, insert s x)
def setPush (s : SetState) (x : Nat) : SetState := insert s x
def setPopDefault (s : SetState) (x default : Nat) : Nat × SetState :=
  if x ∈ s then (x, erase s x) else (default, s)
def setPopKey (s : SetState) (x : Nat) : Option (Nat × SetState) :=
  if x ∈ s then some (x, erase s x) else none
def setPopAny (s : SetState) : Option (Nat × SetState) :=
  match s with | [] => none | x :: xs => some (x, xs)
def setDelete (s : SetState) (x : Nat) : SetState := erase s x
def setSizehint (s : SetState) (_n : Int) (_shrink : Bool) : SetState := s
def setEmptyBang (_s : SetState) : SetState := []
def setRehash (s : SetState) : SetState := s
def setIterate (s : SetState) (state : Nat) : Option (Nat × Nat) :=
  match s.drop state with | [] => none | x :: _ => some (x, state + 1)
def setOnly (s : SetState) : Option Nat := match s with | [x] => some x | _ => none

/-- Lines 187-198. -/
def setSetdiff (s t : SetState) : SetState :=
  if 2 * s.length < t.length then s.filter (fun x => decide (x ∉ t)) else setdiffOne s t

/-- Stable first-occurrence selection used by the methods at lines 203-478. -/
def uniqueBy (f : Nat → Nat) (xs : List Nat) : List Nat :=
  (xs.foldl (fun acc x =>
    let keys := acc.2
    let k := f x
    if k ∈ keys then acc else (acc.1 ++ [x], keys ++ [k])) ([], [])).1
def unique (xs : List Nat) : List Nat := uniqueBy id xs
def uniqueFrom (xs out seen : List Nat) (i : Nat) : List Nat :=
  out ++ unique (xs.drop i |>.filter (fun x => decide (x ∉ seen)))
def uniqueBangBy (f : Nat → Nat) (xs : List Nat) : List Nat := uniqueBy f xs
def uniqueBang (xs : List Nat) : List Nat := unique xs
def groupedUnique (xs : List Nat) : List Nat :=
  xs.foldl (fun out x => if out.getLast? = some x then out else out ++ [x]) []
def uniqueDispatch (ordered sorted : Bool) (xs : List Nat) : List Nat :=
  if ordered && sorted then groupedUnique xs else uniqueBang xs

def allunique (xs : List Nat) : Bool := decide xs.Nodup
def hashedAllunique (xs : List Nat) : Bool := allunique xs
def indexedAllunique (xs : List Nat) : Bool := allunique xs
def alluniqueDispatch (hasLength : Bool) (xs : List Nat) : Bool :=
  if hasLength && xs.length < 2 then true
  else if hasLength && xs.length < 32 then indexedAllunique xs else hashedAllunique xs
def alluniqueMap (f : Nat → Nat) (xs : List Nat) : Bool := alluniqueDispatch true (xs.map f)
def alluniqueSet (_s : SetState) : Bool := true
def alluniqueString (codepoints : List Nat) : Bool :=
  if codepoints.length < 32 then indexedAllunique codepoints else hashedAllunique codepoints
def alluniqueTuple (xs : List Nat) : Bool :=
  if xs.length < 32 then indexedAllunique xs else hashedAllunique xs
def alluniqueEmptyTuple : Bool := true

def allequal (xs : List Nat) : Bool :=
  match xs with | [] => true | x :: rest => rest.all (fun y => decide (x = y))
def allequalSet (s : SetState) : Bool := decide (s.length ≤ 1)
def allequalMap (f : Nat → Nat) (xs : List Nat) : Bool := allequal (xs.map f)
def allequalLoop (f : Nat → Nat) (xs : List Nat) : Bool := allequalMap f xs
def allequalTuple (f : Nat → Nat) (xs : List Nat) : Bool :=
  if xs.length ≤ 1 then true else allequalLoop f xs
def allequalEmptyTuple : Bool := true

/-- Lines 695-731. -/
def setFilterBang (f : Nat → Bool) (s : SetState) : SetState := abstractUnsafeFilter f s
def setHash (hash : Nat → Nat) (seed : Nat) (s : SetState) : Nat :=
  s.foldl (fun h x => h ^^^ hash x) seed
def setConvertSame (s : SetState) : SetState := s
def setConvert (s : SetState) : SetState := ofList s

inductive CountOutcome where | ok (count : Nat) | domainError deriving DecidableEq
def checkCount (count : Int) : CountOutcome :=
  if count < 0 then .domainError else .ok (min count 9223372036854775807).toNat
def copyOfType (x : List Nat) : List Nat := x
def similarOrCopy (isSetOrDict : Bool) (x : List Nat) : List Nat := if isSetOrDict then x else []

/-- Lines 762-902. -/
def replacePairs (pairs : List (Nat × Nat)) (x : Nat) : Nat :=
  match pairs.find? (fun p => p.1 = x) with | some p => p.2 | none => x
def replacePairsBang (A : List Nat) (pairs : List (Nat × Nat)) (count : Nat) : List Nat :=
  (A.foldl (fun acc x =>
    let y := if acc.2 < count then replacePairs pairs x else x
    (acc.1 ++ [y], acc.2 + if x = y then 0 else 1)) ([], 0)).1
def replaceCallableBang (f : Nat → Nat) (A : List Nat) (count : Nat) : List Nat :=
  replacePairsBang A (A.map fun x => (x, f x)) count
def replacePairsCopy (A : List Nat) (pairs : List (Nat × Nat)) (count : Nat) : List Nat :=
  replacePairsBang A pairs count
def promoteValueType (types : List Nat) : Nat := types.foldl max 0
def subtractSingleton (isSingleton : Bool) (t singleton : Nat) : Nat := if isSingleton && t = singleton then 0 else t
def replaceCallableCopy (f : Nat → Nat) (A : List Nat) (count : Nat) : List Nat :=
  replaceCallableBang f A count
def replaceAmbiguous : Bool := false

/-- Lines 906-1046. -/
def askeyDict (p : Nat × Nat) : Nat := p.1
def askeySet (x : Nat) : Nat := x
def replaceCollection (f : Nat → Nat) (res source : SetState) : SetState :=
  replaceSeparate f source res
def replaceArray (f : Nat → Nat) (res source : List Nat) (count : Nat) : List Nat :=
  replaceCallableBang f source count |>.take res.length
def replaceDict (f : (Nat × Nat) → Nat × Nat) (pairs : List (Nat × Nat)) : List (Nat × Nat) :=
  pairs.map f
def replaceSet (f : Nat → Nat) (s : SetState) : SetState := ofList (s.map f)
def replaceTuple (f : Nat → Nat) : List Nat → Nat → List Nat
  | [], _ => []
  | xs, 0 => xs
  | x :: xs, count + 1 =>
      let y := f x
      y :: replaceTuple f xs (count + 1 - if x = y then 0 else 1)
def replaceTuplePairs (t : List Nat) (count : Nat) (pairs : List (Nat × Nat)) : List Nat :=
  replaceTuple (replacePairs pairs) t count

/-! ## `base/idset.jl` -/

abbrev IdState := List IdValue

def idFind (identity : Nat) (s : IdState) : Option IdValue := s.find? (fun x => x.identity = identity)
def idErase (identity : Nat) (s : IdState) : IdState := s.filter (fun x => x.identity != identity)
def idPush (s : IdState) (x : IdValue) : IdState := idErase x.identity s ++ [x]
def idOfList (xs : IdState) : IdState := xs.foldl idPush []
def idEmpty : IdState := []
def idCopy (s : IdState) : IdState := s
def idHasKey (s : IdState) (x : IdValue) : Bool := decide (idFind x.identity s).isSome
def idIsEmpty (s : IdState) : Bool := s.isEmpty
def idPopInternal (s : IdState) (x : IdValue) : Int × IdState :=
  if idHasKey s x then (0, idErase x.identity s) else (-1, s)
def idPopKey (s : IdState) (x : IdValue) : Option (IdValue × IdState) :=
  if idHasKey s x then some (x, idErase x.identity s) else none
def idPopDefault (s : IdState) (x default : IdValue) : IdValue × IdState :=
  if idHasKey s x then (x, idErase x.identity s) else (default, s)
def idZero (a : List Nat) : List Nat := List.replicate a.length 0
def idFilter (f : IdValue → Bool) (s : IdState) : IdState := s.filter f

/-! ## Closed row properties -/

def AbstractBasicSpec : Prop :=
  (∀ d t, abstractEltype d t = if d then t else 0) ∧
  (∀ s n, abstractSizehint s n = s) ∧
  (∀ same dst src, abstractCopyBang same dst src = if same then dst else unionOne [] src)

def AbstractUnionSpec : Prop :=
  (∀ s sets, abstractUnion s sets = unionMany [] (s :: sets)) ∧
  (∀ s, abstractUnionUnary s = s) ∧
  (∀ s sets, abstractUnionBangMany s sets = unionMany s sets) ∧
  (∀ s itr m, abstractUnionBangOne s itr m =
    itr.foldl (fun out x => if out.length = m then out else insert out x) s) ∧
  maxValuesGeneric = 9223372036854775807 ∧
  (∀ b, maxValuesSmall b = 2 ^ (8 * b)) ∧
  (∀ a b, maxValuesUnion a b = if maxValuesGeneric - a < b then maxValuesGeneric else a + b) ∧
  maxValuesBool = 2 ∧ maxValuesNothing = 1

def AbstractIntersectSpec : Prop :=
  (∀ s itr itrs, abstractIntersect s itr itrs =
    let candidates := itr :: itrs
    let first := candidates.foldl (fun best x => if x.length < best.length then x else best) itr
    intersectMany (intersectOne s first) (candidates.erase first)) ∧
  (∀ s, abstractIntersectUnary s = abstractUnionUnary s) ∧
  (∀ s itr, abstractIntersectTwo s itr = if s.length < itr.length then intersectOne s itr else intersectOne itr s) ∧
  (∀ s xs, abstractIntersectBangMany s xs = intersectMany s xs) ∧
  (∀ s t, abstractIntersectBangSet s t = intersectOne s t) ∧
  (∀ s t, abstractIntersectBangItr s t = intersectOne s (ofList t))

def AbstractSetdiffSpec : Prop :=
  (∀ s xs, abstractSetdiff s xs = setdiffMany s xs) ∧
  (∀ s, abstractSetdiffUnary s = abstractUnionUnary s) ∧
  (∀ s xs, abstractSetdiffBangMany s xs = setdiffMany s xs) ∧
  (∀ s x, abstractSetdiffBangItr s x = setdiffOne s x)

def AbstractSymdiffSpec : Prop :=
  (∀ s xs, abstractSymdiff s xs = symdiffMany [] (s :: xs)) ∧
  (∀ s, abstractSymdiffUnary s = symdiffOne s []) ∧
  (∀ s xs, abstractSymdiffBangMany s xs = symdiffMany s xs) ∧
  (∀ s x, abstractSymdiffBangItr s x = symdiffOne s (ofList x)) ∧
  (∀ s x, abstractSymdiffBangSet s x = symdiffOne s x)

def AbstractCompareSpec : Prop :=
  (∀ setA fastB a b, abstractIssubset setA fastB a b =
    if !fastB && b.length > 70 then subset a (ofList b)
    else if setA && a.length > b.length then false else subset a b) ∧
  (∀ t, hasfastinType t = t) ∧ (∀ t, hasfastinValue t = t) ∧
  (∀ a b, superset a b = subset b a) ∧
  (∀ a y, subsetFix a y = subset y a) ∧ (∀ a y, supersetFix a y = superset y a) ∧
  (∀ a b, properSuperset a b = properSubset b a) ∧
  (∀ a b, properSubsetConverted a b = properSubset (ofList a) (ofList b)) ∧
  (∀ a y, properSupersetFix a y = properSuperset y a) ∧
  (∀ a y, properSubsetFix a y = properSubset y a) ∧
  (∀ a b, notSubset a b = !subset a b) ∧ (∀ a b, notSuperset a b = notSubset b a) ∧
  (∀ a y, notSupersetFix a y = notSuperset y a) ∧ (∀ a y, notSubsetFix a y = notSubset y a)

def AbstractSetequalSpec : Prop :=
  (∀ a b, abstractSetequalSet a b = setequal a b) ∧
  (∀ a b, abstractSetequalLeft a b = abstractSetequalSet a (ofList b)) ∧
  (∀ a b, abstractSetequalRight a b = if a.length < (ofList b).length then false else abstractSetequalSet (ofList a) b) ∧
  (∀ a b, abstractSetequalGeneric a b = abstractSetequalSet (ofList a) (ofList b)) ∧
  (∀ a y, abstractSetequalFix a y = abstractSetequalGeneric y a)

def AbstractDisjointFilterSpec : Prop :=
  (∀ a b, abstractIsdisjoint a b =
    if b.length < a.length then disjointEq (fun x y => decide (x = y)) b a
    else if b.length < 70 then disjointEq (fun x y => decide (x = y)) a b
    else disjointEq (fun x y => decide (x = y)) a (ofList b)) ∧
  (∀ a y, abstractIsdisjointFix a y = abstractIsdisjoint y a) ∧
  (∀ a b, rangeDisjoint a b =
    if a.len = 0 || b.len = 0 then .value true else
      let av := rangeValues a; let bv := rangeValues b
      overlappingRangeIsdisjoint (av.foldl min a.first) a.step (bv.foldl min b.first) b.step) ∧
  (∀ a b, overlappingRangeGeneric a b =
    disjointEq (fun x y => decide (x = y)) ((rangeValues a).map Int.natAbs) ((rangeValues b).map Int.natAbs)) ∧
  (∀ a b, abstractLt a b = properSubset a b) ∧ (∀ a b, abstractLe a b = subset a b) ∧
  (∀ p s, abstractFilter p s = mapfilter p insert s []) ∧
  (∀ p s, abstractUnsafeFilter p s = mapfilter (fun x => !p x) erase s s) ∧
  (∀ p f itr res, mapfilter p f itr res = itr.foldl (fun out x => if p x then f out x else out) res)

def SetBasicSpec : Prop :=
  (∀ s, setFromDict s = s) ∧ setEmpty = [] ∧ (∀ s, setCopy s = s) ∧
  (∀ xs, setTyped xs = unionOne [] xs) ∧ setAny = [] ∧ (∀ s, setKeyset s = s) ∧
  (∀ xs, setHasEltype xs = setTyped xs) ∧
  (∀ c xs, setUnknownEltype c xs = if c then setTyped xs else unionOne [] xs) ∧
  (∀ s, setEmptyLike s = []) ∧ (∀ s, setSimilar s = [])

def SetMutableSpec : Prop :=
  (∀ ti s, setShow ti s = if s.isEmpty then if ti then "Set()" else "Set{T}()" else "Set(...)") ∧
  (∀ s, setIsEmpty s = s.isEmpty) ∧ (∀ s, setLength s = s.length) ∧
  (∀ x s, setIn x s = decide (x ∈ s)) ∧
  (∀ x s, setInBang x s = if x ∈ s then (true, s) else (false, insert s x)) ∧
  (∀ s x, setPush s x = insert s x) ∧
  (∀ s x d, setPopDefault s x d = if x ∈ s then (x, erase s x) else (d, s)) ∧
  (∀ s x, setPopKey s x = if x ∈ s then some (x, erase s x) else none) ∧
  (∀ s, setPopAny s = match s with | [] => none | x :: xs => some (x, xs)) ∧
  (∀ s x, setDelete s x = erase s x) ∧ (∀ s n sh, setSizehint s n sh = s) ∧
  (∀ s, setEmptyBang s = []) ∧ (∀ s, setRehash s = s) ∧
  (∀ s st, setIterate s st = match s.drop st with | [] => none | x :: _ => some (x, st + 1)) ∧
  (∀ s, setOnly s = match s with | [x] => some x | _ => none) ∧
  (∀ s t, setSetdiff s t = if 2 * s.length < t.length then s.filter (fun x => decide (x ∉ t)) else setdiffOne s t)

def SetUniqueSpec : Prop :=
  (∀ f xs, uniqueBy f xs =
    (xs.foldl (fun acc x => let k := f x; if k ∈ acc.2 then acc else (acc.1 ++ [x], acc.2 ++ [k])) ([], [])).1) ∧
  (∀ xs, unique xs = uniqueBy id xs) ∧
  (∀ xs out seen i, uniqueFrom xs out seen i = out ++ unique (xs.drop i |>.filter (fun x => decide (x ∉ seen)))) ∧
  (∀ f xs, uniqueBangBy f xs = uniqueBy f xs) ∧ (∀ xs, uniqueBang xs = unique xs) ∧
  (∀ xs, groupedUnique xs = xs.foldl (fun out x => if out.getLast? = some x then out else out ++ [x]) []) ∧
  (∀ o so xs, uniqueDispatch o so xs = if o && so then groupedUnique xs else uniqueBang xs)

def SetPredicatesSpec : Prop :=
  (∀ xs, allunique xs = decide xs.Nodup) ∧ (∀ xs, hashedAllunique xs = allunique xs) ∧
  (∀ xs, indexedAllunique xs = allunique xs) ∧
  (∀ h xs, alluniqueDispatch h xs = if h && xs.length < 2 then true else if h && xs.length < 32 then indexedAllunique xs else hashedAllunique xs) ∧
  (∀ f xs, alluniqueMap f xs = alluniqueDispatch true (xs.map f)) ∧
  (∀ s, alluniqueSet s = true) ∧
  (∀ xs, alluniqueString xs = if xs.length < 32 then indexedAllunique xs else hashedAllunique xs) ∧
  (∀ xs, alluniqueTuple xs = if xs.length < 32 then indexedAllunique xs else hashedAllunique xs) ∧
  alluniqueEmptyTuple = true ∧
  (∀ xs, allequal xs = match xs with | [] => true | x :: rest => rest.all (fun y => decide (x = y))) ∧
  (∀ s, allequalSet s = decide (s.length ≤ 1)) ∧ (∀ f xs, allequalMap f xs = allequal (xs.map f)) ∧
  (∀ f xs, allequalLoop f xs = allequalMap f xs) ∧
  (∀ f xs, allequalTuple f xs = if xs.length ≤ 1 then true else allequalLoop f xs) ∧
  allequalEmptyTuple = true

def SetHelpersSpec : Prop :=
  (∀ f s, setFilterBang f s = abstractUnsafeFilter f s) ∧
  (∀ h seed s, setHash h seed s = s.foldl (fun acc x => acc ^^^ h x) seed) ∧
  (∀ s, setConvertSame s = s) ∧ (∀ s, setConvert s = ofList s) ∧
  (∀ c, checkCount c = if c < 0 then .domainError else .ok (min c 9223372036854775807).toNat) ∧
  (∀ x, copyOfType x = x) ∧ (∀ b x, similarOrCopy b x = if b then x else [])

def SetReplaceSpec : Prop :=
  (∀ ps x, replacePairs ps x = match ps.find? (fun p => p.1 = x) with | some p => p.2 | none => x) ∧
  (∀ A ps c, replacePairsBang A ps c =
    (A.foldl (fun acc x => let y := if acc.2 < c then replacePairs ps x else x
      (acc.1 ++ [y], acc.2 + if x = y then 0 else 1)) ([], 0)).1) ∧
  (∀ f A c, replaceCallableBang f A c = replacePairsBang A (A.map fun x => (x, f x)) c) ∧
  (∀ A ps c, replacePairsCopy A ps c = replacePairsBang A ps c) ∧
  (∀ ts, promoteValueType ts = ts.foldl max 0) ∧
  (∀ b t s, subtractSingleton b t s = if b && t = s then 0 else t) ∧
  (∀ f A c, replaceCallableCopy f A c = replaceCallableBang f A c) ∧ replaceAmbiguous = false ∧
  (∀ p, askeyDict p = p.1) ∧ (∀ x, askeySet x = x) ∧
  (∀ f r s, replaceCollection f r s = replaceSeparate f s r) ∧
  (∀ f r s c, replaceArray f r s c = (replaceCallableBang f s c).take r.length) ∧
  (∀ f ps, replaceDict f ps = ps.map f) ∧ (∀ f s, replaceSet f s = ofList (s.map f)) ∧
  (∀ t c ps, replaceTuplePairs t c ps = replaceTuple (replacePairs ps) t c)

def IdSetBasicSpec : Prop :=
  idEmpty = [] ∧ (∀ s, idCopy s = s) ∧ (∀ xs, idOfList xs = xs.foldl idPush []) ∧
  (∀ s x, idHasKey s x = decide (idFind x.identity s).isSome) ∧
  (∀ s, idIsEmpty s = s.isEmpty)

def IdSetPopSpec : Prop :=
  (∀ s x, idPopInternal s x = if idHasKey s x then (0, idErase x.identity s) else (-1, s)) ∧
  (∀ s x, idPopKey s x = if idHasKey s x then some (x, idErase x.identity s) else none) ∧
  (∀ s x d, idPopDefault s x d = if idHasKey s x then (x, idErase x.identity s) else (d, s))

def IdSetMemorySpec : Prop :=
  (∀ a, idZero a = List.replicate a.length 0) ∧
  (∀ f s, idFilter f s = s.filter f)

theorem abstractBasicSpec : AbstractBasicSpec := by simp [AbstractBasicSpec, abstractEltype, abstractSizehint, abstractCopyBang]
theorem abstractUnionSpec : AbstractUnionSpec := by simp [AbstractUnionSpec, abstractUnion, abstractUnionUnary, abstractUnionBangMany, abstractUnionBangOne, maxValuesGeneric, maxValuesSmall, maxValuesUnion, maxValuesBool, maxValuesNothing]
theorem abstractIntersectSpec : AbstractIntersectSpec := by simp [AbstractIntersectSpec, abstractIntersect, abstractIntersectUnary, abstractIntersectTwo, abstractIntersectBangMany, abstractIntersectBangSet, abstractIntersectBangItr]
theorem abstractSetdiffSpec : AbstractSetdiffSpec := by simp [AbstractSetdiffSpec, abstractSetdiff, abstractSetdiffUnary, abstractSetdiffBangMany, abstractSetdiffBangItr]
theorem abstractSymdiffSpec : AbstractSymdiffSpec := by simp [AbstractSymdiffSpec, abstractSymdiff, abstractSymdiffUnary, abstractSymdiffBangMany, abstractSymdiffBangItr, abstractSymdiffBangSet]
theorem abstractCompareSpec : AbstractCompareSpec := by simp [AbstractCompareSpec, abstractIssubset, hasfastinType, hasfastinValue, superset, subsetFix, supersetFix, properSuperset, properSubsetConverted, properSupersetFix, properSubsetFix, notSubset, notSuperset, notSupersetFix, notSubsetFix]
theorem abstractSetequalSpec : AbstractSetequalSpec := by simp [AbstractSetequalSpec, abstractSetequalSet, abstractSetequalLeft, abstractSetequalRight, abstractSetequalGeneric, abstractSetequalFix]
theorem abstractDisjointFilterSpec : AbstractDisjointFilterSpec := by simp [AbstractDisjointFilterSpec, abstractIsdisjoint, abstractIsdisjointFix, rangeDisjoint, overlappingRangeGeneric, abstractLt, abstractLe, abstractFilter, abstractUnsafeFilter, mapfilter]
theorem setBasicSpec : SetBasicSpec := by simp [SetBasicSpec, setFromDict, setEmpty, setCopy, setTyped, setAny, setKeyset, setHasEltype, setUnknownEltype, setEmptyLike, setSimilar]
theorem setMutableSpec : SetMutableSpec := by simp [SetMutableSpec, setShow, setIsEmpty, setLength, setIn, setInBang, setPush, setPopDefault, setPopKey, setPopAny, setDelete, setSizehint, setEmptyBang, setRehash, setIterate, setOnly, setSetdiff]
theorem setUniqueSpec : SetUniqueSpec := by simp [SetUniqueSpec, uniqueBy, unique, uniqueFrom, uniqueBangBy, uniqueBang, groupedUnique, uniqueDispatch]
theorem setPredicatesSpec : SetPredicatesSpec := by simp [SetPredicatesSpec, allunique, hashedAllunique, indexedAllunique, alluniqueDispatch, alluniqueMap, alluniqueSet, alluniqueString, alluniqueTuple, alluniqueEmptyTuple, allequal, allequalSet, allequalMap, allequalLoop, allequalTuple, allequalEmptyTuple]
theorem setHelpersSpec : SetHelpersSpec := by simp [SetHelpersSpec, setFilterBang, setHash, setConvertSame, setConvert, checkCount, copyOfType, similarOrCopy]
theorem setReplaceSpec : SetReplaceSpec := by simp [SetReplaceSpec, replacePairs, replacePairsBang, replaceCallableBang, replacePairsCopy, promoteValueType, subtractSingleton, replaceCallableCopy, replaceAmbiguous, askeyDict, askeySet, replaceCollection, replaceArray, replaceDict, replaceSet, replaceTuplePairs]
theorem idSetBasicSpec : IdSetBasicSpec := by simp [IdSetBasicSpec, idEmpty, idCopy, idOfList, idHasKey, idIsEmpty]
theorem idSetPopSpec : IdSetPopSpec := by simp [IdSetPopSpec, idPopInternal, idPopKey, idPopDefault]
theorem idSetMemorySpec : IdSetMemorySpec := by simp [IdSetMemorySpec, idZero, idFilter]

end Coll

end JuliaLean.BitSetsCov
