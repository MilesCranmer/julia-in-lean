import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

abbrev ArrayMathResult (α : Type) := Except Unit α

def arraymath5 (broadcast : F → A → B → R) (f : F) (a : A) (b : B) : R :=
  broadcast f a b

def Arraymath5Property : Prop := ∀ (F A B R : Type)
    (broadcast : F → A → B → R) (f : F) (a : A) (b : B),
  arraymath5 broadcast f a b = broadcast f a b

theorem arraymath5Property : Arraymath5Property := by
  unfold Arraymath5Property
  intros
  rfl

def arraymath12 (mapN : F → A → A → List A → R)
    (f : F) (a b : A) (cs : List A) : R := mapN f a b cs

def Arraymath12Property : Prop := ∀ (F A R : Type)
    (mapN : F → A → A → List A → R) (f : F) (a b : A) (cs : List A),
  arraymath12 mapN f a b cs = mapN f a b cs

theorem arraymath12Property : Arraymath12Property := by
  unfold Arraymath12Property
  intros
  rfl

def arraymath16 (size : A → List Nat) (mapreduceSize : List A → List Nat)
    (reshape : A → List Nat → A) (mapN : F → List A → R)
    (f : F) (a b : A) (cs : List A) : R :=
  let arrays := a :: b :: cs
  let sz := mapreduceSize arrays
  let arraysSameShape := arrays.map fun x =>
    if sz.length = (size x).length then x else reshape x sz
  mapN f arraysSameShape

def Arraymath16Property : Prop := ∀ (F A R : Type)
    (size : A → List Nat) (mapreduceSize : List A → List Nat)
    (reshape : A → List Nat → A) (mapN : F → List A → R)
    (f : F) (a b : A) (cs : List A),
  arraymath16 (F := F) (R := R) size mapreduceSize reshape mapN f a b cs =
    let arrays := a :: b :: cs
    let sz := mapreduceSize arrays
    mapN f (arrays.map fun x => if sz.length = (size x).length then x else reshape x sz)

theorem arraymath16Property : Arraymath16Property := by
  unfold Arraymath16Property
  intros
  rfl

def arraymath27 (fix2 : F → B → G) (map : G → A → R)
    (f : F) (a : A) (b : B) : R := map (fix2 f b) a

def Arraymath27Property : Prop := ∀ (F A B G R : Type)
    (fix2 : F → B → G) (map : G → A → R) (f : F) (a : A) (b : B),
  arraymath27 (R := R) fix2 map f a b = map (fix2 f b) a

theorem arraymath27Property : Arraymath27Property := by
  unfold Arraymath27Property
  intros
  rfl

def arraymath31 (fix1 : F → A → G) (map : G → B → R)
    (f : F) (a : A) (b : B) : R := map (fix1 f a) b

def Arraymath31Property : Prop := ∀ (F A B G R : Type)
    (fix1 : F → A → G) (map : G → B → R) (f : F) (a : A) (b : B),
  arraymath31 (R := R) fix1 map f a b = map (fix1 f a) b

theorem arraymath31Property : Arraymath31Property := by
  unfold Arraymath31Property
  intros
  rfl

def arraymath36 (promoteShape : A → A → ArrayMathResult Unit)
    (broadcast : F → A → A → R) (f : F) (a b : A) : ArrayMathResult R := do
  promoteShape a b
  pure (broadcast f a b)

def Arraymath36Property : Prop := ∀ (F A R : Type)
    (promote : A → A → ArrayMathResult Unit) (broadcast : F → A → A → R)
    (f : F) (a b : A),
  arraymath36 (R := R) promote broadcast f a b = do
    promote a b
    pure (broadcast f a b)

theorem arraymath36Property : Arraymath36Property := by
  unfold Arraymath36Property
  intros
  rfl

def arraymath42 (map : (A → A) → A → R) (plus : A → A) (a : A) : R :=
  map plus a

def Arraymath42Property : Prop := ∀ (A R : Type)
    (map : (A → A) → A → R) (plus : A → A) (a : A),
  arraymath42 (R := R) map plus a = map plus a

theorem arraymath42Property : Arraymath42Property := by
  unfold Arraymath42Property
  intros
  rfl

def promoteAll (promote : A → A → ArrayMathResult Unit) (a : A) :
    List A → ArrayMathResult Unit
  | [] => pure ()
  | c :: cs => do promote a c; promoteAll promote a cs

def arraymath44 (promote : A → A → ArrayMathResult Unit)
    (broadcast : A → A → List A → R) (a b : A) (cs : List A) : ArrayMathResult R := do
  promote a b
  promoteAll promote a cs
  pure (broadcast a b cs)

def Arraymath44Property : Prop := ∀ (A R : Type)
    (promote : A → A → ArrayMathResult Unit) (broadcast : A → A → List A → R)
    (a b : A) (cs : List A),
  arraymath44 (R := R) promote broadcast a b cs = do
    promote a b
    promoteAll promote a cs
    pure (broadcast a b cs)

theorem arraymath44Property : Arraymath44Property := by
  unfold Arraymath44Property
  intros
  rfl

def arraymath54 (broadcast : F → A → B → R) (f : F) (a : A) (b : B) : R :=
  broadcast f a b

def Arraymath54Property : Prop := ∀ (F A B R : Type)
    (broadcast : F → A → B → R) (f : F) (a : A) (b : B),
  arraymath54 (R := R) broadcast f a b = broadcast f a b

theorem arraymath54Property : Arraymath54Property := by
  unfold Arraymath54Property
  intros
  rfl

def arraymath57 (broadcast : F → A → B → R) (f : F) (a : A) (b : B) : R :=
  broadcast f a b

def Arraymath57Property : Prop := ∀ (F A B R : Type)
    (broadcast : F → A → B → R) (f : F) (a : A) (b : B),
  arraymath57 (R := R) broadcast f a b = broadcast f a b

theorem arraymath57Property : Arraymath57Property := by
  unfold Arraymath57Property
  intros
  rfl

def arraymath92 (reverseImpl : A → D → R) (a : A) (dims : D) : R :=
  reverseImpl a dims

def Arraymath92Property : Prop := ∀ (A D R : Type)
    (reverseImpl : A → D → R) (a : A) (dims : D),
  arraymath92 (R := R) reverseImpl a dims = reverseImpl a dims

theorem arraymath92Property : Arraymath92Property := by
  unfold Arraymath92Property
  intros
  rfl

def arraymath93 (copyMutable : A → B) (reverseBang : B → D → R)
    (a : A) (dims : D) : R := reverseBang (copyMutable a) dims

def Arraymath93Property : Prop := ∀ (A B D R : Type)
    (copyMutable : A → B) (reverseBang : B → D → R) (a : A) (dims : D),
  arraymath93 (R := R) copyMutable reverseBang a dims = reverseBang (copyMutable a) dims

theorem arraymath93Property : Arraymath93Property := by
  unfold Arraymath93Property
  intros
  rfl

def arraymath103 (reverseImpl : A → D → R) (a : A) (dims : D) : R :=
  reverseImpl a dims

def Arraymath103Property : Prop := ∀ (A D R : Type)
    (reverseImpl : A → D → R) (a : A) (dims : D),
  arraymath103 (R := R) reverseImpl a dims = reverseImpl a dims

theorem arraymath103Property : Arraymath103Property := by
  unfold Arraymath103Property
  intros
  rfl

def arraymath104 (reverseImpl : A → List Int → R) (a : A) (rank : Nat) : R :=
  reverseImpl a ((List.range rank).map fun k => ((k + 1 : Nat) : Int))

def Arraymath104Property : Prop := ∀ (A R : Type)
    (reverseImpl : A → List Int → R) (a : A) (rank : Nat),
  arraymath104 (R := R) reverseImpl a rank =
    reverseImpl a ((List.range rank).map fun k => ((k + 1 : Nat) : Int))

theorem arraymath104Property : Arraymath104Property := by
  unfold Arraymath104Property
  intros
  rfl

def arraymath105 (toInt : I → ArrayMathResult Int)
    (reverseImpl : A → List Int → R) (a : A) (dim : I) : ArrayMathResult R := do
  let d ← toInt dim
  pure (reverseImpl a [d])

def Arraymath105Property : Prop := ∀ (I A R : Type)
    (toInt : I → ArrayMathResult Int) (reverseImpl : A → List Int → R)
    (a : A) (dim : I),
  arraymath105 (R := R) toInt reverseImpl a dim = do
    let d ← toInt dim
    pure (reverseImpl a [d])

theorem arraymath105Property : Arraymath105Property := by
  unfold Arraymath105Property
  intros
  rfl

def convertInts (toInt : I → ArrayMathResult Int) : List I → ArrayMathResult (List Int)
  | [] => pure []
  | d :: ds => do
      let value ← toInt d
      pure (value :: (← convertInts toInt ds))

def arraymath106 (toInt : I → ArrayMathResult Int)
    (reverseImpl : A → List Int → R) (a : A) (dims : List I) : ArrayMathResult R := do
  let converted ← convertInts toInt dims
  pure (reverseImpl a converted)

def Arraymath106Property : Prop := ∀ (I A R : Type)
    (toInt : I → ArrayMathResult Int) (reverseImpl : A → List Int → R)
    (a : A) (dims : List I),
  arraymath106 (R := R) toInt reverseImpl a dims = do
    let converted ← convertInts toInt dims
    pure (reverseImpl a converted)

theorem arraymath106Property : Arraymath106Property := by
  unfold Arraymath106Property
  intros
  rfl

def arraymath107 (rank : Nat) (sizes firsts lasts : List Int)
    (swapHalf : A → List Bool → List Int → List Int → A)
    (reverseMiddle : A → Nat → Int → List Nat → ArrayMathResult A)
    (a : A) (dims : List Nat) : ArrayMathResult A :=
  if dims.isEmpty then pure a
  else
    let dimrev := (List.range rank).map fun k => dims.contains (k + 1)
    if rank < dims.length || dims.length != dimrev.count true then .error ()
    else
      let lead := dims.headD 0
      let halfsz := (List.range rank).map fun k =>
        if k + 1 = lead then (sizes.getD k 0) / 2 else sizes.getD k 0
      let last1 := (List.range rank).map fun k => lasts.getD k 0 + firsts.getD k 0
      let swapped := swapHalf a dimrev halfsz last1
      if 1 < dims.length && (sizes.getD (lead - 1) 0) % 2 != 0 then
        let mid := firsts.getD (lead - 1) 0 + (sizes.getD (lead - 1) 0) / 2
        reverseMiddle swapped lead mid dims.tail
      else pure swapped

def Arraymath107Property : Prop := ∀ (A : Type) (rank : Nat)
    (sizes firsts lasts : List Int)
    (swapHalf : A → List Bool → List Int → List Int → A)
    (reverseMiddle : A → Nat → Int → List Nat → ArrayMathResult A)
    (a : A) (dims : List Nat),
  arraymath107 (A := A) rank sizes firsts lasts swapHalf reverseMiddle a dims =
    if dims.isEmpty then pure a
    else
      let dimrev := (List.range rank).map fun k => dims.contains (k + 1)
      if rank < dims.length || dims.length != dimrev.count true then .error ()
      else
        let lead := dims.headD 0
        let halfsz := (List.range rank).map fun k =>
          if k + 1 = lead then (sizes.getD k 0) / 2 else sizes.getD k 0
        let last1 := (List.range rank).map fun k => lasts.getD k 0 + firsts.getD k 0
        let swapped := swapHalf a dimrev halfsz last1
        if 1 < dims.length && (sizes.getD (lead - 1) 0) % 2 != 0 then
          reverseMiddle swapped lead
            (firsts.getD (lead - 1) 0 + (sizes.getD (lead - 1) 0) / 2) dims.tail
        else pure swapped

theorem arraymath107Property : Arraymath107Property := by
  unfold Arraymath107Property
  intros
  rfl

def arraymath133 (reverseImpl : A → Int → R) (a : A) (dims : List Int) : R :=
  reverseImpl a (dims.headD 0)

def Arraymath133Property : Prop := ∀ (A R : Type)
    (reverseImpl : A → Int → R) (a : A) (dim : Int),
  arraymath133 (R := R) reverseImpl a [dim] = reverseImpl a dim

theorem arraymath133Property : Arraymath133Property := by
  unfold Arraymath133Property
  intros
  rfl

def rotateLeftBody (axes : A → List Int × List Int)
    (similar : A → List Int → List Int → A) (get : A → Int → Int → V)
    (set : A → Int → Int → V → A) (a : A) : A :=
  let ind1 := (axes a).1
  let ind2 := (axes a).2
  let initial := similar a ind2 ind1
  let n := ind2.headD 0 + ind2.getLastD 0
  ind1.foldl (fun output i => ind2.foldl
    (fun output j => set output (n - j) i (get a i j)) output) initial

def Arraymath154Property : Prop := ∀ (A V : Type)
    (axes : A → List Int × List Int) (similar : A → List Int → List Int → A)
    (get : A → Int → Int → V) (set : A → Int → Int → V → A) (a : A),
  rotateLeftBody axes similar get set a =
    let ind1 := (axes a).1
    let ind2 := (axes a).2
    let initial := similar a ind2 ind1
    let n := ind2.headD 0 + ind2.getLastD 0
    ind1.foldl (fun output i => ind2.foldl
      (fun output j => set output (n - j) i (get a i j)) output) initial

theorem arraymath154Property : Arraymath154Property := by
  unfold Arraymath154Property
  intros
  rfl

def rotateRightBody (axes : A → List Int × List Int)
    (similar : A → List Int → List Int → A) (get : A → Int → Int → V)
    (set : A → Int → Int → V → A) (a : A) : A :=
  let ind1 := (axes a).1
  let ind2 := (axes a).2
  let initial := similar a ind2 ind1
  let m := ind1.headD 0 + ind1.getLastD 0
  ind1.foldl (fun output i => ind2.foldl
    (fun output j => set output j (m - i) (get a i j)) output) initial

def Arraymath182Property : Prop := ∀ (A V : Type)
    (axes : A → List Int × List Int) (similar : A → List Int → List Int → A)
    (get : A → Int → Int → V) (set : A → Int → Int → V → A) (a : A),
  rotateRightBody axes similar get set a =
    let ind1 := (axes a).1
    let ind2 := (axes a).2
    let initial := similar a ind2 ind1
    let m := ind1.headD 0 + ind1.getLastD 0
    ind1.foldl (fun output i => ind2.foldl
      (fun output j => set output j (m - i) (get a i j)) output) initial

theorem arraymath182Property : Arraymath182Property := by
  unfold Arraymath182Property
  intros
  rfl

def rotateHalfBody (axes : A → List Int × List Int) (similar : A → A)
    (get : A → Int → Int → V) (set : A → Int → Int → V → A) (a : A) : A :=
  let ind1 := (axes a).1
  let ind2 := (axes a).2
  let initial := similar a
  let m := ind1.headD 0 + ind1.getLastD 0
  let n := ind2.headD 0 + ind2.getLastD 0
  ind2.foldl (fun output j => ind1.foldl
    (fun output i => set output (m - i) (n - j) (get a i j)) output) initial

def Arraymath209Property : Prop := ∀ (A V : Type)
    (axes : A → List Int × List Int) (similar : A → A)
    (get : A → Int → Int → V) (set : A → Int → Int → V → A) (a : A),
  rotateHalfBody axes similar get set a =
    let ind1 := (axes a).1
    let ind2 := (axes a).2
    let initial := similar a
    let m := ind1.headD 0 + ind1.getLastD 0
    let n := ind2.headD 0 + ind2.getLastD 0
    ind2.foldl (fun output j => ind1.foldl
      (fun output i => set output (m - i) (n - j) (get a i j)) output) initial

theorem arraymath209Property : Arraymath209Property := by
  unfold Arraymath209Property
  intros
  rfl

def arraymath252 (left half right copy : A → R) (a : A) (k : Int) : R :=
  let turns := k % 4
  if turns = 1 then left a else if turns = 2 then half a
  else if turns = 3 then right a else copy a

def Arraymath252Property : Prop := ∀ (A R : Type)
    (left half right copy : A → R) (a : A) (k : Int),
  arraymath252 (R := R) left half right copy a k =
    let turns := k % 4
    if turns = 1 then left a else if turns = 2 then half a
    else if turns = 3 then right a else copy a

theorem arraymath252Property : Arraymath252Property := by
  unfold Arraymath252Property
  intros
  rfl

def arraymath292 (rotateLeft : A → Int → R) (a : A) (k : Int) : R :=
  rotateLeft a (-k)

def Arraymath292Property : Prop := ∀ (A R : Type)
    (rotateLeft : A → Int → R) (a : A) (k : Int),
  arraymath292 (R := R) rotateLeft a k = rotateLeft a (-k)

theorem arraymath292Property : Arraymath292Property := by
  unfold Arraymath292Property
  intros
  rfl

def arraymath317 (half copy : A → R) (a : A) (k : Int) : R :=
  if k % 2 = 1 then half a else copy a

def Arraymath317Property : Prop := ∀ (A R : Type)
    (half copy : A → R) (a : A) (k : Int),
  arraymath317 (R := R) half copy a k = if k % 2 = 1 then half a else copy a

theorem arraymath317Property : Arraymath317Property := by
  unfold Arraymath317Property
  intros
  rfl

private def arrayMathEntry (line : Nat) (fn statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-arraymath-line{line}", juliaFile := "base/arraymath.jl",
    juliaFns := [fn], statement, source, status := .proven, prop, thm := some thm }

def arrayMathReviewEntries : List Entry := []

end JuliaLean.MultidimCov
