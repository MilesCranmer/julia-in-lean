import JuliaLean.Reduce
import JuliaLean.ReduceCov.Dims
import JuliaLean.Registry.Types

/-! Method-specific models for `base/reducedim.jl` on master `bbfa0ce4150`. -/

namespace JuliaLean.ReduceCov.ReducedimRows

open JuliaLean.Registry
open JuliaLean.Reduce
open JuliaLean.ReduceCov

/-! Reduced axes, lines 6-35. -/

def m6 (one : α → α) (T : α) : α := one T
def m7 (first : α → β) (singleton : α → β → α) (i : α) : α := singleton i (first i)
def m8 (α : Type) : RJ α := .error (argErr "No method is implemented for reducing index range")
def m15 (axes : α → β) (reduced : β → γ → δ) (a : α) (region : γ) : δ := reduced (axes a) region
def m18 (axes : α → β) (reduced : β → γ → δ) (a : α) (region : γ) : δ := reduced (axes a) region
def m20 (check : List Int → RJ Unit) (reduceIndex : α → α) (axes : List α)
    (region : List Int) : RJ (List α) := do
  check region
  pure (axes.zipIdx 1 |>.map fun p => if p.2 ∈ region then reduceIndex p.1 else p.1)
def m25 (check : List Int → RJ Unit) (reduceIndex : α → α) (empty : α → Bool)
    (axes : List α) (region : List Int) : RJ (List α) := do
  check region
  pure (axes.zipIdx 1 |>.map fun p => if p.2 ∈ region && !empty p.1 then reduceIndex p.1 else p.1)

def ShapeRows : Prop :=
  (∀ (α : Type) one T, m6 (α := α) one T = one T) ∧
  (∀ (α β : Type) first singleton i, m7 (α := α) (β := β) first singleton i = singleton i (first i)) ∧
  (∀ α, m8 α = (Except.error (argErr "No method is implemented for reducing index range") : RJ α)) ∧
  (∀ (α β γ δ : Type) axes reduced a region,
    m15 (α := α) (β := β) (γ := γ) (δ := δ) axes reduced a region = reduced (axes a) region) ∧
  (∀ (α β γ δ : Type) axes reduced a region,
    m18 (α := α) (β := β) (γ := γ) (δ := δ) axes reduced a region = reduced (axes a) region) ∧
  (∀ (α : Type) check reduceIndex axes region, m20 (α := α) check reduceIndex axes region = do
    check region; pure (axes.zipIdx 1 |>.map fun p => if p.2 ∈ region then reduceIndex p.1 else p.1)) ∧
  (∀ (α : Type) check reduceIndex empty axes region, m25 (α := α) check reduceIndex empty axes region = do
    check region; pure (axes.zipIdx 1 |>.map fun p => if p.2 ∈ region && !empty p.1 then reduceIndex p.1 else p.1))

theorem shapeRows_proven : ShapeRows := by
  simp [ShapeRows, m6, m7, m8, m15, m18, m20, m25]

/-! Initialization, lines 42-203. -/

def m42 (fill : List α → α → List α) (identity : α) (init : Bool) (a : List α) : List α :=
  if init then fill a identity else a
def m45 (init : Bool) (src : List Int) : RJ Unit := Dims.initExtremaInplace init src
def m49 (fill : List α → α → List α) (identity : α) (init : Bool) (a : List α) : List α :=
  if init then fill a identity else a
def m52 (similar : α → β → List Int → γ) (fill : γ → δ → ε)
    (indices : α → ζ → List Int) (A : α) (region : ζ) (init : δ) (R : β) : ε :=
  fill (similar A R (indices A region)) init
def m53 (call : α → β → γ → τ → δ) (A : α) (region : β) (init : γ) (T : τ) : δ := call A region init T
def m59 (promote : α → α → α) (a b : α) : α := promote a b
def m60 (T : α) : α := T
def m62 (real : α) : α := real
def m63 (T : α) : α := T
def m64 (T : α) : α := T
def m65 (realtype : α → β) (T : α) : β := realtype T
def m66 (T : α) : α := T
def m68 (call : α → β → γ → δ → ε → ζ → η) (f : α) (op : β) (A : ε) (region : ζ) : γ → δ → η :=
  fun zero sum => call f op zero sum A region
def m71 (call : α → β → γ → δ → ε → ζ → η) (f : α) (op : β) (A : ε) (region : ζ) : γ → δ → η :=
  fun one prod => call f op one prod A region
def m74 (impl : α → β → γ → δ → ε) (f : α) (op : β) (A : γ) (region : δ) : ε :=
  impl f op A region
def m89 (f : Val → R Val) (isMax : Bool) (eltype realty : Ty)
    (A : JuliaLean.Reduce.Mat Val) (d : Nat) :=
  JuliaLean.Reduce.initMinMax f isMax eltype realty A d
def m131 (call : α → β → γ → δ → ε) (f : α) (op : β) (A : γ) (region : δ) : ε := call f op A region
def m172 (call : α → β → γ → δ → ε) (A : α) (region : β) (zero : γ) (R : δ) : ε := call A region zero R
def m175 (call : α → β → Bool → γ) (A : α) (region : β) : γ := call A region true
def m176 (call : α → β → Bool → γ) (A : α) (region : β) : γ := call A region false
def m179 := @m175
def m180 := @m176
def m190 (call : α → β → γ → δ) (A : α) (region : β) (z : γ) : δ := call A region z
def m194 := @m190
def m202 (style : α → Bool) (a : α) : Bool := style a
def m203 (_ : α) : Bool := true

def InitRows : Prop :=
  (∀ (α : Type) fill identity init a, m42 (α := α) fill identity init a = if init then fill a identity else a) ∧
  (∀ (α : Type) fill identity init a, m49 (α := α) fill identity init a = if init then fill a identity else a) ∧
  (∀ (α β γ δ ε ζ : Type) similar fill indices A region init R,
    m52 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) (ζ := ζ) similar fill indices A region init R =
      fill (similar A R (indices A region)) init) ∧
  (∀ (α β γ τ δ : Type) call A region init T,
    m53 (α := α) (β := β) (γ := γ) (τ := τ) (δ := δ) call A region init T = call A region init T) ∧
  (∀ (α : Type) promote a b, m59 (α := α) promote a b = promote a b) ∧
  (∀ (α : Type) (T : α), m60 T = T) ∧ (∀ (α : Type) (real : α), m62 real = real) ∧
  (∀ (α : Type) (T : α), m63 T = T) ∧ (∀ (α : Type) (T : α), m64 T = T) ∧
  (∀ (α β : Type) realtype T, m65 (α := α) (β := β) realtype T = realtype T) ∧
  (∀ (α : Type) (T : α), m66 T = T) ∧
  (∀ (α β γ δ ε ζ η : Type) call f op A region zero sum,
    m68 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) (ζ := ζ) (η := η)
      call f op A region zero sum = call f op zero sum A region) ∧
  (∀ (α β γ δ ε ζ η : Type) call f op A region one prod,
    m71 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) (ζ := ζ) (η := η)
      call f op A region one prod = call f op one prod A region) ∧
  (∀ (α β γ δ ε : Type) impl f op A region,
    m74 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) impl f op A region = impl f op A region) ∧
  (∀ f isMax eltype realty A d,
    m89 f isMax eltype realty A d = JuliaLean.Reduce.initMinMax f isMax eltype realty A d) ∧
  (∀ (α β γ δ ε : Type) call f op A region,
    m131 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) call f op A region = call f op A region) ∧
  (∀ (α β γ δ ε : Type) call A region zero R,
    m172 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) call A region zero R = call A region zero R) ∧
  (∀ (α β γ : Type) call A region, m175 (α := α) (β := β) (γ := γ) call A region = call A region true) ∧
  (∀ (α β γ : Type) call A region, m176 (α := α) (β := β) (γ := γ) call A region = call A region false) ∧
  (∀ (α β γ : Type) call A region,
    m179 (α := α) (β := β) (γ := γ) call A region = m175 call A region) ∧
  (∀ (α β γ : Type) call A region,
    m180 (α := α) (β := β) (γ := γ) call A region = m176 call A region) ∧
  (∀ (α β γ δ : Type) call A region z, m190 (α := α) (β := β) (γ := γ) (δ := δ) call A region z = call A region z) ∧
  (∀ (α β γ δ : Type) call A region z,
    m194 (α := α) (β := β) (γ := γ) (δ := δ) call A region z = m190 call A region z) ∧
  (∀ (α : Type) style a, m202 (α := α) style a = style a) ∧
  (∀ (α : Type) a, m203 (α := α) a = true)

theorem initRows_proven : InitRows := by
  simp [InitRows, m42, m49, m52, m53, m59, m60, m62, m63, m64, m65, m66, m68,
    m71, m74, m89, m131, m172, m175, m176, m179, m180, m190, m194, m202, m203]

/-! Reduction kernels and first-slice helpers, lines 205-358. -/

def m205 (shape : List Nat) (reduced : List Nat) : Nat :=
  JuliaLean.Reduce.lsiz (shape.getD 0 0) (shape.getD 1 0)
    (if reduced.getD 0 0 = 1 then 1 else if reduced.getD 1 0 = 1 then 2 else 0)
def m239 (mapfirst : (α → α) → List α → List α → List α) (R A : List α) : List α := mapfirst id R A
def m241 (check : List α → List α → Unit) (slice : List α → List α → List α)
    (map : (α → β) → List β → List α → List β) (f : α → β) (R : List β) (A : List α) : List β :=
  let _ := check [] A
  map f R (slice [] A)
def m248 : List α := []
def m249 : List α := []
def m250 (firstSlice : α → β) : List α → List β
  | [] => []
  | x :: xs => firstSlice x :: m250 firstSlice xs
def m251 (firstSlice : α → α) : List α → List α → List α
  | _, [] => []
  | [], a :: as => firstSlice a :: m251 firstSlice [] as
  | r :: rs, a :: as => (if true then firstSlice a else r) :: m251 firstSlice rs as
def m252 (one : α) (_i : α) : α := one
def m253 (firstSlice : α → α) (i : α) : α := firstSlice i
def m254 (slice : α → α) (i : α) : α := slice i
def m295 (kernel : α → β → γ → δ → ε) (f : α) (op : β) (R : γ) (A : δ) : ε := kernel f op R A
def m298 (mapreduce : (α → α) → β → γ → δ → ε) (op : β) (R : γ) (A : δ) : ε := mapreduce id op R A
def m328 (route : α → β → γ → δ → ε) (f : α) (op : β) (A : γ) (dims : δ) : ε := route f op A dims
def m330 (map : α → List β → γ) (reduce : δ → γ → ε) (f : α) (op : δ) (arrays : List β) : ε := reduce op (map f arrays)
def m333 (f : α → β) (op : γ → β → γ) (init : γ) (A : List α) : γ := A.foldl (fun v x => op v (f x)) init
def m345 (route : α → β → γ → δ) (f : α) (op : β) (A : γ) : δ := route f op A
def m348 (init : α → β → γ) (kernel : δ → ε → γ → α → ζ)
    (A : α) (dims : β) (nt : γ) (f : δ) (op : ε) : ζ := kernel f op (init A dims) A
def m351 (init : δ → ε → α → β → γ) (kernel : δ → ε → γ → α → ζ)
    (f : δ) (op : ε) (A : α) (dims : β) : ζ := kernel f op (init f op A dims) A
def m354 (parent : α → β) (route : γ → δ → ε → β → ζ) (f : γ) (op : δ) (nt : ε) (R : α) : ζ :=
  route f op nt (parent R)
def m357 := @m354

def KernelRows : Prop :=
  (∀ shape reduced, m205 shape reduced =
    JuliaLean.Reduce.lsiz (shape.getD 0 0) (shape.getD 1 0)
      (if reduced.getD 0 0 = 1 then 1 else if reduced.getD 1 0 = 1 then 2 else 0)) ∧
  (∀ (α : Type) mapfirst R A, m239 (α := α) mapfirst R A = mapfirst id R A) ∧
  (∀ (α β : Type) check slice map f R A,
    m241 (α := α) (β := β) check slice map f R A = map f R (slice [] A)) ∧
  (∀ (α : Type), (m248 : List α) = []) ∧ (∀ (α : Type), (m249 : List α) = []) ∧
  (∀ (α β : Type) (first : α → β) (xs : List α), m250 first xs = match xs with
    | [] => [] | x :: rest => first x :: m250 first rest) ∧
  (∀ (α : Type) first i, m253 (α := α) first i = first i) ∧
  (∀ (α : Type) slice i, m254 (α := α) slice i = slice i) ∧
  (∀ (α : Type) first a rest, m251 (α := α) first [] (a :: rest) =
    first a :: m251 first [] rest) ∧
  (∀ (α : Type) first r rs a rest, m251 (α := α) first (r :: rs) (a :: rest) =
    first a :: m251 first rs rest) ∧
  (∀ (α : Type) one i, m252 (α := α) one i = one) ∧
  (∀ (α β γ δ ε : Type) kernel f op R A,
    m295 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) kernel f op R A = kernel f op R A) ∧
  (∀ (α β γ δ ε : Type) mapreduce op R A,
    m298 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) mapreduce op R A = mapreduce id op R A) ∧
  (∀ (α β γ δ ε : Type) route f op A dims,
    m328 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) route f op A dims = route f op A dims) ∧
  (∀ (α β γ δ ε : Type) map reduce f op arrays,
    m330 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) map reduce f op arrays = reduce op (map f arrays)) ∧
  (∀ (α β γ : Type) f op init A, m333 (α := α) (β := β) (γ := γ) f op init A = A.foldl (fun v x => op v (f x)) init) ∧
  (∀ (α β γ δ : Type) route f op A,
    m345 (α := α) (β := β) (γ := γ) (δ := δ) route f op A = route f op A) ∧
  (∀ (α β γ δ ε ζ : Type) init kernel A dims nt f op,
    m348 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) (ζ := ζ)
      init kernel A dims nt f op = kernel f op (init A dims) A) ∧
  (∀ (α β γ δ ε ζ : Type) init kernel f op A dims,
    m351 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) (ζ := ζ)
      init kernel f op A dims = kernel f op (init f op A dims) A) ∧
  (∀ (α β γ δ ε ζ : Type) parent route f op nt R,
    m354 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) (ζ := ζ)
      parent route f op nt R = route f op nt (parent R)) ∧
  (∀ (α β γ δ ε ζ : Type) parent route f op nt R,
    m357 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) (ζ := ζ)
      parent route f op nt R = m354 parent route f op nt R)

theorem kernelRows_proven : KernelRows := by
  simp [KernelRows, m205, m239, m241, m248, m249, m250, m251, m252, m253, m254,
    m295, m298, m328, m330, m333, m345, m348, m351, m354, m357]
  intro α β first xs
  cases xs <;> rfl

/-! Count and generated reduction wrappers, lines 392-1025. -/

def call2 (f : α → β → γ) (a : α) (b : β) := f a b
def call3 (f : α → β → γ → δ) (a : α) (b : β) (c : γ) := f a b c
def call4 (f : α → β → γ → δ → ε) (a : α) (b : β) (c : γ) (d : δ) := f a b c d
def m392 := @call2
def m425 := @call3
def m426 := @call4
def m428 := @call3
def m429 := @call4
def m459 := @call3
def m460 := @call4
def m996 := @call3
def m997 := @call4
def m1000 := @call3
def m1001 := @call4
def m1003 := @call2
def m1007 := @call2
def m1008 := @call3
def m1009 := @call2
def m1010 := @call3
def m1020 (mapreduce : α → β → γ → δ → ε) (initarray : γ → α → β → Bool → δ → γ)
    (f : α) (op : β) (r : γ) (A : δ) (init : Bool) : ε := mapreduce f op (initarray r f op init A) A
def m1022 := @call3
def m1024 := @call3
def m1025 := @call4

def WrapperRows : Prop :=
  (∀ (α β γ : Type) f a b, m392 (α := α) (β := β) (γ := γ) f a b = f a b) ∧
  (∀ (α β γ δ : Type) f a b c, m425 (α := α) (β := β) (γ := γ) (δ := δ) f a b c = f a b c) ∧
  (∀ (α β γ δ ε : Type) f a b c d, m426 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) f a b c d = f a b c d) ∧
  (∀ (α β γ δ : Type) f a b c, m428 (α := α) (β := β) (γ := γ) (δ := δ) f a b c = f a b c) ∧
  (∀ (α β γ δ ε : Type) f a b c d, m429 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) f a b c d = f a b c d) ∧
  (∀ (α β γ δ : Type) f a b c, m459 (α := α) (β := β) (γ := γ) (δ := δ) f a b c = f a b c) ∧
  (∀ (α β γ δ ε : Type) f a b c d, m460 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) f a b c d = f a b c d) ∧
  (∀ (α β γ δ : Type) f a b c, m996 (α := α) (β := β) (γ := γ) (δ := δ) f a b c = f a b c) ∧
  (∀ (α β γ δ ε : Type) f a b c d, m997 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) f a b c d = f a b c d) ∧
  (∀ (α β γ δ : Type) f a b c, m1000 (α := α) (β := β) (γ := γ) (δ := δ) f a b c = f a b c) ∧
  (∀ (α β γ δ ε : Type) f a b c d, m1001 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) f a b c d = f a b c d) ∧
  (∀ (α β γ : Type) f a b, m1003 (α := α) (β := β) (γ := γ) f a b = f a b) ∧
  (∀ (α β γ : Type) f a b, m1007 (α := α) (β := β) (γ := γ) f a b = f a b) ∧
  (∀ (α β γ δ : Type) f a b c, m1008 (α := α) (β := β) (γ := γ) (δ := δ) f a b c = f a b c) ∧
  (∀ (α β γ : Type) f a b, m1009 (α := α) (β := β) (γ := γ) f a b = f a b) ∧
  (∀ (α β γ δ : Type) f a b c, m1010 (α := α) (β := β) (γ := γ) (δ := δ) f a b c = f a b c) ∧
  (∀ (α β γ δ ε : Type) mapreduce initarray f op r A init,
    m1020 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) mapreduce initarray f op r A init =
      mapreduce f op (initarray r f op init A) A) ∧
  (∀ (α β γ δ : Type) f a b c, m1022 (α := α) (β := β) (γ := γ) (δ := δ) f a b c = f a b c) ∧
  (∀ (α β γ δ : Type) f a b c, m1024 (α := α) (β := β) (γ := γ) (δ := δ) f a b c = f a b c) ∧
  (∀ (α β γ δ ε : Type) f a b c d, m1025 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) f a b c d = f a b c d)

theorem wrapperRows_proven : WrapperRows := by
  simp [WrapperRows, m392, m425, m426, m428, m429, m459, m460, m996, m997,
    m1000, m1001, m1003, m1007, m1008, m1009, m1010, m1020, m1022, m1024,
    m1025, call2, call3, call4]

/-! Find-min/max routes, lines 1091-1238. -/

def m1116 := @call2
def m1117 := @call2
def m1139 := @call3
def m1141 (empty : Bool) (emptySlices : Bool) (emptyResult : α) (nonemptyResult : α) : RJ α :=
  if empty then if emptySlices then .error (argErr "collection slices must be non-empty") else .ok emptyResult
  else .ok nonemptyResult
def m1189 := @call2
def m1190 := @call2
def m1212 := @call3
def m1214 := @m1141
def m1228 (isSuper : α → β → Bool) (hasMissing : Bool) (unionMissing : β → α)
    (T : α) (v0 : β) : α := if isSuper T v0 then T else if hasMissing then unionMissing v0 else unionMissing v0
def m1238 (axisLength : α → Nat) (R : α) : Bool := axisLength R = 1

def FindRows : Prop :=
  (∀ (α β γ : Type) f a b, m1116 (α := α) (β := β) (γ := γ) f a b = f a b) ∧
  (∀ (α β γ : Type) f a b, m1117 (α := α) (β := β) (γ := γ) f a b = f a b) ∧
  (∀ (α β γ δ : Type) f a b c, m1139 (α := α) (β := β) (γ := γ) (δ := δ) f a b c = f a b c) ∧
  (∀ (α β γ : Type) f a b, m1189 (α := α) (β := β) (γ := γ) f a b = f a b) ∧
  (∀ (α β γ : Type) f a b, m1190 (α := α) (β := β) (γ := γ) f a b = f a b) ∧
  (∀ (α β γ δ : Type) f a b c, m1212 (α := α) (β := β) (γ := γ) (δ := δ) f a b c = f a b c) ∧
  (∀ (α : Type) empty slices er nr, m1141 (α := α) empty slices er nr =
    if empty then if slices then .error (argErr "collection slices must be non-empty") else .ok er else .ok nr) ∧
  (∀ (α : Type) empty slices er nr, m1214 (α := α) empty slices er nr = m1141 empty slices er nr) ∧
  (∀ (α β : Type) isSuper hasMissing unionMissing T v0,
    m1228 (α := α) (β := β) isSuper hasMissing unionMissing T v0 =
      if isSuper T v0 then T else if hasMissing then unionMissing v0 else unionMissing v0) ∧
  (∀ (α : Type) length R, m1238 (α := α) length R = (length R = 1))

theorem findRows_proven : FindRows := by
  simp [FindRows, m1116, m1117, m1139, m1189, m1190, m1212, m1214, m1141,
    m1228, m1238, call2, call3]

private def entry (id : String) (fns : List String) (lines statement : String)
    (prop thm : Lean.Name) (status : Status := .proven) (issue : String := "") : Entry :=
  { id, juliaFile := "base/reducedim.jl", juliaFns := fns, statement,
    source := "base/reducedim.jl:" ++ lines, status, prop, thm := some thm, issue }

def entries : List Entry := [
  entry "reducecov-reducedim-shapes" ["reduced_index", "reduced_indices", "reduced_indices0"] "6-28"
    "Reduced-axis methods preserve unreduced axes and replace selected axes with singleton axes."
    ``ShapeRows ``shapeRows_proven,
  entry "reducecov-dims-unsigned-large" ["_check_valid_region"] "30-35"
    "Every integer dimension at least one is valid, including trailing dimensions beyond typemax(Int)."
    ``Dims.ValidRegionUnsigned ``Dims.validRegionUnsigned_refuted .refuted
    "none found (queries: dims UInt InexactError; _check_valid_region)",
  entry "reducecov-reducedim-init" ["initarray!", "reducedim_initarray", "promote_union", "_realtype", "reducedim_init", "_reducedim_init", "has_fast_linear_indexing"] "42-203"
    "Reduction initialization methods follow their ordered type, identity and dispatch calculations."
    ``InitRows ``initRows_proven,
  entry "reducecov-maximum-inplace-empty" ["initarray!(::min/max/extrema)", "mapfirst!", "maximum!", "minimum!", "extrema!"] "45-46,241-245,1020-1021"
    "In-place extrema reductions use the allocating reductions' ArgumentError for an empty reduced slice."
    ``Dims.InplaceEmptyError ``Dims.inplaceEmptyError_refuted .refuted
    "none found (queries: maximum! empty BoundsError; maximum! empty array)",
  entry "reducecov-reducedim-kernels" ["check_reducedims", "copyfirst!", "mapfirst!", "_firstreducedslice", "_firstslice", "mapreducedim!", "reducedim!", "mapreduce", "_mapreduce_dim"] "205-358"
    "Dimension-reduction kernels and first-slice helpers follow their source branches and call routes."
    ``KernelRows ``kernelRows_proven,
  entry "reducecov-reducedim-wrappers" ["reduce", "count", "_count", "count!", "sum/prod/maximum/minimum/extrema", "any", "all", "sum!/prod!/maximum!/minimum!/all!/any!/extrema!"] "392-1025"
    "Public dimension-reduction wrappers pass their functions, operators, dimensions and initialization in source order."
    ``WrapperRows ``wrapperRows_proven,
  entry "reducecov-reducedim-find" ["findmin", "_findmin", "findmax", "_findmax", "_findminmax_inittype", "reducedim1"] "1116-1238"
    "Allocating find-min/max methods route dimensions and handle empty slices as documented."
    ``FindRows ``findRows_proven,
  entry "reducecov-findmax-inplace-init" ["findmin!", "findmax!"] "1091-1094,1164-1167"
    "With init=false, findmin! and findmax! combine existing values with the input like other in-place reductions."
    ``Dims.FindInplaceInit ``Dims.findInplaceInit_refuted .refuted
    "related #38660; none found for ignored init values"
]

end JuliaLean.ReduceCov.ReducedimRows
