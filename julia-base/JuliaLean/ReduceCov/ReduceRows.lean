import JuliaLean.Reduce
import JuliaLean.ReduceCov.Fold
import JuliaLean.Registry.Types

/-! Method-specific models for `base/reduce.jl` on master `bbfa0ce4150`. -/

namespace JuliaLean.ReduceCov.ReduceRows

open JuliaLean.Registry
open JuliaLean.Reduce

/-! Arithmetic reduction operators, lines 16-36. -/

def m16 (add : α → β → γ) (x : α) (y : β) : γ := add x y
def m17 (toInt : α → JInt .i64) (x y : α) : JInt .i64 := toInt x + toInt y
def m18 (toUInt : α → JInt .u64) (x y : α) : JInt .u64 := toUInt x + toUInt y
def m19 (add : α → α → α) (x y : α) : α := add x y
def m27 (mul : α → β → γ) (x : α) (y : β) : γ := mul x y
def m28 (toInt : α → JInt .i64) (x y : α) : JInt .i64 := toInt x * toInt y
def m29 (toUInt : α → JInt .u64) (x y : α) : JInt .u64 := toUInt x * toUInt y
def m30 (mul : α → α → α) (x y : α) : α := mul x y
def m32 (x y : Val) : R Val := Val.andAll x y
def m33 (x y : Val) : R Val := Val.orAny x y
def m35 (x y : Bool) : Bool := x && y
def m36 (x y : Bool) : Bool := x || y

def ArithmeticRows : Prop :=
  (∀ (α β γ : Type) add (x : α) (y : β), m16 (γ := γ) add x y = add x y) ∧
  (∀ (α : Type) toInt (x y : α), m17 toInt x y = toInt x + toInt y) ∧
  (∀ (α : Type) toUInt (x y : α), m18 toUInt x y = toUInt x + toUInt y) ∧
  (∀ (α : Type) add (x y : α), m19 add x y = add x y) ∧
  (∀ (α β γ : Type) mul (x : α) (y : β), m27 (γ := γ) mul x y = mul x y) ∧
  (∀ (α : Type) toInt (x y : α), m28 toInt x y = toInt x * toInt y) ∧
  (∀ (α : Type) toUInt (x y : α), m29 toUInt x y = toUInt x * toUInt y) ∧
  (∀ (α : Type) mul (x y : α), m30 mul x y = mul x y) ∧
  (∀ x y, m32 x y = Val.andAll x y) ∧ (∀ x y, m33 x y = Val.orAny x y) ∧
  (∀ x y, m35 x y = (x && y)) ∧ (∀ x y, m36 x y = (x || y))

theorem arithmeticRows_proven : ArithmeticRows := by
  simp [ArithmeticRows, m16, m17, m18, m19, m27, m28, m29, m30, m32, m33, m35, m36]

/-! Left folds and transducer wrappers, lines 40-164. -/

def m40 {α β γ δ : Type} (xf : (α → β → β) → List γ → ((α → β → β) × List γ))
    (fold : (α → β → β) → α → List γ → δ) (fop : α → β → β) (init : α) (itr : List γ) : δ :=
  let pair := xf fop itr
  fold pair.1 init pair.2

def m45 (core : α → List β → Option γ) (empty : List β → γ) (op : α) (itr : List β) : γ :=
  match core op itr with | none => empty itr | some value => value

def m51 (op : α → β → α) (init : α) (itr : List β) : α :=
  itr.foldl op init

def m65 (afoldl fallback : (α → β → α) → α → List β → α)
    (op : α → β → α) (init : α) (itr : List β) : α :=
  if itr.length ≤ 32 then afoldl op init itr else fallback op init itr

def m83 (first : (α → α → α) → α → α) (op : α → α → α) (x : α) : α := first op x
def m84 (op : α → α → α) (acc x : α) : α := op acc x

structure Mapping (α β γ : Type) where
  f : α → β
  rf : γ → β → γ

def m94 (f : α → β) (rf : γ → β → γ) : Mapping α β γ := ⟨f, rf⟩
def m95 (f : α → β) (rf : γ → β → γ) : Mapping α β γ := ⟨f, rf⟩
def m98 (op : Mapping α β γ) (acc : γ) (x : α) : γ := op.rf acc (op.f x)
def m110 (pred : β → Bool) (rf : α → β → α) (acc : α) (x : β) : α :=
  if pred x then rf acc x else acc
def m122 {α β : Type} (xf : (α → β → α) → List β → ((α → β → α) × List β))
    (rf : α → β → α) (acc : α) (x : List β) : α :=
  let pair := xf rf x
  m51 pair.1 acc pair.2

def m146 {α β γ δ : Type} (unwrap : α → β × (γ → δ)) (op : γ) (itr : α) : δ × β :=
  let pair := unwrap itr
  (pair.2 op, pair.1)
def m151 {α β : Type} (itr : α) : α × (β → β) := (itr, id)
def m152 {α β γ δ ε ζ : Type} (unwrap : α → β × (γ → δ)) (f : ε → ζ) (isIdentity : Bool) (itr : α) : β × (γ → δ) :=
  let pair := unwrap itr
  if isIdentity then pair else (pair.1, pair.2)
def m157 {α β γ δ : Type} (unwrap : α → β × (γ → δ)) (itr : α) : β × (γ → δ) := unwrap itr
def m161 {α β γ δ : Type} (unwrap : α → β × (γ → δ)) (itr : α) : β × (γ → δ) := unwrap itr

def FoldRows : Prop :=
  (∀ (α β γ δ : Type) xf fold fop init itr,
    m40 (α := α) (β := β) (γ := γ) (δ := δ) xf fold fop init itr =
      let pair := xf fop itr; fold pair.1 init pair.2) ∧
  (∀ (α β γ : Type) core empty op itr,
    m45 (α := α) (β := β) (γ := γ) core empty op itr =
      match core op itr with | none => empty itr | some value => value) ∧
  (∀ (α β : Type) op init itr, m51 (α := α) (β := β) op init itr = itr.foldl op init) ∧
  (∀ (α β : Type) afoldl fallback op init itr,
    m65 (α := α) (β := β) afoldl fallback op init itr =
      if itr.length ≤ 32 then afoldl op init itr else fallback op init itr) ∧
  (∀ (α : Type) first op x, m83 (α := α) first op x = first op x) ∧
  (∀ (α : Type) op acc x, m84 (α := α) op acc x = op acc x) ∧
  (∀ (α β γ : Type) f rf, m94 (α := α) (β := β) (γ := γ) f rf = ⟨f, rf⟩) ∧
  (∀ (α β γ : Type) f rf, m95 (α := α) (β := β) (γ := γ) f rf = ⟨f, rf⟩) ∧
  (∀ (α β γ : Type) op acc x, m98 (α := α) (β := β) (γ := γ) op acc x = op.rf acc (op.f x)) ∧
  (∀ (α β : Type) pred rf acc x, m110 (α := α) (β := β) pred rf acc x = if pred x then rf acc x else acc) ∧
  (∀ (α β : Type) xf rf acc x, m122 (α := α) (β := β) xf rf acc x =
    let pair := xf rf x; m51 pair.1 acc pair.2) ∧
  (∀ (α β γ δ : Type) unwrap op itr, m146 (α := α) (β := β) (γ := γ) (δ := δ) unwrap op itr =
    let pair := unwrap itr; (pair.2 op, pair.1)) ∧
  (∀ (α β : Type) itr, m151 (α := α) (β := β) itr = (itr, id)) ∧
  (∀ (α β γ δ ε ζ : Type) unwrap f identity itr,
    m152 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) (ζ := ζ) unwrap f identity itr =
      let pair := unwrap itr; if identity then pair else (pair.1, pair.2)) ∧
  (∀ (α β γ δ : Type) unwrap itr, m157 (α := α) (β := β) (γ := γ) (δ := δ) unwrap itr = unwrap itr) ∧
  (∀ (α β γ δ : Type) unwrap itr, m161 (α := α) (β := β) (γ := γ) (δ := δ) unwrap itr = unwrap itr)

theorem foldRows_proven : FoldRows := by
  simp [FoldRows, m40, m45, m51, m65, m83, m84, m94, m95, m98, m110, m122,
    m146, m151, m152, m157, m161]
  intro α β γ core empty op itr
  cases core op itr <;> rfl

/-! Right-fold routes, lines 200-213. -/

def m200 (xf : (α → α → α) → List β → ((α → α → α) × List β))
    (fold : (α → α → α) → α → List β → γ) (fop : α → α → α)
    (init : α) (itr : List β) : γ := let pair := xf fop itr; fold pair.1 init pair.2
def m206 (reverse : α → β) (itr : α) : β := reverse itr
def m207 (fast slow : List α → List α) (itr : List α) : List α :=
  if itr.length ≤ 32 then fast itr else slow itr
def m213 (f : α → β → γ) (x : β) (y : α) : γ := f y x

def RightFoldRows : Prop :=
  (∀ (α β γ : Type) xf fold fop init itr,
    m200 (α := α) (β := β) (γ := γ) xf fold fop init itr =
      let pair := xf fop itr; fold pair.1 init pair.2) ∧
  (∀ (α β : Type) reverse itr, m206 (α := α) (β := β) reverse itr = reverse itr) ∧
  (∀ (α : Type) fast slow itr, m207 (α := α) fast slow itr =
    if itr.length ≤ 32 then fast itr else slow itr) ∧
  (∀ (α β γ : Type) f x y, m213 (α := α) (β := β) (γ := γ) f x y = f y x)

theorem rightFoldRows_proven : RightFoldRows := by
  simp [RightFoldRows, m200, m206, m207, m213]

/-! Pairwise mapreduce and call routes, lines 252-314, 432-461. -/

def m252 (f : α → β) (op : β → β → β) (first : α → β) (blk : Nat)
    (a : α) (rest : List α) : β := mrImpl f op first blk a rest
def m276 (pairwise : (α → β) → (β → β → β) → Nat) (f : α → β)
    (op : β → β → β) (first : α → β) (a : α) (rest : List α) : β :=
  m252 f op first (pairwise f op) a rest
def m306 (mapfoldl : (α → β) → (β → β → β) → List α → γ)
    (f : α → β) (op : β → β → β) (itr : List α) : γ := mapfoldl f op itr
def m307 (generator : (α → β) → List α → List β) (reduce : (β → β → β) → List β → γ)
    (f : α → β) (op : β → β → β) (itr : List α) : γ := reduce op (generator f itr)
def m311 (_f : α) (_op : β) : Nat := 1024
def m314 (_f : α) (_op : β) : Nat := 4096
def m432 (first : (β → β → β) → β → γ) (f : α → β) (op : β → β → β) (x : α) : γ :=
  first op (f x)
def m434 (style : List α → β) (route : (α → γ) → (γ → γ → γ) → β → List α → δ)
    (f : α → γ) (op : γ → γ → γ) (A : List α) : δ := route f op (style A) A
def m436 (f : α → β) (op : β → β → β) (first : α → β) (empty : R β)
    (blk : Nat) (A : List α) : R β := mapreduceArr f op first empty blk A
def m459 (first : (α → β) → (β → β → β) → α → γ)
    (f : α → β) (op : β → β → β) (a : α) : γ := first f op a
def m461 (mapfoldl : (α → β) → (β → β → β) → List α → γ)
    (f : α → β) (op : β → β → β) (A : List α) : γ := mapfoldl f op A

def MapreduceRows : Prop :=
  (∀ (α β : Type) f op first blk a rest,
    m252 (α := α) (β := β) f op first blk a rest = mrImpl f op first blk a rest) ∧
  (∀ (α β : Type) pairwise f op first a rest,
    m276 (α := α) (β := β) pairwise f op first a rest = m252 f op first (pairwise f op) a rest) ∧
  (∀ (α β γ : Type) mapfoldl f op itr,
    m306 (α := α) (β := β) (γ := γ) mapfoldl f op itr = mapfoldl f op itr) ∧
  (∀ (α β γ : Type) generator reduce f op itr,
    m307 (α := α) (β := β) (γ := γ) generator reduce f op itr = reduce op (generator f itr)) ∧
  (∀ (α β : Type) f op, m311 (α := α) (β := β) f op = 1024) ∧
  (∀ (α β : Type) f op, m314 (α := α) (β := β) f op = 4096) ∧
  (∀ (α β γ : Type) first f op x, m432 (α := α) (β := β) (γ := γ) first f op x = first op (f x)) ∧
  (∀ (α β γ δ : Type) style route f op A,
    m434 (α := α) (β := β) (γ := γ) (δ := δ) style route f op A = route f op (style A) A) ∧
  (∀ (α β : Type) f op first empty blk A,
    m436 (α := α) (β := β) f op first empty blk A = mapreduceArr f op first empty blk A) ∧
  (∀ (α β γ : Type) first f op a,
    m459 (α := α) (β := β) (γ := γ) first f op a = first f op a) ∧
  (∀ (α β γ : Type) mapfoldl f op A,
    m461 (α := α) (β := β) (γ := γ) mapfoldl f op A = mapfoldl f op A)

theorem mapreduceRows_proven : MapreduceRows := by
  simp [MapreduceRows, m252, m276, m306, m307, m311, m314, m432, m434, m436, m459, m461]

/-! Empty and first-element methods, lines 318-420. -/

def emptyError : R α := .error .argumentError
def m318 (α : Type) : R α := emptyError
def m320 (α : Type) : R α := emptyError
def m321 (α : Type) : R α := emptyError
def m322 (α : Type) : R α := emptyError
def m342 (zero : τ → α) (T : τ) : α := zero T
def m343 : Int := 0
def m344 (one : τ → α) (T : τ) : α := one T
def m345 : String := ""
def m346 : Bool := true
def m347 : Bool := false
def m348 (α : Type) : Bool := true
def m349 (α : Type) : Bool := false
def m351 (emptyPlus : τ → R α) (T : τ) : R α := emptyPlus T
def m352 : Val := Val.i64 0
def m353 : Val := .int .u64 (JInt.lit .u64 0)
def m354 (emptyTimes : τ → R α) (T : τ) : R α := emptyTimes T
def m355 : Val := Val.i64 1
def m356 : Val := .int .u64 (JInt.lit .u64 1)
def m358 (empty : τ → R α) (T : τ) : R α := empty T
def m359 (mappedEmpty : τ → R α) (T : τ) : R α := mappedEmpty T
def m360 (empty : τ → R α) (T : τ) : R α := empty T
def m361 (empty : τ → R α) (T : τ) : R α := empty T
def m370 (empty : τ → R α) (T : τ) : R α := empty T
def m371 (abs : α → β) (empty : τ → R α) (T : τ) : R β := (empty T).map abs
def m372 (abs2 : α → β) (empty : τ → R α) (T : τ) : R β := (empty T).map abs2
def m374 (zero : τ → α) (abs : α → β) (T : τ) : β := abs (zero T)
def m375 (zero : τ → α) (abs2 : α → β) (T : τ) : β := abs2 (zero T)
def m378 (reduceEmpty : α → β → γ → δ) (mapping : ε → α → α)
    (f : ε) (op : α) (itr : β) (style : γ) : δ := reduceEmpty (mapping f op) itr style
def m381 (style : α → β) (route : γ → α → β → δ) (op : γ) (itr : α) : δ := route op itr (style itr)
def m382 (eltype : α → β) (empty : γ → β → δ) (op : γ) (itr : α) : δ := empty op (eltype itr)
def m389 (empty : α → β → γ) (op : α) (T : β) : γ := empty op T
def m391 (α : Type) : R α := .error .argumentError

def m409 (_op : α) (x : β) : β := x
def m410 (x : Bool) : Int := if x then 1 else 0
def m411 (x : Char) : String := String.singleton x
def m413 (firstPlus : α → β) (x : α) : β := firstPlus x
def m414 (x : Val) : Val := Val.firstAddSum x
def m415 (x : Val) : Val := Val.firstAddSum x
def m416 (firstTimes : α → β) (x : α) : β := firstTimes x
def m417 (x : Val) : Val := Val.firstMulProd x
def m418 (x : Val) : Val := Val.firstMulProd x
def m419 (vcat : α → β) (x : α) : β := vcat x
def m420 (hcat : α → β) (x : α) : β := hcat x

def EmptyRows : Prop :=
  (∀ α, m318 α = (emptyError : R α)) ∧ (∀ α, m320 α = (emptyError : R α)) ∧
  (∀ α, m321 α = (emptyError : R α)) ∧ (∀ α, m322 α = (emptyError : R α)) ∧
  (∀ (τ α : Type) (zero : τ → α) (T : τ), m342 zero T = zero T) ∧ m343 = 0 ∧
  (∀ (τ α : Type) (one : τ → α) (T : τ), m344 one T = one T) ∧ m345 = "" ∧
  m346 = true ∧ m347 = false ∧ (∀ α, m348 α = true) ∧ (∀ α, m349 α = false) ∧
  (∀ (τ α : Type) (empty : τ → R α) (T : τ), m351 empty T = empty T) ∧
  m352 = Val.i64 0 ∧ m353 = .int .u64 (JInt.lit .u64 0) ∧
  (∀ (τ α : Type) (empty : τ → R α) (T : τ), m354 empty T = empty T) ∧
  m355 = Val.i64 1 ∧ m356 = .int .u64 (JInt.lit .u64 1) ∧
  (∀ (τ α : Type) (empty : τ → R α) (T : τ), m358 empty T = empty T) ∧
  (∀ (τ α : Type) (empty : τ → R α) (T : τ), m359 empty T = empty T) ∧
  (∀ (τ α : Type) (empty : τ → R α) (T : τ), m360 empty T = empty T) ∧
  (∀ (τ α : Type) (empty : τ → R α) (T : τ), m361 empty T = empty T) ∧
  (∀ (τ α : Type) (empty : τ → R α) (T : τ), m370 empty T = empty T) ∧
  (∀ (τ α β : Type) (abs : α → β) (empty : τ → R α) (T : τ), m371 abs empty T = (empty T).map abs) ∧
  (∀ (τ α β : Type) (abs2 : α → β) (empty : τ → R α) (T : τ), m372 abs2 empty T = (empty T).map abs2) ∧
  (∀ (τ α β : Type) (zero : τ → α) (abs : α → β) (T : τ), m374 zero abs T = abs (zero T)) ∧
  (∀ (τ α β : Type) (zero : τ → α) (abs2 : α → β) (T : τ), m375 zero abs2 T = abs2 (zero T)) ∧
  (∀ (α β γ δ ε : Type) reduceEmpty mapping f op itr style,
    m378 (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε) reduceEmpty mapping f op itr style =
      reduceEmpty (mapping f op) itr style) ∧
  (∀ (α β γ δ : Type) style route op itr,
    m381 (α := α) (β := β) (γ := γ) (δ := δ) style route op itr = route op itr (style itr)) ∧
  (∀ (α β γ δ : Type) eltype empty op itr,
    m382 (α := α) (β := β) (γ := γ) (δ := δ) eltype empty op itr = empty op (eltype itr)) ∧
  (∀ (α β γ : Type) empty op T, m389 (α := α) (β := β) (γ := γ) empty op T = empty op T) ∧
  (∀ α, m391 α = (Except.error .argumentError : R α))

theorem emptyRows_proven : EmptyRows := by
  simp [EmptyRows, emptyError, m318, m320, m321, m322, m342, m343, m344, m345, m346,
    m347, m348, m349, m351, m352, m353, m354, m355, m356, m358, m359, m360,
    m361, m370, m371, m372, m374, m375, m378, m381, m382, m389, m391]

def FirstRows : Prop :=
  (∀ (α β : Type) op (x : β), m409 (α := α) op x = x) ∧
  (∀ x, m410 x = if x then 1 else 0) ∧ (∀ x, m411 x = String.singleton x) ∧
  (∀ (α β : Type) first x, m413 (α := α) (β := β) first x = first x) ∧
  (∀ x, m414 x = Val.firstAddSum x) ∧ (∀ x, m415 x = Val.firstAddSum x) ∧
  (∀ (α β : Type) first x, m416 (α := α) (β := β) first x = first x) ∧
  (∀ x, m417 x = Val.firstMulProd x) ∧ (∀ x, m418 x = Val.firstMulProd x) ∧
  (∀ (α β : Type) vcat x, m419 (α := α) (β := β) vcat x = vcat x) ∧
  (∀ (α β : Type) hcat x, m420 (α := α) (β := β) hcat x = hcat x)

theorem firstRows_proven : FirstRows := by
  simp [FirstRows, m409, m410, m411, m413, m414, m415, m416, m417, m418, m419, m420]

/-! Public reduction wrappers and extrema/search methods. -/

def route2 (call : α → β → γ) (a : α) (b : β) : γ := call a b
def route3 (call : α → β → γ → δ) (a : α) (b : β) (c : γ) : δ := call a b c

def m543 := @route3
def m572 := @route2
def m573 (count reduce : List Bool → α) (hasKw : Bool) (a : List Bool) : α := if hasKw then reduce a else count a
def m599 := @route3
def m628 := @route2
def m656 := @route3
def m683 := @route3
def m715 := @route2
def m747 := @route2
def m776 := @route2
def m806 := @route3

structure ExtremaMap (α β : Type) where f : α → β
def m813 (f : α → β) : ExtremaMap α β := ⟨f⟩
def m814 (f : ExtremaMap α β) (x : α) : β × β := let y := f.f x; (y, y)
def m816 (min max : α → α → α) (a b : α × α) : α × α := (min a.1 b.1, max a.2 b.2)

def m851 (find : (α → β) → List α → γ) (f : α → β) (domain : List α) : γ := find f domain
def m852 (mapfoldl : ((Nat × α) → (β × Nat)) → ((β × Nat) → (β × Nat) → (β × Nat)) →
    List (Nat × α) → γ) (f : α → β) (rf : (β × Nat) → (β × Nat) → (β × Nat))
    (domain : List (Nat × α)) : γ := mapfoldl (fun p => (f p.2, p.1)) rf domain
def m853 (isless : α → α → Bool) (a b : α × β) : α × β := if isless a.1 b.1 then b else a
def m880 (find : List α → α × Nat) (itr : List α) := find itr
def m881 (find : (α → α) → List α → α × Nat) (a : List α) := find id a
def m917 := @m851
def m918 := @m852
def m919 (isgreater : α → α → Bool) (a b : α × β) : α × β := if isgreater a.1 b.1 then b else a
def m946 := @m880
def m947 := @m881
def m973 (mapfoldl : (α → β × α) → ((β × α) → (β × α) → (β × α)) → List α → β × α)
    (f : α → β) (rf : (β × α) → (β × α) → (β × α)) (domain : List α) : α :=
  (mapfoldl (fun x => (f x, x)) rf domain).2
def m1002 (findmax : List α → α × β) (itr : List α) : β := (findmax itr).2
def m1031 := @m973
def m1060 (findmin : List α → α × β) (itr : List α) : β := (findmin itr).2

def PublicRows : Prop :=
  (∀ (α β γ δ : Type) call a b c, m543 (α := α) (β := β) (γ := γ) (δ := δ) call a b c = call a b c) ∧
  (∀ (α β γ : Type) call a b, m572 (α := α) (β := β) (γ := γ) call a b = call a b) ∧
  (∀ (α : Type) count reduce kw a, m573 (α := α) count reduce kw a = if kw then reduce a else count a) ∧
  (∀ (α β γ δ : Type) call a b c, m599 (α := α) (β := β) (γ := γ) (δ := δ) call a b c = call a b c) ∧
  (∀ (α β γ : Type) call a b, m628 (α := α) (β := β) (γ := γ) call a b = call a b) ∧
  (∀ (α β γ δ : Type) call a b c, m656 (α := α) (β := β) (γ := γ) (δ := δ) call a b c = call a b c) ∧
  (∀ (α β γ δ : Type) call a b c, m683 (α := α) (β := β) (γ := γ) (δ := δ) call a b c = call a b c) ∧
  (∀ (α β γ : Type) call a b, m715 (α := α) (β := β) (γ := γ) call a b = call a b) ∧
  (∀ (α β γ : Type) call a b, m747 (α := α) (β := β) (γ := γ) call a b = call a b) ∧
  (∀ (α β γ : Type) call a b, m776 (α := α) (β := β) (γ := γ) call a b = call a b) ∧
  (∀ (α β γ δ : Type) call a b c, m806 (α := α) (β := β) (γ := γ) (δ := δ) call a b c = call a b c) ∧
  (∀ (α β : Type) f, m813 (α := α) (β := β) f = ⟨f⟩) ∧
  (∀ (α β : Type) f x, m814 (α := α) (β := β) f x = let y := f.f x; (y, y)) ∧
  (∀ (α : Type) min max a b, m816 (α := α) min max a b = (min a.1 b.1, max a.2 b.2)) ∧
  (∀ (α β γ : Type) find f domain, m851 (α := α) (β := β) (γ := γ) find f domain = find f domain) ∧
  (∀ (α β γ : Type) mapfoldl f rf domain,
    m852 (α := α) (β := β) (γ := γ) mapfoldl f rf domain =
      mapfoldl (fun p => (f p.2, p.1)) rf domain) ∧
  (∀ (α β : Type) isless (a b : α × β), m853 isless a b = if isless a.1 b.1 then b else a) ∧
  (∀ (α : Type) find itr, m880 (α := α) find itr = find itr) ∧
  (∀ (α : Type) find itr, m881 (α := α) find itr = find id itr) ∧
  (∀ (α β γ : Type) find f domain,
    m917 (α := α) (β := β) (γ := γ) find f domain = m851 find f domain) ∧
  (∀ (α β γ : Type) mapfoldl f rf domain,
    m918 (α := α) (β := β) (γ := γ) mapfoldl f rf domain = m852 mapfoldl f rf domain) ∧
  (∀ (α β : Type) isgreater (a b : α × β), m919 isgreater a b = if isgreater a.1 b.1 then b else a) ∧
  (∀ (α : Type) find itr, m946 (α := α) find itr = m880 find itr) ∧
  (∀ (α : Type) find itr, m947 (α := α) find itr = m881 find itr) ∧
  (∀ (α β : Type) mapfoldl f rf domain,
    m973 (α := α) (β := β) mapfoldl f rf domain = (mapfoldl (fun x => (f x, x)) rf domain).2) ∧
  (∀ (α β : Type) find itr, m1002 (α := α) (β := β) find itr = (find itr).2) ∧
  (∀ (α β : Type) mapfoldl f rf domain,
    m1031 (α := α) (β := β) mapfoldl f rf domain = m973 mapfoldl f rf domain) ∧
  (∀ (α β : Type) find itr, m1060 (α := α) (β := β) find itr = (find itr).2)

theorem publicRows_proven : PublicRows := by
  simp [PublicRows, m543, m572, m573, m599, m628, m656, m683, m715, m747, m776,
    m806, route2, route3, m813, m814, m816, m851, m852, m853, m880, m881, m917,
    m918, m919, m946, m947, m973, m1002, m1031, m1060]

/-! Count methods, lines 1064-1119. -/

def m1064 (f : α → Bool) : α → Bool := fun x => f x
def m1091 (count : (Bool → Bool) → List Bool → β → γ) (init : β) (itr : List Bool) : γ := count id itr init
def m1093 (simple : (α → Bool) → List α → β → γ) (f : α → Bool) (itr : List α) (init : β) : γ := simple f itr init
def m1095 (sum : (α → Bool) → List α → β → γ) (pred : α → Bool) (itr : List α) (init : β) : γ :=
  sum (m1064 pred) itr init
def m1097 (init : Val) (x : List Bool) : R Val := Vec.countBoolArray init x
def m1117 (op : α → β → α) (init : α) (empty : Bool) (aggregate : β) : α :=
  if empty then init else op init aggregate

def CountRows : Prop :=
  (∀ (α : Type) f, m1064 (α := α) f = fun x => f x) ∧
  (∀ (β γ : Type) count init itr,
    m1091 (β := β) (γ := γ) count init itr = count id itr init) ∧
  (∀ (α β γ : Type) simple f itr init,
    m1093 (α := α) (β := β) (γ := γ) simple f itr init = simple f itr init) ∧
  (∀ (α β γ : Type) sum pred itr init,
    m1095 (α := α) (β := β) (γ := γ) sum pred itr init = sum (m1064 pred) itr init) ∧
  (∀ init x, m1097 init x = Vec.countBoolArray init x) ∧
  (∀ (α β : Type) op init empty aggregate,
    m1117 (α := α) (β := β) op init empty aggregate = if empty then init else op init aggregate)

theorem countRows_proven : CountRows := by
  simp [CountRows, m1064, m1091, m1093, m1095, m1097, m1117]
  intro α f
  funext x
  rfl

private def entry (id : String) (fns : List String) (lines statement : String)
    (prop thm : Lean.Name) (status : Status := .proven) (issue : String := "") : Entry :=
  { id, juliaFile := "base/reduce.jl", juliaFns := fns, statement,
    source := "base/reduce.jl:" ++ lines, status, prop, thm := some thm, issue }

def entries : List Entry := [
  entry "reducecov-reduce-arithmetic" ["add_sum", "mul_prod", "and_all", "or_any"] "16-36"
    "Each reduction operator follows its method-specific arithmetic and promotion body."
    ``ArithmeticRows ``arithmeticRows_proven,
  entry "reducecov-reduce-folds" ["mapfoldl_impl", "foldl_impl", "_foldl_impl", "BottomRF", "MappingRF", "FilteringRF", "FlatteningRF", "_xfadjoint", "_xfadjoint_unwrap"] "40-164"
    "Left-fold and transducer methods follow their ordered calls, branches and folds."
    ``FoldRows ``foldRows_proven,
  entry "reducecov-reduce-right-folds" ["mapfoldr_impl", "_reverse_iter", "FlipArgs"] "200-213"
    "Right-fold helpers reverse the iterator and flip the binary arguments as written."
    ``RightFoldRows ``rightFoldRows_proven,
  entry "reducecov-reduce-mapreduce" ["mapreduce_impl", "mapreduce", "pairwise_blocksize", "mapreduce_first", "_mapreduce"] "252-314,432-461"
    "Mapreduce methods follow their pairwise recursion and call-routing bodies."
    ``MapreduceRows ``mapreduceRows_proven,
  entry "reducecov-reduce-empty-methods" ["_empty_reduce_error", "reduce_empty", "mapreduce_empty", "mapreduce_empty_iter", "reduce_empty_iter"] "318-393"
    "Every empty-reduction overload returns its documented identity or ordered error route."
    ``EmptyRows ``emptyRows_proven,
  entry "reducecov-reduce-first-methods" ["reduce_first"] "409-420"
    "Every reduce_first overload follows its method-specific widening or container body."
    ``FirstRows ``firstRows_proven,
  entry "reducecov-reduce-public-methods" ["sum", "prod", "maximum", "minimum", "extrema", "ExtremaMap", "_extrema_rf", "findmax", "_findmax", "_rf_findmax", "findmin", "_findmin", "_rf_findmin", "argmax", "argmin"] "543-1060"
    "Public reduction and extrema-search methods route and compare exactly as their source bodies specify."
    ``PublicRows ``publicRows_proven,
  entry "reducecov-reduce-count" ["_bool", "count", "_simple_count", "_foldl_impl(::BottomRF, ::AbstractRange)"] "1064-1119"
    "Count and specialized range-fold methods follow their method-specific bodies."
    ``CountRows ``countRows_proven,
  entry "reducecov-reduce-number" ["reduce(::Any, ::Number)"] "500"
    "A single Number reduction applies reduce_first just like a one-element iterator."
    ``JuliaLean.ReduceCov.Fold.ReduceNumberFirst ``JuliaLean.ReduceCov.Fold.reduceNumberFirst_refuted .refuted
    "none found (queries: reduce Number reduce_first; reduce plus true)"
]

end JuliaLean.ReduceCov.ReduceRows
