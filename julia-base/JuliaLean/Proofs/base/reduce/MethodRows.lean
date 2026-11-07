import JuliaLean.base.reduce
import JuliaLean.Proofs.base.accumulate.ReductionClaims
import JuliaLean.Proofs.base.reduce.number
import JuliaLean.Registry.Types

/-! Method-specific models for `base/reduce.jl` on master `bbfa0ce4150`. -/

namespace JuliaLean.ReduceCov.ReduceRows

open JuliaLean.Registry
open JuliaLean.Reduce

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

def entries : List Entry := []

end JuliaLean.ReduceCov.ReduceRows
