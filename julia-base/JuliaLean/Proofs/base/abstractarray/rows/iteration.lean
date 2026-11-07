import JuliaLean.base.abstractarray
import JuliaLean.Proofs.base.abstractarray.rows.basic


namespace JuliaLean.AbstractArrayCov.Rows.Iteration

open JuliaLean
open JuliaLean.Registry
open JuliaLean.AbstractArrayCov.Rows.Basic

def Property322 : Prop := ∀ (α β : Type) (keys : List α → β) itrs,
  method322 keys itrs = keys itrs
theorem property322 : Property322 := by unfold Property322; intros; rfl

def Property325 : Prop := ∀ (α β : Type) (axes1 : α → β) a,
  method325 axes1 a = axes1 a
theorem property325 : Property325 := by unfold Property325; intros; rfl

def Property329 : Prop := ∀ a b, method329 a b = a ++ " and " ++ b
theorem property329 : Property329 := by unfold Property329; intros; rfl

def Property330 : Prop := ∀ a b rest,
  method330 a b rest = a ++ ", " ++ joinCommaAnd (b :: rest)
theorem property330 : Property330 := by unfold Property330; intros; rfl

def Property331 : Prop := ∀ indices a bs,
  method331 indices a bs = .error ("all inputs to eachindex must have the same " ++
    indices ++ ", got " ++ joinCommaAnd (a :: bs))
theorem property331 : Property331 := by unfold Property331; intros; rfl

def Property384 : Prop := ∀ (α σ β : Type) (style : α → σ) (each : σ → α → β) a,
  method384 style each a = each (style a) a
theorem property384 : Property384 := by unfold Property384; intros; rfl

def Property386 : Prop := ∀ (α β σ γ : Type) (style : α → β → σ)
    (each : σ → α → β → γ) a b,
  method386 style each a b = each (style a b) a b
theorem property386 : Property386 := by unfold Property386; intros; rfl

def Property390 : Prop := ∀ (α σ β : Type) (style : α → List α → σ)
    (each : σ → α → List α → β) a bs,
  method390 style each a bs = each (style a bs) a bs
theorem property390 : Property390 := by unfold Property390; intros; rfl

def Property394 : Prop := ∀ (α β : Type) (length : α → Nat)
    (uncheckedOneTo : Nat → β) a,
  method394 length uncheckedOneTo a = uncheckedOneTo (length a)
theorem property394 : Property394 := by unfold Property394; intros; rfl

def Property395 : Prop := ∀ (α β : Type) (length : α → Nat) (oneto : Nat → β) a,
  method395 length oneto a = oneto (length a)
theorem property395 : Property395 := by unfold Property395; intros; rfl

def Property396 : Prop := ∀ (α β : Type) (axes1 : α → β) a,
  method396 axes1 a = axes1 a
theorem property396 : Property396 := by unfold Property396; intros; rfl

def Property397 : Prop := ∀ (α β : Type) [Repr β] [BEq β]
    (each : α → β) a bs,
  method397 each a bs =
    let ia := each a
    let ibs := bs.map each
    if ibs.all (· == ia) then .ok ia
    else .error ("all inputs to eachindex must have the same indices, got " ++
      joinCommaAnd (toString (repr ia) :: ibs.map (toString ∘ repr)))
theorem property397 : Property397 := by unfold Property397; intros; rfl

def Property407 : Prop := ∀ (σ α β : Type) (eachindex : σ → α → List α → β)
    style a bs,
  method407 eachindex style a bs = eachindex style a bs
theorem property407 : Property407 := by unfold Property407; intros; rfl

def Property429 : Prop := ∀ (α β : Type) (eachindex : α → List β) a,
  method429 eachindex a = listLast (eachindex a)
theorem property429 : Property429 := by unfold Property429; intros; rfl

def Property430 : Prop := ∀ (α β γ : Type) (axes : α → β → List γ) a d,
  method430 axes a d = listLast (axes a d)
theorem property430 : Property430 := by unfold Property430; intros; rfl

def Property452 : Prop := ∀ (α β : Type) (eachindex : α → List β) a,
  method452 eachindex a = listFirst (eachindex a)
theorem property452 : Property452 := by unfold Property452; intros; rfl

def Property453 : Prop := ∀ (α β γ : Type) (axes : α → β → List γ) a d,
  method453 axes a d = listFirst (axes a d)
theorem property453 : Property453 := by unfold Property453; intros; rfl

def Property455 : Prop := ∀ (α β γ : Type) (eachindex : α → List β)
    (getindex : α → β → Jl γ) a,
  method455 eachindex getindex a = do
    let i ← listFirst (eachindex a)
    getindex a i
theorem property455 : Property455 := by unfold Property455; intros; rfl

def Property474 : Prop := ∀ (α β σ : Type) (iterate : α → Option (β × σ)) itr,
  method474 iterate itr = match iterate itr with
    | none => .error (.argumentError "collection must be non-empty")
    | some result => .ok result.1
theorem property474 : Property474 := by
  unfold Property474
  intro α β σ iterate itr
  cases h : iterate itr <;> simp [method474, h]

def Property505 : Prop := ∀ (α β γ : Type) (take : α → Int → β) (collect : β → γ) itr n,
  method505 take collect itr n = collect (take itr n)
theorem property505 : Property505 := by unfold Property505; intros; rfl

def Property507 : Prop := ∀ (α β γ : Type) (checkedLength : α → Jl Int)
    (range : Int → β) (getindex : α → β → Jl γ) v n,
  method507 checkedLength range getindex v n = do
    if n < 0 then throw (.argumentError "Number of elements must be non-negative")
    let len ← checkedLength v
    getindex v (range (min n len))
theorem property507 : Property507 := by unfold Property507; intros; rfl

def Property530 : Prop := ∀ (α β γ : Type) (lastindex : α → β)
    (getindex : α → β → γ) a,
  method530 lastindex getindex a = getindex a (lastindex a)
theorem property530 : Property530 := by unfold Property530; intros; rfl

def Property555 : Prop := ∀ (α β γ δ ε : Type) (reverse : α → β)
    (take : β → Int → γ) (collect : γ → δ) (reverseBang : δ → ε) itr n,
  method555 reverse take collect reverseBang itr n =
    reverseBang (collect (take (reverse itr) n))
theorem property555 : Property555 := by unfold Property555; intros; rfl

def Property557 : Prop := ∀ (α β γ : Type) (checkedLength : α → Jl Int)
    (lastindex : α → Int) (range : Int → Int → β) (getindex : α → β → Jl γ) v n,
  method557 checkedLength lastindex range getindex v n = do
    if n < 0 then throw (.argumentError "Number of elements must be non-negative")
    let len ← checkedLength v
    getindex v (range (lastindex v) (min n len))
theorem property557 : Property557 := by unfold Property557; intros; rfl

def Property597 : Prop := ∀ (α : Type) (strides size : α → List I64)
    (ndims : α → Nat) a k,
  method597 strides size ndims a k = do
    let st := strides a
    if k ≤ ndims a then tupleGet st (← JInt.convert (IntTy.i64.name) .i64 k)
    else if ndims a = 0 then .ok (i64 1)
    else do
      let sz := size a
      let firstSt ← tupleGet st (i64 1)
      let firstSz ← tupleGet sz (i64 1)
      .ok (strideTail ((st.drop 1).zip (sz.drop 1)) (firstSt * firstSz))
theorem property597 : Property597 := by unfold Property597; intros; rfl

def Property609 : Prop := ∀ s d rest,
  method609 s d rest = s :: sizeToStrides (s * d) rest
theorem property609 : Property609 := by unfold Property609; intros; rfl

def Property610 : Prop := ∀ s d, method610 s d = [s]
theorem property610 : Property610 := by unfold Property610; intros; rfl

def Property611 : Prop := ∀ s, method611 s = []
theorem property611 : Property611 := by unfold Property611; intros; rfl

def Property613 : Prop := ∀ (α : Type) (checkbounds : α → List Int → Jl Unit) a indices,
  method613 checkbounds a indices = do checkbounds a indices; return true
theorem property613 : Property613 := by unfold Property613; intros; rfl

def Property619 : Prop := ∀ (α : Type) (ndims : α → Int)
    (size : α → Int → Jl I64) a n,
  method619 ndims size a n = do
    let mut s := i64 1
    for i in intRange n (ndims a) do s := s * (← size a i)
    return s
theorem property619 : Property619 := by unfold Property619; intros; rfl

def Property626 : Prop := ∀ (α : Type) (length : α → I64) inds n,
  method626 length inds n = do
    let mut s := i64 1
    for i in intRange n inds.length do
      let axis ← tupleGet inds (← JInt.convert (IntTy.i64.name) .i64 i)
      s := s * length axis
    return s
theorem property626 : Property626 := by unfold Property626; intros; rfl

def Property634 : Prop := ∀ (α : Type) (length : α → I64) inds,
  method634 length inds = (inds.map length).foldl (· * ·) (i64 1)
theorem property634 : Property634 := by unfold Property634; intros; rfl

private def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/abstractarray.jl", juliaFns := [fn], statement, source,
    status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.AbstractArrayCov.Rows.Iteration
