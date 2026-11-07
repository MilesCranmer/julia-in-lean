import JuliaLean.base.abstractarray
import JuliaLean.Proofs.base.abstractarray.rows.copy


namespace JuliaLean.AbstractArrayCov.Rows.Index

open JuliaLean
open JuliaLean.Registry

def Property1279 : Prop := ∀ (α β γ : Type) (cconvert : α → β)
    (unsafeConvert : β → γ) x,
  method1279 cconvert unsafeConvert x = unsafeConvert (cconvert x)
theorem property1279 : Property1279 := by unfold Property1279; intros; rfl

def Property1280 : Prop := ∀ (α : Type) (pointer : α → I64)
    (offset : α → Int → Int) x i,
  method1280 pointer offset x i = do
    let off ← JInt.convert (IntTy.i64.name) .i64 (offset x i)
    return pointer x + off
theorem property1280 : Property1280 := by unfold Property1280; intros; rfl

def Property1286 : Prop := ∀ (α β : Type) (linear : α → List β → I64)
    (firstLinear : α → I64) (elsize : α → I64) x indices,
  method1286 linear firstLinear elsize x indices =
    (linear x indices - firstLinear x) * elsize x
theorem property1286 : Property1286 := by unfold Property1286; intros; rfl

def Property1287 : Prop := ∀ (α β : Type) (subscripts : α → List β → List I64)
    (strides origins : α → List I64) (elsize : α → I64) x indices,
  method1287 subscripts strides origins elsize x indices =
    let js := subscripts x indices
    ((offsetTerms js (strides x) (origins x)).foldl (· + ·) (i64 0)) * elsize x
theorem property1287 : Property1287 := by unfold Property1287; intros; rfl

def Property1363 : Prop := ∀ (α σ ι κ β : Type) (style : α → σ)
    (canonical : σ → α → List ι → Jl Unit) (toIndices : α → List ι → Jl (List κ))
    (get : σ → α → List κ → Jl β) a indices,
  method1363 style canonical toIndices get a indices = do
    canonical (style a) a indices
    let js ← toIndices a indices
    get (style a) a js
theorem property1363 : Property1363 := by unfold Property1363; intros; rfl

def Property1369 : Prop := ∀ (α ι κ β : Type) (toIndices : α → List ι → Jl (List κ))
    (get : α → List κ → Jl β) a indices,
  method1369 toIndices get a indices = do get a (← toIndices a indices)
theorem property1369 : Property1369 := by unfold Property1369; intros; rfl

def Property1371 : Prop := ∀ (α ι β : Type) (getindex : α → List ι → β) a indices,
  method1371 getindex a indices = getindex a indices
theorem property1371 : Property1371 := by unfold Property1371; intros; rfl

def Property1376 : Prop := ∀ func typeName,
  method1376 func typeName = ⟨func, typeName⟩
theorem property1376 : Property1376 := by unfold Property1376; intros; rfl

def Property1379 : Prop := ∀ typeName, method1379 typeName = .error ⟨"getindex", typeName⟩
theorem property1379 : Property1379 := by unfold Property1379; intros; rfl

def Property1381 : Prop := ∀ typeName, method1381 typeName = .error ⟨"getindex", typeName⟩
theorem property1381 : Property1381 := by unfold Property1381; intros; rfl

def Property1383 : Prop := ∀ _args : Unit, method1383 = ()
theorem property1383 : Property1383 := by unfold Property1383; intros; rfl

def Property1386 : Prop := ∀ (β : Type) arrayType indexTypes,
  (method1386 arrayType indexTypes : Except String β) =
    .error ("getindex for " ++ arrayType ++ " with types " ++ indexTypes ++ " is not supported")
theorem property1386 : Property1386 := by unfold Property1386; intros; rfl

def Property1390 : Prop := ∀ (α β : Type) (getindex : α → Int → β) a i,
  method1390 getindex a i = getindex a i
theorem property1390 : Property1390 := by unfold Property1390; intros; rfl

def Property1391 : Prop := ∀ (α β : Type) (getindex : α → Int → β) a i,
  method1391 getindex a i = getindex a i
theorem property1391 : Property1391 := by unfold Property1391; intros; rfl

def Property1392 : Prop := ∀ (α β : Type) (checkbounds : α → List Int → Jl Unit)
    (linear : α → List Int → Int) (getindex : α → Int → Jl β) a indices,
  method1392 checkbounds linear getindex a indices = do
    checkbounds a indices
    getindex a (linear a indices)
theorem property1392 : Property1392 := by unfold Property1392; intros; rfl

def Property1398 : Prop := ∀ i, method1398 i = i
theorem property1398 : Property1398 := by unfold Property1398; intros; rfl

def Property1399 : Prop := ∀ i rest, method1399 i rest = i
theorem property1399 : Property1399 := by unfold Property1399; intros; rfl

def Property1400 : Prop := ∀ (α : Type) (linear : α → List Int) a,
  method1400 linear a = match linear a with | i :: _ => .ok i | [] => .error .boundsError
theorem property1400 : Property1400 := by
  unfold Property1400
  intro α linearFn a
  cases h : linearFn a <;> simp [method1400, h]

def Property1401 : Prop := ∀ (α : Type) (sub2ind : α → List Int → Int) a indices,
  method1401 sub2ind a indices = sub2ind a indices
theorem property1401 : Property1401 := by unfold Property1401; intros; rfl

def Property1404 : Prop := ∀ (α β : Type) (checkbounds : α → List Int → Jl Unit)
    (subscripts : α → List Int → List Int) (getindex : α → List Int → Jl β) a indices,
  method1404 checkbounds subscripts getindex a indices = do
    checkbounds a indices
    getindex a (subscripts a indices)
theorem property1404 : Property1404 := by unfold Property1404; intros; rfl

def Property1410 : Prop := ∀ (α β : Type) (getindex : α → List Int → β) a indices,
  method1410 getindex a indices = getindex a indices
theorem property1410 : Property1410 := by unfold Property1410; intros; rfl

def Property1414 : Prop := ∀ (α β : Type) (ind2sub : α → Int → β) a i,
  method1414 ind2sub a i = ind2sub a i
theorem property1414 : Property1414 := by unfold Property1414; intros; rfl

def Property1415 : Prop := ∀ rank, method1415 rank = List.replicate rank 1
theorem property1415 : Property1415 := by unfold Property1415; intros; rfl

def Property1416 : Prop := ∀ _array : Unit, method1416 = []
theorem property1416 : Property1416 := by unfold Property1416; intros; rfl

def Property1417 : Prop := ∀ i, method1417 i = []
theorem property1417 : Property1417 := by unfold Property1417; intros; rfl

def Property1418 : Prop := ∀ indices, method1418 indices = []
theorem property1418 : Property1418 := by unfold Property1418; intros; rfl

def Property1419 : Prop := ∀ (α β : Type) (split : List Int → Nat → List Int × List Int)
    (finish : α → List Int → List Int → β) a rank indices,
  method1419 split finish a rank indices =
    let parts := split indices rank; finish a parts.1 parts.2
theorem property1419 : Property1419 := by unfold Property1419; intros; rfl

def Property1424 : Prop := ∀ (α β γ δ : Type) (axes : α → β)
    (finish : α → β → γ → δ) a j,
  method1424 axes finish a j = finish a (axes a) j
theorem property1424 : Property1424 := by unfold Property1424; intros; rfl

def Property1426 : Prop := ∀ (α : Type) (remaining : List Int → List α → List α)
    (first : α → Int) (axes : α → List α) a j,
  method1426 remaining first axes a j = j ++ ((remaining j (axes a)).drop 1).map first
theorem property1426 : Property1426 := by unfold Property1426; intros; rfl

def Property1431 : Prop := ∀ (α β : Type) (j : α) (remainder : β),
  method1431 j remainder = j
theorem property1431 : Property1431 := by unfold Property1431; intros; rfl

def Property1432 : Prop := ∀ (α : Type) (indices : α), method1432 indices = indices
theorem property1432 : Property1432 := by unfold Property1432; intros; rfl

def Property1433 : Prop := ∀ (α β : Type) (head : α) (tail : β), method1433 head tail = tail
theorem property1433 : Property1433 := by unfold Property1433; intros; rfl

def Property1434 : Prop := ∀ (α β γ : Type) (remaining : List α → List β → γ) heads tails,
  method1434 remaining heads tails = remaining heads.tail tails.tail
theorem property1434 : Property1434 := by unfold Property1434; intros; rfl

def Property1435 : Prop := ∀ i, method1435 i = []
theorem property1435 : Property1435 := by unfold Property1435; intros; rfl

def Property1436 : Prop := ∀ (α β : Type) (ind2sub : α → Int → β) shape i,
  method1436 ind2sub shape i = ind2sub shape i
theorem property1436 : Property1436 := by unfold Property1436; intros; rfl

def Property1464 : Prop := ∀ (α σ ι κ β : Type) (style : α → σ)
    (canonical : σ → α → List ι → Jl Unit) (toIndices : α → List ι → Jl (List κ))
    (set : σ → α → β → List κ → Jl α) a value indices,
  method1464 style canonical toIndices set a value indices = do
    canonical (style a) a indices
    let js ← toIndices a indices
    set (style a) a value js
theorem property1464 : Property1464 := by unfold Property1464; intros; rfl

def Property1469 : Prop := ∀ (α β ι γ : Type) (setindex : α → β → List ι → γ) a value indices,
  method1469 setindex a value indices = setindex a value indices
theorem property1469 : Property1469 := by unfold Property1469; intros; rfl

def Property1475 : Prop := ∀ typeName, method1475 typeName = .error ⟨"setindex!", typeName⟩
theorem property1475 : Property1475 := by unfold Property1475; intros; rfl

def Property1477 : Prop := ∀ typeName, method1477 typeName = .error ⟨"setindex!", typeName⟩
theorem property1477 : Property1477 := by unfold Property1477; intros; rfl

def Property1479 : Prop := ∀ _args : Unit, method1479 = ()
theorem property1479 : Property1479 := by unfold Property1479; intros; rfl

def Property1482 : Prop := ∀ (β : Type) arrayType indexTypes,
  (method1482 arrayType indexTypes : Except String β) =
    .error ("setindex! for " ++ arrayType ++ " with types " ++ indexTypes ++ " is not supported")
theorem property1482 : Property1482 := by unfold Property1482; intros; rfl

def Property1486 : Prop := ∀ (α β γ : Type) (setindex : α → β → Int → γ) a value i,
  method1486 setindex a value i = setindex a value i
theorem property1486 : Property1486 := by unfold Property1486; intros; rfl

def Property1487 : Prop := ∀ (α β : Type) (checkbounds : α → List Int → Jl Unit)
    (linear : α → List Int → Int) (setindex : α → β → Int → Jl α) a value indices,
  method1487 checkbounds linear setindex a value indices = do
    checkbounds a indices
    setindex a value (linear a indices)
theorem property1487 : Property1487 := by unfold Property1487; intros; rfl

def Property1495 : Prop := ∀ (α β γ : Type) (setindex : α → β → List Int → γ) a value indices,
  method1495 setindex a value indices = setindex a value indices
theorem property1495 : Property1495 := by unfold Property1495; intros; rfl

def Property1499 : Prop := ∀ (α β : Type) (checkbounds : α → List Int → Jl Unit)
    (subscripts : α → List Int → List Int) (setindex : α → β → List Int → Jl α)
    a value indices,
  method1499 checkbounds subscripts setindex a value indices = do
    checkbounds a indices
    setindex a value (subscripts a indices)
theorem property1499 : Property1499 := by unfold Property1499; intros; rfl

private def entry (line : Nat) (slug fn statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id := s!"abstractarraycov-line{line}-{slug}", juliaFile := "base/abstractarray.jl",
    juliaFns := [fn], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.AbstractArrayCov.Rows.Index
