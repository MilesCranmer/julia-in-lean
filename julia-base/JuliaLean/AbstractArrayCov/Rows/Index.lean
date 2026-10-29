import JuliaLean.AbstractArrayCov.Rows.Copy

/-! Method-specific models for `base/abstractarray.jl:1279-1504`. -/

namespace JuliaLean.AbstractArrayCov.Rows.Index

open JuliaLean
open JuliaLean.Registry

abbrev I64 := JInt .i64
def i64 (x : Int) : I64 := JInt.lit .i64 x

structure CanonicalIndexErrorModel where
  func : String
  typeName : String
  deriving Repr, DecidableEq

/-- One-argument `pointer`, line 1279. -/
def method1279 (cconvert : α → β) (unsafeConvert : β → γ) (x : α) : γ :=
  unsafeConvert (cconvert x)
def Property1279 : Prop := ∀ (α β γ : Type) (cconvert : α → β)
    (unsafeConvert : β → γ) x,
  method1279 cconvert unsafeConvert x = unsafeConvert (cconvert x)
theorem property1279 : Property1279 := by unfold Property1279; intros; rfl

/-- Indexed `pointer`, lines 1280-1283. -/
def method1280 (pointer : α → I64) (offset : α → Int → Int) (x : α) (i : Int) : Jl I64 := do
  let off ← JInt.convert .i64 (offset x i)
  return pointer x + off
def Property1280 : Prop := ∀ (α : Type) (pointer : α → I64)
    (offset : α → Int → Int) x i,
  method1280 pointer offset x i = do
    let off ← JInt.convert .i64 (offset x i)
    return pointer x + off
theorem property1280 : Property1280 := by unfold Property1280; intros; rfl

/-- Dense-array `_memory_offset`, line 1286. -/
def method1286 (linear : α → List β → I64) (firstLinear : α → I64)
    (elsize : α → I64) (x : α) (indices : List β) : I64 :=
  (linear x indices - firstLinear x) * elsize x
def Property1286 : Prop := ∀ (α β : Type) (linear : α → List β → I64)
    (firstLinear : α → I64) (elsize : α → I64) x indices,
  method1286 linear firstLinear elsize x indices =
    (linear x indices - firstLinear x) * elsize x
theorem property1286 : Property1286 := by unfold Property1286; intros; rfl

def offsetTerms : List I64 → List I64 → List I64 → List I64
  | i :: is, s :: ss, o :: os => s * (i - o) :: offsetTerms is ss os
  | _, _, _ => []

/-- Generic-array `_memory_offset`, lines 1287-1290. -/
def method1287 (subscripts : α → List β → List I64) (strides origins : α → List I64)
    (elsize : α → I64) (x : α) (indices : List β) : I64 :=
  let js := subscripts x indices
  ((offsetTerms js (strides x) (origins x)).foldl (· + ·) (i64 0)) * elsize x
def Property1287 : Prop := ∀ (α β : Type) (subscripts : α → List β → List I64)
    (strides origins : α → List I64) (elsize : α → I64) x indices,
  method1287 subscripts strides origins elsize x indices =
    let js := subscripts x indices
    ((offsetTerms js (strides x) (origins x)).foldl (· + ·) (i64 0)) * elsize x
theorem property1287 : Property1287 := by unfold Property1287; intros; rfl

/-- Generic `getindex`, lines 1363-1367. -/
def method1363 (style : α → σ) (canonical : σ → α → List ι → Jl Unit)
    (toIndices : α → List ι → Jl (List κ)) (get : σ → α → List κ → Jl β)
    (a : α) (indices : List ι) : Jl β := do
  canonical (style a) a indices
  let js ← toIndices a indices
  get (style a) a js
def Property1363 : Prop := ∀ (α σ ι κ β : Type) (style : α → σ)
    (canonical : σ → α → List ι → Jl Unit) (toIndices : α → List ι → Jl (List κ))
    (get : σ → α → List κ → Jl β) a indices,
  method1363 style canonical toIndices get a indices = do
    canonical (style a) a indices
    let js ← toIndices a indices
    get (style a) a js
theorem property1363 : Property1363 := by unfold Property1363; intros; rfl

/-- Integer-only Array `getindex`, line 1369. -/
def method1369 (toIndices : α → List ι → Jl (List κ))
    (get : α → List κ → Jl β) (a : α) (indices : List ι) : Jl β := do
  get a (← toIndices a indices)
def Property1369 : Prop := ∀ (α ι κ β : Type) (toIndices : α → List ι → Jl (List κ))
    (get : α → List κ → Jl β) a indices,
  method1369 toIndices get a indices = do get a (← toIndices a indices)
theorem property1369 : Property1369 := by unfold Property1369; intros; rfl

/-- `unsafe_getindex`, line 1371. -/
def method1371 (getindex : α → List ι → β) (a : α) (indices : List ι) : β :=
  getindex a indices
def Property1371 : Prop := ∀ (α ι β : Type) (getindex : α → List ι → β) a indices,
  method1371 getindex a indices = getindex a indices
theorem property1371 : Property1371 := by unfold Property1371; intros; rfl

/-- Inner `CanonicalIndexError` constructor, line 1376. -/
def method1376 (func typeName : String) : CanonicalIndexErrorModel := ⟨func, typeName⟩
def Property1376 : Prop := ∀ func typeName,
  method1376 func typeName = ⟨func, typeName⟩
theorem property1376 : Property1376 := by unfold Property1376; intros; rfl

/-- Linear canonical-get guard, lines 1379-1380. -/
def method1379 (typeName : String) : Except CanonicalIndexErrorModel Unit :=
  .error ⟨"getindex", typeName⟩
def Property1379 : Prop := ∀ typeName, method1379 typeName = .error ⟨"getindex", typeName⟩
theorem property1379 : Property1379 := by unfold Property1379; intros; rfl

/-- Cartesian canonical-get guard, lines 1381-1382. -/
def method1381 (typeName : String) : Except CanonicalIndexErrorModel Unit :=
  .error ⟨"getindex", typeName⟩
def Property1381 : Prop := ∀ typeName, method1381 typeName = .error ⟨"getindex", typeName⟩
theorem property1381 : Property1381 := by unfold Property1381; intros; rfl

/-- Noncanonical get guard, line 1383. -/
def method1383 : Unit := ()
def Property1383 : Prop := ∀ _args : Unit, method1383 = ()
theorem property1383 : Property1383 := by unfold Property1383; intros; rfl

/-- Unsupported `_getindex` fallback, lines 1386-1387. -/
def method1386 (arrayType indexTypes : String) : Except String β :=
  .error ("getindex for " ++ arrayType ++ " with types " ++ indexTypes ++ " is not supported")
def Property1386 : Prop := ∀ (β : Type) arrayType indexTypes,
  (method1386 arrayType indexTypes : Except String β) =
    .error ("getindex for " ++ arrayType ++ " with types " ++ indexTypes ++ " is not supported")
theorem property1386 : Property1386 := by unfold Property1386; intros; rfl

/-- Linear vector scalar `_getindex`, line 1390. -/
def method1390 (getindex : α → Int → β) (a : α) (i : Int) : β := getindex a i
def Property1390 : Prop := ∀ (α β : Type) (getindex : α → Int → β) a i,
  method1390 getindex a i = getindex a i
theorem property1390 : Property1390 := by unfold Property1390; intros; rfl

/-- Linear array scalar `_getindex`, line 1391. -/
def method1391 (getindex : α → Int → β) (a : α) (i : Int) : β := getindex a i
def Property1391 : Prop := ∀ (α β : Type) (getindex : α → Int → β) a i,
  method1391 getindex a i = getindex a i
theorem property1391 : Property1391 := by unfold Property1391; intros; rfl

/-- Linear multi-index `_getindex`, lines 1392-1397. -/
def method1392 (checkbounds : α → List Int → Jl Unit)
    (linear : α → List Int → Int) (getindex : α → Int → Jl β)
    (a : α) (indices : List Int) : Jl β := do
  checkbounds a indices
  getindex a (linear a indices)
def Property1392 : Prop := ∀ (α β : Type) (checkbounds : α → List Int → Jl Unit)
    (linear : α → List Int → Int) (getindex : α → Int → Jl β) a indices,
  method1392 checkbounds linear getindex a indices = do
    checkbounds a indices
    getindex a (linear a indices)
theorem property1392 : Property1392 := by unfold Property1392; intros; rfl

/-- Single-index `_to_linear_index`, line 1398. -/
def method1398 (i : Int) : Int := i
def Property1398 : Prop := ∀ i, method1398 i = i
theorem property1398 : Property1398 := by unfold Property1398; intros; rfl

/-- Vector multi-index `_to_linear_index`, line 1399. -/
def method1399 (i : Int) (_rest : List Int) : Int := i
def Property1399 : Prop := ∀ i rest, method1399 i rest = i
theorem property1399 : Property1399 := by unfold Property1399; intros; rfl

/-- Zero-index `_to_linear_index`, line 1400. -/
def method1400 (linearIndices : α → List Int) (a : α) : Jl Int :=
  match linearIndices a with | i :: _ => .ok i | [] => .error .boundsError
def Property1400 : Prop := ∀ (α : Type) (linear : α → List Int) a,
  method1400 linear a = match linear a with | i :: _ => .ok i | [] => .error .boundsError
theorem property1400 : Property1400 := by
  unfold Property1400
  intro α linearFn a
  cases h : linearFn a <;> simp [method1400, h]

/-- Multi-index `_to_linear_index`, line 1401. -/
def method1401 (sub2ind : α → List Int → Int) (a : α) (indices : List Int) : Int :=
  sub2ind a indices
def Property1401 : Prop := ∀ (α : Type) (sub2ind : α → List Int → Int) a indices,
  method1401 sub2ind a indices = sub2ind a indices
theorem property1401 : Property1401 := by unfold Property1401; intros; rfl

/-- Cartesian multi-index `_getindex`, lines 1404-1409. -/
def method1404 (checkbounds : α → List Int → Jl Unit)
    (subscripts : α → List Int → List Int) (getindex : α → List Int → Jl β)
    (a : α) (indices : List Int) : Jl β := do
  checkbounds a indices
  getindex a (subscripts a indices)
def Property1404 : Prop := ∀ (α β : Type) (checkbounds : α → List Int → Jl Unit)
    (subscripts : α → List Int → List Int) (getindex : α → List Int → Jl β) a indices,
  method1404 checkbounds subscripts getindex a indices = do
    checkbounds a indices
    getindex a (subscripts a indices)
theorem property1404 : Property1404 := by unfold Property1404; intros; rfl

/-- Canonical Cartesian `_getindex`, lines 1410-1413. -/
def method1410 (getindex : α → List Int → β) (a : α) (indices : List Int) : β :=
  getindex a indices
def Property1410 : Prop := ∀ (α β : Type) (getindex : α → List Int → β) a indices,
  method1410 getindex a indices = getindex a indices
theorem property1410 : Property1410 := by unfold Property1410; intros; rfl

/-- One-index `_to_subscript_indices`, line 1414. -/
def method1414 (ind2sub : α → Int → β) (a : α) (i : Int) : β := ind2sub a i
def Property1414 : Prop := ∀ (α β : Type) (ind2sub : α → Int → β) a i,
  method1414 ind2sub a i = ind2sub a i
theorem property1414 : Property1414 := by unfold Property1414; intros; rfl

/-- Zero-index general-rank `_to_subscript_indices`, line 1415. -/
def method1415 (rank : Nat) : List Int := List.replicate rank 1
def Property1415 : Prop := ∀ rank, method1415 rank = List.replicate rank 1
theorem property1415 : Property1415 := by unfold Property1415; intros; rfl

/-- Zero-rank zero-index `_to_subscript_indices`, line 1416. -/
def method1416 : List Int := []
def Property1416 : Prop := ∀ _array : Unit, method1416 = []
theorem property1416 : Property1416 := by unfold Property1416; intros; rfl

/-- Zero-rank one-index `_to_subscript_indices`, line 1417. -/
def method1417 (_i : Int) : List Int := []
def Property1417 : Prop := ∀ i, method1417 i = []
theorem property1417 : Property1417 := by unfold Property1417; intros; rfl

/-- Zero-rank vararg `_to_subscript_indices`, line 1418. -/
def method1418 (_indices : List Int) : List Int := []
def Property1418 : Prop := ∀ indices, method1418 indices = []
theorem property1418 : Property1418 := by unfold Property1418; intros; rfl

/-- General integer `_to_subscript_indices`, lines 1419-1423. -/
def method1419 (split : List Int → Nat → List Int × List Int)
    (finish : α → List Int → List Int → β) (a : α) (rank : Nat) (indices : List Int) : β :=
  let parts := split indices rank
  finish a parts.1 parts.2
def Property1419 : Prop := ∀ (α β : Type) (split : List Int → Nat → List Int × List Int)
    (finish : α → List Int → List Int → β) a rank indices,
  method1419 split finish a rank indices =
    let parts := split indices rank; finish a parts.1 parts.2
theorem property1419 : Property1419 := by unfold Property1419; intros; rfl

/-- Empty-remainder `_to_subscript_indices`, lines 1424-1425. -/
def method1424 (axes : α → β) (finish : α → β → γ → δ) (a : α) (j : γ) : δ :=
  finish a (axes a) j
def Property1424 : Prop := ∀ (α β γ δ : Type) (axes : α → β)
    (finish : α → β → γ → δ) a j,
  method1424 axes finish a j = finish a (axes a) j
theorem property1424 : Property1424 := by unfold Property1424; intros; rfl

/-- `__to_subscript_indices`, lines 1426-1430. -/
def method1426 (remaining : List Int → List α → List α)
    (first : α → Int) (axes : α → List α) (a : α) (j : List Int) : List Int :=
  j ++ ((remaining j (axes a)).drop 1).map first
def Property1426 : Prop := ∀ (α : Type) (remaining : List Int → List α → List α)
    (first : α → Int) (axes : α → List α) a j,
  method1426 remaining first axes a j = j ++ ((remaining j (axes a)).drop 1).map first
theorem property1426 : Property1426 := by unfold Property1426; intros; rfl

/-- Nonempty-remainder `_to_subscript_indices`, line 1431. -/
def method1431 (j : α) (_remainder : β) : α := j
def Property1431 : Prop := ∀ (α β : Type) (j : α) (remainder : β),
  method1431 j remainder = j
theorem property1431 : Property1431 := by unfold Property1431; intros; rfl

/-- Canonical-rank `_to_subscript_indices`, line 1432. -/
def method1432 (indices : α) : α := indices
def Property1432 : Prop := ∀ (α : Type) (indices : α), method1432 indices = indices
theorem property1432 : Property1432 := by unfold Property1432; intros; rfl

/-- Singleton-head `_remaining_size`, line 1433. -/
def method1433 (_head : α) (tail : β) : β := tail
def Property1433 : Prop := ∀ (α β : Type) (head : α) (tail : β), method1433 head tail = tail
theorem property1433 : Property1433 := by unfold Property1433; intros; rfl

/-- Recursive `_remaining_size`, line 1434. -/
def method1434 (remaining : List α → List β → γ) (heads : List α) (tails : List β) : γ :=
  remaining heads.tail tails.tail
def Property1434 : Prop := ∀ (α β γ : Type) (remaining : List α → List β → γ) heads tails,
  method1434 remaining heads tails = remaining heads.tail tails.tail
theorem property1434 : Property1434 := by unfold Property1434; intros; rfl

/-- Empty-shape `_unsafe_ind2sub`, line 1435. -/
def method1435 (_i : Int) : List Int := []
def Property1435 : Prop := ∀ i, method1435 i = []
theorem property1435 : Property1435 := by unfold Property1435; intros; rfl

/-- Nonempty `_unsafe_ind2sub`, line 1436. -/
def method1436 (ind2sub : α → Int → β) (shape : α) (i : Int) : β := ind2sub shape i
def Property1436 : Prop := ∀ (α β : Type) (ind2sub : α → Int → β) shape i,
  method1436 ind2sub shape i = ind2sub shape i
theorem property1436 : Property1436 := by unfold Property1436; intros; rfl

/-- Generic `setindex!`, lines 1464-1468. -/
def method1464 (style : α → σ) (canonical : σ → α → List ι → Jl Unit)
    (toIndices : α → List ι → Jl (List κ)) (set : σ → α → β → List κ → Jl α)
    (a : α) (value : β) (indices : List ι) : Jl α := do
  canonical (style a) a indices
  let js ← toIndices a indices
  set (style a) a value js
def Property1464 : Prop := ∀ (α σ ι κ β : Type) (style : α → σ)
    (canonical : σ → α → List ι → Jl Unit) (toIndices : α → List ι → Jl (List κ))
    (set : σ → α → β → List κ → Jl α) a value indices,
  method1464 style canonical toIndices set a value indices = do
    canonical (style a) a indices
    let js ← toIndices a indices
    set (style a) a value js
theorem property1464 : Property1464 := by unfold Property1464; intros; rfl

/-- `unsafe_setindex!`, lines 1469-1473. -/
def method1469 (setindex : α → β → List ι → γ) (a : α) (value : β) (indices : List ι) : γ :=
  setindex a value indices
def Property1469 : Prop := ∀ (α β ι γ : Type) (setindex : α → β → List ι → γ) a value indices,
  method1469 setindex a value indices = setindex a value indices
theorem property1469 : Property1469 := by unfold Property1469; intros; rfl

/-- Linear canonical-set guard, lines 1475-1476. -/
def method1475 (typeName : String) : Except CanonicalIndexErrorModel Unit :=
  .error ⟨"setindex!", typeName⟩
def Property1475 : Prop := ∀ typeName, method1475 typeName = .error ⟨"setindex!", typeName⟩
theorem property1475 : Property1475 := by unfold Property1475; intros; rfl

/-- Cartesian canonical-set guard, lines 1477-1478. -/
def method1477 (typeName : String) : Except CanonicalIndexErrorModel Unit :=
  .error ⟨"setindex!", typeName⟩
def Property1477 : Prop := ∀ typeName, method1477 typeName = .error ⟨"setindex!", typeName⟩
theorem property1477 : Property1477 := by unfold Property1477; intros; rfl

/-- Noncanonical set guard, line 1479. -/
def method1479 : Unit := ()
def Property1479 : Prop := ∀ _args : Unit, method1479 = ()
theorem property1479 : Property1479 := by unfold Property1479; intros; rfl

/-- Unsupported `_setindex!` fallback, lines 1482-1483. -/
def method1482 (arrayType indexTypes : String) : Except String β :=
  .error ("setindex! for " ++ arrayType ++ " with types " ++ indexTypes ++ " is not supported")
def Property1482 : Prop := ∀ (β : Type) arrayType indexTypes,
  (method1482 arrayType indexTypes : Except String β) =
    .error ("setindex! for " ++ arrayType ++ " with types " ++ indexTypes ++ " is not supported")
theorem property1482 : Property1482 := by unfold Property1482; intros; rfl

/-- Linear scalar `_setindex!`, line 1486. -/
def method1486 (setindex : α → β → Int → γ) (a : α) (value : β) (i : Int) : γ :=
  setindex a value i
def Property1486 : Prop := ∀ (α β γ : Type) (setindex : α → β → Int → γ) a value i,
  method1486 setindex a value i = setindex a value i
theorem property1486 : Property1486 := by unfold Property1486; intros; rfl

/-- Linear multi-index `_setindex!`, lines 1487-1492. -/
def method1487 (checkbounds : α → List Int → Jl Unit) (linear : α → List Int → Int)
    (setindex : α → β → Int → Jl α) (a : α) (value : β) (indices : List Int) : Jl α := do
  checkbounds a indices
  setindex a value (linear a indices)
def Property1487 : Prop := ∀ (α β : Type) (checkbounds : α → List Int → Jl Unit)
    (linear : α → List Int → Int) (setindex : α → β → Int → Jl α) a value indices,
  method1487 checkbounds linear setindex a value indices = do
    checkbounds a indices
    setindex a value (linear a indices)
theorem property1487 : Property1487 := by unfold Property1487; intros; rfl

/-- Canonical Cartesian `_setindex!`, lines 1495-1498. -/
def method1495 (setindex : α → β → List Int → γ) (a : α) (value : β) (indices : List Int) : γ :=
  setindex a value indices
def Property1495 : Prop := ∀ (α β γ : Type) (setindex : α → β → List Int → γ) a value indices,
  method1495 setindex a value indices = setindex a value indices
theorem property1495 : Property1495 := by unfold Property1495; intros; rfl

/-- Cartesian multi-index `_setindex!`, lines 1499-1504. -/
def method1499 (checkbounds : α → List Int → Jl Unit)
    (subscripts : α → List Int → List Int) (setindex : α → β → List Int → Jl α)
    (a : α) (value : β) (indices : List Int) : Jl α := do
  checkbounds a indices
  setindex a value (subscripts a indices)
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
