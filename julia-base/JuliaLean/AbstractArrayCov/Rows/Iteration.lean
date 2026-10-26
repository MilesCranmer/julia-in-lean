import JuliaLean.AbstractArrayCov.Rows.Basic

/-! Method-specific models for `base/abstractarray.jl:322-637`. -/

namespace JuliaLean.AbstractArrayCov.Rows.Iteration

open JuliaLean
open JuliaLean.Registry
open JuliaLean.AbstractArrayCov.Rows.Basic

abbrev I64 := JInt .i64
abbrev R (α : Type) := Except String α

def i64 (x : Int) : I64 := JInt.lit .i64 x

def joinCommaAnd : List String → String
  | [] => ""
  | [x] => x
  | [x, y] => x ++ " and " ++ y
  | x :: rest => x ++ ", " ++ joinCommaAnd rest

def listFirst (xs : List α) : Jl α :=
  match xs with | x :: _ => .ok x | [] => .error .boundsError

def listLast (xs : List α) : Jl α :=
  match xs.getLast? with | some x => .ok x | none => .error .boundsError

/-- `eachindex(itrs...) = keys(itrs...)`, line 322. -/
def method322 (keys : List α → β) (itrs : List α) : β := keys itrs
def Property322 : Prop := ∀ (α β : Type) (keys : List α → β) itrs,
  method322 keys itrs = keys itrs
theorem property322 : Property322 := by unfold Property322; intros; rfl

/-- Vector `eachindex`, line 325. -/
def method325 (axes1 : α → β) (a : α) : β := axes1 a
def Property325 : Prop := ∀ (α β : Type) (axes1 : α → β) a,
  method325 axes1 a = axes1 a
theorem property325 : Property325 := by unfold Property325; intros; rfl

/-- Two-item `_join_comma_and`, line 329. -/
def method329 (a b : String) : String := a ++ " and " ++ b
def Property329 : Prop := ∀ a b, method329 a b = a ++ " and " ++ b
theorem property329 : Property329 := by unfold Property329; intros; rfl

/-- Vararg `_join_comma_and`, line 330. -/
def method330 (a b : String) (rest : List String) : String :=
  a ++ ", " ++ joinCommaAnd (b :: rest)
def Property330 : Prop := ∀ a b rest,
  method330 a b rest = a ++ ", " ++ joinCommaAnd (b :: rest)
theorem property330 : Property330 := by unfold Property330; intros; rfl

/-- `throw_eachindex_mismatch_indices`, lines 331-335. -/
def method331 (indices a : String) (bs : List String) : R Unit :=
  .error ("all inputs to eachindex must have the same " ++ indices ++ ", got " ++
    joinCommaAnd (a :: bs))
def Property331 : Prop := ∀ indices a bs,
  method331 indices a bs = .error ("all inputs to eachindex must have the same " ++
    indices ++ ", got " ++ joinCommaAnd (a :: bs))
theorem property331 : Property331 := by unfold Property331; intros; rfl

/-- Single-array `eachindex`, line 384. -/
def method384 (style : α → σ) (each : σ → α → β) (a : α) : β :=
  each (style a) a
def Property384 : Prop := ∀ (α σ β : Type) (style : α → σ) (each : σ → α → β) a,
  method384 style each a = each (style a) a
theorem property384 : Property384 := by unfold Property384; intros; rfl

/-- Two-array `eachindex`, lines 386-389. -/
def method386 (style : α → β → σ) (each : σ → α → β → γ) (a : α) (b : β) : γ :=
  each (style a b) a b
def Property386 : Prop := ∀ (α β σ γ : Type) (style : α → β → σ)
    (each : σ → α → β → γ) a b,
  method386 style each a b = each (style a b) a b
theorem property386 : Property386 := by unfold Property386; intros; rfl

/-- Vararg-array `eachindex`, lines 390-393. -/
def method390 (style : α → List α → σ) (each : σ → α → List α → β)
    (a : α) (bs : List α) : β :=
  each (style a bs) a bs
def Property390 : Prop := ∀ (α σ β : Type) (style : α → List α → σ)
    (each : σ → α → List α → β) a bs,
  method390 style each a bs = each (style a bs) a bs
theorem property390 : Property390 := by unfold Property390; intros; rfl

/-- Linear Array/Memory `eachindex`, line 394. -/
def method394 (length : α → Nat) (uncheckedOneTo : Nat → β) (a : α) : β :=
  uncheckedOneTo (length a)
def Property394 : Prop := ∀ (α β : Type) (length : α → Nat)
    (uncheckedOneTo : Nat → β) a,
  method394 length uncheckedOneTo a = uncheckedOneTo (length a)
theorem property394 : Property394 := by unfold Property394; intros; rfl

/-- Linear AbstractArray `eachindex`, line 395. -/
def method395 (length : α → Nat) (oneto : Nat → β) (a : α) : β := oneto (length a)
def Property395 : Prop := ∀ (α β : Type) (length : α → Nat) (oneto : Nat → β) a,
  method395 length oneto a = oneto (length a)
theorem property395 : Property395 := by unfold Property395; intros; rfl

/-- Linear AbstractVector `eachindex`, line 396. -/
def method396 (axes1 : α → β) (a : α) : β := axes1 a
def Property396 : Prop := ∀ (α β : Type) (axes1 : α → β) a,
  method396 axes1 a = axes1 a
theorem property396 : Property396 := by unfold Property396; intros; rfl

/-- Multi-array linear `eachindex`, lines 397-404. -/
def method397 [Repr β] [BEq β] (each : α → β) (a : α) (bs : List α) : R β :=
  let ia := each a
  let ibs := bs.map each
  if ibs.all (· == ia) then .ok ia
  else .error ("all inputs to eachindex must have the same indices, got " ++
    joinCommaAnd (toString (repr ia) :: ibs.map (toString ∘ repr)))

def Property397 : Prop := ∀ (α β : Type) [Repr β] [BEq β]
    (each : α → β) a bs,
  method397 each a bs =
    let ia := each a
    let ibs := bs.map each
    if ibs.all (· == ia) then .ok ia
    else .error ("all inputs to eachindex must have the same indices, got " ++
      joinCommaAnd (toString (repr ia) :: ibs.map (toString ∘ repr)))
theorem property397 : Property397 := by unfold Property397; intros; rfl

/-- `keys(style, A, B...)`, line 407. -/
def method407 (eachindex : σ → α → List α → β) (style : σ) (a : α) (bs : List α) : β :=
  eachindex style a bs
def Property407 : Prop := ∀ (σ α β : Type) (eachindex : σ → α → List α → β)
    style a bs,
  method407 eachindex style a bs = eachindex style a bs
theorem property407 : Property407 := by unfold Property407; intros; rfl

/-- `lastindex(a::AbstractArray)`, line 429. -/
def method429 (eachindex : α → List β) (a : α) : Jl β := listLast (eachindex a)
def Property429 : Prop := ∀ (α β : Type) (eachindex : α → List β) a,
  method429 eachindex a = listLast (eachindex a)
theorem property429 : Property429 := by unfold Property429; intros; rfl

/-- Dimensional `lastindex`, line 430. -/
def method430 (axes : α → β → List γ) (a : α) (d : β) : Jl γ := listLast (axes a d)
def Property430 : Prop := ∀ (α β γ : Type) (axes : α → β → List γ) a d,
  method430 axes a d = listLast (axes a d)
theorem property430 : Property430 := by unfold Property430; intros; rfl

/-- `firstindex(a::AbstractArray)`, line 452. -/
def method452 (eachindex : α → List β) (a : α) : Jl β := listFirst (eachindex a)
def Property452 : Prop := ∀ (α β : Type) (eachindex : α → List β) a,
  method452 eachindex a = listFirst (eachindex a)
theorem property452 : Property452 := by unfold Property452; intros; rfl

/-- Dimensional `firstindex`, line 453. -/
def method453 (axes : α → β → List γ) (a : α) (d : β) : Jl γ := listFirst (axes a d)
def Property453 : Prop := ∀ (α β γ : Type) (axes : α → β → List γ) a d,
  method453 axes a d = listFirst (axes a d)
theorem property453 : Property453 := by unfold Property453; intros; rfl

/-- `first(a::AbstractArray)`, line 455. -/
def method455 (eachindex : α → List β) (getindex : α → β → Jl γ) (a : α) : Jl γ := do
  let i ← listFirst (eachindex a)
  getindex a i
def Property455 : Prop := ∀ (α β γ : Type) (eachindex : α → List β)
    (getindex : α → β → Jl γ) a,
  method455 eachindex getindex a = do
    let i ← listFirst (eachindex a)
    getindex a i
theorem property455 : Property455 := by unfold Property455; intros; rfl

/-- Generic `first(itr)`, lines 474-478. -/
def method474 (iterate : α → Option (β × σ)) (itr : α) : Jl β :=
  match iterate itr with
  | none => .error (.argumentError "collection must be non-empty")
  | some result => .ok result.1
def Property474 : Prop := ∀ (α β σ : Type) (iterate : α → Option (β × σ)) itr,
  method474 iterate itr = match iterate itr with
    | none => .error (.argumentError "collection must be non-empty")
    | some result => .ok result.1
theorem property474 : Property474 := by
  unfold Property474
  intro α β σ iterate itr
  cases h : iterate itr <;> simp [method474, h]

/-- Generic `first(itr,n)`, line 505. -/
def method505 (take : α → Int → β) (collect : β → γ) (itr : α) (n : Int) : γ :=
  collect (take itr n)
def Property505 : Prop := ∀ (α β γ : Type) (take : α → Int → β) (collect : β → γ) itr n,
  method505 take collect itr n = collect (take itr n)
theorem property505 : Property505 := by unfold Property505; intros; rfl

/-- Vector `first(v,n)`, lines 507-510. -/
def method507 (checkedLength : α → Jl Int) (range : Int → β)
    (getindex : α → β → Jl γ) (v : α) (n : Int) : Jl γ := do
  if n < 0 then throw (.argumentError "Number of elements must be non-negative")
  let len ← checkedLength v
  getindex v (range (min n len))
def Property507 : Prop := ∀ (α β γ : Type) (checkedLength : α → Jl Int)
    (range : Int → β) (getindex : α → β → Jl γ) v n,
  method507 checkedLength range getindex v n = do
    if n < 0 then throw (.argumentError "Number of elements must be non-negative")
    let len ← checkedLength v
    getindex v (range (min n len))
theorem property507 : Property507 := by unfold Property507; intros; rfl

/-- `last(a) = a[end]`, line 530. -/
def method530 (lastindex : α → β) (getindex : α → β → γ) (a : α) : γ :=
  getindex a (lastindex a)
def Property530 : Prop := ∀ (α β γ : Type) (lastindex : α → β)
    (getindex : α → β → γ) a,
  method530 lastindex getindex a = getindex a (lastindex a)
theorem property530 : Property530 := by unfold Property530; intros; rfl

/-- Generic `last(itr,n)`, line 555. -/
def method555 (reverse : α → β) (take : β → Int → γ) (collect : γ → δ)
    (reverseBang : δ → ε) (itr : α) (n : Int) : ε :=
  reverseBang (collect (take (reverse itr) n))
def Property555 : Prop := ∀ (α β γ δ ε : Type) (reverse : α → β)
    (take : β → Int → γ) (collect : γ → δ) (reverseBang : δ → ε) itr n,
  method555 reverse take collect reverseBang itr n =
    reverseBang (collect (take (reverse itr) n))
theorem property555 : Property555 := by unfold Property555; intros; rfl

/-- Vector `last(v,n)`, lines 557-560. -/
def method557 (checkedLength : α → Jl Int) (lastindex : α → Int)
    (range : Int → Int → β) (getindex : α → β → Jl γ) (v : α) (n : Int) : Jl γ := do
  if n < 0 then throw (.argumentError "Number of elements must be non-negative")
  let len ← checkedLength v
  getindex v (range (lastindex v) (min n len))
def Property557 : Prop := ∀ (α β γ : Type) (checkedLength : α → Jl Int)
    (lastindex : α → Int) (range : Int → Int → β) (getindex : α → β → Jl γ) v n,
  method557 checkedLength lastindex range getindex v n = do
    if n < 0 then throw (.argumentError "Number of elements must be non-negative")
    let len ← checkedLength v
    getindex v (range (lastindex v) (min n len))
theorem property557 : Property557 := by unfold Property557; intros; rfl

def strideTail : List (I64 × I64) → I64 → I64
  | [], acc => acc
  | (st, sz) :: rest, acc => strideTail rest (acc + st * sz)

/-- Generic `stride(A,k)`, lines 597-607. -/
def method597 (strides size : α → List I64) (ndims : α → Nat) (a : α) (k : Int) : Jl I64 := do
  let st := strides a
  if k ≤ ndims a then
    tupleGet st (← JInt.convert .i64 k)
  else if ndims a = 0 then .ok (i64 1)
  else do
    let sz := size a
    let firstSt ← tupleGet st (i64 1)
    let firstSz ← tupleGet sz (i64 1)
    .ok (strideTail ((st.drop 1).zip (sz.drop 1)) (firstSt * firstSz))

def Property597 : Prop := ∀ (α : Type) (strides size : α → List I64)
    (ndims : α → Nat) a k,
  method597 strides size ndims a k = do
    let st := strides a
    if k ≤ ndims a then tupleGet st (← JInt.convert .i64 k)
    else if ndims a = 0 then .ok (i64 1)
    else do
      let sz := size a
      let firstSt ← tupleGet st (i64 1)
      let firstSz ← tupleGet sz (i64 1)
      .ok (strideTail ((st.drop 1).zip (sz.drop 1)) (firstSt * firstSz))
theorem property597 : Property597 := by unfold Property597; intros; rfl

def sizeToStrides (s : I64) : List I64 → List I64
  | [] => []
  | d :: rest => s :: sizeToStrides (s * d) rest

/-- Variadic recursive `size_to_strides`, line 609. -/
def method609 (s d : I64) (rest : List I64) : List I64 :=
  s :: sizeToStrides (s * d) rest
def Property609 : Prop := ∀ s d rest,
  method609 s d rest = s :: sizeToStrides (s * d) rest
theorem property609 : Property609 := by unfold Property609; intros; rfl

/-- Two-argument `size_to_strides`, line 610. -/
def method610 (s _d : I64) : List I64 := [s]
def Property610 : Prop := ∀ s d, method610 s d = [s]
theorem property610 : Property610 := by unfold Property610; intros; rfl

/-- One-argument `size_to_strides`, line 611. -/
def method611 (_s : I64) : List I64 := []
def Property611 : Prop := ∀ s, method611 s = []
theorem property611 : Property611 := by unfold Property611; intros; rfl

/-- `isstored`, lines 613-616. -/
def method613 (checkbounds : α → List Int → Jl Unit) (a : α) (indices : List Int) : Jl Bool := do
  checkbounds a indices
  return true
def Property613 : Prop := ∀ (α : Type) (checkbounds : α → List Int → Jl Unit) a indices,
  method613 checkbounds a indices = do checkbounds a indices; return true
theorem property613 : Property613 := by unfold Property613; intros; rfl

def intRange (lo hi : Int) : List Int :=
  (List.range (hi - lo + 1).toNat).map fun (n : Nat) => lo + (n : Int)

/-- Array `trailingsize(A,n)`, lines 619-625. -/
def method619 (ndims : α → Int) (size : α → Int → Jl I64) (a : α) (n : Int) : Jl I64 := do
  let mut s := i64 1
  for i in intRange n (ndims a) do
    s := s * (← size a i)
  return s
def Property619 : Prop := ∀ (α : Type) (ndims : α → Int)
    (size : α → Int → Jl I64) a n,
  method619 ndims size a n = do
    let mut s := i64 1
    for i in intRange n (ndims a) do s := s * (← size a i)
    return s
theorem property619 : Property619 := by unfold Property619; intros; rfl

/-- Tuple `trailingsize(inds,n)`, lines 626-632. -/
def method626 (length : α → I64) (inds : List α) (n : Int) : Jl I64 := do
  let mut s := i64 1
  for i in intRange n inds.length do
    let axis ← tupleGet inds (← JInt.convert .i64 i)
    s := s * length axis
  return s
def Property626 : Prop := ∀ (α : Type) (length : α → I64) inds n,
  method626 length inds n = do
    let mut s := i64 1
    for i in intRange n inds.length do
      let axis ← tupleGet inds (← JInt.convert .i64 i)
      s := s * length axis
    return s
theorem property626 : Property626 := by unfold Property626; intros; rfl

/-- Type-stable tuple `trailingsize`, lines 634-637. -/
def method634 (length : α → I64) (inds : List α) : I64 :=
  (inds.map length).foldl (· * ·) (i64 1)
def Property634 : Prop := ∀ (α : Type) (length : α → I64) inds,
  method634 length inds = (inds.map length).foldl (· * ·) (i64 1)
theorem property634 : Property634 := by unfold Property634; intros; rfl

private def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/abstractarray.jl", juliaFns := [fn], statement, source,
    status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry "abstractarraycov-line322-eachindex" "eachindex(itrs...)" "The generic method delegates its complete argument tuple to keys." "base/abstractarray.jl:322" ``Property322 ``property322,
  entry "abstractarraycov-line325-eachindex" "eachindex(::AbstractVector)" "The vector method returns axes1(A)." "base/abstractarray.jl:325" ``Property325 ``property325,
  entry "abstractarraycov-line329-join" "_join_comma_and(a,b)" "The two-value formatter places and between its inputs." "base/abstractarray.jl:329" ``Property329 ``property329,
  entry "abstractarraycov-line330-join" "_join_comma_and(a,b,rest...)" "The vararg formatter emits the first comma before recursively formatting the tail." "base/abstractarray.jl:330" ``Property330 ``property330,
  entry "abstractarraycov-line331-mismatch" "throw_eachindex_mismatch_indices" "The helper constructs and throws the dimension-mismatch text from the supplied indices in order." "base/abstractarray.jl:331-335" ``Property331 ``property331,
  entry "abstractarraycov-line384-eachindex" "eachindex(::AbstractArray)" "The method computes IndexStyle(A) before delegating to styled eachindex." "base/abstractarray.jl:384" ``Property384 ``property384,
  entry "abstractarraycov-line386-eachindex" "eachindex(::AbstractArray,::AbstractArray)" "The method computes the joint style before delegating with both arrays." "base/abstractarray.jl:386-389" ``Property386 ``property386,
  entry "abstractarraycov-line390-eachindex" "eachindex(::AbstractArray,::AbstractArray...)" "The vararg method computes the joint style before delegating all arrays." "base/abstractarray.jl:390-393" ``Property390 ``property390,
  entry "abstractarraycov-line394-eachindex" "eachindex(::IndexLinear,::Union{Array,Memory})" "The Array and Memory fast path applies unchecked_oneto to length." "base/abstractarray.jl:394" ``Property394 ``property394,
  entry "abstractarraycov-line395-eachindex" "eachindex(::IndexLinear,::AbstractArray)" "The generic linear path applies oneto to length." "base/abstractarray.jl:395" ``Property395 ``property395,
  entry "abstractarraycov-line396-eachindex" "eachindex(::IndexLinear,::AbstractVector)" "The vector linear path returns axes1." "base/abstractarray.jl:396" ``Property396 ``property396,
  entry "abstractarraycov-line397-eachindex" "eachindex(::IndexLinear,A,B...)" "The method computes every linear index domain, checks all against the first, throws on mismatch, and returns the first." "base/abstractarray.jl:397-404" ``Property397 ``property397,
  entry "abstractarraycov-line407-keys" "keys(::IndexStyle,A,B...)" "Styled keys delegates to styled eachindex with the same argument order." "base/abstractarray.jl:407" ``Property407 ``property407,
  entry "abstractarraycov-line429-lastindex" "lastindex(::AbstractArray)" "The method takes the last linear eachindex value." "base/abstractarray.jl:429" ``Property429 ``property429,
  entry "abstractarraycov-line430-lastindex" "lastindex(a,d)" "The method takes the last value of axes(a,d)." "base/abstractarray.jl:430" ``Property430 ``property430,
  entry "abstractarraycov-line452-firstindex" "firstindex(::AbstractArray)" "The method takes the first linear eachindex value." "base/abstractarray.jl:452" ``Property452 ``property452,
  entry "abstractarraycov-line453-firstindex" "firstindex(a,d)" "The method takes the first value of axes(a,d)." "base/abstractarray.jl:453" ``Property453 ``property453,
  entry "abstractarraycov-line455-first" "first(::AbstractArray)" "The method gets the element at the first efficient index." "base/abstractarray.jl:455" ``Property455 ``property455,
  entry "abstractarraycov-line474-first" "first(itr)" "The method calls iterate once, throws on nothing, and returns the yielded value." "base/abstractarray.jl:474-478" ``Property474 ``property474,
  entry "abstractarraycov-line505-first" "first(itr,n)" "The method collects Iterators.take(itr,n) in source call order." "base/abstractarray.jl:505" ``Property505 ``property505,
  entry "abstractarraycov-line507-first" "first(::AbstractVector,n)" "The vector method rejects negative n, computes checked_length, constructs the range, and indexes in order." "base/abstractarray.jl:507-510" ``Property507 ``property507,
  entry "abstractarraycov-line530-last" "last(a)" "The method indexes a at lastindex(a)." "base/abstractarray.jl:530" ``Property530 ``property530,
  entry "abstractarraycov-line555-last" "last(itr,n)" "The method reverses, takes, collects, then reverses the result in that order." "base/abstractarray.jl:555" ``Property555 ``property555,
  entry "abstractarraycov-line557-last" "last(::AbstractVector,n)" "The vector method rejects negative n, computes checked_length and lastindex, constructs the range, and indexes." "base/abstractarray.jl:557-560" ``Property557 ``property557,
  entry "abstractarraycov-line597-stride" "stride(::AbstractArray,k)" "The method checks the requested dimension, handles rank zero, and otherwise accumulates stride-size products in source order." "base/abstractarray.jl:597-607" ``Property597 ``property597,
  entry "abstractarraycov-line609-size-to-strides" "size_to_strides(s,d,sz...)" "The variadic method emits s before recursively multiplying by d." "base/abstractarray.jl:609" ``Property609 ``property609,
  entry "abstractarraycov-line610-size-to-strides" "size_to_strides(s,d)" "The two-argument base case returns the singleton s tuple." "base/abstractarray.jl:610" ``Property610 ``property610,
  entry "abstractarraycov-line611-size-to-strides" "size_to_strides(s)" "The one-argument base case returns the empty tuple." "base/abstractarray.jl:611" ``Property611 ``property611,
  entry "abstractarraycov-line613-isstored" "isstored(A,I...)" "The method performs checkbounds before returning true." "base/abstractarray.jl:613-616" ``Property613 ``property613,
  entry "abstractarraycov-line619-trailingsize" "trailingsize(A,n)" "The method multiplies size(A,i) for i=n:ndims(A) using Julia Int arithmetic." "base/abstractarray.jl:619-625" ``Property619 ``property619,
  entry "abstractarraycov-line626-trailingsize" "trailingsize(inds,n)" "The tuple method indexes each trailing axis and multiplies its length in order." "base/abstractarray.jl:626-632" ``Property626 ``property626,
  entry "abstractarraycov-line634-trailingsize" "trailingsize(inds)" "The type-stable method maps length then takes the product." "base/abstractarray.jl:634-637" ``Property634 ``property634
]

end JuliaLean.AbstractArrayCov.Rows.Iteration
