import JuliaLean.MultidimCov.AbstractArrayInterfaceFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.SubarrayFaithfulB

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful

/-! Faithful source-order models for the reviewed HOLLOW methods in
`base/subarray.jl:257-419`. -/

/-- `unsafe_view(AbstractArray, indices...)`, lines 257-259. -/
def m257 (construct : A → List I → JResult R) (array : A) (indices : List I) : JResult R :=
  construct array indices
def P257 : Prop := ∀ {A I R : Type} (construct : A → List I → JResult R) array indices,
  m257 construct array indices = construct array indices
theorem p257 : P257 := by unfold P257; intros; rfl

/-- CartesianIndex{1}-array scan in `_maybe_reindex`, lines 273-274. -/
def m273 (tail : A → JResult T) (recurse : V → I → T → JResult R)
    (view : V) (indices : I) (scan : A) : JResult R := do
  let rest ← tail scan
  recurse view indices rest
def P273 : Prop := ∀ {A T V I R : Type} (tail : A → JResult T)
    (recurse : V → I → T → JResult R) view indices scan,
  m273 tail recurse view indices scan = do let rest ← tail scan; recurse view indices rest
theorem p273 : P273 := by unfold P273; intros; rfl

/-- General tuple scan in `_maybe_reindex`, line 275. -/
def m275 (tail : A → JResult T) (recurse : V → I → T → JResult R)
    (view : V) (indices : I) (scan : A) : JResult R := do
  let rest ← tail scan
  recurse view indices rest
def P275 : Prop := ∀ {A T V I R : Type} (tail : A → JResult T)
    (recurse : V → I → T → JResult R) view indices scan,
  m275 tail recurse view indices scan = do let rest ← tail scan; recurse view indices rest
theorem p275 : P275 := by unfold P275; intros; rfl

/-- Terminal `_maybe_reindex`, lines 276-279. -/
def m276 (parent : V → P) (storedIndices : V → PI)
    (reindex : PI → I → JResult RI) (toIndices : P → RI → JResult TI)
    (construct : P → TI → JResult R) (view : V) (indices : I) : JResult R := do
  let combined ← reindex (storedIndices view) indices
  let converted ← toIndices (parent view) combined
  construct (parent view) converted
def P276 : Prop := ∀ {V P PI I RI TI R : Type} (parent : V → P) (storedIndices : V → PI)
    (reindex : PI → I → JResult RI) (toIndices : P → RI → JResult TI)
    (construct : P → TI → JResult R) view indices,
  m276 parent storedIndices reindex toIndices construct view indices = do
    let combined ← reindex (storedIndices view) indices
    let converted ← toIndices (parent view) combined
    construct (parent view) converted
theorem p276 : P276 := by unfold P276; intros; rfl

/-- Scalar-parent-index `reindex`, lines 295-296. -/
def m295 (recurse : List P → List S → JResult (List O)) (inject : P → O)
    (head : P) (parentRest : List P) (subindices : List S) : JResult (List O) := do
  let tail ← recurse parentRest subindices
  .ok (inject head :: tail)
def P295 : Prop := ∀ {P S O : Type} (recurse : List P → List S → JResult (List O))
    (inject : P → O) head parentRest subindices,
  m295 recurse inject head parentRest subindices = do
    let tail ← recurse parentRest subindices
    .ok (inject head :: tail)
theorem p295 : P295 := by unfold P295; intros; rfl

/-- Slice-parent-index `reindex`, lines 299-300. -/
def m299 (recurse : List P → List S → JResult (List O)) (inject : S → O)
    (_slice : P) (parentRest : List P) (head : S) (subRest : List S) : JResult (List O) := do
  let tail ← recurse parentRest subRest
  .ok (inject head :: tail)
def P299 : Prop := ∀ {P S O : Type} (recurse : List P → List S → JResult (List O))
    (inject : S → O) (slice : P) parentRest head subRest,
  m299 recurse inject slice parentRest head subRest = do
    let tail ← recurse parentRest subRest
    .ok (inject head :: tail)
theorem p299 : P299 := by unfold P299; intros; rfl

/-- Vector-parent-index `reindex`, lines 303-304. -/
def m303 (getindex : A → S → JResult O) (recurse : List P → List S → JResult (List O))
    (array : A) (parentRest : List P) (head : S) (subRest : List S) : JResult (List O) := do
  let value ← getindex array head
  let tail ← recurse parentRest subRest
  .ok (value :: tail)
def P303 : Prop := ∀ {A S O P : Type} (getindex : A → S → JResult O)
    (recurse : List P → List S → JResult (List O)) array parentRest head subRest,
  m303 getindex recurse array parentRest head subRest = do
    let value ← getindex array head
    let tail ← recurse parentRest subRest
    .ok (value :: tail)
theorem p303 : P303 := by unfold P303; intros; rfl

/-- Matrix-parent-index `reindex`, lines 307-308. -/
def m307 (getindex : A → S → S → JResult O)
    (recurse : List P → List S → JResult (List O)) (array : A) (parentRest : List P)
    (first second : S) (subRest : List S) : JResult (List O) := do
  let value ← getindex array first second
  let tail ← recurse parentRest subRest
  .ok (value :: tail)
def P307 : Prop := ∀ {A S O P : Type} (getindex : A → S → S → JResult O)
    (recurse : List P → List S → JResult (List O)) array parentRest first second subRest,
  m307 getindex recurse array parentRest first second subRest = do
    let value ← getindex array first second
    let tail ← recurse parentRest subRest
    .ok (value :: tail)
theorem p307 : P307 := by unfold P307; intros; rfl

/-- N-dimensional parent-array `reindex`, lines 311-312. -/
def m311 (splitAt : Nat → List S → List S × List S)
    (getindex : A → List S → JResult O) (recurse : List P → List S → JResult (List O))
    (array : A) (rank : Nat) (parentRest : List P) (subindices : List S) : JResult (List O) := do
  let parts := splitAt rank subindices
  let value ← getindex array parts.1
  let tail ← recurse parentRest parts.2
  .ok (value :: tail)
def P311 : Prop := ∀ {S A O P : Type} (splitAt : Nat → List S → List S × List S)
    (getindex : A → List S → JResult O) (recurse : List P → List S → JResult (List O))
    array rank parentRest subindices,
  m311 splitAt getindex recurse array rank parentRest subindices = do
    let parts := splitAt rank subindices
    let value ← getindex array parts.1
    let tail ← recurse parentRest parts.2
    .ok (value :: tail)
theorem p311 : P311 := by unfold P311; intros; rfl

/-- General SubArray `getindex`, lines 316-320. -/
def m316 (checkbounds : V → List Int → JResult Unit) (storedIndices : V → PI)
    (reindex : PI → List Int → JResult RI) (parent : V → P)
    (getindex : P → RI → JResult T) (view : V) (indices : List Int) : JResult T := do
  checkbounds view indices
  let combined ← reindex (storedIndices view) indices
  getindex (parent view) combined
def P316 : Prop := ∀ {V PI RI P T : Type} (checkbounds : V → List Int → JResult Unit)
    (storedIndices : V → PI) (reindex : PI → List Int → JResult RI) (parent : V → P)
    (getindex : P → RI → JResult T) view indices,
  m316 checkbounds storedIndices reindex parent getindex view indices = do
    checkbounds view indices
    let combined ← reindex (storedIndices view) indices
    getindex (parent view) combined
theorem p316 : P316 := by unfold P316; intros; rfl

/-- Fast range `_reindexlinear`, line 328. -/
def m328 (multiply : Int → R → JResult M) (add : Int → M → JResult O)
    (offset stride : Int) (range : R) : JResult O := do
  let scaled ← multiply stride range
  add offset scaled
def P328 : Prop := ∀ {R M O : Type} (multiply : Int → R → JResult M)
    (add : Int → M → JResult O) offset stride range,
  m328 multiply add offset stride range = do let scaled ← multiply stride range; add offset scaled
theorem p328 : P328 := by unfold P328; intros; rfl

/-- Fast-contiguous range `_reindexlinear`, line 352. -/
def m352 (add : Int → R → JResult O) (offset : Int) (range : R) : JResult O := add offset range
def P352 : Prop := ∀ {R O : Type} (add : Int → R → JResult O) offset range,
  m352 add offset range = add offset range
theorem p352 : P352 := by unfold P352; intros; rfl

/-- Fast-contiguous one-based-range `getindex`, lines 376-380. -/
def m376 (checkbounds : V → R → JResult Unit) (reindexLinear : V → R → JResult PR)
    (parent : V → P) (getindex : P → PR → JResult T) (view : V) (range : R) : JResult T := do
  checkbounds view range
  let shifted ← reindexLinear view range
  getindex (parent view) shifted
def P376 : Prop := ∀ {V R PR P T : Type} (checkbounds : V → R → JResult Unit)
    (reindexLinear : V → R → JResult PR) (parent : V → P)
    (getindex : P → PR → JResult T) view range,
  m376 checkbounds reindexLinear parent getindex view range = do
    checkbounds view range
    let shifted ← reindexLinear view range
    getindex (parent view) shifted
theorem p376 : P376 := by unfold P376; intros; rfl

/-- General SubArray `setindex!`, lines 386-390. -/
def m386 (checkbounds : V → List Int → JResult Unit) (storedIndices : V → PI)
    (reindex : PI → List Int → JResult RI) (parent : V → P)
    (setindex : P → X → RI → JResult Unit) (view : V) (value : X)
    (indices : List Int) : JResult V := do
  checkbounds view indices
  let combined ← reindex (storedIndices view) indices
  setindex (parent view) value combined
  .ok view
def P386 : Prop := ∀ {V PI RI P X : Type} (checkbounds : V → List Int → JResult Unit)
    (storedIndices : V → PI) (reindex : PI → List Int → JResult RI) (parent : V → P)
    (setindex : P → X → RI → JResult Unit) view value indices,
  m386 checkbounds storedIndices reindex parent setindex view value indices = do
    checkbounds view indices
    let combined ← reindex (storedIndices view) indices
    setindex (parent view) value combined
    .ok view
theorem p386 : P386 := by unfold P386; intros; rfl

/-- Fast SubArray scalar `setindex!`, lines 392-396. -/
def m392 (checkbounds : V → Int → JResult Unit) (reindexLinear : V → Int → JResult PI)
    (parent : V → P) (setindex : P → X → PI → JResult Unit)
    (view : V) (value : X) (index : Int) : JResult V := do
  checkbounds view index
  let shifted ← reindexLinear view index
  setindex (parent view) value shifted
  .ok view
def P392 : Prop := ∀ {V PI P X : Type} (checkbounds : V → Int → JResult Unit)
    (reindexLinear : V → Int → JResult PI) (parent : V → P)
    (setindex : P → X → PI → JResult Unit) view value index,
  m392 checkbounds reindexLinear parent setindex view value index = do
    checkbounds view index
    let shifted ← reindexLinear view index
    setindex (parent view) value shifted
    .ok view
theorem p392 : P392 := by unfold P392; intros; rfl

/-- One-dimensional fast SubArray scalar `setindex!`, lines 398-402. -/
def m398 := @m392
def P398 : Prop := ∀ {V PI P X : Type} (checkbounds : V → Int → JResult Unit)
    (reindexLinear : V → Int → JResult PI) (parent : V → P)
    (setindex : P → X → PI → JResult Unit) view value index,
  m398 checkbounds reindexLinear parent setindex view value index =
    m392 checkbounds reindexLinear parent setindex view value index
theorem p398 : P398 := by unfold P398; intros; rfl

/-- Fast SubArray range `setindex!`, lines 405-409. -/
def m405 (checkbounds : V → R → JResult Unit) (reindexLinear : V → R → JResult PI)
    (parent : V → P) (setindex : P → X → PI → JResult Unit)
    (view : V) (value : X) (range : R) : JResult V := do
  checkbounds view range
  let shifted ← reindexLinear view range
  setindex (parent view) value shifted
  .ok view
def P405 : Prop := ∀ {V R PI P X : Type} (checkbounds : V → R → JResult Unit)
    (reindexLinear : V → R → JResult PI) (parent : V → P)
    (setindex : P → X → PI → JResult Unit) view value range,
  m405 checkbounds reindexLinear parent setindex view value range = do
    checkbounds view range
    let shifted ← reindexLinear view range
    setindex (parent view) value shifted
    .ok view
theorem p405 : P405 := by unfold P405; intros; rfl

/-- General SubArray `isassigned`, lines 414-418. -/
def m414 (checkbounds : V → List Int → JResult Bool) (storedIndices : V → PI)
    (reindex : PI → List Int → JResult RI) (parent : V → P)
    (isassigned : P → RI → JResult Bool) (view : V) (indices : List Int) : JResult Bool := do
  let inBounds ← checkbounds view indices
  if ¬inBounds then .ok false
  else do
    let combined ← reindex (storedIndices view) indices
    isassigned (parent view) combined
def P414 : Prop := ∀ {V PI RI P : Type} (checkbounds : V → List Int → JResult Bool)
    (storedIndices : V → PI) (reindex : PI → List Int → JResult RI) (parent : V → P)
    (isassigned : P → RI → JResult Bool) view indices,
  m414 checkbounds storedIndices reindex parent isassigned view indices = do
    let inBounds ← checkbounds view indices
    if ¬inBounds then .ok false
    else do
      let combined ← reindex (storedIndices view) indices
      isassigned (parent view) combined
theorem p414 : P414 := by unfold P414; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-subarray-faithful-{line}", juliaFile := "base/subarray.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry 257 "unsafe_view(AbstractArray,indices...)" "Unsafe view delegates the actual array and complete ViewIndex tuple to SubArray construction." "base/subarray.jl:257-259" ``P257 ``p257,
  entry 273 "_maybe_reindex(CartesianIndex{1} array)" "The scan computes tail of the actual tuple before recursion." "base/subarray.jl:273-274" ``P273 ``p273,
  entry 275 "_maybe_reindex(any tuple)" "The general scan computes tail of the actual tuple before recursion." "base/subarray.jl:275" ``P275 ``p275,
  entry 276 "_maybe_reindex(empty scan)" "Terminal reindexing uses the actual stored indices and parent, converts the combined indices, then constructs one SubArray layer." "base/subarray.jl:276-279" ``P276 ``p276,
  entry 295 "reindex(scalar parent index)" "A scalar parent index is preserved and recursion consumes no subindex." "base/subarray.jl:295-296" ``P295 ``p295,
  entry 299 "reindex(Slice parent index)" "A Slice passes the actual subindex through and recursion consumes one subindex." "base/subarray.jl:299-300" ``P299 ``p299,
  entry 303 "reindex(vector parent index)" "Vector reindexing performs the actual lookup with any subindex before recursive tail composition." "base/subarray.jl:303-304" ``P303 ``p303,
  entry 307 "reindex(matrix parent index)" "Matrix reindexing performs the actual two-index lookup and consumes exactly two subindices." "base/subarray.jl:307-308" ``P307 ``p307,
  entry 311 "reindex(N-dimensional parent index)" "General array reindexing splits the actual subindices at rank, indexes with the prefix and recurses on the suffix." "base/subarray.jl:311-312" ``P311 ``p311,
  entry 316 "getindex(SubArray,Int...)" "General SubArray indexing checks bounds, fully reindexes and looks up the actual parent with complete error propagation." "base/subarray.jl:316-320" ``P316 ``p316,
  entry 328 "_reindexlinear(FastSubArray,range)" "Fast range reindexing broadcasts stride multiplication then offset addition while preserving the range result." "base/subarray.jl:328" ``P328 ``p328,
  entry 352 "_reindexlinear(FastContiguousSubArray,range)" "Contiguous range reindexing adds the cached offset to the actual range object." "base/subarray.jl:352" ``P352 ``p352,
  entry 376 "getindex(FastContiguousSubArray,one-based range)" "Contiguous range indexing checks bounds, preserves the shifted range object and indexes the actual parent." "base/subarray.jl:376-380" ``P376 ``p376,
  entry 386 "setindex!(SubArray,Int...)" "General assignment checks bounds, fully reindexes, propagates parent-write failure and returns the view only after success." "base/subarray.jl:386-390" ``P386 ``p386,
  entry 392 "setindex!(FastSubArray,Int)" "Fast scalar assignment checks bounds, shifts the index, propagates the parent write and returns the view." "base/subarray.jl:392-396" ``P392 ``p392,
  entry 398 "setindex!(FastSubArray{N=1},Int)" "The one-dimensional specialization has the complete fast scalar assignment behavior." "base/subarray.jl:398-402" ``P398 ``p398,
  entry 405 "setindex!(FastSubArray,range)" "Fast range assignment preserves the range object through bounds, shifting and parent write, returning the view only after success." "base/subarray.jl:405-409" ``P405 ``p405,
  entry 414 "isassigned(SubArray,Int...)" "General isassigned returns false after a failed bounds predicate and otherwise fully reindexes and delegates to the actual parent." "base/subarray.jl:414-418" ``P414 ``p414
]

end JuliaLean.MultidimCov.SubarrayFaithfulB
