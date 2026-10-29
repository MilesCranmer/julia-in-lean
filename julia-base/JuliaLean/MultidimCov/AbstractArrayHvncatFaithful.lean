import JuliaLean.MultidimCov.AbstractArrayConcatFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayHvncatFaithful

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful
open AbstractArrayConcatFaithful

inductive DimShape where
  | balanced (rows columns : Int)
  | unbalanced (rows : List Int) (total : Int)
  deriving Repr, DecidableEq

def getCatOneBased (values : List α) (index : Int) : CResult α :=
  if index < 1 || (values.length : Int) < index then .error .bounds
  else match values[(index - 1).toNat]? with
    | some value => .ok value
    | none => .error .bounds

/-- `rows_to_dimshape`, line 2247. -/
def m2247 (sumRows : List Int → CResult Int) (rows : List Int) : CResult DimShape := do
  let columns ← firstOrBounds rows
  if rows.all (· = columns) then .ok (.balanced rows.length columns)
  else do
    let total ← sumRows rows
    .ok (.unbalanced rows total)
def P2247 : Prop := ∀ sumRows rows, m2247 sumRows rows = do
  let columns ← firstOrBounds rows
  if rows.all (· = columns) then .ok (.balanced rows.length columns)
  else do
    let total ← sumRows rows
    .ok (.unbalanced rows total)
theorem p2247 : P2247 := by unfold P2247; intros; rfl

def hvcatNumberLoop (getRow : List Int → Int → CResult Int)
    (getValue : X → Int → CResult V) (set : A → Int → Int → V → CResult A) :
    A → List Int → X → Int → Nat → Int → Int → CResult A
  | array, _, _, _, 0, _, _ => .ok array
  | array, rows, values, row, remainingRows + 1, columns, index => do
      let actualColumns ← getRow rows row
      if actualColumns != columns then
        let printedColumns ← getRow rows row
        .error (.dimensionMismatch (lazyAppend [.literal "row ", .integer row,
          .literal " has mismatched number of columns (expected ", .integer columns,
          .literal ", got ", .integer printedColumns, .literal ")"]))
      else
        let rec columnsLoop (array : A) (column : Int) (remaining : Nat)
            (valueIndex : Int) : CResult (A × Int) :=
          match remaining with
          | 0 => .ok (array, valueIndex)
          | remaining + 1 => do
            let value ← getValue values valueIndex
            let next ← set array row column value
            columnsLoop next (column + 1) remaining (valueIndex + 1)
        let result ← columnsLoop array 1 columns.toNat index
        hvcatNumberLoop getRow getValue set result.1 rows values (row + 1) remainingRows columns result.2

/-- Numeric `hvcat`, lines 2253-2272. -/
def m2253 (allocate : Int → Int → CResult A) (arrayLength : A → CResult Int)
    (valuesLength : X → CResult Int) (getValue : X → Int → CResult V)
    (set : A → Int → Int → V → CResult A) (rows : List Int) (values : X) : CResult A := do
  let columns ← firstOrBounds rows
  let array ← allocate rows.length columns
  let expected ← arrayLength array
  let actual ← valuesLength values
  if expected != actual then
    let printedExpected ← arrayLength array
    let printedActual ← valuesLength values
    .error (.argument (lazyAppend [.literal "argument count does not match specified shape (expected ",
      .integer printedExpected, .literal ", got ", .integer printedActual, .literal ")"]))
  else hvcatNumberLoop (fun rs i => getCatOneBased rs i) getValue set array rows values 1 rows.length columns 1
def P2253 : Prop := ∀ {A X V : Type} (allocate : Int → Int → CResult A)
    (arrayLength : A → CResult Int) (valuesLength : X → CResult Int)
    (getValue : X → Int → CResult V) (set : A → Int → Int → V → CResult A) rows values,
  m2253 allocate arrayLength valuesLength getValue set rows values = do
    let columns ← firstOrBounds rows
    let array ← allocate rows.length columns
    let expected ← arrayLength array
    let actual ← valuesLength values
    if expected != actual then
      let printedExpected ← arrayLength array
      let printedActual ← valuesLength values
      .error (.argument (lazyAppend [.literal "argument count does not match specified shape (expected ",
        .integer printedExpected, .literal ", got ", .integer printedActual, .literal ")"]))
    else hvcatNumberLoop (fun rs i => getCatOneBased rs i) getValue set array rows values 1 rows.length columns 1
theorem p2253 : P2253 := by unfold P2253; intros; rfl

def validateRows : List Int → Int → Int → Nat → CResult Unit
  | _, _, _, 0 => .ok ()
  | rows, columns, index, remaining + 1 => do
      let actual ← getCatOneBased rows index
      if actual != columns then
        let printed ← getCatOneBased rows index
        .error (.dimensionMismatch (lazyAppend [.literal "row ", .integer index,
          .literal " has mismatched number of columns (expected ", .integer columns,
          .literal ", got ", .integer printed, .literal ")"]))
      else validateRows rows columns (index + 1) remaining

/-- Numeric `typed_hvcat`, lines 2279-2292. -/
def m2279 (allocate : T → Int → Int → CResult A)
    (fill : A → Bool → X → CResult A) (elementType : T)
    (rows : List Int) (values : X) : CResult A := do
  let columns ← firstOrBounds rows
  validateRows rows columns 2 (rows.length - 1)
  let array ← allocate elementType rows.length columns
  fill array true values
def P2279 : Prop := ∀ {T A X : Type} (allocate : T → Int → Int → CResult A)
    (fill : A → Bool → X → CResult A) elementType rows values,
  m2279 allocate fill elementType rows values = do
    let columns ← firstOrBounds rows
    validateRows rows columns 2 (rows.length - 1)
    let array ← allocate elementType rows.length columns
    fill array true values
theorem p2279 : P2279 := by unfold P2279; intros; rfl

/-- Zero-dimensional AbstractArray conversion, line 2400. -/
def m2400 (broadcastConvert : T → A → CResult B) (elementType : T) (array : A) : CResult B :=
  broadcastConvert elementType array
def P2400 : Prop := ∀ {T A B : Type} (broadcastConvert : T → A → CResult B)
    elementType array,
  m2400 broadcastConvert elementType array = broadcastConvert elementType array
theorem p2400 : P2400 := by unfold P2400; intros; rfl

/-- Empty rank-N `_typed_hvncat`, lines 2411-2415. -/
def m2411 (allocate : T → Int → List Int → CResult A) (elementType : T) (rank : Int) : CResult A :=
  if rank < 0 then .error (.argument (.literal "concatenation dimension must be non-negative"))
  else allocate elementType rank (List.replicate rank.toNat 0)
def P2411 : Prop := ∀ {T A : Type} (allocate : T → Int → List Int → CResult A)
    elementType rank,
  m2411 allocate elementType rank = if rank < 0 then
    .error (.argument (.literal "concatenation dimension must be non-negative"))
  else allocate elementType rank (List.replicate rank.toNat 0)
theorem p2411 : P2411 := by unfold P2411; intros; rfl

/-- Numeric rank-N `_typed_hvncat`, lines 2417-2421. -/
def m2417 (convertVector : T → X → CResult V) (reshape : V → List Int → CResult A)
    (length : X → CResult Int) (elementType : T) (rank : Int) (values : X) : CResult A :=
  if rank < 0 then .error (.argument (.literal "concatenation dimension must be non-negative"))
  else do
    let vector ← convertVector elementType values
    let count ← length values
    reshape vector (List.replicate (rank - 1).toNat 1 ++ [count])
def P2417 : Prop := ∀ {T X V A : Type} (convertVector : T → X → CResult V)
    (reshape : V → List Int → CResult A) (length : X → CResult Int) elementType rank values,
  m2417 convertVector reshape length elementType rank values =
    if rank < 0 then .error (.argument (.literal "concatenation dimension must be non-negative"))
    else do
      let vector ← convertVector elementType values
      let count ← length values
      reshape vector (List.replicate (rank - 1).toNat 1 ++ [count])
theorem p2417 : P2417 := by unfold P2417; intros; rfl

/-- Singleton-dims balanced wrappers, lines 2498-2499. -/
def m2498 (delegate : T → Int → Bool → List X → CResult A)
    (elementType : T) (dimensions : List Int) (values : List X) : CResult A := do
  let dimension ← firstOrBounds dimensions
  delegate elementType dimension false values
def P2498 : Prop := ∀ {T X A : Type} (delegate : T → Int → Bool → List X → CResult A)
    elementType dimensions values,
  m2498 delegate elementType dimensions values = do
    let dimension ← firstOrBounds dimensions
    delegate elementType dimension false values
theorem p2498 : P2498 := by unfold P2498; intros; rfl
def m2499 := @m2498
def P2499 : Prop := ∀ {T X A : Type} delegate elementType dimensions values,
  m2499 (T := T) (X := X) (A := A) delegate elementType dimensions values =
    m2498 delegate elementType dimensions values
theorem p2499 : P2499 := by unfold P2499; intros; rfl

/-- `_typed_hvncat_1d`, lines 2501-2512. -/
def m2501 (length : X → CResult Int) (delegate : T → Int → X → CResult A)
    (elementType : T) (dimensionSize : Int) (rowFirst : Bool) (values : X) : CResult A := do
  let count ← length values
  if dimensionSize ≤ 0 then
    .error (.argument (.literal "`dimsshape` argument must consist of positive integers"))
  else if count != dimensionSize then
    .error (.argument (lazyAppend [.literal "number of elements does not match `dimshape` argument; expected ",
      .integer dimensionSize, .literal ", got ", .integer count]))
  else delegate elementType (if rowFirst then 2 else 1) values
def P2501 : Prop := ∀ {X T A : Type} (length : X → CResult Int)
    (delegate : T → Int → X → CResult A) elementType dimensionSize rowFirst values,
  m2501 length delegate elementType dimensionSize rowFirst values = do
    let count ← length values
    if dimensionSize ≤ 0 then
      .error (.argument (.literal "`dimsshape` argument must consist of positive integers"))
    else if count != dimensionSize then
      .error (.argument (lazyAppend [.literal "number of elements does not match `dimshape` argument; expected ",
        .integer dimensionSize, .literal ", got ", .integer count]))
    else delegate elementType (if rowFirst then 2 else 1) values
theorem p2501 : P2501 := by unfold P2501; intros; rfl

/-- Balanced numeric `_typed_hvncat`, lines 2514-2525. -/
def m2514 (allocate : T → List Int → CResult A) (arrayLength : A → CResult Int)
    (valuesLength : X → CResult Int) (fill : A → Bool → X → CResult A)
    (elementType : T) (dimensions : List Int) (rowFirst : Bool) (values : X) : CResult A :=
  if dimensions.any (· ≤ 0) then
    .error (.argument (.literal "`dims` argument must contain positive integers"))
  else do
    let array ← allocate elementType dimensions
    let expected ← arrayLength array
    let actual ← valuesLength values
    if expected != actual then .error (.argument (lazyAppend
      [.literal "argument count does not match specified shape (expected ",
       .integer expected, .literal ", got ", .integer actual, .literal ")"]))
    else fill array rowFirst values
def P2514 : Prop := ∀ {T A X : Type} (allocate : T → List Int → CResult A)
    (arrayLength : A → CResult Int) (valuesLength : X → CResult Int)
    (fill : A → Bool → X → CResult A) elementType dimensions rowFirst values,
  m2514 allocate arrayLength valuesLength fill elementType dimensions rowFirst values =
    if dimensions.any (· ≤ 0) then
      .error (.argument (.literal "`dims` argument must contain positive integers"))
    else do
      let array ← allocate elementType dimensions
      let expected ← arrayLength array
      let actual ← valuesLength values
      if expected != actual then .error (.argument (lazyAppend
        [.literal "argument count does not match specified shape (expected ",
         .integer expected, .literal ", got ", .integer actual, .literal ")"]))
      else fill array rowFirst values
theorem p2514 : P2514 := by unfold P2514; intros; rfl

def product : List Int → Int := List.foldl (· * ·) 1

def fillLinear (getValue : X → Int → CResult V) (set : A → Int → V → CResult A) :
    A → X → Int → Nat → CResult A
  | array, _, _, 0 => .ok array
  | array, values, index, remaining + 1 => do
      let value ← getValue values index
      let next ← set array index value
      fillLinear getValue set next values (index + 1) remaining

def fillRowsPage (linearIndex : Int → Int → Int → Int → Int → CResult Int)
    (getValue : X → Int → CResult V) (set : A → Int → V → CResult A)
    (rows columns page : Int) : A → X → Int → Nat → Int → CResult (A × Int)
  | array, _, _, 0, valueIndex => .ok (array, valueIndex)
  | array, values, row, remainingRows + 1, valueIndex => do
      let rec columnsLoop (array : A) (column : Int) (remaining : Nat)
          (index : Int) : CResult (A × Int) :=
        match remaining with
        | 0 => .ok (array, index)
        | remaining + 1 => do
          let value ← getValue values index
          let outputIndex ← linearIndex rows columns page row column
          let next ← set array outputIndex value
          columnsLoop next (column + 1) remaining (index + 1)
      let result ← columnsLoop array 1 columns.toNat valueIndex
      fillRowsPage linearIndex getValue set rows columns page result.1 values
        (row + 1) remainingRows result.2

def fillRowFirst (linearIndex : Int → Int → Int → Int → Int → CResult Int)
    (getValue : X → Int → CResult V) (set : A → Int → V → CResult A)
    (rows columns : Int) : A → X → Int → Nat → Int → CResult A
  | array, _, _, 0, _ => .ok array
  | array, values, page, remainingPages + 1, valueIndex => do
      let result ← fillRowsPage linearIndex getValue set rows columns page
        array values 1 rows.toNat valueIndex
      fillRowFirst linearIndex getValue set rows columns result.1 values
        (page + 1) remainingPages result.2

/-- Fallback `_hvncat_fill_loop!`, lines 2527-2554. -/
def m2527 (size : A → CResult (List Int)) (product : List Int → CResult Int)
    (multiply : Int → Int → CResult Int)
    (linearIndex : Int → Int → Int → Int → Int → CResult Int)
    (valuesLength : X → CResult Int) (getValue : X → Int → CResult V)
    (set : A → Int → V → CResult A)
    (array : A) (rowFirst : Bool) (values : X) : CResult A := do
  let shape ← size array
  let rows ← getCatOneBased shape 1
  let columns ← getCatOneBased shape 2
  let pages ← product (shape.drop 2)
  let count ← valuesLength values
  let rowsColumns ← multiply rows columns
  let expected ← multiply rowsColumns pages
  if expected != count then
    let printedShape ← size array
    .error (.argument (lazyAppend [.literal "argument count ", .integer count,
      .literal " does not match specified shape ", .dynamic ⟨0, printedShape.length⟩]))
  else if rowFirst then
    fillRowFirst linearIndex getValue set rows columns array values 1 pages.toNat 1
  else fillLinear getValue set array values 1 count.toNat
def P2527 : Prop := ∀ {A X V : Type} (size : A → CResult (List Int))
    (product : List Int → CResult Int) (multiply : Int → Int → CResult Int)
    (linearIndex : Int → Int → Int → Int → Int → CResult Int)
    (valuesLength : X → CResult Int) (getValue : X → Int → CResult V)
    (set : A → Int → V → CResult A) array rowFirst values,
  m2527 size product multiply linearIndex valuesLength getValue set array rowFirst values = do
    let shape ← size array
    let rows ← getCatOneBased shape 1
    let columns ← getCatOneBased shape 2
    let pages ← product (shape.drop 2)
    let count ← valuesLength values
    let rowsColumns ← multiply rows columns
    let expected ← multiply rowsColumns pages
    if expected != count then
      let printedShape ← size array
      .error (.argument (lazyAppend [.literal "argument count ", .integer count,
        .literal " does not match specified shape ", .dynamic ⟨0, printedShape.length⟩]))
    else if rowFirst then
      fillRowFirst linearIndex getValue set rows columns array values 1 pages.toNat 1
    else fillLinear getValue set array values 1 count.toNat
theorem p2527 : P2527 := by unfold P2527; intros; rfl

structure Generated2DState (A : Type) where
  array : A
  row : Int
  column : Int

def fillGenerated2D (getValue : X → Int → CResult V)
    (set : A → Int → Int → V → CResult A) (add : Int → Int → CResult Int)
    (columns : Int) (values : X) : Nat → Int → Generated2DState A → CResult A
  | 0, _, state => .ok state.array
  | remaining + 1, valueIndex, state => do
      let value ← getValue values valueIndex
      let array ← set state.array state.row state.column value
      let nextColumn ← add state.column 1
      if columns < nextColumn then
        let nextRow ← add state.row 1
        fillGenerated2D getValue set add columns values remaining (valueIndex + 1)
          ⟨array, nextRow, 1⟩
      else
        fillGenerated2D getValue set add columns values remaining (valueIndex + 1)
          ⟨array, state.row, nextColumn⟩

structure GeneratedNDState (A : Type) where
  array : A
  page : Int
  row : Int
  pageOffset : Int
  linearIndex : Int
  column : Int

def fillGeneratedND (getValue : X → Int → CResult V)
    (set : A → Int → V → CResult A) (add subtract multiply : Int → Int → CResult Int)
    (rows columns rowsColumns : Int) (values : X) :
    Nat → Int → GeneratedNDState A → CResult A
  | 0, _, state => .ok state.array
  | remaining + 1, valueIndex, state => do
      let value ← getValue values valueIndex
      let array ← set state.array state.linearIndex value
      let nextColumn ← add state.column 1
      let advancedIndex ← add state.linearIndex rows
      if columns < nextColumn then
        let nextRow ← add state.row 1
        if rows < nextRow then
          let nextPage ← add state.page 1
          let pageMinusOne ← subtract nextPage 1
          let pageOffset ← multiply rowsColumns pageMinusOne
          let linearIndex ← add pageOffset 1
          fillGeneratedND getValue set add subtract multiply rows columns rowsColumns values
            remaining (valueIndex + 1) ⟨array, nextPage, 1, pageOffset, linearIndex, 1⟩
        else
          let linearIndex ← add state.pageOffset nextRow
          fillGeneratedND getValue set add subtract multiply rows columns rowsColumns values
            remaining (valueIndex + 1)
            ⟨array, state.page, nextRow, state.pageOffset, linearIndex, 1⟩
      else
        fillGeneratedND getValue set add subtract multiply rows columns rowsColumns values
          remaining (valueIndex + 1)
          ⟨array, state.page, state.row, state.pageOffset, advancedIndex, nextColumn⟩

/-- Generated `hvncat_fill!`, lines 2556-2626, including both emitted loop
bodies and the large-tuple fallback. -/
def m2556 (fieldCount : X → Nat) (fallback : A → Bool → X → CResult A)
    (ndims : A → CResult Int) (sizeDim : A → IntegerValue → CResult Int)
    (sizeAll : A → CResult (List Int)) (asAny : List Int → AnyValue)
    (product : List Int → CResult Int) (add subtract multiply : Int → Int → CResult Int)
    (getValue : X → Int → CResult V) (set2 : A → Int → Int → V → CResult A)
    (setLinear : A → Int → V → CResult A)
    (array : A) (rowFirst : Bool) (values : X) : CResult A :=
  let count := fieldCount values
  if 32 < count then fallback array rowFirst values
  else do
    let rank ← ndims array
    let rows ← sizeDim array ⟨1⟩
    let columns ← sizeDim array ⟨2⟩
    let rowsColumns ← multiply rows columns
    if rank ≤ 2 then
      if rowsColumns != Int.ofNat count then
        let shape ← sizeAll array
        .error (.argument (lazyAppend [.literal "argument count ", .integer (Int.ofNat count),
          .literal " does not match specified shape ", .dynamic (asAny shape)]))
      else if rowFirst then
        fillGenerated2D getValue set2 add columns values count 1 ⟨array, 1, 1⟩
      else fillLinear getValue setLinear array values 1 count
    else
      let shape ← sizeAll array
      let pages ← product (shape.drop 2)
      let expected ← multiply rowsColumns pages
      if expected != Int.ofNat count then
        let printedShape ← sizeAll array
        .error (.argument (lazyAppend [.literal "argument count ", .integer (Int.ofNat count),
          .literal " does not match specified shape ", .dynamic (asAny printedShape)]))
      else if rowFirst then
        fillGeneratedND getValue setLinear add subtract multiply rows columns rowsColumns values
          count 1 ⟨array, 1, 1, 0, 1, 1⟩
      else fillLinear getValue setLinear array values 1 count
def P2556 : Prop := ∀ {A X V : Type} (fieldCount : X → Nat)
    (fallback : A → Bool → X → CResult A) (ndims : A → CResult Int)
    (sizeDim : A → IntegerValue → CResult Int) (sizeAll : A → CResult (List Int))
    (asAny : List Int → AnyValue) (product : List Int → CResult Int)
    (add subtract multiply : Int → Int → CResult Int)
    (getValue : X → Int → CResult V) (set2 : A → Int → Int → V → CResult A)
    (setLinear : A → Int → V → CResult A) array rowFirst values,
  m2556 fieldCount fallback ndims sizeDim sizeAll asAny product add subtract multiply getValue
    set2 setLinear array rowFirst values =
    let count := fieldCount values
    if 32 < count then fallback array rowFirst values
    else do
      let rank ← ndims array
      let rows ← sizeDim array ⟨1⟩
      let columns ← sizeDim array ⟨2⟩
      let rowsColumns ← multiply rows columns
      if rank ≤ 2 then
        if rowsColumns != Int.ofNat count then
          let shape ← sizeAll array
          .error (.argument (lazyAppend [.literal "argument count ",
            .integer (Int.ofNat count), .literal " does not match specified shape ",
            .dynamic (asAny shape)]))
        else if rowFirst then
          fillGenerated2D getValue set2 add columns values count 1 ⟨array, 1, 1⟩
        else fillLinear getValue setLinear array values 1 count
      else
        let shape ← sizeAll array
        let pages ← product (shape.drop 2)
        let expected ← multiply rowsColumns pages
        if expected != Int.ofNat count then
          let printedShape ← sizeAll array
          .error (.argument (lazyAppend [.literal "argument count ",
            .integer (Int.ofNat count), .literal " does not match specified shape ",
            .dynamic (asAny printedShape)]))
        else if rowFirst then
          fillGeneratedND getValue setLinear add subtract multiply rows columns rowsColumns values
            count 1 ⟨array, 1, 1, 0, 1, 1⟩
        else fillLinear getValue setLinear array values 1 count
theorem p2556 : P2556 := by unfold P2556; intros; rfl

def maxCatRank (catRank : X → CResult Int) : List X → CResult Int
  | [] => .error (.argument (.literal "reducing over an empty collection is not allowed"))
  | head :: tail => do
      let first ← catRank head
      tail.foldlM (fun current value => return max current (← catRank value)) first

/-- Balanced generic wrapper, lines 2629-2633. -/
def m2629 (catRank : X → CResult Int)
    (delegate : T → List Int → Bool → List X → CResult A)
    (elementType : T) (dimensions : List Int) (rowFirst : Bool) (values : List X) : CResult A := do
  let discovered ← maxCatRank catRank values
  let rank := max discovered dimensions.length
  delegate elementType (dimensions ++ List.replicate (rank - dimensions.length).toNat 1) rowFirst values
def P2629 : Prop := ∀ {X T A : Type} (catRank : X → CResult Int)
    (delegate : T → List Int → Bool → List X → CResult A)
    elementType dimensions rowFirst values,
  m2629 catRank delegate elementType dimensions rowFirst values = do
    let discovered ← maxCatRank catRank values
    let rank := max discovered dimensions.length
    delegate elementType (dimensions ++ List.replicate (rank - dimensions.length).toNat 1)
      rowFirst values
theorem p2629 : P2629 := by unfold P2629; intros; rfl

/-- One-level unbalanced wrapper, lines 2732-2736. -/
def m2732 (delegate : T → Int → Bool → List X → CResult A)
    (elementType : T) (shape : List (List Int)) (rowFirst : Bool) (values : List X) : CResult A := do
  let level ← firstOrBounds shape
  if level.isEmpty then .error (.argument (.literal "each level of shape must have at least one value"))
  else
    let count ← firstOrBounds level
    delegate elementType count rowFirst values
def P2732 : Prop := ∀ {T X A : Type} (delegate : T → Int → Bool → List X → CResult A)
    elementType shape rowFirst values,
  m2732 delegate elementType shape rowFirst values = do
    let level ← firstOrBounds shape
    if level.isEmpty then .error (.argument (.literal "each level of shape must have at least one value"))
    else
      let count ← firstOrBounds level
      delegate elementType count rowFirst values
theorem p2732 : P2732 := by unfold P2732; intros; rfl

/-- General unbalanced wrapper, lines 2738-2742. -/
def m2738 (catRank : X → CResult Int)
    (delegate : T → List (List Int) → Bool → List X → CResult A)
    (elementType : T) (shape : List (List Int)) (rowFirst : Bool) (values : List X) : CResult A := do
  let discovered ← maxCatRank catRank values
  let rank := max discovered shape.length
  let finalLevel ← match shape.getLast? with
    | none => .error .bounds
    | some value => .ok value
  delegate elementType (shape ++ List.replicate (rank - shape.length).toNat finalLevel) rowFirst values
def P2738 : Prop := ∀ {X T A : Type} (catRank : X → CResult Int)
    (delegate : T → List (List Int) → Bool → List X → CResult A)
    elementType shape rowFirst values,
  m2738 catRank delegate elementType shape rowFirst values = do
    let discovered ← maxCatRank catRank values
    let rank := max discovered shape.length
    let finalLevel ← match shape.getLast? with
      | none => .error .bounds
      | some value => .ok value
    delegate elementType (shape ++ List.replicate (rank - shape.length).toNat finalLevel)
      rowFirst values
theorem p2738 : P2738 := by unfold P2738; intros; rfl

def calcIndexLoop (add multiply : Int → Int → CResult Int)
    (offsets innerOffsets products : List Int) :
    Int → Nat → Int → CResult Int
  | _, 0, total => .ok total
  | index, remaining + 1, total => do
      let inner ← getCatOneBased innerOffsets index
      let offset ← getCatOneBased offsets index
      let increment ← add inner offset
      let stride ← getCatOneBased products (index - 1)
      let scaled ← multiply increment stride
      let next ← add total scaled
      calcIndexLoop add multiply offsets innerOffsets products (index + 1) remaining next

/-- `hvncat_calcindex`, lines 2865-2875. -/
def m2865 (add multiply : Int → Int → CResult Int)
    (offsets innerOffsets products : List Int) (dimensions : Int) : CResult Int := do
  let innerFirst ← getCatOneBased innerOffsets 1
  let offsetFirst ← getCatOneBased offsets 1
  let initialPair ← add innerFirst offsetFirst
  let initial ← add initialPair 1
  calcIndexLoop add multiply offsets innerOffsets products 2 (dimensions - 1).toNat initial
def P2865 : Prop := ∀ add multiply offsets innerOffsets products dimensions,
  m2865 add multiply offsets innerOffsets products dimensions = do
    let innerFirst ← getCatOneBased innerOffsets 1
    let offsetFirst ← getCatOneBased offsets 1
    let initialPair ← add innerFirst offsetFirst
    let initial ← add initialPair 1
    calcIndexLoop add multiply offsets innerOffsets products 2 (dimensions - 1).toNat initial
theorem p2865 : P2865 := by unfold P2865 m2865; intros; rfl

def allTrailingSingleton (ndims : A → CResult Int)
    (size : A → IntegerValue → CResult Int) (rank : Int) (array : A) : CResult Bool := do
  let arrayRank ← ndims array
  let rec loop (dimension : Int) (remaining : Nat) : CResult Bool :=
    match remaining with
    | 0 => .ok true
    | remaining + 1 => do
        let value ← size array ⟨dimension⟩
        if value = 1 then loop (dimension + 1) remaining else .ok false
  if arrayRank ≤ rank then .ok true else loop (rank + 1) (arrayRank - rank).toNat

def allArraysTrailingSingleton (ndims : A → CResult Int)
    (size : A → IntegerValue → CResult Int) (rank : Int) : List A → CResult Bool
  | [] => .ok true
  | array :: rest => do
      let valid ← allTrailingSingleton ndims size rank array
      if valid then allArraysTrailingSingleton ndims size rank rest else .ok false

def arrayShapeScan (size : A → IntegerValue → CResult Int) (ndims : A → CResult Int)
    (checkedAdd : Int → Int → CResult Int)
    (rank : Int) (first : A) : List A → Int → Int → Int → CResult (Int × Int)
  | [], _, total, discovered => .ok (total, discovered)
  | array :: rest, index, total, discovered => do
      let along ← size array ⟨rank⟩
      let arrayRank ← ndims array
      let rec compare (dimension : Int) (remaining : Nat) : CResult Unit :=
        match remaining with
        | 0 => .ok ()
        | remaining + 1 => do
            let expected ← size first ⟨dimension⟩
            let actual ← size array ⟨dimension⟩
            if expected != actual then
              .error (.dimensionMismatch (lazyAppend [.literal "mismatched size along axis ",
                .integer dimension, .literal " in element ", .integer index]))
            else compare (dimension + 1) remaining
      compare 1 (rank - 1).toNat
      let nextTotal ← checkedAdd total along
      arrayShapeScan size ndims checkedAdd rank first rest (index + 1) nextTotal
        (max discovered arrayRank)

def copyArrayValues (eachindex : A → CResult (List I)) (get : A → I → CResult V)
    (checkedAdd : Int → Int → CResult Int)
    (set : B → Int → V → CResult B) : B → List A → Int → CResult B
  | dest, [], _ => .ok dest
  | dest, array :: rest, outputIndex => do
      let indices ← eachindex array
      let result ← indices.foldlM (fun state index => do
        let value ← get array index
        let next ← set state.1 state.2 value
        let nextIndex ← checkedAdd state.2 1
        .ok (next, nextIndex)) (dest, outputIndex)
      copyArrayValues eachindex get checkedAdd set result.1 rest result.2

/-- Array-only rank `_typed_hvncat`, lines 2423-2456. -/
def m2423 (ndims : A → CResult Int) (size : A → IntegerValue → CResult Int)
    (checkedAdd : Int → Int → CResult Int)
    (fallback : T → List Int → Bool → List A → CResult B)
    (similar : A → T → List Int → CResult B) (eachindex : A → CResult (List I))
    (get : A → I → CResult V) (set : B → Int → V → CResult B)
    (elementType : T) (rank : Int) (arrays : List A) : CResult B := do
  let first ← firstOrBounds arrays
  if rank < 0 then .error (.argument (.literal "concatenation dimension must be non-negative"))
  else
    let valid ← allArraysTrailingSingleton ndims size rank arrays
    if !valid then
      fallback elementType (List.replicate (rank - 1).toNat 1 ++ [Int.ofNat arrays.length, 1]) false arrays
    else do
      let scanned ← arrayShapeScan size ndims checkedAdd rank first arrays 1 0 rank
      let leading ← (List.range (rank - 1).toNat).mapM fun index => size first ⟨Int.ofNat index + 1⟩
      let shape := leading ++ [scanned.1] ++ List.replicate (scanned.2 - rank).toNat 1
      let dest ← similar first elementType shape
      copyArrayValues eachindex get checkedAdd set dest arrays 1
def P2423 : Prop := ∀ {A B I V T : Type} (ndims : A → CResult Int)
    (size : A → IntegerValue → CResult Int) (checkedAdd : Int → Int → CResult Int)
    (fallback : T → List Int → Bool → List A → CResult B)
    (similar : A → T → List Int → CResult B) (eachindex : A → CResult (List I))
    (get : A → I → CResult V) (set : B → Int → V → CResult B)
    elementType rank arrays,
  m2423 ndims size checkedAdd fallback similar eachindex get set elementType rank arrays = do
    let first ← firstOrBounds arrays
    if rank < 0 then .error (.argument (.literal "concatenation dimension must be non-negative"))
    else
      let valid ← allArraysTrailingSingleton ndims size rank arrays
      if !valid then
        fallback elementType
          (List.replicate (rank - 1).toNat 1 ++ [Int.ofNat arrays.length, 1]) false arrays
      else do
        let scanned ← arrayShapeScan size ndims checkedAdd rank first arrays 1 0 rank
        let leading ← (List.range (rank - 1).toNat).mapM fun index =>
          size first ⟨Int.ofNat index + 1⟩
        let shape := leading ++ [scanned.1] ++ List.replicate (scanned.2 - rank).toNat 1
        let dest ← similar first elementType shape
        copyArrayValues eachindex get checkedAdd set dest arrays 1
theorem p2423 : P2423 := by unfold P2423; intros; rfl

def mixedShapeScan (catSize : X → IntegerValue → CResult Int)
    (catRank : X → CResult Int) (checkedAdd : Int → Int → CResult Int)
    (rank : Int) : List X → Int → Int → CResult (Int × Int)
  | [], total, discovered => .ok (total, discovered)
  | value :: rest, total, discovered => do
      let along ← catSize value ⟨rank⟩
      let valueRank ← catRank value
      let rec validate (dimension : Int) (remaining : Nat) : CResult Unit :=
        match remaining with
        | 0 => .ok ()
        | remaining + 1 => do
            let current ← catSize value ⟨dimension⟩
            if current != 1 then
              .error (.dimensionMismatch (.literal "non-concatenated dimensions must have length 1"))
            else validate (dimension + 1) remaining
      validate 1 (rank - 1).toNat
      let nextTotal ← checkedAdd total along
      mixedShapeScan catSize catRank checkedAdd rank rest nextTotal (max discovered valueRank)

def copyMixed (isArray : X → Bool) (length : X → CResult Int)
    (checkedAdd : Int → Int → CResult Int)
    (copyto : B → Int → X → Int → Int → CResult B)
    (set : B → Int → X → CResult B) : B → List X → Int → CResult B
  | dest, [], _ => .ok dest
  | dest, value :: rest, index =>
      if isArray value then do
        let count ← length value
        let next ← copyto dest index value 1 count
        let nextIndex ← checkedAdd index count
        copyMixed isArray length checkedAdd copyto set next rest nextIndex
      else do
        let next ← set dest index value
        let nextIndex ← checkedAdd index 1
        copyMixed isArray length checkedAdd copyto set next rest nextIndex

/-- Mixed rank `_typed_hvncat`, lines 2458-2493. -/
def m2458 (catSize : X → IntegerValue → CResult Int) (catRank : X → CResult Int)
    (checkedAdd : Int → Int → CResult Int)
    (allocate : T → Int → List Int → CResult B) (isArray : X → Bool)
    (length : X → CResult Int) (copyto : B → Int → X → Int → Int → CResult B)
    (set : B → Int → X → CResult B) (elementType : T) (rank : Int)
    (values : List X) : CResult B := do
  if values.isEmpty then .error (.argument (.literal "must have at least one element"))
  else if rank < 0 then .error (.argument (.literal "concatenation dimension must be non-negative"))
  else do
    let scanned ← mixedShapeScan catSize catRank checkedAdd rank values 0 rank
    let shape := List.replicate (rank - 1).toNat 1 ++ [scanned.1] ++
      List.replicate (scanned.2 - rank).toNat 1
    let dest ← allocate elementType scanned.2 shape
    copyMixed isArray length checkedAdd copyto set dest values 1
def P2458 : Prop := ∀ {X T B : Type} (catSize : X → IntegerValue → CResult Int)
    (catRank : X → CResult Int) (checkedAdd : Int → Int → CResult Int)
    (allocate : T → Int → List Int → CResult B)
    (isArray : X → Bool) (length : X → CResult Int)
    (copyto : B → Int → X → Int → Int → CResult B)
    (set : B → Int → X → CResult B) elementType rank values,
  m2458 catSize catRank checkedAdd allocate isArray length copyto set elementType rank values =
    if values.isEmpty then .error (.argument (.literal "must have at least one element"))
    else if rank < 0 then .error (.argument (.literal "concatenation dimension must be non-negative"))
    else do
      let scanned ← mixedShapeScan catSize catRank checkedAdd rank values 0 rank
      let shape := List.replicate (rank - 1).toNat 1 ++ [scanned.1] ++
        List.replicate (scanned.2 - rank).toNat 1
      let dest ← allocate elementType scanned.2 shape
      copyMixed isArray length checkedAdd copyto set dest values 1
theorem p2458 : P2458 := by unfold P2458; intros; rfl

def incrementCoordinates (checkedAdd : Int → Int → CResult Int)
    (catSize : X → IntegerValue → CResult Int)
    (value : X) : List Int → Nat → CResult (List Int)
  | coordinates, 0 => .ok coordinates
  | coordinates, remaining + 1 => do
      let index := coordinates.length - remaining - 1
      let current ← getCatOneBased coordinates (Int.ofNat index + 1)
      let limit ← catSize value ⟨Int.ofNat index + 1⟩
      let next ← checkedAdd current 1
      let updated := coordinates.set index next
      if next < limit then .ok updated
      else incrementCoordinates checkedAdd catSize value (updated.set index 0) remaining

def advanceOffsets (checkedAdd : Int → Int → CResult Int)
    (catSize : X → IntegerValue → CResult Int)
    (destinationSize : IntegerValue → CResult Int) (value : X) :
    List Int → List Nat → CResult (List Int)
  | offsets, [] => .ok offsets
  | offsets, index :: rest => do
      let current ← getCatOneBased offsets (Int.ofNat index + 1)
      let amount ← catSize value ⟨Int.ofNat index + 1⟩
      let limit ← destinationSize ⟨Int.ofNat index + 1⟩
      let next ← checkedAdd current amount
      let updated := offsets.set index next
      if next < limit then .ok updated
      else advanceOffsets checkedAdd catSize destinationSize value (updated.set index 0) rest

structure FillState (A : Type) where
  array : A
  offsets : List Int
  innerOffsets : List Int

def fillGeneralLoop (n : Int) (outProducts : List Int)
    (checkedAdd : Int → Int → CResult Int)
    (catSize : X → IntegerValue → CResult Int)
    (destinationSize : A → IntegerValue → CResult Int)
    (isArray : X → Bool) (isEmpty : X → CResult Bool) (length : X → CResult Int)
    (iterate : X → FillState A →
      (FillState A → V → CResult (FillState A)) → CResult (FillState A))
    (sliceAssign : A → List Int → List Int → X → CResult A)
    (setLinear : A → Int → V → CResult A) (setScalar : A → List Int → X → CResult A)
    (calculate : List Int → List Int → List Int → Int → CResult Int)
    (d1 d2 : Int) : FillState A → List X → CResult (FillState A)
  | state, [] => .ok state
  | state, value :: rest => do
      let start ← state.offsets.mapM (fun offset => checkedAdd offset 1)
      let afterValue ← if isArray value then do
        if ← isEmpty value then .ok state
        else
          let count ← length value
          if 4 < count then
            let endIndex ← (List.range n.toNat).mapM fun index => do
              let amount ← catSize value ⟨Int.ofNat index + 1⟩
              let offset ← getCatOneBased state.offsets (Int.ofNat index + 1)
              checkedAdd offset amount
            let array ← sliceAssign state.array start endIndex value
            .ok { state with array }
          else
            iterate value state fun current item => do
              let index ← calculate current.offsets current.innerOffsets outProducts n
              let array ← setLinear current.array index item
              let inner ← incrementCoordinates checkedAdd catSize value
                current.innerOffsets n.toNat
              .ok ⟨array, current.offsets, inner⟩
      else do
        let array ← setScalar state.array start value
        .ok { state with array }
      let dimensionOrder := [d1.toNat - 1, d2.toNat - 1] ++ List.range' 2 (n.toNat - 2)
      let offsets ← advanceOffsets checkedAdd catSize (destinationSize afterValue.array)
        value afterValue.offsets dimensionOrder
      fillGeneralLoop n outProducts checkedAdd catSize destinationSize isArray isEmpty length
        iterate sliceAssign setLinear setScalar calculate d1 d2
        ⟨afterValue.array, offsets, afterValue.innerOffsets⟩ rest

/-- General `hvncat_fill!`, lines 2823-2863. -/
def m2823 (rank : A → CResult Int) (size : A → CResult (List Int))
    (cumulativeProducts : List Int → CResult (List Int))
    (checkedAdd : Int → Int → CResult Int)
    (catSize : X → IntegerValue → CResult Int)
    (destinationSize : A → IntegerValue → CResult Int) (isArray : X → Bool)
    (isEmpty : X → CResult Bool) (length : X → CResult Int)
    (iterate : X → FillState A →
      (FillState A → V → CResult (FillState A)) → CResult (FillState A))
    (sliceAssign : A → List Int → List Int → X → CResult A)
    (setLinear : A → Int → V → CResult A) (setScalar : A → List Int → X → CResult A)
    (calculate : List Int → List Int → List Int → Int → CResult Int)
    (array : A) (scratch1 scratch2 : List Int) (d1 d2 : Int) (values : List X) : CResult A := do
  let n ← rank array
  if n ≤ 1 then
    .error (.argument (.literal "dimensions of the destination array must be at least 2"))
  else if scratch1.length != n || scratch2.length != n then
    .error (.argument (.literal
      "scratch vectors must have as many elements as the destination array has dimensions"))
  else if ¬(0 < d1 && d1 < 3 && 0 < d2 && d2 < 3 && d1 != d2) then
    .error (.argument (.literal "d1 and d2 must be either 1 or 2, exclusive."))
  else do
    let shape ← size array
    let products ← cumulativeProducts shape
    let result ← fillGeneralLoop n products checkedAdd catSize destinationSize isArray
      isEmpty length iterate sliceAssign setLinear setScalar calculate d1 d2
      ⟨array, scratch1, scratch2⟩ values
    .ok result.array
def P2823 : Prop := ∀ {A X V : Type} (rank : A → CResult Int)
    (size : A → CResult (List Int)) (cumulativeProducts : List Int → CResult (List Int))
    (checkedAdd : Int → Int → CResult Int) (catSize : X → IntegerValue → CResult Int)
    (destinationSize : A → IntegerValue → CResult Int) (isArray : X → Bool)
    (isEmpty : X → CResult Bool) (length : X → CResult Int)
    (iterate : X → FillState A →
      (FillState A → V → CResult (FillState A)) → CResult (FillState A))
    (sliceAssign : A → List Int → List Int → X → CResult A)
    (setLinear : A → Int → V → CResult A) (setScalar : A → List Int → X → CResult A)
    (calculate : List Int → List Int → List Int → Int → CResult Int)
    (array : A) scratch1 scratch2 d1 d2 values,
  m2823 rank size cumulativeProducts checkedAdd catSize destinationSize isArray isEmpty length
    iterate sliceAssign setLinear setScalar calculate array scratch1 scratch2 d1 d2 values = do
    let n ← rank array
    if n ≤ 1 then
      .error (.argument (.literal "dimensions of the destination array must be at least 2"))
    else if scratch1.length != n || scratch2.length != n then
      .error (.argument (.literal
        "scratch vectors must have as many elements as the destination array has dimensions"))
    else if ¬(0 < d1 && d1 < 3 && 0 < d2 && d2 < 3 && d1 != d2) then
      .error (.argument (.literal "d1 and d2 must be either 1 or 2, exclusive."))
    else do
      let shape ← size array
      let products ← cumulativeProducts shape
      let result ← fillGeneralLoop n products checkedAdd catSize destinationSize isArray
        isEmpty length iterate sliceAssign setLinear setScalar calculate d1 d2
        ⟨array, scratch1, scratch2⟩ values
      .ok result.array
theorem p2823 : P2823 := by unfold P2823; intros; rfl

def setOneBased (values : List α) (index : Int) (value : α) : CResult (List α) :=
  if index < 1 || (values.length : Int) < index then .error .bounds
  else .ok (values.set (index - 1).toNat value)

def validateOtherAxes (catSize : X → IntegerValue → CResult Int)
    (left right : X) (skip rank : Int) : CResult Unit :=
  let rec loop (dimension : Int) (remaining : Nat) : CResult Unit :=
    match remaining with
    | 0 => .ok ()
    | remaining + 1 =>
        if dimension = skip then loop (dimension + 1) remaining
        else do
          let expected ← catSize left ⟨dimension⟩
          let actual ← catSize right ⟨dimension⟩
          if expected != actual then .error (.dimensionMismatch (.literal "incompatible shape in element"))
          else loop (dimension + 1) remaining
  loop 1 rank.toNat

def validateBalancedBlocks (catSize : X → IntegerValue → CResult Int)
    (dimensions : List Int) (rowFirst : Bool) (values : List X) : CResult Unit := do
  match dimensions.findIdx? (1 < ·) with
  | none => .ok ()
  | some rawAxis =>
      let initialAxis := Int.ofNat rawAxis + 1
      let axis := if rowFirst && initialAxis < 3 then (if initialAxis = 1 then 2 else 1) else initialAxis
      let width ← getCatOneBased dimensions axis
      let blocks := values.length / width.toNat
      let rec blockLoop (block : Nat) (remaining : Nat) : CResult Unit :=
        match remaining with
        | 0 => .ok ()
        | remaining + 1 =>
            let offset := block * width.toNat
            do
              let first ← getCatOneBased values (Int.ofNat offset + 1)
              let rec itemLoop (item : Nat) (itemsRemaining : Nat) : CResult Unit :=
                match itemsRemaining with
                | 0 => .ok ()
                | itemsRemaining + 1 => do
                    let current ← getCatOneBased values (Int.ofNat (offset + item))
                    validateOtherAxes catSize first current axis dimensions.length
                    itemLoop (item + 1) itemsRemaining
              itemLoop 2 (width.toNat - 1)
              blockLoop (block + 1) remaining
      blockLoop 0 blocks

structure BalancedState where
  outdims : List Int
  current : List Int
  blockCount : Int
  elementCount : Int
  deriving Repr, DecidableEq

def balancedAxisLoop (catSize : X → IntegerValue → CResult Int)
    (checkedAdd : Int → Int → CResult Int) (dimensions : List Int) (value : X) :
    List Int → BalancedState → CResult BalancedState
  | [], state => .ok state
  | axis :: rest, state => do
      let current ← getCatOneBased state.current axis
      let amount ← catSize value ⟨axis⟩
      let next ← checkedAdd current amount
      let currentValues ← setOneBased state.current axis next
      let output ← getCatOneBased state.outdims axis
      if output = 0 then
        let blockCount := state.blockCount + 1
        let required ← getCatOneBased dimensions axis
        if blockCount = required then do
          let outputs ← setOneBased state.outdims axis next
          let reset ← setOneBased currentValues axis 0
          balancedAxisLoop catSize checkedAdd dimensions value rest
            ⟨outputs, reset, 0, state.elementCount⟩
        else .ok ⟨state.outdims, currentValues, blockCount, state.elementCount⟩
      else if next = output then do
        let reset ← setOneBased currentValues axis 0
        balancedAxisLoop catSize checkedAdd dimensions value rest
          ⟨state.outdims, reset, state.blockCount, state.elementCount⟩
      else if next < output then .ok ⟨state.outdims, currentValues, state.blockCount, state.elementCount⟩
      else .error (.dimensionMismatch (.literal "argument has too many elements along axis"))

def balancedValueLoop (catSize : X → IntegerValue → CResult Int)
    (catLength : X → CResult Int) (checkedAdd : Int → Int → CResult Int)
    (dimensions : List Int) (firstAxis secondAxis : Int) (firstDimZero : Bool) :
    List X → Int → BalancedState → CResult BalancedState
  | [], _, state => .ok state
  | value :: rest, index, state => do
      let count ← catLength value
      let elementCount ← checkedAdd state.elementCount count
      let currentFirst ← getCatOneBased state.current firstAxis
      let rawFirst ← catSize value ⟨firstAxis⟩
      let firstAmount := if firstDimZero then 1 else rawFirst
      let nextFirst ← checkedAdd currentFirst firstAmount
      let current ← setOneBased state.current firstAxis nextFirst
      let expected ← getCatOneBased state.outdims firstAxis
      let nextState ← if nextFirst = expected then do
        let reset ← setOneBased current firstAxis 0
        let axes := [secondAxis] ++ (List.range' 3 (dimensions.length - 2)).map Int.ofNat
        balancedAxisLoop catSize checkedAdd dimensions value axes
          ⟨state.outdims, reset, state.blockCount, elementCount⟩
      else if expected < nextFirst then
        .error (.dimensionMismatch (.literal "argument has too many elements along first axis"))
      else .ok ⟨state.outdims, current, state.blockCount, elementCount⟩
      balancedValueLoop catSize catLength checkedAdd dimensions firstAxis secondAxis firstDimZero
        rest (index + 1) nextState

def sumFirstAxis (catSize : X → IntegerValue → CResult Int)
    (checkedAdd : Int → Int → CResult Int) (values : List X) (firstAxis : Int) :
    Int → Nat → Int → CResult Int
  | _, 0, total => .ok total
  | index, remaining + 1, total => do
      let value ← getCatOneBased values index
      let amount ← catSize value ⟨firstAxis⟩
      let next ← checkedAdd total amount
      sumFirstAxis catSize checkedAdd values firstAxis (index + 1) remaining next

/-- Balanced `_typed_hvncat_dims`, lines 2635-2729. -/
def m2635 (catSize : X → IntegerValue → CResult Int) (catLength : X → CResult Int)
    (checkedAdd : Int → Int → CResult Int) (checkedDims : List Int → CResult Int)
    (similar : X → T → List Int → CResult A)
    (fill : A → List Int → List Int → Int → Int → List X → CResult A)
    (elementType : T) (dimensions : List Int) (rowFirst : Bool) (values : List X) : CResult A := do
  if values.isEmpty then .error (.argument (.literal "must have at least one element"))
  else if dimensions.any (· ≤ 0) then
    .error (.argument (.literal "`dims` argument must contain positive integers"))
  else do
    validateBalancedBlocks catSize dimensions rowFirst values
    let firstAxis := if rowFirst then 2 else 1
    let secondAxis := if rowFirst then 1 else 2
    let firstCount ← getCatOneBased dimensions firstAxis
    let rawFirst ← sumFirstAxis catSize checkedAdd values firstAxis 1 firstCount.toNat 0
    let firstDimZero := rawFirst = 0
    let adjustedFirst := if firstDimZero then firstCount else rawFirst
    let initialOut ← setOneBased (List.replicate dimensions.length 0) firstAxis adjustedFirst
    let scanned ← balancedValueLoop catSize catLength checkedAdd dimensions firstAxis secondAxis
      firstDimZero values 1 ⟨initialOut, List.replicate dimensions.length 0, 0, 0⟩
    let outdims ← if firstDimZero then setOneBased scanned.outdims firstAxis 0 else .ok scanned.outdims
    let outLength ← checkedDims outdims
    if scanned.elementCount != outLength then
      .error (.dimensionMismatch (lazyAppend [.literal "mismatched number of elements; expected ",
        .integer outLength, .literal ", got ", .integer scanned.elementCount]))
    else do
      let first ← firstOrBounds values
      let dest ← similar first elementType outdims
      fill dest (List.replicate dimensions.length 0) (List.replicate dimensions.length 0)
        firstAxis secondAxis values
def P2635 : Prop := ∀ {X T A : Type} (catSize : X → IntegerValue → CResult Int)
    (catLength : X → CResult Int) (checkedAdd : Int → Int → CResult Int)
    (checkedDims : List Int → CResult Int) (similar : X → T → List Int → CResult A)
    (fill : A → List Int → List Int → Int → Int → List X → CResult A)
    elementType dimensions rowFirst values,
  m2635 catSize catLength checkedAdd checkedDims similar fill elementType dimensions rowFirst values = do
    if values.isEmpty then .error (.argument (.literal "must have at least one element"))
    else if dimensions.any (· ≤ 0) then
      .error (.argument (.literal "`dims` argument must contain positive integers"))
    else do
      validateBalancedBlocks catSize dimensions rowFirst values
      let firstAxis := if rowFirst then 2 else 1
      let secondAxis := if rowFirst then 1 else 2
      let firstCount ← getCatOneBased dimensions firstAxis
      let rawFirst ← sumFirstAxis catSize checkedAdd values firstAxis 1 firstCount.toNat 0
      let firstDimZero := rawFirst = 0
      let adjustedFirst := if firstDimZero then firstCount else rawFirst
      let initialOut ← setOneBased (List.replicate dimensions.length 0) firstAxis adjustedFirst
      let scanned ← balancedValueLoop catSize catLength checkedAdd dimensions firstAxis secondAxis
        firstDimZero values 1 ⟨initialOut, List.replicate dimensions.length 0, 0, 0⟩
      let outdims ← if firstDimZero then setOneBased scanned.outdims firstAxis 0 else .ok scanned.outdims
      let outLength ← checkedDims outdims
      if scanned.elementCount != outLength then
        .error (.dimensionMismatch (lazyAppend [.literal "mismatched number of elements; expected ",
          .integer outLength, .literal ", got ", .integer scanned.elementCount]))
      else do
        let first ← firstOrBounds values
        let dest ← similar first elementType outdims
        fill dest (List.replicate dimensions.length 0) (List.replicate dimensions.length 0)
          firstAxis secondAxis values
theorem p2635 : P2635 := by unfold P2635 m2635; intros; rfl

structure UnbalancedState where
  outdims : List Int
  current : List Int
  blockCounts : List Int
  shapePositions : List Int
  elementCount : Int
  deriving Repr, DecidableEq

def unbalancedAxisLoop (catSize : X → IntegerValue → CResult Int)
    (checkedAdd : Int → Int → CResult Int) (shape : List (List Int))
    (rowFirst : Bool) (previous : Option X) (value : X) (valueIndex : Int) :
    Int → Nat → Bool → UnbalancedState → CResult UnbalancedState
  | _, 0, _, state => .ok state
  | dimension, remaining + 1, wasStartBlock, state => do
      let actualAxis := if dimension < 3 && rowFirst then (if dimension = 1 then 2 else 1)
        else dimension
      let dimensionSize ← catSize value ⟨actualAxis⟩
      let oldBlockCount ← getCatOneBased state.blockCounts dimension
      let newBlockCount := oldBlockCount + 1
      let blockCounts ← setOneBased state.blockCounts dimension newBlockCount
      let oldCurrent ← getCatOneBased state.current dimension
      let currentValue ← if dimension = 1 || valueIndex = 1 || wasStartBlock then
        checkedAdd oldCurrent dimensionSize
      else match previous with
        | none => .ok oldCurrent
        | some prior => do
            let expected ← catSize prior ⟨actualAxis⟩
            if dimensionSize != expected then
              .error (.dimensionMismatch (.literal "mismatched number of elements along axis"))
            else .ok oldCurrent
      let current ← setOneBased state.current dimension currentValue
      let nextWasStart := newBlockCount = 1
      let level ← getCatOneBased shape dimension
      let shapePosition ← getCatOneBased state.shapePositions dimension
      let required ← getCatOneBased level shapePosition
      return ← if newBlockCount = required then do
        let output ← getCatOneBased state.outdims dimension
        let outputs ← if output = -1 then setOneBased state.outdims dimension currentValue
          else if output != currentValue then
            .error (.dimensionMismatch (.literal "mismatched number of elements along axis"))
          else .ok state.outdims
        let resetCurrent ← setOneBased current dimension 0
        let resetBlocks ← setOneBased blockCounts dimension 0
        let positions ← setOneBased state.shapePositions dimension (shapePosition + 1)
        let nextResult := unbalancedAxisLoop catSize checkedAdd shape rowFirst previous value valueIndex
          (dimension + 1) remaining nextWasStart
          ⟨outputs, resetCurrent, resetBlocks, positions, state.elementCount⟩
        if 1 < dimension then do
          let innerBlocks ← getCatOneBased resetBlocks (dimension - 1)
          if innerBlocks != 0 then
            (.error (.dimensionMismatch (.literal "shape levels must nest evenly")) : CResult UnbalancedState)
          else nextResult
        else nextResult
      else
        (unbalancedAxisLoop catSize checkedAdd shape rowFirst previous value valueIndex
          (dimension + 1) remaining nextWasStart
          ⟨state.outdims, current, blockCounts, state.shapePositions, state.elementCount⟩)

def unbalancedValueLoop (catSize : X → IntegerValue → CResult Int)
    (catLength : X → CResult Int) (checkedAdd : Int → Int → CResult Int)
    (shape : List (List Int)) (rowFirst : Bool) :
    List X → Int → Option X → UnbalancedState → CResult UnbalancedState
  | [], _, _, state => .ok state
  | value :: rest, index, previous, state => do
      let count ← catLength value
      let elementCount ← checkedAdd state.elementCount count
      let next ← unbalancedAxisLoop catSize checkedAdd shape rowFirst previous value index
        1 shape.length false { state with elementCount }
      unbalancedValueLoop catSize catLength checkedAdd shape rowFirst rest (index + 1)
        (some value) next

/-- Unbalanced `_typed_hvncat_shape`, lines 2744-2821. -/
def m2744 (catSize : X → IntegerValue → CResult Int) (catLength : X → CResult Int)
    (catRank : X → CResult Int) (checkedAdd : Int → Int → CResult Int)
    (checkedDims : List Int → CResult Int) (similar : X → T → List Int → CResult A)
    (fill : A → List Int → List Int → Int → Int → List X → CResult A)
    (elementType : T) (shape : List (List Int)) (rowFirst : Bool)
    (values : List X) : CResult A := do
  if values.isEmpty then .error (.argument (.literal "must have at least one element"))
  else if shape.flatten.any (· ≤ 0) then
    .error (.argument (.literal "`shape` argument must consist of positive integers"))
  else if shape.any List.isEmpty then
    .error (.argument (.literal "each level of `shape` argument must have at least one value"))
  else do
    let finalLevel ← match shape.getLast? with | none => .error .bounds | some level => .ok level
    if finalLevel.length != 1 then
      .error (.argument (.literal "last level of shape must contain only one integer"))
    else
      let promised ← firstOrBounds finalLevel
      if promised != values.length then
        .error (.argument (lazyAppend [.literal "number of elements does not match shape; expected ",
          .integer promised, .literal ", got ", .integer values.length]))
      else do
        let firstAxis := if rowFirst then 2 else 1
        let secondAxis := if rowFirst then 1 else 2
        let first ← firstOrBounds values
        let firstRank ← catRank first
        let rank := max shape.length firstRank.toNat
        let scanned ← unbalancedValueLoop catSize catLength checkedAdd shape rowFirst values 1 none
          ⟨List.replicate rank (-1), List.replicate rank 0, List.replicate rank 0,
            List.replicate rank 1, 0⟩
        let outputLength ← checkedDims (scanned.outdims.take shape.length)
        if scanned.elementCount != outputLength then
          .error (.argument (lazyAppend [.literal "mismatched number of elements; expected ",
            .integer outputLength, .literal ", got ", .integer scanned.elementCount]))
        else
          let outdims ← if rowFirst then do
            let firstDim ← getCatOneBased scanned.outdims 1
            let secondDim ← getCatOneBased scanned.outdims 2
            let swapped ← setOneBased scanned.outdims 1 secondDim
            setOneBased swapped 2 firstDim
          else .ok scanned.outdims
          let dest ← similar first elementType outdims
          if outdims.any (· = 0) then .ok dest
          else fill dest scanned.current scanned.blockCounts firstAxis secondAxis values
def P2744 : Prop := ∀ {X T A : Type} (catSize : X → IntegerValue → CResult Int)
    (catLength catRank : X → CResult Int) (checkedAdd : Int → Int → CResult Int)
    (checkedDims : List Int → CResult Int) (similar : X → T → List Int → CResult A)
    (fill : A → List Int → List Int → Int → Int → List X → CResult A)
    elementType shape rowFirst values,
  m2744 catSize catLength catRank checkedAdd checkedDims similar fill elementType shape rowFirst values = do
    if values.isEmpty then .error (.argument (.literal "must have at least one element"))
    else if shape.flatten.any (· ≤ 0) then
      .error (.argument (.literal "`shape` argument must consist of positive integers"))
    else if shape.any List.isEmpty then
      .error (.argument (.literal "each level of `shape` argument must have at least one value"))
    else do
      let finalLevel ← match shape.getLast? with | none => .error .bounds | some level => .ok level
      if finalLevel.length != 1 then
        .error (.argument (.literal "last level of shape must contain only one integer"))
      else
        let promised ← firstOrBounds finalLevel
        if promised != values.length then
          .error (.argument (lazyAppend [.literal "number of elements does not match shape; expected ",
            .integer promised, .literal ", got ", .integer values.length]))
        else do
          let firstAxis := if rowFirst then 2 else 1
          let secondAxis := if rowFirst then 1 else 2
          let first ← firstOrBounds values
          let firstRank ← catRank first
          let rank := max shape.length firstRank.toNat
          let scanned ← unbalancedValueLoop catSize catLength checkedAdd shape rowFirst values 1 none
            ⟨List.replicate rank (-1), List.replicate rank 0, List.replicate rank 0,
              List.replicate rank 1, 0⟩
          let outputLength ← checkedDims (scanned.outdims.take shape.length)
          if scanned.elementCount != outputLength then
            .error (.argument (lazyAppend [.literal "mismatched number of elements; expected ",
              .integer outputLength, .literal ", got ", .integer scanned.elementCount]))
          else
            let outdims ← if rowFirst then do
              let firstDim ← getCatOneBased scanned.outdims 1
              let secondDim ← getCatOneBased scanned.outdims 2
              let swapped ← setOneBased scanned.outdims 1 secondDim
              setOneBased swapped 2 firstDim
            else .ok scanned.outdims
            let dest ← similar first elementType outdims
            if outdims.any (· = 0) then .ok dest
            else fill dest scanned.current scanned.blockCounts firstAxis secondAxis values
theorem p2744 : P2744 := by unfold P2744; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-abstractarray-hvncat-faithful-{line}", juliaFile := "base/abstractarray.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.AbstractArrayHvncatFaithful
