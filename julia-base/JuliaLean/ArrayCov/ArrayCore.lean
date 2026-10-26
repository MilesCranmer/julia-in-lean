import JuliaLean.Core
import JuliaLean.ArrayCov.Simple

namespace JuliaLean.ArrayCov

inductive ExprModel where
  | atom (value : Int)
  | node (head : Int) (args : List ExprModel)
  | ref (array : ExprModel) (indices : List ExprModel)
  | assign (left right : ExprModel)
  | call (fn : Int) (args : List ExprModel)

def array132SafeIndexMacro (escape recurse : ExprModel → ExprModel)
    (expression : ExprModel) : ExprModel := escape (recurse expression)

def array135SafeIndex (recurse : ExprModel → ExprModel)
    (safeGet safeSet : Int) : ExprModel → ExprModel
  | ExprModel.atom value => .atom value
  | ExprModel.assign (ExprModel.ref array indices) right =>
      .call safeSet (array :: recurse right :: indices.map recurse)
  | ExprModel.ref array indices => .call safeGet (array :: indices)
  | ExprModel.node head args => .node head (args.map recurse)
  | ExprModel.assign left right => .assign (recurse left) (recurse right)
  | ExprModel.call fn args => .call fn (args.map recurse)

def array159VectLoop (setindex : List Int → Nat → Int → List Int) :
    List Int → Nat → List Int → List Int
  | output, _, [] => output
  | output, index, value :: rest =>
      array159VectLoop setindex (setindex output index value) (index + 1) rest

def array159Vect (allocate : Nat → List Int)
    (setindex : List Int → Nat → Int → List Int) (values : List Int) : List Int :=
  array159VectLoop setindex (allocate values.length) 1 values

def array183VectPromoted (promoteType : List Int → Int)
    (typedLiteral : Int → List Int → Jl (List Int)) (values : List Int) : Jl (List Int) :=
  typedLiteral (promoteType values) values

def ArraySyntaxAndVectCorrect : Prop :=
  (∀ escape recurse expression, array132SafeIndexMacro escape recurse expression =
      escape (recurse expression)) ∧
  (∀ recurse get set array indices, array135SafeIndex recurse get set (.ref array indices) =
      .call get (array :: indices)) ∧
  (∀ recurse get set array indices right,
      array135SafeIndex recurse get set (.assign (.ref array indices) right) =
      .call set (array :: recurse right :: indices.map recurse)) ∧
  (∀ recurse get set head args, array135SafeIndex recurse get set (.node head args) =
      .node head (args.map recurse)) ∧
  (∀ allocate set values, array159Vect allocate set values =
      array159VectLoop set (allocate values.length) 1 values) ∧
  (∀ promote literal values, array183VectPromoted promote literal values =
      literal (promote values) values)

theorem arraySyntaxAndVectCorrect : ArraySyntaxAndVectCorrect := by
  simp [ArraySyntaxAndVectCorrect, array132SafeIndexMacro, array135SafeIndex,
    array159Vect, array183VectPromoted]

structure DenseArrayModel where
  data : List Int
  assigned : List Bool
  dims : List Int
  deriving Repr, DecidableEq

def array209UnsetIndex (checkbounds : DenseArrayModel → JInt64 → Bool)
    (unset : DenseArrayModel → JInt64 → DenseArrayModel)
    (array : DenseArrayModel) (index : JInt64) : Jl DenseArrayModel :=
  if checkbounds array index then .ok (unset array index) else .error .boundsError

def array219ElsizePtr (isAny : Int → Bool) (isDataType : Int → Bool)
    (pointerSize : JInt64) (coreSize alignment : Int → JInt64)
    (align : JInt64 → JInt64 → JInt64) (type : Int) : Jl JInt64 :=
  if isAny type then .ok pointerSize
  else if !isDataType type then .error (.methodError "sizeof")
  else .ok (align (coreSize type) (alignment type))

def array231IsAssigned (checkbounds : DenseArrayModel → List JInt64 → Bool)
    (sub2ind : List Int → List JInt64 → JInt64)
    (memoryAssigned : DenseArrayModel → JInt64 → Bool)
    (array : DenseArrayModel) (indices : List JInt64) : Bool :=
  if !checkbounds array indices then false
  else memoryAssigned array (sub2ind array.dims indices)

def array239IsAssignedVector (checkbounds : DenseArrayModel → JInt64 → Bool)
    (memoryAssigned : DenseArrayModel → JInt64 → Bool)
    (array : DenseArrayModel) (index : JInt64) : Bool :=
  if !checkbounds array index then false else memoryAssigned array index

def array259UnsafeCopyPtr (alignedSize : Int → JInt64)
    (memmove : Int → JInt64 → JInt64 → JInt64 → Int)
    (memory type : Int) (dest src count : JInt64) : JInt64 × Int :=
  let memory := memmove memory dest src (count * alignedSize type)
  (dest, memory)

def array276UnsafeCopyArray
    (memoryRef : DenseArrayModel → JInt64 → JInt64)
    (copyPtr : Int → JInt64 → JInt64 → JInt64 → Int)
    (memory : Int)
    (dest : DenseArrayModel) (destOffset : JInt64)
    (src : DenseArrayModel) (srcOffset count : JInt64) : DenseArrayModel × Int :=
  if count.val = 0 then (dest, memory)
  else
    let memory := copyPtr memory (memoryRef dest destOffset) (memoryRef src srcOffset) count
    (dest, memory)

def array288Copyto (copyImpl : DenseArrayModel → Int → DenseArrayModel → Int → Int → Jl DenseArrayModel)
    (dest : DenseArrayModel) (destOffset : Int) (src : DenseArrayModel)
    (srcOffset count : Int) : Jl DenseArrayModel :=
  copyImpl dest destOffset src srcOffset count

def array290CopytoArrayMemory := array288Copyto
def array292CopytoMemoryArray := array288Copyto
def array296CopytoSameArray := array288Copyto

def ArrayStorageRoutesCorrect : Prop :=
  (∀ bounds unset array index, array209UnsetIndex bounds unset array index =
      if bounds array index then .ok (unset array index) else .error .boundsError) ∧
  (∀ any datatype ptr size alignment align type,
      array219ElsizePtr any datatype ptr size alignment align type =
      if any type then .ok ptr
      else if !datatype type then .error (.methodError "sizeof")
      else .ok (align (size type) (alignment type))) ∧
  (∀ bounds sub assigned array indices, array231IsAssigned bounds sub assigned array indices =
      if !bounds array indices then false else assigned array (sub array.dims indices)) ∧
  (∀ bounds assigned array index, array239IsAssignedVector bounds assigned array index =
      if !bounds array index then false else assigned array index) ∧
  (∀ size move memory type dest src count,
      array259UnsafeCopyPtr size move memory type dest src count =
      (dest, move memory dest src (count * size type))) ∧
  (∀ ref copy memory dest doffs src soffs count,
      array276UnsafeCopyArray ref copy memory dest doffs src soffs count =
      if count.val = 0 then (dest, memory)
      else (dest, copy memory (ref dest doffs) (ref src soffs) count)) ∧
  (∀ copy dest doffs src soffs count, array288Copyto copy dest doffs src soffs count =
      copy dest doffs src soffs count) ∧
  (∀ copy dest doffs src soffs count, array290CopytoArrayMemory copy dest doffs src soffs count =
      copy dest doffs src soffs count) ∧
  (∀ copy dest doffs src soffs count, array292CopytoMemoryArray copy dest doffs src soffs count =
      copy dest doffs src soffs count) ∧
  (∀ copy dest doffs src soffs count, array296CopytoSameArray copy dest doffs src soffs count =
      copy dest doffs src soffs count)

theorem arrayStorageRoutesCorrect : ArrayStorageRoutesCorrect := by
  simp [ArrayStorageRoutesCorrect, array209UnsetIndex, array219ElsizePtr,
    array231IsAssigned, array239IsAssignedVector, array259UnsafeCopyPtr,
    array276UnsafeCopyArray, array288Copyto, array290CopytoArrayMemory,
    array292CopytoMemoryArray, array296CopytoSameArray]

def array373FillLoop (setindex : DenseArrayModel → Nat → Int → DenseArrayModel) :
    DenseArrayModel → Nat → Nat → Int → DenseArrayModel
  | array, _, 0, _ => array
  | array, index, fuel + 1, value =>
      array373FillLoop setindex (setindex array index value) (index + 1) fuel value

def array368Fill (isType : Int → Bool) (convert : Int → Jl Int)
    (fillTyped : DenseArrayModel → Int → DenseArrayModel)
    (array : DenseArrayModel) (value : Int) : Jl DenseArrayModel := do
  let value ← if isType value then pure value else convert value
  pure (fillTyped array value)

def array373Fill (setindex : DenseArrayModel → Nat → Int → DenseArrayModel)
    (array : DenseArrayModel) (value : Int) : DenseArrayModel :=
  array373FillLoop setindex array 1 array.data.length value

def array391Copy (allocate : Nat → DenseArrayModel)
    (unsafeCopy : DenseArrayModel → DenseArrayModel → Nat → DenseArrayModel)
    (array : DenseArrayModel) : DenseArrayModel :=
  let output := allocate array.data.length
  let output := unsafeCopy output array array.data.length
  { output with dims := array.dims }

def array402Take (sameRef sameSize : DenseArrayModel → DenseArrayModel → Bool)
    (setRef setSize : DenseArrayModel → DenseArrayModel → DenseArrayModel)
    (dest src : DenseArrayModel) : DenseArrayModel :=
  let dest := if sameRef dest src then dest else setRef dest src
  if sameSize dest src then dest else setSize dest src

def array445LiteralLoop (setindex : List Int → Nat → Int → Jl (List Int)) :
    List Int → Nat → List Int → Jl (List Int)
  | output, _, [] => .ok output
  | output, index, value :: rest => do
      let output ← setindex output index value
      array445LiteralLoop setindex output (index + 1) rest

def array445TypedLiteral (allocate : Nat → List Int)
    (tupleSet foldSet : List Int → Nat → Int → Jl (List Int))
    (isTuple : Bool) (values : List Int) : Jl (List Int) :=
  let output := allocate values.length
  if isTuple then array445LiteralLoop tupleSet output 1 values
  else array445LiteralLoop foldSet output 1 values

def array463AnyLoop (setindex : List Int → Nat → Int → List Int) :
    List Int → Nat → List Int → List Int
  | output, _, [] => output
  | output, index, value :: rest =>
      array463AnyLoop setindex (setindex output index value) (index + 1) rest

def array463AnyLiteral (allocate : Nat → List Int)
    (setindex : List Int → Nat → Int → List Int) (values : List Int) : List Int :=
  array463AnyLoop setindex (allocate values.length) 1 values

def array471AnyEmpty (_ : Unit) : List Int := []

def array473FillBytes (convert : Int → Jl Int)
    (memset : DenseArrayModel → Int → Nat → DenseArrayModel)
    (alreadyType : Int → Bool) (array : DenseArrayModel) (value : Int) : Jl DenseArrayModel := do
  let value ← if alreadyType value then pure value else convert value
  pure (memset array value array.data.length)

def ArrayFillCopyLiteralCorrect : Prop :=
  (∀ isType convert fill array value, array368Fill isType convert fill array value = do
      let value ← if isType value then pure value else convert value
      pure (fill array value)) ∧
  (∀ set array value, array373Fill set array value =
      array373FillLoop set array 1 array.data.length value) ∧
  (∀ allocate copy array, array391Copy allocate copy array =
      let output := copy (allocate array.data.length) array array.data.length
      { output with dims := array.dims }) ∧
  (∀ sameRef sameSize setRef setSize dest src,
      array402Take sameRef sameSize setRef setSize dest src =
      let dest := if sameRef dest src then dest else setRef dest src
      if sameSize dest src then dest else setSize dest src) ∧
  (∀ allocate tupleSet foldSet isTuple values,
      array445TypedLiteral allocate tupleSet foldSet isTuple values =
      let output := allocate values.length
      if isTuple then array445LiteralLoop tupleSet output 1 values
      else array445LiteralLoop foldSet output 1 values) ∧
  (∀ allocate set values, array463AnyLiteral allocate set values =
      array463AnyLoop set (allocate values.length) 1 values) ∧
  (∀ u, array471AnyEmpty u = []) ∧
  (∀ convert memset same array value, array473FillBytes convert memset same array value = do
      let value ← if same value then pure value else convert value
      pure (memset array value array.data.length))

theorem arrayFillCopyLiteralCorrect : ArrayFillCopyLiteralCorrect := by
  simp [ArrayFillCopyLiteralCorrect, array368Fill, array373Fill, array391Copy,
    array402Take, array445TypedLiteral, array463AnyLiteral,
    array471AnyEmpty, array473FillBytes]

end JuliaLean.ArrayCov
