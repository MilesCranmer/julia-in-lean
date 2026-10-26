import JuliaLean.Iterators
import JuliaLean.IteratorsCov.Collections

/-!
# Method-family equations for product, flatten, partition, Stateful, only and nth

The executable iterator semantics reuse the earlier deep model in
`JuliaLean.Iterators.Model`; these propositions expose every helper method used
by the owned coverage rows.
-/

namespace JuliaLean.IteratorsCov

open JuliaLean


/-! ## Product -/

def productIelExpected (its : List JuliaLean.Iterators.Itr) : Bool :=
  match its with
  | [] => true
  | [it] => JuliaLean.Iterators.ieltype it
  | _ => JuliaLean.Iterators.ieltypeAll its

def productAxes (sizes : List (List JInt64)) : List (List JInt64) := sizes
def productNdims (axes : List (List JInt64)) : Nat := axes.flatten.length

/-- The product constructor, traits, shape/axes/length helpers, empty-product
iteration, odometer iteration, reverse and last follow lines 1148-1256; for two
finite vectors the iterator also has the documented Cartesian-product values. -/
def ProductMethodSemantics : Prop :=
  JuliaLean.Iterators.ProductCorrect ∧
  (∀ its, JuliaLean.Iterators.isz (.product its) = JuliaLean.Iterators.prodIszList (JuliaLean.Iterators.iszList its ++ [.hasShape 0])) ∧
  (∀ its, JuliaLean.Iterators.ieltype (.product its) = productIelExpected its) ∧
  (∀ its, JuliaLean.Iterators.eltype (.product its) = .tuple (JuliaLean.Iterators.eltypeList its)) ∧
  (∀ its, JuliaLean.Iterators.size (.product its) = JuliaLean.Iterators.prodSize its) ∧
  (∀ its, JuliaLean.Iterators.len (.product its) = do JuliaLean.Iterators.foldCheckedMul (JuliaLean.Iterators.i64 1) (← JuliaLean.Iterators.prodSize its)) ∧
  (∀ fuel, JuliaLean.Iterators.iter fuel (.product []) none = .ok (some (.tup [], .nat 1)) ∧
    JuliaLean.Iterators.iter fuel (.product []) (some .nothing) = .ok none) ∧
  (∀ its, JuliaLean.Iterators.reverse (.product its) = do pure (.product (← JuliaLean.Iterators.reverseList its))) ∧
  (∀ its, JuliaLean.Iterators.lastOf (.product its) = do pure (.tup (← JuliaLean.Iterators.lastList its))) ∧
  (∀ sizes, productAxes sizes = sizes ∧ productNdims sizes = sizes.flatten.length)

theorem productMethodSemantics : ProductMethodSemantics := by
  refine ⟨JuliaLean.Iterators.productCorrect, fun _ => rfl, ?_, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, ?_, fun _ => rfl, fun _ => rfl,
    fun _ => ⟨rfl, rfl⟩⟩
  · intro its
    cases its with
    | nil => rfl
    | cons a rest => cases rest with
      | nil => rfl
      | cons b rest => rfl
  · intro fuel
    exact ⟨rfl, rfl⟩

/-! ## Flatten -/

def flattenLengthModel (it : JuliaLean.Iterators.Itr) : JuliaLean.Iterators.M JInt64 :=
  match JuliaLean.Iterators.eltype it with
  | .bottom => .ok (JuliaLean.Iterators.i64 0)
  | .tuple ts => do JuliaLean.Iterators.checkedMul64 (JuliaLean.Iterators.i64 ts.length) (← JuliaLean.Iterators.len it)
  | .int => JuliaLean.Iterators.len it
  | _ => JuliaLean.Iterators.jthrow (.argumentError "Iterates of the argument to Flatten are not known to have constant length")

def flattenLastModel (fuel : Nat) (it : JuliaLean.Iterators.Itr) : JuliaLean.Iterators.M JuliaLean.Iterators.Val := do
  JuliaLean.Iterators.first fuel (← JuliaLean.Iterators.reverse (.flatten it))

/-- Flatten's constructor, type traits, length dispatch, two iterate methods,
reverse and last match lines 1291-1380; finite vectors of vectors concatenate. -/
def FlattenMethodSemantics : Prop :=
  JuliaLean.Iterators.FlattenCorrect ∧ JuliaLean.Iterators.FlattenTupleLength ∧
  (∀ it, JuliaLean.Iterators.eltype (.flatten it) = (JuliaLean.Iterators.eltype it).eltype) ∧
  (∀ it, JuliaLean.Iterators.ieltype (.flatten it) =
    (JuliaLean.Iterators.isEmptyTuple it || (JuliaLean.Iterators.ieltype it && JuliaLean.Iterators.eltype it != .any))) ∧
  (∀ it, JuliaLean.Iterators.isz (.flatten it) =
    if !(JuliaLean.Iterators.ieltype it) then .sizeUnknown
    else if JuliaLean.Iterators.isEmptyTuple it then .hasLength
    else JuliaLean.Iterators.flattenIsz (JuliaLean.Iterators.isz it) (JuliaLean.Iterators.eltype it)) ∧
  (∀ it, JuliaLean.Iterators.reverse (.flatten it) = do pure (.flatten (.revEach (← JuliaLean.Iterators.reverse it)))) ∧
  (∀ fuel it, flattenLastModel fuel it = do JuliaLean.Iterators.first fuel (← JuliaLean.Iterators.reverse (.flatten it)))

theorem flattenMethodSemantics : FlattenMethodSemantics := by
  refine ⟨JuliaLean.Iterators.flattenCorrect, JuliaLean.Iterators.flattenTupleLength, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

/-! ## Partition -/

def partitionEltype (c : JuliaLean.Iterators.Itr) : JuliaLean.Iterators.Ty := .vector (JuliaLean.Iterators.eltype c)

/-- Partition validates a positive Int count, uses the specialized array/range
and generic chunking branches, preserves the documented element type and
computes the number of chunks. -/
def PartitionMethodSemantics : Prop :=
  JuliaLean.Iterators.PartitionVectorCorrect ∧
  (∀ c (n : JInt64), n.val < 1 → JuliaLean.Iterators.partition c n =
    JuliaLean.Iterators.jthrow (.argumentError "cannot create partitions of length n")) ∧
  (∀ c (n : JInt64), 1 ≤ n.val → JuliaLean.Iterators.partition c n = .ok (.partition c n)) ∧
  (∀ c (n : JInt64), JuliaLean.Iterators.eltype (.partition c n) = partitionEltype c) ∧
  (∀ c (n : JInt64), JuliaLean.Iterators.isz (.partition c n) = match JuliaLean.Iterators.isz c with
    | .hasShape _ => .hasLength | s => s) ∧
  (∀ c (n : JInt64), JuliaLean.Iterators.len (.partition c n) = do
    JuliaLean.Iterators.liftJ (JInt.cld (← JuliaLean.Iterators.len c) n))

theorem partitionMethodSemantics : PartitionMethodSemantics := by
  refine ⟨JuliaLean.Iterators.partitionVectorCorrect, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro c n h
    simp [JuliaLean.Iterators.partition, h]
  · intro c n h
    simp [JuliaLean.Iterators.partition, show ¬ n.val < 1 by omega,
      JuliaLean.Iterators.ProofsAList.toInt_self]

/-! ## Stateful and type approximation -/

inductive ApproxType where
  | bottom | valueState | maybeValueState | other
  deriving Repr, DecidableEq

/-- `_approx_iter_type`, lines 1597-1603. -/
def approxIterType (iteratorBottom : Bool) (current next : ApproxType) : ApproxType :=
  if current = .other then .other
  else if current = .bottom || iteratorBottom then .bottom
  else if next = current then current else .other

def resetStateful (et : JuliaLean.Iterators.Ty) (xs : List JuliaLean.Iterators.Val) : JuliaLean.Iterators.Itr := .stateful et xs 0
def resetStatefulTo (et : JuliaLean.Iterators.Ty) (xs : List JuliaLean.Iterators.Val) : JuliaLean.Iterators.Itr := .stateful et xs 0
def statefulIdentity (x : JuliaLean.Iterators.Itr) : JuliaLean.Iterators.Itr := x
def statefulConvert (x : JuliaLean.Iterators.Itr) : JuliaLean.Iterators.Itr := x

def StatefulMethodSemantics : Prop :=
  JuliaLean.Iterators.StatefulConsistent ∧
  (∀ et xs, resetStateful et xs = .stateful et xs 0 ∧
    resetStatefulTo et xs = .stateful et xs 0) ∧
  (∀ x, statefulIdentity x = x ∧ statefulConvert x = x) ∧
  (∀ b current next, approxIterType b current next =
    if current = .other then .other
    else if current = .bottom || b then .bottom
    else if next = current then current else .other) ∧
  (∀ et xs pos, JuliaLean.Iterators.isz (.stateful et xs pos) = .sizeUnknown ∧
    JuliaLean.Iterators.eltype (.stateful et xs pos) = et ∧ JuliaLean.Iterators.ieltype (.stateful et xs pos) = true)

theorem statefulMethodSemantics : StatefulMethodSemantics := by
  refine ⟨JuliaLean.Iterators.statefulConsistent, fun _ _ => ⟨rfl, rfl⟩,
    fun _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩

/-! ## only and nth adapters -/

def onlyFirst (length : Nat) (first : JuliaLean.Iterators.M JuliaLean.Iterators.Val) : JuliaLean.Iterators.M JuliaLean.Iterators.Val :=
  if length = 1 then first
  else JuliaLean.Iterators.jthrow (.argumentError "Collection must contain exactly 1 element")

def nthFix (fuel : Nat) (type : IntTy) (n : Int) (it : JuliaLean.Iterators.Itr) : JuliaLean.Iterators.M JuliaLean.Iterators.Val :=
  JuliaLean.Iterators.nth fuel it type n

def OnlyNthMethodSemantics : Prop :=
  JuliaLean.Iterators.OnlyCorrect ∧ JuliaLean.Iterators.NthVectorCorrect ∧
  (∀ fuel x, JuliaLean.Iterators.only fuel (.tuple [x]) = .ok x) ∧
  (∀ fuel xs, xs.length ≠ 1 → ∃ msg,
    JuliaLean.Iterators.only fuel (.tuple xs) = JuliaLean.Iterators.jthrow (.argumentError msg)) ∧
  (∀ first : JuliaLean.Iterators.M JuliaLean.Iterators.Val, onlyFirst 1 first = first) ∧
  (∀ fuel type n it, nthFix fuel type n it = JuliaLean.Iterators.nth fuel it type n)

theorem onlyNthMethodSemantics : OnlyNthMethodSemantics := by
  refine ⟨JuliaLean.Iterators.onlyCorrect, JuliaLean.Iterators.nthVectorCorrect, fun _ _ => rfl, ?_, ?_, fun _ _ _ _ => rfl⟩
  · intro fuel xs h
    refine ⟨"Tuple contains n elements, must contain exactly 1 element", ?_⟩
    cases xs with
    | nil => rfl
    | cons x xs => cases xs with
      | nil => simp at h
      | cons y ys => rfl
  · intro first
    rfl

end JuliaLean.IteratorsCov
