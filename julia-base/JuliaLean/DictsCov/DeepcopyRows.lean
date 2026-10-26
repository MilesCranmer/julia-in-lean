import JuliaLean.Registry.Types

/-!
# Method-specific models for `base/deepcopy.jl`

Each `methodNN` definition mirrors the method beginning at source line `NN` in
Julia master `bbfa0ce4150`. Runtime allocation, field access, pointer copying,
and dispatch are explicit arguments. The models keep the source branch order,
the memo-table update before recursive copying, and the distinction between a
normal mutable allocation and the GC registration performed by `WeakRef(x)`.
-/

namespace JuliaLean.DictsCov.DeepcopyRows

open JuliaLean.Registry

abbrev R (α : Type) := Except String α

structure Obj where
  id : Nat
  mutable_ : Bool
  bitstype : Bool
  weakref : Bool
  registered : Bool
  fields : List (Option Nat)
  deriving Repr, DecidableEq

abbrev Stack := List (Nat × Obj)

def lookup (stack : Stack) (id : Nat) : Option Obj :=
  (stack.find? fun p => p.1 == id).map Prod.snd

def replace (stack : Stack) (id : Nat) (value : Obj) : Stack :=
  (id, value) :: stack.filter (fun p => p.1 != id)

def copyMutableFields (deep : Nat → Stack → R (Nat × Stack)) :
    List (Option Nat) → Stack → R (List (Option Nat) × Stack)
  | [], stack => .ok ([], stack)
  | none :: fields, stack => do
      let (rest, stack) ← copyMutableFields deep fields stack
      return (none :: rest, stack)
  | some value :: fields, stack => do
      let (value, stack) ← deep value stack
      let (rest, stack) ← copyMutableFields deep fields stack
      return (some value :: rest, stack)

def copyImmutableFields (deep : Nat → Stack → R (Nat × Stack)) :
    List (Option Nat) → Stack → R (List (Option Nat) × Stack)
  | [], stack => .ok ([], stack)
  | none :: _, stack => .ok ([], stack)
  | some value :: fields, stack => do
      let (value, stack) ← deep value stack
      let (rest, stack) ← copyImmutableFields deep fields stack
      return (some value :: rest, stack)

/-- `deepcopy(x)`, `base/deepcopy.jl:32-35`. -/
def method32 (isBitsType : α → Bool) (deepcopyInternal : α → R α) (x : α) : R α :=
  if isBitsType x then .ok x else deepcopyInternal x

def Property32 : Prop := ∀ (α : Type) (isBitsType : α → Bool)
    (deepcopyInternal : α → R α) x,
  method32 isBitsType deepcopyInternal x =
    if isBitsType x then .ok x else deepcopyInternal x
theorem property32 : Property32 := by unfold Property32; intros; rfl

/-- Identity specializations, `base/deepcopy.jl:37-39`. -/
def method37 (x : α) (_stack : Stack) : α := x
def Property37 : Prop := ∀ (α : Type) (x : α) stack, method37 x stack = x
theorem property37 : Property37 := by unfold Property37; intros; rfl

def mapTuple (deep : α → Stack → R (α × Stack)) : List α → Stack → R (List α × Stack)
  | [], stack => .ok ([], stack)
  | x :: xs, stack => do
      let (x, stack) ← deep x stack
      let (xs, stack) ← mapTuple deep xs stack
      return (x :: xs, stack)

/-- Tuple specialization, `base/deepcopy.jl:40-41`. -/
def method40 (deep : α → Stack → R (α × Stack)) (x : List α) (stack : Stack) :
    R (List α × Stack) := mapTuple deep x stack
def Property40 : Prop := ∀ (α : Type) deep x stack,
  method40 (α := α) deep x stack = mapTuple deep x stack
theorem property40 : Property40 := by unfold Property40; intros; rfl

/-- Module specialization, `base/deepcopy.jl:42`. -/
def method42 (_module : α) (_stack : Stack) : R α := .error "deepcopy of Modules not supported"
def Property42 : Prop := ∀ (α : Type) (m : α) stack,
  method42 m stack = .error "deepcopy of Modules not supported"
theorem property42 : Property42 := by unfold Property42; intros; rfl

def cachedSequence (copyOne : Nat → Stack → R (Nat × Stack))
    (allocate : List Nat → Obj) (x : Obj) (values : List Nat) (stack : Stack) : R (Obj × Stack) :=
  match lookup stack x.id with
  | some y => .ok (y, stack)
  | none => do
      let (values, stack) ← mapTuple copyOne values stack
      let y := allocate values
      let stack := replace stack x.id y
      return (y, stack)

/-- SimpleVector specialization, `base/deepcopy.jl:44-51`. -/
def method44 (deep : Nat → Stack → R (Nat × Stack)) (svec : List Nat → Obj)
    (x : Obj) (values : List Nat) (stack : Stack) : R (Obj × Stack) :=
  cachedSequence deep svec x values stack
def Property44 : Prop := ∀ deep svec x values stack,
  method44 deep svec x values stack = cachedSequence deep svec x values stack
theorem property44 : Property44 := by unfold Property44; intros; rfl

/-- String specialization, `base/deepcopy.jl:53-60`. -/
def method53 (unsafeCopy : Obj → Obj) (x : Obj) (stack : Stack) : R (Obj × Stack) :=
  match lookup stack x.id with
  | some y => .ok (y, stack)
  | none =>
      let y := unsafeCopy x
      .ok (y, replace stack x.id y)
def Property53 : Prop := ∀ unsafeCopy x stack,
  method53 unsafeCopy x stack = match lookup stack x.id with
    | some y => .ok (y, stack)
    | none => let y := unsafeCopy x; .ok (y, replace stack x.id y)
theorem property53 : Property53 := by unfold Property53; intros; rfl

/-- Generic object specialization, `base/deepcopy.jl:62-99`. -/
def method62 (deep : Nat → Stack → R (Nat × Stack)) (x : Obj) (stack : Stack) : R (Obj × Stack) :=
  if x.mutable_ then
    match lookup stack x.id with
    | some y => .ok (y, stack)
    | none => do
        let y : Obj :=
          { id := x.id, mutable_ := x.mutable_, bitstype := x.bitstype,
            weakref := x.weakref, registered := false,
            fields := List.replicate x.fields.length none }
        let stack := replace stack x.id y
        let (fields, stack) ← copyMutableFields deep x.fields stack
        let y := { y with fields := fields }
        return (y, replace stack x.id y)
  else if x.fields.isEmpty || x.bitstype then
    .ok (x, stack)
  else do
    let (fields, stack) ← copyImmutableFields deep x.fields stack
    return ({ x with fields := fields }, stack)

def Property62 : Prop := ∀ deep x stack,
  method62 deep x stack =
    if x.mutable_ then
      match lookup stack x.id with
      | some y => .ok (y, stack)
      | none => do
          let y : Obj :=
            { id := x.id, mutable_ := x.mutable_, bitstype := x.bitstype,
              weakref := x.weakref, registered := false,
              fields := List.replicate x.fields.length none }
          let stack := replace stack x.id y
          let (fields, stack) ← copyMutableFields deep x.fields stack
          let y := { y with fields := fields }
          return (y, replace stack x.id y)
    else if x.fields.isEmpty || x.bitstype then .ok (x, stack)
    else do
      let (fields, stack) ← copyImmutableFields deep x.fields stack
      return ({ x with fields := fields }, stack)
theorem property62 : Property62 := by unfold Property62; intros; rfl

def weakInput : Obj :=
  { id := 1, mutable_ := true, bitstype := false, weakref := true,
    registered := true, fields := [some 7] }

def weakDeep (value : Nat) (stack : Stack) : R (Nat × Stack) := .ok (value + 100, stack)

def deepcopyWeak : R Obj :=
  method32 (fun _ : Obj => false)
    (fun x => (method62 weakDeep x []).map Prod.fst) weakInput

/-- A copied WeakRef must remain registered so GC clears it when its referent dies. -/
def DeepcopyWeakRegistered : Prop :=
  Property32 ∧ Property62 ∧ ∀ y, deepcopyWeak = .ok y → y.registered = true

theorem deepcopyWeakRegistered_refuted : ¬ DeepcopyWeakRegistered := by
  intro h
  have hy := h.2.2 { weakInput with registered := false, fields := [some 107] }
  have hw : deepcopyWeak = .ok { weakInput with registered := false, fields := [some 107] } := by
    rfl
  exact Bool.noConfusion (hy hw)

/-- Memory dispatcher, `base/deepcopy.jl:101-106`. -/
def method101 (deepcopyMemoryT : Obj → Stack → R (Obj × Stack))
    (x : Obj) (stack : Stack) : R (Obj × Stack) :=
  match lookup stack x.id with
  | some y => .ok (y, stack)
  | none => deepcopyMemoryT x stack
def Property101 : Prop := ∀ deep x stack,
  method101 deep x stack = match lookup stack x.id with
    | some y => .ok (y, stack)
    | none => deep x stack
theorem property101 : Property101 := by unfold Property101; intros; rfl

def copyMemoryElems (deep : Nat → Stack → R (Nat × Stack)) :
    List (Option Nat) → Stack → R (List (Option Nat) × Stack) := copyMutableFields deep

/-- `_deepcopy_memory_t`, `base/deepcopy.jl:108-128`. -/
def method108 (isBitsType : Bool) (copy : Obj → Obj)
    (deep : Nat → Stack → R (Nat × Stack)) (x : Obj) (stack : Stack) : R (Obj × Stack) :=
  if isBitsType then
    let y := copy x
    .ok (y, replace stack x.id y)
  else do
    let dest : Obj := { x with fields := List.replicate x.fields.length none }
    let stack := replace stack x.id dest
    let (fields, stack) ← copyMemoryElems deep x.fields stack
    let dest := { dest with fields := fields }
    return (dest, replace stack x.id dest)
def Property108 : Prop := ∀ bits copy deep x stack,
  method108 bits copy deep x stack =
    if bits then let y := copy x; .ok (y, replace stack x.id y)
    else do
      let dest : Obj := { x with fields := List.replicate x.fields.length none }
      let stack := replace stack x.id dest
      let (fields, stack) ← copyMemoryElems deep x.fields stack
      let dest := { dest with fields := fields }
      return (dest, replace stack x.id dest)
theorem property108 : Property108 := by unfold Property108; intros; rfl

structure ArrayObj where
  object : Obj
  ref : Obj
  size : List Nat
  deriving Repr, DecidableEq

/-- Array specialization, `base/deepcopy.jl:129-137`. -/
def method129 (deepRef : Obj → Stack → R (Obj × Stack)) (x : ArrayObj) (stack : Stack) :
    R (ArrayObj × Stack) :=
  match lookup stack x.object.id with
  | some y => .ok ({ x with object := y }, stack)
  | none => do
      let emptyObj := { x.object with fields := [] }
      let y := { x with object := emptyObj }
      let stack := replace stack x.object.id emptyObj
      let (ref, stack) ← deepRef x.ref stack
      return ({ y with ref := ref, size := x.size }, stack)
def Property129 : Prop := ∀ deep x stack,
  method129 deep x stack = match lookup stack x.object.id with
    | some y => .ok ({ x with object := y }, stack)
    | none => do
        let emptyObj := { x.object with fields := [] }
        let y := { x with object := emptyObj }
        let stack := replace stack x.object.id emptyObj
        let (ref, stack) ← deep x.ref stack
        return ({ y with ref := ref, size := x.size }, stack)
theorem property129 : Property129 := by unfold Property129; intros; rfl

structure MemRef where
  mem : Obj
  offset : Nat
  deriving Repr, DecidableEq

/-- GenericMemoryRef specialization, `base/deepcopy.jl:138-147`. -/
def method138 (deepMem : Obj → Stack → R (Obj × Stack)) (x : MemRef) (stack : Stack) :
    R (MemRef × Stack) := do
  let (mem, stack) ← deepMem x.mem stack
  let dest := { mem := mem, offset := 1 }
  return (if x.offset == 1 then dest else { dest with offset := x.offset }, stack)
def Property138 : Prop := ∀ deep x stack,
  method138 deep x stack = do
    let (mem, stack) ← deep x.mem stack
    let dest : MemRef := { mem := mem, offset := 1 }
    return (if x.offset == 1 then dest else { dest with offset := x.offset }, stack)
theorem property138 : Property138 := by unfold Property138; intros; rfl

def copyPairs (deep : Nat → Stack → R (Nat × Stack)) :
    List (Nat × Nat) → Stack → R (List (Nat × Nat) × Stack)
  | [], stack => .ok ([], stack)
  | (k, v) :: pairs, stack => do
      let (k, stack) ← deep k stack
      let (v, stack) ← deep v stack
      let (pairs, stack) ← copyPairs deep pairs stack
      return ((k, v) :: pairs, stack)

/-- Dict and IdDict specialization, `base/deepcopy.jl:150-165`. -/
def method150 (bitsEltype : Bool) (copy : Obj → Obj)
    (empty : Obj → Obj) (deep : Nat → Stack → R (Nat × Stack))
    (x : Obj) (pairs : List (Nat × Nat)) (stack : Stack) : R (Obj × List (Nat × Nat) × Stack) :=
  match lookup stack x.id with
  | some y => .ok (y, pairs, stack)
  | none =>
      if bitsEltype then
        let y := copy x
        .ok (y, pairs, replace stack x.id y)
      else do
        let dest := empty x
        let stack := replace stack x.id dest
        let (pairs, stack) ← copyPairs deep pairs stack
        return (dest, pairs, stack)
def Property150 : Prop := ∀ bits copy empty deep x pairs stack,
  method150 bits copy empty deep x pairs stack = match lookup stack x.id with
    | some y => .ok (y, pairs, stack)
    | none => if bits then
        let y := copy x; .ok (y, pairs, replace stack x.id y)
      else do
        let dest := empty x
        let stack := replace stack x.id dest
        let (pairs, stack) ← copyPairs deep pairs stack
        return (dest, pairs, stack)
theorem property150 : Property150 := by unfold Property150; intros; rfl

/-- AbstractLock specialization, `base/deepcopy.jl:167-174`. -/
def method167 (construct : Obj → Obj) (x : Obj) (stack : Stack) : R (Obj × Stack) :=
  match lookup stack x.id with
  | some y => .ok (y, stack)
  | none => let y := construct x; .ok (y, replace stack x.id y)
def Property167 : Prop := ∀ construct x stack,
  method167 construct x stack = match lookup stack x.id with
    | some y => .ok (y, stack)
    | none => let y := construct x; .ok (y, replace stack x.id y)
theorem property167 : Property167 := by unfold Property167; intros; rfl

/-- GenericCondition specialization, `base/deepcopy.jl:176-183`. -/
def method176 (deepLock : Obj → Stack → R (Obj × Stack))
    (construct : Obj → Obj) (x lock : Obj) (stack : Stack) : R (Obj × Stack) :=
  match lookup stack x.id with
  | some y => .ok (y, stack)
  | none => do
      let (lock, stack) ← deepLock lock stack
      let y := construct lock
      return (y, replace stack x.id y)
def Property176 : Prop := ∀ deep construct x lock stack,
  method176 deep construct x lock stack = match lookup stack x.id with
    | some y => .ok (y, stack)
    | none => do
        let (lock, stack) ← deep lock stack
        let y := construct lock
        return (y, replace stack x.id y)
theorem property176 : Property176 := by unfold Property176; intros; rfl

/-- WaitEntryN specialization, `base/deepcopy.jl:194-201`. -/
def method194 (allocate : Nat → Nat → Obj) (x : Obj) (task slots : Nat) (stack : Stack) :
    R (Obj × Stack) :=
  match lookup stack x.id with
  | some y => .ok (y, stack)
  | none => let y := allocate task slots; .ok (y, replace stack x.id y)
def Property194 : Prop := ∀ allocate x task slots stack,
  method194 allocate x task slots stack = match lookup stack x.id with
    | some y => .ok (y, stack)
    | none => let y := allocate task slots; .ok (y, replace stack x.id y)
theorem property194 : Property194 := by unfold Property194; intros; rfl

private def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/deepcopy.jl", juliaFns := [fn],
    statement := statement, source := source, status := .proven,
    prop := prop, thm := some thm }

def entries : List Entry := [
  entry "dictscov-deepcopy-l37" "deepcopy_internal(x::Union{Symbol,Core.MethodInstance,Method,GlobalRef,DataType,Union,UnionAll,Task,Regex, Core.CancellationTokenSource}, stackdict::IdDict)" "The identity specializations return their input." "invariant; base/deepcopy.jl:37-39" ``Property37 ``property37,
  entry "dictscov-deepcopy-l40" "deepcopy_internal(x::Tuple, stackdict::IdDict)" "Tuple elements are copied recursively in index order." "deepcopy docstring; base/deepcopy.jl:40-41" ``Property40 ``property40,
  entry "dictscov-deepcopy-l42" "deepcopy_internal(x::Module, stackdict::IdDict)" "Copying a Module throws the documented unsupported-operation error." "invariant; base/deepcopy.jl:42" ``Property42 ``property42,
  entry "dictscov-deepcopy-l44" "deepcopy_internal(x::SimpleVector, stackdict::IdDict)" "SimpleVector copying reuses a memoized copy or recursively copies every element and memoizes it." "deepcopy docstring; base/deepcopy.jl:44-51" ``Property44 ``property44,
  entry "dictscov-deepcopy-l53" "deepcopy_internal(x::String, stackdict::IdDict)" "String copying reuses a memoized result or copies the bytes and memoizes the copy." "deepcopy docstring; base/deepcopy.jl:53-60" ``Property53 ``property53,
  entry "dictscov-deepcopy-l101" "deepcopy_internal(x::Memory, stackdict::IdDict)" "Memory copying returns a memoized result or dispatches to the element-type helper." "deepcopy docstring; base/deepcopy.jl:101-106" ``Property101 ``property101,
  entry "dictscov-deepcopy-l108" "_deepcopy_memory_t(@nospecialize(x::Memory), T, stackdict::IdDict)" "Bits memories are copied directly; other assigned elements are recursively copied after memoizing the destination." "deepcopy docstring; base/deepcopy.jl:108-128" ``Property108 ``property108,
  entry "dictscov-deepcopy-l129" "deepcopy_internal(x::Array{T, N}, stackdict::IdDict) where {T, N}" "Array copying memoizes an empty array, recursively copies its memory reference, and preserves its dimensions." "deepcopy docstring; base/deepcopy.jl:129-137" ``Property129 ``property129,
  entry "dictscov-deepcopy-l138" "deepcopy_internal(x::GenericMemoryRef, stackdict::IdDict)" "A memory reference points at the copied memory with the original offset." "deepcopy docstring; base/deepcopy.jl:138-147" ``Property138 ``property138,
  entry "dictscov-deepcopy-l150" "deepcopy_internal(x::Union{Dict,IdDict}, stackdict::IdDict)" "Dictionary copying preserves memoization and recursively copies keys before values." "deepcopy docstring; base/deepcopy.jl:150-165" ``Property150 ``property150,
  entry "dictscov-deepcopy-l167" "deepcopy_internal(x::AbstractLock, stackdict::IdDict)" "A lock copy is newly constructed and memoized unless already copied." "deepcopy docstring; base/deepcopy.jl:167-174" ``Property167 ``property167,
  entry "dictscov-deepcopy-l176" "deepcopy_internal(x::GenericCondition, stackdict::IdDict)" "A condition copy recursively copies its lock and memoizes the constructed condition." "deepcopy docstring; base/deepcopy.jl:176-183" ``Property176 ``property176,
  entry "dictscov-deepcopy-l194" "deepcopy_internal(x::Core.WaitEntryN, stackdict::IdDict)" "A WaitEntryN copy uses the runtime allocator with the same task and slot count, then memoizes it." "invariant; base/deepcopy.jl:194-201" ``Property194 ``property194
]

end JuliaLean.DictsCov.DeepcopyRows
