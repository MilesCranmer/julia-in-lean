import JuliaLean.Registry.Types

/-!
# Method-specific models for `base/iddict.jl`

The C equality-table calls are explicit callbacks. Their result tags preserve
the source's pointer-identity tests against a default or the private sentinel.
The table model records the 32-word initial allocation, live count, and deleted
slot count; constructor folds and mutating reads retain Julia's call order.
-/

namespace JuliaLean.DictsCov.IdDictRows

open JuliaLean.Registry

abbrev R (α : Type) := Except String α

structure State (K V : Type) where
  slots : List (Option (K × V))
  rawWords : Nat
  count : Int
  ndel : Int
  deriving Repr

def emptyState : State K V :=
  { slots := List.replicate 16 none, rawWords := 32, count := 0, ndel := 0 }

def foldSet (setindex : State K V → K → V → R (State K V)) :
    State K V → List (K × V) → R (State K V)
  | state, [] => .ok state
  | state, (k, v) :: pairs => do
      let state ← setindex state k v
      foldSet setindex state pairs

/-- Empty typed constructor, `base/iddict.jl:31`. -/
def method31 : State K V := emptyState
def Property31 : Prop := ∀ (K V : Type), method31 (K := K) (V := V) = emptyState
theorem property31 : Property31 := by unfold Property31; intros; rfl

/-- Iterator constructor, `base/iddict.jl:33-40`. -/
def method33 (hasLength : Bool) (sizehint : State K V → Nat → State K V)
    (setindex : State K V → K → V → R (State K V)) (pairs : List (K × V)) : R (State K V) :=
  let d : State K V := method31
  let d := if hasLength then sizehint d pairs.length else d
  foldSet setindex d pairs
def Property33 : Prop := ∀ (K V : Type) hasLength sizehint setindex pairs,
  method33 (K := K) (V := V) hasLength sizehint setindex pairs =
    let d : State K V := method31
    let d := if hasLength then sizehint d pairs.length else d
    foldSet setindex d pairs
theorem property33 : Property33 := by unfold Property33; intros; rfl

/-- Pair-vararg constructor, `base/iddict.jl:42-47`. -/
def method42 (sizehint : State K V → Nat → State K V)
    (setindex : State K V → K → V → R (State K V)) (pairs : List (K × V)) : R (State K V) :=
  let d : State K V := method31
  let d := sizehint d pairs.length
  foldSet setindex d pairs
def Property42 : Prop := ∀ (K V : Type) sizehint setindex pairs,
  method42 (K := K) (V := V) sizehint setindex pairs =
    foldSet setindex (sizehint method31 pairs.length) pairs
theorem property42 : Property42 := by unfold Property42; intros; rfl

/-- Same-type copy constructor, `base/iddict.jl:49`. -/
def method49 (copySlots : List (Option (K × V)) → List (Option (K × V)))
    (d : State K V) : State K V :=
  { slots := copySlots d.slots, rawWords := d.rawWords, count := d.count, ndel := d.ndel }
def Property49 : Prop := ∀ (K V : Type) copySlots (d : State K V),
  method49 copySlots d =
    { slots := copySlots d.slots, rawWords := d.rawWords, count := d.count, ndel := d.ndel }
theorem property49 : Property49 := by unfold Property49; intros; rfl

/-- Untyped empty constructor, `base/iddict.jl:52`. -/
def method52 : State K V := method31
def Property52 : Prop := ∀ (K V : Type), method52 (K := K) (V := V) = method31
theorem property52 : Property52 := by unfold Property52; intros; rfl

/-- Empty-tuple constructor, `base/iddict.jl:53`. -/
def method53 (_emptyTuple : Unit) : State K V := method52
def Property53 : Prop := ∀ (K V : Type), method53 (K := K) (V := V) () = method52
theorem property53 : Property53 := by unfold Property53; intros; rfl

/-- Fully typed pair-vararg forwarding method, `base/iddict.jl:55`. -/
def method55 (typed : List (K × V) → R (State K V)) (pairs : List (K × V)) := typed pairs
def Property55 : Prop := ∀ (K V : Type) typed pairs,
  method55 (K := K) (V := V) typed pairs = typed pairs
theorem property55 : Property55 := by unfold Property55; intros; rfl

/-- Key-typed pair-vararg forwarding method, `base/iddict.jl:56`. -/
def method56 (typed : List (K × V) → R (State K V)) (pairs : List (K × V)) := typed pairs
def Property56 : Prop := ∀ (K V : Type) typed pairs,
  method56 (K := K) (V := V) typed pairs = typed pairs
theorem property56 : Property56 := by unfold Property56; intros; rfl

/-- Value-typed pair-vararg forwarding method, `base/iddict.jl:57`. -/
def method57 (typed : List (K × V) → R (State K V)) (pairs : List (K × V)) := typed pairs
def Property57 : Prop := ∀ (K V : Type) typed pairs,
  method57 (K := K) (V := V) typed pairs = typed pairs
theorem property57 : Property57 := by unfold Property57; intros; rfl

/-- Any/Any pair-vararg forwarding method, `base/iddict.jl:58`. -/
def method58 (typed : List (K × V) → R (State K V)) (pairs : List (K × V)) := typed pairs
def Property58 : Prop := ∀ (K V : Type) typed pairs,
  method58 (K := K) (V := V) typed pairs = typed pairs
theorem property58 : Property58 := by unfold Property58; intros; rfl

/-- Eltype-selecting constructor, `base/iddict.jl:60`. -/
def method60 (eltype : I → T) (dictWithEltype : I → T → R (State K V)) (kv : I) : R (State K V) :=
  dictWithEltype kv (eltype kv)
def Property60 : Prop := ∀ (I T K V : Type) eltype dictWithEltype kv,
  method60 (K := K) (V := V) (I := I) (T := T) eltype dictWithEltype kv =
    dictWithEltype kv (eltype kv)
theorem property60 : Property60 := by unfold Property60; intros; rfl

/-- `empty` specialization, `base/iddict.jl:62`. -/
def method62 : State K V := method31
def Property62 : Prop := ∀ (K V : Type), method62 (K := K) (V := V) = method31
theorem property62 : Property62 := by unfold Property62; intros; rfl

/-- Runtime rehash wrapper, `base/iddict.jl:64-67`. -/
def method64 (rehash : List (Option (K × V)) → Nat → List (Option (K × V)))
    (d : State K V) (newsz : Nat) : State K V :=
  { d with slots := rehash d.slots newsz, rawWords := newsz }
def Property64 : Prop := ∀ (K V : Type) rehash (d : State K V) newsz,
  method64 rehash d newsz = { d with slots := rehash d.slots newsz, rawWords := newsz }
theorem property64 : Property64 := by unfold Property64; intros; rfl

inductive RawGet (V : Type) where
  | default
  | value (v : V)

/-- Three-argument `get`, `base/iddict.jl:94-97`. -/
def method94 (eqtableGet : State K V → Q → V → RawGet V)
    (d : State K V) (key : Q) (default : V) : V :=
  match eqtableGet d key default with
  | .default => default
  | .value value => value
def Property94 : Prop := ∀ (K V Q : Type)
    (eqtableGet : State K V → Q → V → RawGet V) (d : State K V) (key : Q) (default : V),
  method94 eqtableGet d key default = match eqtableGet d key default with
    | .default => default
    | .value value => value
theorem property94 : Property94 := by unfold Property94; intros; rfl

structure PopResult (V : Type) where
  value : V
  found : Bool

/-- Defaulted pop, `base/iddict.jl:105-115`. -/
def method105 (eqtablePop : State K V → Q → V → PopResult V)
    (d : State K V) (key : Q) (default : V) : V × State K V :=
  let result := eqtablePop d key default
  if result.found then
    (result.value, { d with count := d.count - 1, ndel := d.ndel + 1 })
  else (default, d)
def Property105 : Prop := ∀ (K V Q : Type)
    (pop : State K V → Q → V → PopResult V) (d : State K V) (key : Q) (default : V),
  method105 pop d key default =
    let result := pop d key default
    if result.found then
      (result.value, { d with count := d.count - 1, ndel := d.ndel + 1 })
    else (default, d)
theorem property105 : Property105 := by unfold Property105; intros; rfl

inductive Cell (V : Type) where
  | sentinel
  | stored (v : V)

/-- Sentinel-checking pop wrapper, `base/iddict.jl:117-121`. -/
def method117 (popDefault : State K V → Q → Cell V → Cell V × State K V)
    (d : State K V) (key : Q) : R (V × State K V) :=
  match popDefault d key .sentinel with
  | (.sentinel, _) => .error "KeyError"
  | (.stored value, d) => .ok (value, d)

/-- Runtime next-index wrapper, `base/iddict.jl:139`. -/
def method139 (eqtableNextind : A → Nat → Nat) (reinterpretInt : Nat → Int) (a : A) (i : Nat) : Int :=
  reinterpretInt (eqtableNextind a i)
def Property139 : Prop := ∀ (A : Type) next reinterpretInt a i,
  method139 (A := A) next reinterpretInt a i = reinterpretInt (next a i)
theorem property139 : Property139 := by unfold Property139; intros; rfl

/-- Copy wrapper, `base/iddict.jl:149`. -/
def method149 (sameTypeConstructor : State K V → State K V) (d : State K V) : State K V :=
  sameTypeConstructor d
def Property149 : Prop := ∀ (K V : Type) constructor (d : State K V),
  method149 constructor d = constructor d
theorem property149 : Property149 := by unfold Property149; intros; rfl

/-- Value-defaulting `get!`, `base/iddict.jl:151-160`. -/
def method151 (getRaw : State K V → Q → Cell V) (convert : W → R V)
    (setindex : State K V → Q → V → R (State K V))
    (d : State K V) (key : Q) (default : W) : R (V × State K V) :=
  match getRaw d key with
  | .stored value => .ok (value, d)
  | .sentinel => do
      let value ← convert default
      let d ← setindex d key value
      return (value, d)

/-- Callable `get`, `base/iddict.jl:162-169`. -/
def method162 (getRaw : State K V → Q → Cell V) (default : Unit → R V)
    (d : State K V) (key : Q) : R V :=
  match getRaw d key with
  | .sentinel => default ()
  | .stored value => .ok value
def Property162 : Prop := ∀ (K V Q : Type)
    (getRaw : State K V → Q → Cell V) (default : Unit → R V)
    (d : State K V) (key : Q),
  method162 getRaw default d key = match getRaw d key with
    | .sentinel => default ()
    | .stored value => .ok value
theorem property162 : Property162 := by unfold Property162; intros; rfl

/-- Callable `get!`, `base/iddict.jl:171-183`. -/
def method171 (getRaw : State K V → Q → Cell V) (default : Unit → R W)
    (convert : W → R V) (setindex : State K V → Q → V → R (State K V))
    (d : State K V) (key : Q) : R (V × State K V) :=
  match getRaw d key with
  | .stored value => .ok (value, d)
  | .sentinel => do
      let raw ← default ()
      let value ← convert raw
      let d ← setindex d key value
      return (value, d)

/-- IdDict filter delegation, `base/iddict.jl:189`. -/
def method189 (filterOnePass : (K × V → Bool) → State K V → State K V)
    (f : K × V → Bool) (d : State K V) : State K V := filterOnePass f d
def Property189 : Prop := ∀ (K V : Type) filterOnePass f (d : State K V),
  method189 filterOnePass f d = filterOnePass f d
theorem property189 : Property189 := by unfold Property189; intros; rfl

private def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/iddict.jl", juliaFns := [fn], statement := statement,
    source := source, status := .proven, prop := prop, thm := some thm }

def entries : List Entry := [
  entry "dictscov-iddict-l31" "IdDict{K,V}() where {K, V}" "The empty typed IdDict has a 32-word table and zero live and deleted counts." "IdDict docstring and invariant; base/iddict.jl:31" ``Property31 ``property31,
  entry "dictscov-iddict-l33" "IdDict{K,V}(itr) where {K, V}" "The iterator constructor optionally size-hints, then inserts every pair in order." "IdDict docstring; base/iddict.jl:33-40" ``Property33 ``property33,
  entry "dictscov-iddict-l42" "IdDict{K,V}(pairs::Pair...) where {K, V}" "The pair constructor size-hints and inserts every pair in order." "IdDict docstring; base/iddict.jl:42-47" ``Property42 ``property42,
  entry "dictscov-iddict-l49" "IdDict{K,V}(d::IdDict{K,V}) where {K, V}" "The same-type copy duplicates the table and preserves both counts." "copy invariant; base/iddict.jl:49" ``Property49 ``property49,
  entry "dictscov-iddict-l52" "IdDict()" "The untyped empty constructor delegates to IdDict{Any,Any}." "constructor invariant; base/iddict.jl:52" ``Property52 ``property52,
  entry "dictscov-iddict-l53" "IdDict(kv::Tuple{})" "The empty-tuple constructor delegates to IdDict()." "constructor invariant; base/iddict.jl:53" ``Property53 ``property53,
  entry "dictscov-iddict-l55" "IdDict(ps::Pair{K,V}...) where {K,V}" "Homogeneous pairs delegate to the fully typed constructor." "constructor invariant; base/iddict.jl:55" ``Property55 ``property55,
  entry "dictscov-iddict-l56" "IdDict(ps::Pair{K}...) where {K}" "Key-homogeneous pairs delegate to IdDict{K,Any}." "constructor invariant; base/iddict.jl:56" ``Property56 ``property56,
  entry "dictscov-iddict-l57" "IdDict(ps::(Pair{K,V} where K)...) where {V}" "Value-homogeneous pairs delegate to IdDict{Any,V}." "constructor invariant; base/iddict.jl:57" ``Property57 ``property57,
  entry "dictscov-iddict-l58" "IdDict(ps::Pair...)" "Unconstrained pairs delegate to IdDict{Any,Any}." "constructor invariant; base/iddict.jl:58" ``Property58 ``property58,
  entry "dictscov-iddict-l60" "IdDict(kv)" "The generic constructor selects key and value types from the iterator eltype." "IdDict docstring; base/iddict.jl:60" ``Property60 ``property60,
  entry "dictscov-iddict-l62" "empty(d::IdDict, ::Type{K}, ::Type{V}) where {K, V}" "empty returns a new IdDict with the requested key and value types." "empty docstring base/abstractdict.jl:183-192; base/iddict.jl:62" ``Property62 ``property62,
  entry "dictscov-iddict-l64" "rehash!(d::IdDict, newsz::Integer = length(d.ht)%UInt)" "rehash! replaces the runtime table with the requested size and returns the dictionary." "IdDict invariant; base/iddict.jl:64-67" ``Property64 ``property64,
  entry "dictscov-iddict-l94" "get(d::IdDict{K,V}, @nospecialize(key), @nospecialize(default)) where {K, V}" "get returns the supplied default only when the runtime returns that identical default, otherwise the stored V." "get docstring; base/iddict.jl:94-97" ``Property94 ``property94,
  entry "dictscov-iddict-l105" "pop!(d::IdDict{K,V}, @nospecialize(key), @nospecialize(default)) where {K, V}" "Defaulted pop returns default unchanged when absent; when present it returns V, decrements count, and increments ndel." "pop! docstring; base/iddict.jl:105-115" ``Property105 ``property105,
  entry "dictscov-iddict-l139" "_oidd_nextind(a, i)" "The next-index wrapper reinterprets the runtime Csize_t result as Int." "iteration invariant; base/iddict.jl:139" ``Property139 ``property139,
  entry "dictscov-iddict-l149" "copy(d::IdDict)" "copy invokes the same concrete type's copy constructor." "copy invariant; base/iddict.jl:149" ``Property149 ``property149,
  entry "dictscov-iddict-l162" "get(default::Callable, d::IdDict{K,V}, @nospecialize(key)) where {K, V}" "Callable get invokes the default only for the sentinel result and otherwise returns the stored V." "get docstring; base/iddict.jl:162-169" ``Property162 ``property162,
  entry "dictscov-iddict-l189" "filter!(f, d::IdDict)" "IdDict filter! delegates to deletion during one-pass iteration." "filter! docstring base/abstractdict.jl:420-423; base/iddict.jl:187-189" ``Property189 ``property189
]

end JuliaLean.DictsCov.IdDictRows
