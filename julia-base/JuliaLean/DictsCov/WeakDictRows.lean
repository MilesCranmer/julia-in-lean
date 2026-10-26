import JuliaLean.Registry.Types

/-!
# Method-specific models for `base/weakdict.jl`

`none` represents a cleared weak reference. Locks are explicit callbacks for
the one-line forwarding methods; the larger method models contain the exact
body executed while the lock is held. Cleanup and iteration traverse stored
entries in source order, including the dead-entry skipping behavior.
-/

namespace JuliaLean.DictsCov.WeakDictRows

open JuliaLean.Registry

abbrev R (α : Type) := Except String α

structure WK (K V : Type) where
  entries : List (Option K × V)
  dirty : Bool
  deriving Repr

def wkEmpty : WK K V := ⟨[], false⟩

def method8 (d : WK K V) (_key : K) : WK K V := { d with dirty := true }
def Property8 : Prop := ∀ (K V : Type) (d : WK K V) key,
  method8 d key = { d with dirty := true }
theorem property8 : Property8 := by unfold Property8; intros; rfl

def method31 : WK K V := wkEmpty
def Property31 : Prop := ∀ (K V : Type), method31 (K := K) (V := V) = wkEmpty
theorem property31 : Property31 := by unfold Property31; intros; rfl

def wkFold (setindex : WK K V → K → V → R (WK K V)) :
    WK K V → List (K × V) → R (WK K V)
  | dict, [] => .ok dict
  | dict, (key, value) :: rest => do
      let dict ← setindex dict key value
      wkFold setindex dict rest

def method37 (setindex : WK K V → K → V → R (WK K V))
    (pairs : List (K × V)) : R (WK K V) := wkFold setindex method31 pairs
def Property37 : Prop := ∀ (K V : Type)
    (setindex : WK K V → K → V → R (WK K V)) pairs,
  method37 setindex pairs = wkFold setindex method31 pairs
theorem property37 : Property37 := by unfold Property37; intros; rfl

def method44 (setindex : WK K V → K → V → R (WK K V)) (pair : K × V) :=
  setindex method31 pair.1 pair.2
def Property44 : Prop := ∀ (K V : Type)
    (setindex : WK K V → K → V → R (WK K V)) pair,
  method44 setindex pair = setindex method31 pair.1 pair.2
theorem property44 : Property44 := by unfold Property44; intros; rfl

def method45 (sizehint : WK K V → Nat → WK K V)
    (setindex : WK K V → K → V → R (WK K V)) (pairs : List (K × V)) :=
  wkFold setindex (sizehint method31 pairs.length) pairs
def Property45 : Prop := ∀ (K V : Type) sizehint
    (setindex : WK K V → K → V → R (WK K V)) pairs,
  method45 sizehint setindex pairs = wkFold setindex (sizehint method31 pairs.length) pairs
theorem property45 : Property45 := by unfold Property45; intros; rfl

def method53 : WK K V := method31
def Property53 : Prop := ∀ (K V : Type), method53 (K := K) (V := V) = method31
theorem property53 : Property53 := by unfold Property53; intros; rfl

def method55 (_emptyTuple : Unit) : WK K V := method53
def Property55 : Prop := ∀ (K V : Type), method55 (K := K) (V := V) () = method53
theorem property55 : Property55 := by unfold Property55; intros; rfl

def method56 (construct : WK K V → R (WK K V)) (d : WK K V) := construct d
def Property56 : Prop := ∀ (K V : Type) construct (d : WK K V),
  method56 construct d = construct d
theorem property56 : Property56 := by unfold Property56; intros; rfl

def method58 (construct : List (K × V) → R (WK K V)) (pairs : List (K × V)) := construct pairs
def Property58 : Prop := ∀ (K V : Type) construct pairs,
  method58 (K := K) (V := V) construct pairs = construct pairs
theorem property58 : Property58 := by unfold Property58; intros; rfl

def method59 (construct : List (K × V) → R (WK K V)) (pairs : List (K × V)) := construct pairs
def Property59 : Prop := ∀ (K V : Type) construct pairs,
  method59 (K := K) (V := V) construct pairs = construct pairs
theorem property59 : Property59 := by unfold Property59; intros; rfl

def method60 (construct : List (K × V) → R (WK K V)) (pairs : List (K × V)) := construct pairs
def Property60 : Prop := ∀ (K V : Type) construct pairs,
  method60 (K := K) (V := V) construct pairs = construct pairs
theorem property60 : Property60 := by unfold Property60; intros; rfl

def method61 (construct : List (K × V) → R (WK K V)) (pairs : List (K × V)) := construct pairs
def Property61 : Prop := ∀ (K V : Type) construct pairs,
  method61 (K := K) (V := V) construct pairs = construct pairs
theorem property61 : Property61 := by unfold Property61; intros; rfl

def method63 (eltype : I → T) (dictWithEltype : I → T → R (WK K V)) (kv : I) :=
  dictWithEltype kv (eltype kv)
def Property63 : Prop := ∀ (I T K V : Type) (eltype : I → T)
    (dictWithEltype : I → T → R (WK K V)) (kv : I),
  method63 (K := K) (V := V) eltype dictWithEltype kv = dictWithEltype kv (eltype kv)
theorem property63 : Property63 := by unfold Property63; intros; rfl

def method65 (h : WK K V) : WK K V :=
  if h.dirty then ⟨h.entries.filter (fun pair => pair.1.isSome), false⟩ else h
def Property65 : Prop := ∀ (K V : Type) (h : WK K V),
  method65 h = if h.dirty then
    ⟨h.entries.filter (fun pair => pair.1.isSome), false⟩ else h
theorem property65 : Property65 := by unfold Property65; intros; rfl

def method79 (sizehint : WK K V → Nat → Bool → WK K V)
    (d : WK K V) (newsz : Nat) (shrink : Bool) := sizehint d newsz shrink
def Property79 : Prop := ∀ (K V : Type) sizehint (d : WK K V) newsz shrink,
  method79 sizehint d newsz shrink = sizehint d newsz shrink
theorem property79 : Property79 := by unfold Property79; intros; rfl

def method80 : WK K V := method31
def Property80 : Prop := ∀ (K V : Type), method80 (K := K) (V := V) = method31
theorem property80 : Property80 := by unfold Property80; intros; rfl

inductive IteratorSizeTag where | sizeUnknown deriving Repr, DecidableEq
def method82 : IteratorSizeTag := .sizeUnknown
def Property82 : Prop := ∀ (_K _V : Type), method82 = .sizeUnknown
theorem property82 : Property82 := by unfold Property82; intros; rfl

def method84 (islocked : L → Bool) (lock : L) := islocked lock
def Property84 : Prop := ∀ (L : Type) islocked lock,
  method84 (L := L) islocked lock = islocked lock
theorem property84 : Property84 := by unfold Property84; intros; rfl

def method85 (lockFn : L → A) (lock : L) := lockFn lock
def Property85 : Prop := ∀ (L A : Type) lockFn lock,
  method85 (L := L) (A := A) lockFn lock = lockFn lock
theorem property85 : Property85 := by unfold Property85; intros; rfl

def method86 (unlock : L → A) (lock : L) := unlock lock
def Property86 : Prop := ∀ (L A : Type) unlock lock,
  method86 (L := L) (A := A) unlock lock = unlock lock
theorem property86 : Property86 := by unfold Property86; intros; rfl

def method87 (lockFn : (Unit → A) → L → A) (f : Unit → A) (lock : L) := lockFn f lock
def Property87 : Prop := ∀ (L A : Type) lockFn f lock,
  method87 (L := L) (A := A) lockFn f lock = lockFn f lock
theorem property87 : Property87 := by unfold Property87; intros; rfl

def method88 (trylock : (Unit → A) → L → A) (f : Unit → A) (lock : L) := trylock f lock
def Property88 : Prop := ∀ (L A : Type) trylock f lock,
  method88 (L := L) (A := A) trylock f lock = trylock f lock
theorem property88 : Property88 := by unfold Property88; intros; rfl

structure WeakSlot (K : Type) where
  value : Option K
  registered : Bool
  deriving Repr

def method90 (isK : Q → Bool) (isNothing : Q → Bool)
    (cleanup : W → R W) (getkey : W → Q → Option (WeakSlot Q))
    (register : W → Q → W) (setWeakValue : WeakSlot Q → Q → WeakSlot Q)
    (newWeak : Q → WeakSlot Q) (setindex : W → WeakSlot Q → V → R W)
    (wkh : W) (value : V) (key : Q) : R W :=
  if !isK key then .error "invalid WeakKeyDict key type"
  else if isNothing key then .error "nothing is not a valid WeakKeyDict key"
  else do
    let wkh ← cleanup wkh
    match getkey wkh key with
    | none => setindex (register wkh key) (newWeak key) value
    | some weak => setindex wkh (setWeakValue weak key) value
def Property90 : Prop := ∀ (Q V W : Type) isK isNothing cleanup getkey register
    setWeakValue newWeak setindex wkh value key,
  method90 (Q := Q) (V := V) (W := W) isK isNothing cleanup getkey register
      setWeakValue newWeak setindex wkh value key =
    if !isK key then .error "invalid WeakKeyDict key type"
    else if isNothing key then .error "nothing is not a valid WeakKeyDict key"
    else do
      let wkh ← cleanup wkh
      match getkey wkh key with
      | none => setindex (register wkh key) (newWeak key) value
      | some weak => setindex wkh (setWeakValue weak key) value
theorem property90 : Property90 := by unfold Property90; intros; rfl

def method108 (lookup : W → Q → Option V) (setindex : W → Q → V → R (V × W))
    (wkh : W) (key : Q) (default : V) : R (V × W) :=
  match lookup wkh key with | some value => .ok (value, wkh) | none => setindex wkh key default
def Property108 : Prop := ∀ (W Q V : Type) lookup setindex wkh key default,
  method108 (W := W) (Q := Q) (V := V) lookup setindex wkh key default =
    match lookup wkh key with | some value => .ok (value, wkh) | none => setindex wkh key default
theorem property108 : Property108 := by unfold Property108; intros; rfl

def method118 (lookup : W → Q → Option V) (default : Unit → R V)
    (setindex : W → Q → V → R (V × W)) (wkh : W) (key : Q) : R (V × W) :=
  match lookup wkh key with
  | some value => .ok (value, wkh)
  | none => do let value ← default (); setindex wkh key value
def Property118 : Prop := ∀ (W Q V : Type) lookup default setindex wkh key,
  method118 (W := W) (Q := Q) (V := V) lookup default setindex wkh key =
    match lookup wkh key with
    | some value => .ok (value, wkh)
    | none => do let value ← default (); setindex wkh key value
theorem property118 : Property118 := by unfold Property118; intros; rfl

def method129 (getWeak : W → Q → Option (WeakSlot K))
    (wkh : W) (key : Q) (default : K) : K :=
  match getWeak wkh key with | none => default | some weak => weak.value.getD default
def Property129 : Prop := ∀ (W Q K : Type) getWeak wkh key default,
  method129 (W := W) (Q := Q) (K := K) getWeak wkh key default =
    match getWeak wkh key with | none => default | some weak => weak.value.getD default
theorem property129 : Property129 := by unfold Property129; intros; rfl

def method138 (mapValues : (V → V) → W → W) (f : V → V) (dict : W) : W := mapValues f dict
def Property138 : Prop := ∀ (V W : Type) mapValues f dict,
  method138 (V := V) (W := W) mapValues f dict = mapValues f dict
theorem property138 : Property138 := by unfold Property138; intros; rfl

def method140 (isNothing : Q → Bool) (get : W → Q → V → V)
    (wkh : W) (key : Q) (default : V) : R V :=
  if isNothing key then .error "KeyError" else .ok (get wkh key default)
def Property140 : Prop := ∀ (W Q V : Type) (isNothing : Q → Bool)
    (get : W → Q → V → V) (wkh : W) (key : Q) (default : V),
  method140 (W := W) isNothing get wkh key default =
    if isNothing key then .error "KeyError" else .ok (get wkh key default)
theorem property140 : Property140 := by unfold Property140; intros; rfl

def method146 (isNothing : Q → Bool) (get : (Unit → R V) → W → Q → R V)
    (default : Unit → R V) (wkh : W) (key : Q) : R V :=
  if isNothing key then .error "KeyError" else get default wkh key
def Property146 : Prop := ∀ (W Q V : Type) (isNothing : Q → Bool)
    (get : (Unit → R V) → W → Q → R V) (default : Unit → R V)
    (wkh : W) (key : Q),
  method146 (W := W) isNothing get default wkh key =
    if isNothing key then .error "KeyError" else get default wkh key
theorem property146 : Property146 := by unfold Property146; intros; rfl

def method152 (isNothing : Q → Bool) (pop : W → Q → R (V × W))
    (wkh : W) (key : Q) : R (V × W) :=
  if isNothing key then .error "KeyError" else pop wkh key
def Property152 : Prop := ∀ (W Q V : Type) (isNothing : Q → Bool)
    (pop : W → Q → R (V × W)) (wkh : W) (key : Q),
  method152 (W := W) (V := V) isNothing pop wkh key =
    if isNothing key then .error "KeyError" else pop wkh key
theorem property152 : Property152 := by unfold Property152; intros; rfl

def method158 (isNothing : Q → Bool) (pop : W → Q → V → V × W)
    (wkh : W) (key : Q) (default : V) : V × W :=
  if isNothing key then (default, wkh) else pop wkh key default
def Property158 : Prop := ∀ (W Q V : Type) (isNothing : Q → Bool)
    (pop : W → Q → V → V × W) (wkh : W) (key : Q) (default : V),
  method158 (W := W) isNothing pop wkh key default =
    if isNothing key then (default, wkh) else pop wkh key default
theorem property158 : Property158 := by unfold Property158; intros; rfl

def method164 (isNothing : Q → Bool) (delete : W → Q → W) (wkh : W) (key : Q) : W :=
  if isNothing key then wkh else delete wkh key
def Property164 : Prop := ∀ (W Q : Type) (isNothing : Q → Bool)
    (delete : W → Q → W) (wkh : W) (key : Q),
  method164 (W := W) isNothing delete wkh key =
    if isNothing key then wkh else delete wkh key
theorem property164 : Property164 := by unfold Property164; intros; rfl

def method171 (empty : W → W) (wkh : W) : W := empty wkh
def Property171 : Prop := ∀ (W : Type) empty wkh,
  method171 (W := W) empty wkh = empty wkh
theorem property171 : Property171 := by unfold Property171; intros; rfl

def method177 (isNothing : Q → Bool) (haskey : W → Q → Bool) (wkh : W) (key : Q) : Bool :=
  if isNothing key then false else haskey wkh key
def Property177 : Prop := ∀ (W Q : Type) (isNothing : Q → Bool)
    (haskey : W → Q → Bool) (wkh : W) (key : Q),
  method177 (W := W) isNothing haskey wkh key =
    if isNothing key then false else haskey wkh key
theorem property177 : Property177 := by unfold Property177; intros; rfl

def method183 (isNothing : Q → Bool) (getindex : W → Q → R V) (wkh : W) (key : Q) : R V :=
  if isNothing key then .error "KeyError" else getindex wkh key
def Property183 : Prop := ∀ (W Q V : Type) (isNothing : Q → Bool)
    (getindex : W → Q → R V) (wkh : W) (key : Q),
  method183 (W := W) (V := V) isNothing getindex wkh key =
    if isNothing key then .error "KeyError" else getindex wkh key
theorem property183 : Property183 := by unfold Property183; intros; rfl

def method189 (length : W → Nat) (wkh : W) : Bool := length wkh == 0
def Property189 : Prop := ∀ (W : Type) length wkh,
  method189 (W := W) length wkh = (length wkh == 0)
theorem property189 : Property189 := by unfold Property189; intros; rfl

def wkIter : Nat → List (Option K × V) → Nat → Option ((K × V) × Nat)
  | 0, _, _ => none
  | fuel + 1, entries, index =>
      match entries[index]? with
      | none => none
      | some (none, _) => wkIter fuel entries (index + 1)
      | some (some key, value) => some ((key, value), index + 1)

def method197 (fuel : Nat) (entries : List (Option K × V)) (state : Nat) :=
  wkIter fuel entries state
def Property197 : Prop := ∀ (K V : Type) fuel entries state,
  method197 (K := K) (V := V) fuel entries state = wkIter fuel entries state
theorem property197 : Property197 := by unfold Property197; intros; rfl

def method212 (only : W → (W → Option P) → R P) (first : W → Option P) (dict : W) :=
  only dict first
def Property212 : Prop := ∀ (W P : Type) only first dict,
  method212 (W := W) (P := P) only first dict = only dict first
theorem property212 : Property212 := by unfold Property212; intros; rfl

def method214 (filterOnePass : (P → Bool) → W → W) (f : P → Bool) (dict : W) :=
  filterOnePass f dict
def Property214 : Prop := ∀ (W P : Type) filterOnePass f dict,
  method214 (W := W) (P := P) filterOnePass f dict = filterOnePass f dict
theorem property214 : Property214 := by unfold Property214; intros; rfl

/-! ## `WeakValueIdDict` -/

structure WV (K V : Type) where
  entries : List (K × Option V)
  dirty : Bool
  deriving Repr

def wvEmpty : WV K V := ⟨[], false⟩

def method222 (d : WV K V) (_value : V) : WV K V := { d with dirty := true }
def Property222 : Prop := ∀ (K V : Type) (d : WV K V) value,
  method222 d value = { d with dirty := true }
theorem property222 : Property222 := by unfold Property222; intros; rfl

def method244 : WV K V := wvEmpty
def Property244 : Prop := ∀ (K V : Type), method244 (K := K) (V := V) = wvEmpty
theorem property244 : Property244 := by unfold Property244; intros; rfl

def wvFold (setindex : WV K V → K → V → R (WV K V)) :
    WV K V → List (K × V) → R (WV K V)
  | dict, [] => .ok dict
  | dict, (key, value) :: rest => do
      let dict ← setindex dict key value
      wvFold setindex dict rest

def method250 (setindex : WV K V → K → V → R (WV K V)) (pairs : List (K × V)) :=
  wvFold setindex method244 pairs
def Property250 : Prop := ∀ (K V : Type)
    (setindex : WV K V → K → V → R (WV K V)) pairs,
  method250 setindex pairs = wvFold setindex method244 pairs
theorem property250 : Property250 := by unfold Property250; intros; rfl

def method257 (setindex : WV K V → K → V → R (WV K V)) (pair : K × V) :=
  setindex method244 pair.1 pair.2
def Property257 : Prop := ∀ (K V : Type)
    (setindex : WV K V → K → V → R (WV K V)) pair,
  method257 setindex pair = setindex method244 pair.1 pair.2
theorem property257 : Property257 := by unfold Property257; intros; rfl

def method258 (setindex : WV K V → K → V → R (WV K V)) (pairs : List (K × V)) :=
  wvFold setindex method244 pairs
def Property258 : Prop := ∀ (K V : Type)
    (setindex : WV K V → K → V → R (WV K V)) pairs,
  method258 setindex pairs = wvFold setindex method244 pairs
theorem property258 : Property258 := by unfold Property258; intros; rfl

def method265 : WV K V := method244
def Property265 : Prop := ∀ (K V : Type), method265 (K := K) (V := V) = method244
theorem property265 : Property265 := by unfold Property265; intros; rfl

def method267 (_emptyTuple : Unit) : WV K V := method265
def Property267 : Prop := ∀ (K V : Type), method267 (K := K) (V := V) () = method265
theorem property267 : Property267 := by unfold Property267; intros; rfl

def method268 (construct : WV K V → R (WV K V)) (d : WV K V) := construct d
def Property268 : Prop := ∀ (K V : Type) construct (d : WV K V),
  method268 construct d = construct d
theorem property268 : Property268 := by unfold Property268; intros; rfl

def method270 (construct : List (K × V) → R (WV K V)) (pairs : List (K × V)) := construct pairs
def Property270 : Prop := ∀ (K V : Type) construct pairs,
  method270 (K := K) (V := V) construct pairs = construct pairs
theorem property270 : Property270 := by unfold Property270; intros; rfl

def method271 (construct : List (K × V) → R (WV K V)) (pairs : List (K × V)) := construct pairs
def Property271 : Prop := ∀ (K V : Type) construct pairs,
  method271 (K := K) (V := V) construct pairs = construct pairs
theorem property271 : Property271 := by unfold Property271; intros; rfl

def method272 (construct : List (K × V) → R (WV K V)) (pairs : List (K × V)) := construct pairs
def Property272 : Prop := ∀ (K V : Type) construct pairs,
  method272 (K := K) (V := V) construct pairs = construct pairs
theorem property272 : Property272 := by unfold Property272; intros; rfl

def method273 (construct : List (K × V) → R (WV K V)) (pairs : List (K × V)) := construct pairs
def Property273 : Prop := ∀ (K V : Type) construct pairs,
  method273 (K := K) (V := V) construct pairs = construct pairs
theorem property273 : Property273 := by unfold Property273; intros; rfl

def method275 (eltype : I → T) (dictWithEltype : I → T → R (WV K V)) (kv : I) :=
  dictWithEltype kv (eltype kv)
def Property275 : Prop := ∀ (I T K V : Type) (eltype : I → T)
    (dictWithEltype : I → T → R (WV K V)) (kv : I),
  method275 (K := K) (V := V) eltype dictWithEltype kv = dictWithEltype kv (eltype kv)
theorem property275 : Property275 := by unfold Property275; intros; rfl

def method279 (h : WV K V) : WV K V :=
  ⟨h.entries.filter (fun pair => pair.2.isSome), false⟩
def Property279 : Prop := ∀ (K V : Type) (h : WV K V),
  method279 h = ⟨h.entries.filter (fun pair => pair.2.isSome), false⟩
theorem property279 : Property279 := by unfold Property279; intros; rfl

def method290 (sweep : WV K V → WV K V) (h : WV K V) : WV K V :=
  if h.dirty then sweep h else h
def Property290 : Prop := ∀ (K V : Type) sweep (h : WV K V),
  method290 sweep h = if h.dirty then sweep h else h
theorem property290 : Property290 := by unfold Property290; intros; rfl

def method292 : WV K V := method244
def Property292 : Prop := ∀ (K V : Type), method292 (K := K) (V := V) = method244
theorem property292 : Property292 := by unfold Property292; intros; rfl

def method294 : IteratorSizeTag := .sizeUnknown
def Property294 : Prop := ∀ (_K _V : Type), method294 = .sizeUnknown
theorem property294 : Property294 := by unfold Property294; intros; rfl

def method296 (islocked : L → Bool) (lock : L) := islocked lock
def Property296 : Prop := ∀ (L : Type) islocked lock,
  method296 (L := L) islocked lock = islocked lock
theorem property296 : Property296 := by unfold Property296; intros; rfl

def method297 (lockFn : L → A) (lock : L) := lockFn lock
def Property297 : Prop := ∀ (L A : Type) lockFn lock,
  method297 (L := L) (A := A) lockFn lock = lockFn lock
theorem property297 : Property297 := by unfold Property297; intros; rfl

def method298 (unlock : L → A) (lock : L) := unlock lock
def Property298 : Prop := ∀ (L A : Type) unlock lock,
  method298 (L := L) (A := A) unlock lock = unlock lock
theorem property298 : Property298 := by unfold Property298; intros; rfl

def method299 (lockFn : (Unit → A) → L → A) (f : Unit → A) (lock : L) := lockFn f lock
def Property299 : Prop := ∀ (L A : Type) lockFn f lock,
  method299 (L := L) (A := A) lockFn f lock = lockFn f lock
theorem property299 : Property299 := by unfold Property299; intros; rfl

def method300 (trylock : (Unit → A) → L → A) (f : Unit → A) (lock : L) := trylock f lock
def Property300 : Prop := ∀ (L A : Type) trylock f lock,
  method300 (L := L) (A := A) trylock f lock = trylock f lock
theorem property300 : Property300 := by unfold Property300; intros; rfl

def method302 (isK : Q → Bool) (isNothingKey : Q → Bool) (isNothingValue : W → Bool)
    (cleanup : D → D) (register : D → W → D) (setWeak : D → Q → W → R D)
    (dict : D) (value : W) (key : Q) : R D :=
  if !isK key then .error "invalid WeakValueIdDict key type"
  else if isNothingKey key then .error "nothing is not a valid WeakValueIdDict key"
  else if isNothingValue value then .error "nothing is not a valid WeakValueIdDict value"
  else setWeak (register (cleanup dict) value) key value
def Property302 : Prop := ∀ (D Q W : Type) isK isNothingKey isNothingValue cleanup
    register setWeak dict value key,
  method302 (D := D) (Q := Q) (W := W) isK isNothingKey isNothingValue cleanup
      register setWeak dict value key =
    if !isK key then .error "invalid WeakValueIdDict key type"
    else if isNothingKey key then .error "nothing is not a valid WeakValueIdDict key"
    else if isNothingValue value then .error "nothing is not a valid WeakValueIdDict value"
    else setWeak (register (cleanup dict) value) key value
theorem property302 : Property302 := by unfold Property302; intros; rfl

def method318 (getWeak : D → Q → Option (Option V)) (dict : D) (key : Q) : Option V :=
  match getWeak dict key with | none => none | some weakValue => weakValue
def Property318 : Prop := ∀ (D Q V : Type) getWeak dict key,
  method318 (D := D) (Q := Q) (V := V) getWeak dict key =
    match getWeak dict key with | none => none | some weakValue => weakValue
theorem property318 : Property318 := by unfold Property318; intros; rfl

def method324 (isNothing : Q → Bool) (getValue : D → Q → Option V)
    (dict : D) (key : Q) (default : V) : R V :=
  if isNothing key then .error "KeyError" else .ok ((getValue dict key).getD default)
def Property324 : Prop := ∀ (D Q V : Type) (isNothing : Q → Bool)
    (getValue : D → Q → Option V) (dict : D) (key : Q) (default : V),
  method324 (D := D) (V := V) isNothing getValue dict key default =
    if isNothing key then .error "KeyError" else .ok ((getValue dict key).getD default)
theorem property324 : Property324 := by unfold Property324; intros; rfl

def method331 (isNothing : Q → Bool) (getValue : D → Q → Option V)
    (default : Unit → R V) (dict : D) (key : Q) : R V :=
  if isNothing key then .error "KeyError" else
    match getValue dict key with | none => default () | some value => .ok value
def Property331 : Prop := ∀ (D Q V : Type) (isNothing : Q → Bool)
    (getValue : D → Q → Option V) (default : Unit → R V) (dict : D) (key : Q),
  method331 (D := D) isNothing getValue default dict key =
    if isNothing key then .error "KeyError" else
      match getValue dict key with | none => default () | some value => .ok value
theorem property331 : Property331 := by unfold Property331; intros; rfl

def method338 (getValue : D → Q → Option V) (setindex : D → Q → W → R D)
    (cast : W → R V) (dict : D) (key : Q) (default : W) : R (V × D) :=
  match getValue dict key with
  | some value => .ok (value, dict)
  | none => do
      let dict ← setindex dict key default
      let value ← cast default
      return (value, dict)
def Property338 : Prop := ∀ (D Q V W : Type) (getValue : D → Q → Option V)
    (setindex : D → Q → W → R D) (cast : W → R V)
    (dict : D) (key : Q) (default : W),
  method338 (D := D) (Q := Q) (V := V) getValue setindex cast dict key default =
    match getValue dict key with
    | some value => .ok (value, dict)
    | none => do
        let dict ← setindex dict key default
        let value ← cast default
        return (value, dict)
theorem property338 : Property338 := by unfold Property338; intros; rfl

def method346 (getValue : D → Q → Option V) (default : Unit → R W)
    (setindex : D → Q → W → R D) (cast : W → R V)
    (dict : D) (key : Q) : R (V × D) :=
  match getValue dict key with
  | some value => .ok (value, dict)
  | none => do
      let raw ← default ()
      let dict ← setindex dict key raw
      let value ← cast raw
      return (value, dict)
def Property346 : Prop := ∀ (D Q V W : Type) (getValue : D → Q → Option V)
    (default : Unit → R W) (setindex : D → Q → W → R D) (cast : W → R V)
    (dict : D) (key : Q),
  method346 (D := D) (Q := Q) (V := V) getValue default setindex cast dict key =
    match getValue dict key with
    | some value => .ok (value, dict)
    | none => do
        let raw ← default ()
        let dict ← setindex dict key raw
        let value ← cast raw
        return (value, dict)
theorem property346 : Property346 := by unfold Property346; intros; rfl

def method356 (isNothing : Q → Bool) (getValue : D → Q → Option V)
    (castKey : Q → R K) (dict : D) (key : Q) (default : K) : R K :=
  if isNothing key then .ok default
  else match getValue dict key with
    | none => .ok default
    | some _ => castKey key
def Property356 : Prop := ∀ (D Q V K : Type) (isNothing : Q → Bool)
    (getValue : D → Q → Option V) (castKey : Q → R K)
    (dict : D) (key : Q) (default : K),
  method356 (D := D) (V := V) isNothing getValue castKey dict key default =
    if isNothing key then .ok default
    else match getValue dict key with | none => .ok default | some _ => castKey key
theorem property356 : Property356 := by unfold Property356; intros; rfl

def method364 (isNothing : Q → Bool) (getValue : D → Q → Option V)
    (dict : D) (key : Q) : R V :=
  if isNothing key then .error "KeyError" else
    match getValue dict key with | none => .error "KeyError" | some value => .ok value
def Property364 : Prop := ∀ (D Q V : Type) (isNothing : Q → Bool)
    (getValue : D → Q → Option V) (dict : D) (key : Q),
  method364 (D := D) isNothing getValue dict key =
    if isNothing key then .error "KeyError" else
      match getValue dict key with | none => .error "KeyError" | some value => .ok value
theorem property364 : Property364 := by unfold Property364; intros; rfl

def method373 (isNothing : Q → Bool) (getValue : D → Q → Option V)
    (dict : D) (key : Q) : Bool :=
  if isNothing key then false else (getValue dict key).isSome
def Property373 : Prop := ∀ (D Q V : Type) (isNothing : Q → Bool)
    (getValue : D → Q → Option V) (dict : D) (key : Q),
  method373 (D := D) (V := V) isNothing getValue dict key =
    if isNothing key then false else (getValue dict key).isSome
theorem property373 : Property373 := by unfold Property373; intros; rfl

def method380 (isNothing : Q → Bool) (delete : D → Q → D) (dict : D) (key : Q) : D :=
  if isNothing key then dict else delete dict key
def Property380 : Prop := ∀ (D Q : Type) (isNothing : Q → Bool)
    (delete : D → Q → D) (dict : D) (key : Q),
  method380 (D := D) isNothing delete dict key =
    if isNothing key then dict else delete dict key
theorem property380 : Property380 := by unfold Property380; intros; rfl

def method388 (isNothing : Q → Bool) (getValue : D → Q → Option V)
    (delete : D → Q → D) (dict : D) (key : Q) : R (V × D) :=
  if isNothing key then .error "KeyError" else
    match getValue dict key with
    | none => .error "KeyError"
    | some value => .ok (value, delete dict key)
def Property388 : Prop := ∀ (D Q V : Type) (isNothing : Q → Bool)
    (getValue : D → Q → Option V) (delete : D → Q → D) (dict : D) (key : Q),
  method388 (D := D) isNothing getValue delete dict key =
    if isNothing key then .error "KeyError" else
      match getValue dict key with
      | none => .error "KeyError"
      | some value => .ok (value, delete dict key)
theorem property388 : Property388 := by unfold Property388; intros; rfl

def method397 (isNothing : Q → Bool) (getValue : D → Q → Option V)
    (delete : D → Q → D) (dict : D) (key : Q) (default : V) : V × D :=
  if isNothing key then (default, dict)
  else ((getValue dict key).getD default, delete dict key)
def Property397 : Prop := ∀ (D Q V : Type) (isNothing : Q → Bool)
    (getValue : D → Q → Option V) (delete : D → Q → D)
    (dict : D) (key : Q) (default : V),
  method397 (D := D) isNothing getValue delete dict key default =
    if isNothing key then (default, dict)
    else ((getValue dict key).getD default, delete dict key)
theorem property397 : Property397 := by unfold Property397; intros; rfl

def method406 (empty : D → D) (clearDirty : D → D) (dict : D) : D :=
  clearDirty (empty dict)
def Property406 : Prop := ∀ (D : Type) empty clearDirty dict,
  method406 (D := D) empty clearDirty dict = clearDirty (empty dict)
theorem property406 : Property406 := by unfold Property406; intros; rfl

def countLive : List (K × Option V) → Nat
  | [] => 0
  | (_, value) :: rest => (if value.isSome then 1 else 0) + countLive rest

def method414 (entries : List (K × Option V)) : Nat := countLive entries
def Property414 : Prop := ∀ (K V : Type) entries,
  method414 (K := K) (V := V) entries = countLive entries
theorem property414 : Property414 := by unfold Property414; intros; rfl

def method423 (length : D → Nat) (dict : D) : Bool := length dict == 0
def Property423 : Prop := ∀ (D : Type) length dict,
  method423 (D := D) length dict = (length dict == 0)
theorem property423 : Property423 := by unfold Property423; intros; rfl

def livePairs : List (K × Option V) → List (K × V)
  | [] => []
  | (key, none) :: rest => livePairs rest
  | (key, some value) :: rest => (key, value) :: livePairs rest

def method425 (entries : List (K × Option V))
    (snapshot : Option (List (K × V) × Nat)) : Option ((K × V) × (List (K × V) × Nat)) :=
  let (pairs, index) := snapshot.getD (livePairs entries, 0)
  let index := index + 1
  match pairs[index - 1]? with
  | none => none
  | some pair => some (pair, (pairs, index))
def Property425 : Prop := ∀ (K V : Type) entries snapshot,
  method425 (K := K) (V := V) entries snapshot =
    let (pairs, index) := snapshot.getD (livePairs entries, 0)
    let index := index + 1
    match pairs[index - 1]? with
    | none => none
    | some pair => some (pair, (pairs, index))
theorem property425 : Property425 := by unfold Property425; intros; rfl

private def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/weakdict.jl", juliaFns := [fn], statement := statement,
    source := source, status := .proven, prop := prop, thm := some thm }

def entries : List Entry := [
  entry "dictscov-weakdict-l8" "(d::WeakKeyDictFinalizer)(k)" "The WeakKeyDict finalizer marks its dictionary dirty." "weak-key cleanup invariant; base/weakdict.jl:8" ``Property8 ``property8,
  entry "dictscov-weakdict-l31" "WeakKeyDict{K,V}() where {K, V}" "The empty constructor creates an empty table, lock, clean flag, and self-referential finalizer." "WeakKeyDict docstring; base/weakdict.jl:31-35" ``Property31 ``property31,
  entry "dictscov-weakdict-l37" "WeakKeyDict{K,V}(kv) where V where K" "The iterator constructor inserts every pair in order." "WeakKeyDict docstring; base/weakdict.jl:37-43" ``Property37 ``property37,
  entry "dictscov-weakdict-l44" "WeakKeyDict{K,V}(p::Pair) where V where K" "The one-pair constructor inserts the pair into a new dictionary." "WeakKeyDict constructor invariant; base/weakdict.jl:44" ``Property44 ``property44,
  entry "dictscov-weakdict-l45" "WeakKeyDict{K,V}(ps::Pair...) where V where K" "The pair constructor size-hints and inserts every pair in order." "WeakKeyDict docstring; base/weakdict.jl:45-52" ``Property45 ``property45,
  entry "dictscov-weakdict-l53" "WeakKeyDict()" "The untyped constructor delegates to WeakKeyDict{Any,Any}." "constructor invariant; base/weakdict.jl:53" ``Property53 ``property53,
  entry "dictscov-weakdict-l55" "WeakKeyDict(kv::Tuple{})" "The empty-tuple constructor delegates to WeakKeyDict()." "constructor invariant; base/weakdict.jl:55" ``Property55 ``property55,
  entry "dictscov-weakdict-l56" "copy(d::WeakKeyDict)" "copy constructs a WeakKeyDict from the source iteration." "copy invariant; base/weakdict.jl:56" ``Property56 ``property56,
  entry "dictscov-weakdict-l58" "WeakKeyDict(ps::Pair{K,V}...) where {K,V}" "Homogeneous pairs delegate to the fully typed constructor." "constructor invariant; base/weakdict.jl:58" ``Property58 ``property58,
  entry "dictscov-weakdict-l59" "WeakKeyDict(ps::Pair{K}...) where {K}" "Key-homogeneous pairs delegate to WeakKeyDict{K,Any}." "constructor invariant; base/weakdict.jl:59" ``Property59 ``property59,
  entry "dictscov-weakdict-l60" "WeakKeyDict(ps::(Pair{K,V} where K)...) where {V}" "Value-homogeneous pairs delegate to WeakKeyDict{Any,V}." "constructor invariant; base/weakdict.jl:60" ``Property60 ``property60,
  entry "dictscov-weakdict-l61" "WeakKeyDict(ps::Pair...)" "Unconstrained pairs delegate to WeakKeyDict{Any,Any}." "constructor invariant; base/weakdict.jl:61" ``Property61 ``property61,
  entry "dictscov-weakdict-l63" "WeakKeyDict(kv)" "The generic constructor selects key and value types from iterator eltype." "WeakKeyDict docstring; base/weakdict.jl:63" ``Property63 ``property63,
  entry "dictscov-weakdict-l65" "_cleanup_locked(h::WeakKeyDict)" "Cleanup clears dirty and deletes every entry whose weak key has been cleared." "weak-key invariant; base/weakdict.jl:65-77" ``Property65 ``property65,
  entry "dictscov-weakdict-l79" "sizehint!(d::WeakKeyDict, newsz::Integer; shrink::Bool = true)" "sizehint! forwards size and shrink to the underlying table while locked." "sizehint! invariant; base/weakdict.jl:79" ``Property79 ``property79,
  entry "dictscov-weakdict-l80" "empty(d::WeakKeyDict, ::Type{K}, ::Type{V}) where {K, V}" "empty returns a new WeakKeyDict with the requested types." "empty docstring; base/weakdict.jl:80" ``Property80 ``property80,
  entry "dictscov-weakdict-l82" "IteratorSize(::Type{<:WeakKeyDict})" "WeakKeyDict reports SizeUnknown because collection can change its live keys." "iterator invariant; base/weakdict.jl:82" ``Property82 ``property82,
  entry "dictscov-weakdict-l84" "islocked(wkh::WeakKeyDict)" "islocked delegates to the contained lock." "lock invariant; base/weakdict.jl:84" ``Property84 ``property84,
  entry "dictscov-weakdict-l85" "lock(wkh::WeakKeyDict)" "lock delegates to the contained lock." "lock invariant; base/weakdict.jl:85" ``Property85 ``property85,
  entry "dictscov-weakdict-l86" "unlock(wkh::WeakKeyDict)" "unlock delegates to the contained lock." "lock invariant; base/weakdict.jl:86" ``Property86 ``property86,
  entry "dictscov-weakdict-l87" "lock(f, wkh::WeakKeyDict)" "Functional lock delegates the function and contained lock." "lock invariant; base/weakdict.jl:87" ``Property87 ``property87,
  entry "dictscov-weakdict-l88" "trylock(f, wkh::WeakKeyDict)" "Functional trylock delegates the function and contained lock." "lock invariant; base/weakdict.jl:88" ``Property88 ``property88,
  entry "dictscov-weakdict-l90" "setindex!(wkh::WeakKeyDict{K}, v, key) where K" "Insertion validates the key, cleans dead entries, registers a new weak key or retargets the existing wrapper, and stores the value." "WeakKeyDict docstring and invariant; base/weakdict.jl:90-107" ``Property90 ``property90,
  entry "dictscov-weakdict-l108" "get!(wkh::WeakKeyDict{K}, key, default) where {K}" "Value get! returns a present value or inserts and returns the supplied default." "get! invariant; base/weakdict.jl:108-117" ``Property108 ``property108,
  entry "dictscov-weakdict-l118" "get!(default::Callable, wkh::WeakKeyDict{K}, key) where {K}" "Callable get! calls, inserts, and returns the default only when absent." "get! invariant; base/weakdict.jl:118-127" ``Property118 ``property118,
  entry "dictscov-weakdict-l129" "getkey(wkh::WeakKeyDict{K}, kk, default) where K" "getkey returns the live referenced key or its supplied default." "getkey invariant; base/weakdict.jl:129-136" ``Property129 ``property129,
  entry "dictscov-weakdict-l138" "map!(f, iter::ValueIterator{<:WeakKeyDict})" "map! delegates to the values of the underlying strong table." "map! docstring; base/weakdict.jl:138" ``Property138 ``property138,
  entry "dictscov-weakdict-l140" "get(wkh::WeakKeyDict{K}, key, default) where {K}" "get rejects nothing and otherwise delegates while locked." "get invariant; base/weakdict.jl:140-145" ``Property140 ``property140,
  entry "dictscov-weakdict-l146" "get(default::Callable, wkh::WeakKeyDict{K}, key) where {K}" "Callable get rejects nothing and otherwise delegates lazily while locked." "get invariant; base/weakdict.jl:146-151" ``Property146 ``property146,
  entry "dictscov-weakdict-l152" "pop!(wkh::WeakKeyDict{K}, key) where {K}" "pop! rejects nothing and otherwise delegates while locked." "pop! invariant; base/weakdict.jl:152-157" ``Property152 ``property152,
  entry "dictscov-weakdict-l158" "pop!(wkh::WeakKeyDict{K}, key, default) where {K}" "Defaulted pop returns default for nothing and otherwise delegates while locked." "pop! invariant; base/weakdict.jl:158-163" ``Property158 ``property158,
  entry "dictscov-weakdict-l164" "delete!(wkh::WeakKeyDict, key)" "delete! ignores nothing and otherwise deletes from the underlying table while locked." "delete! invariant; base/weakdict.jl:164-170" ``Property164 ``property164,
  entry "dictscov-weakdict-l171" "empty!(wkh::WeakKeyDict)" "empty! clears the underlying table while locked and returns the wrapper." "empty! invariant; base/weakdict.jl:171-176" ``Property171 ``property171,
  entry "dictscov-weakdict-l177" "haskey(wkh::WeakKeyDict{K}, key) where {K}" "haskey is false for nothing and otherwise delegates while locked." "haskey invariant; base/weakdict.jl:177-182" ``Property177 ``property177,
  entry "dictscov-weakdict-l183" "getindex(wkh::WeakKeyDict{K}, key) where {K}" "Indexing rejects nothing and otherwise delegates while locked." "KeyError invariant; base/weakdict.jl:183-188" ``Property183 ``property183,
  entry "dictscov-weakdict-l189" "isempty(wkh::WeakKeyDict)" "WeakKeyDict is empty exactly when its reported length is zero." "iterator invariant; base/weakdict.jl:189" ``Property189 ``property189,
  entry "dictscov-weakdict-l197" "iterate(t::WeakKeyDict{K,V}, state...) where {K, V}" "Iteration skips cleared weak keys and returns each live key-value pair with resumable state." "WeakKeyDict docstring; base/weakdict.jl:197-210" ``Property197 ``property197,
  entry "dictscov-weakdict-l212" "Iterators.only(d::WeakKeyDict)" "only delegates to Iterators._only using first." "Iterators.only invariant; base/weakdict.jl:212" ``Property212 ``property212,
  entry "dictscov-weakdict-l214" "filter!(f, d::WeakKeyDict)" "WeakKeyDict filter! delegates to one-pass deletion." "filter! invariant; base/weakdict.jl:214" ``Property214 ``property214,
  entry "dictscov-weakdict-l222" "(d::WeakValueIdDictFinalizer)(v)" "The WeakValueIdDict finalizer marks its dictionary dirty." "weak-value cleanup invariant; base/weakdict.jl:222" ``Property222 ``property222,
  entry "dictscov-weakdict-l244" "WeakValueIdDict{K,V}() where {K, V}" "The empty constructor creates an empty identity table, lock, clean flag, and typed finalizer." "WeakValueIdDict docstring; base/weakdict.jl:244-248" ``Property244 ``property244,
  entry "dictscov-weakdict-l250" "WeakValueIdDict{K,V}(kv) where V where K" "The iterator constructor inserts every pair in order." "WeakValueIdDict docstring; base/weakdict.jl:250-256" ``Property250 ``property250,
  entry "dictscov-weakdict-l257" "WeakValueIdDict{K,V}(p::Pair) where V where K" "The one-pair constructor inserts the pair into a new dictionary." "constructor invariant; base/weakdict.jl:257" ``Property257 ``property257,
  entry "dictscov-weakdict-l258" "WeakValueIdDict{K,V}(ps::Pair...) where V where K" "The pair constructor inserts every pair in order." "constructor invariant; base/weakdict.jl:258-264" ``Property258 ``property258,
  entry "dictscov-weakdict-l265" "WeakValueIdDict()" "The untyped constructor delegates to WeakValueIdDict{Any,Any}." "constructor invariant; base/weakdict.jl:265" ``Property265 ``property265,
  entry "dictscov-weakdict-l267" "WeakValueIdDict(kv::Tuple{})" "The empty-tuple constructor delegates to WeakValueIdDict()." "constructor invariant; base/weakdict.jl:267" ``Property267 ``property267,
  entry "dictscov-weakdict-l268" "copy(d::WeakValueIdDict)" "copy constructs a WeakValueIdDict from the source iteration." "copy invariant; base/weakdict.jl:268" ``Property268 ``property268,
  entry "dictscov-weakdict-l270" "WeakValueIdDict(ps::Pair{K,V}...) where {K,V}" "Homogeneous pairs delegate to the fully typed constructor." "constructor invariant; base/weakdict.jl:270" ``Property270 ``property270,
  entry "dictscov-weakdict-l271" "WeakValueIdDict(ps::Pair{K}...) where {K}" "Key-homogeneous pairs delegate to WeakValueIdDict{K,Any}." "constructor invariant; base/weakdict.jl:271" ``Property271 ``property271,
  entry "dictscov-weakdict-l272" "WeakValueIdDict(ps::(Pair{K,V} where K)...) where {V}" "Value-homogeneous pairs delegate to WeakValueIdDict{Any,V}." "constructor invariant; base/weakdict.jl:272" ``Property272 ``property272,
  entry "dictscov-weakdict-l273" "WeakValueIdDict(ps::Pair...)" "Unconstrained pairs delegate to WeakValueIdDict{Any,Any}." "constructor invariant; base/weakdict.jl:273" ``Property273 ``property273,
  entry "dictscov-weakdict-l275" "WeakValueIdDict(kv)" "The generic constructor selects key and value types from iterator eltype." "WeakValueIdDict docstring; base/weakdict.jl:275" ``Property275 ``property275,
  entry "dictscov-weakdict-l279" "_sweep_locked(h::WeakValueIdDict{K}) where {K}" "Sweep collects dead keys, deletes them after iteration, and clears dirty." "weak-value invariant; base/weakdict.jl:279-289" ``Property279 ``property279,
  entry "dictscov-weakdict-l290" "_cleanup_locked(h::WeakValueIdDict)" "Cleanup sweeps only when dirty and otherwise returns the dictionary unchanged." "weak-value invariant; base/weakdict.jl:290" ``Property290 ``property290,
  entry "dictscov-weakdict-l292" "empty(d::WeakValueIdDict, ::Type{K}, ::Type{V}) where {K, V}" "empty returns a new WeakValueIdDict with the requested types." "empty docstring; base/weakdict.jl:292" ``Property292 ``property292,
  entry "dictscov-weakdict-l294" "IteratorSize(::Type{<:WeakValueIdDict})" "WeakValueIdDict reports SizeUnknown because collection can clear values." "iterator invariant; base/weakdict.jl:294" ``Property294 ``property294,
  entry "dictscov-weakdict-l296" "islocked(h::WeakValueIdDict)" "islocked delegates to the contained lock." "lock invariant; base/weakdict.jl:296" ``Property296 ``property296,
  entry "dictscov-weakdict-l297" "lock(h::WeakValueIdDict)" "lock delegates to the contained lock." "lock invariant; base/weakdict.jl:297" ``Property297 ``property297,
  entry "dictscov-weakdict-l298" "unlock(h::WeakValueIdDict)" "unlock delegates to the contained lock." "lock invariant; base/weakdict.jl:298" ``Property298 ``property298,
  entry "dictscov-weakdict-l299" "lock(f, h::WeakValueIdDict)" "Functional lock delegates the function and contained lock." "lock invariant; base/weakdict.jl:299" ``Property299 ``property299,
  entry "dictscov-weakdict-l300" "trylock(f, h::WeakValueIdDict)" "Functional trylock delegates the function and contained lock." "lock invariant; base/weakdict.jl:300" ``Property300 ``property300,
  entry "dictscov-weakdict-l302" "setindex!(h::WeakValueIdDict{K,V}, v, key) where {K,V}" "Insertion validates key and sentinel restrictions, cleans, registers the value, and stores a weak reference." "WeakValueIdDict docstring and invariant; base/weakdict.jl:302-315" ``Property302 ``property302,
  entry "dictscov-weakdict-l318" "_getvalue(h::WeakValueIdDict, key)" "_getvalue returns nothing for an absent or cleared wrapper and the live value otherwise." "weak-value invariant; base/weakdict.jl:318-322" ``Property318 ``property318,
  entry "dictscov-weakdict-l324" "get(h::WeakValueIdDict{K,V}, key, default) where {K,V}" "get rejects nothing and returns the live V or its supplied default." "get invariant; base/weakdict.jl:324-330" ``Property324 ``property324,
  entry "dictscov-weakdict-l331" "get(default::Callable, h::WeakValueIdDict{K,V}, key) where {K,V}" "Callable get rejects nothing and invokes its default only without a live value." "get invariant; base/weakdict.jl:331-337" ``Property331 ``property331,
  entry "dictscov-weakdict-l338" "get!(h::WeakValueIdDict{K,V}, key, default) where {K,V}" "Value get! returns a live V or stores the default and enforces the V return cast." "get! invariant; base/weakdict.jl:338-345" ``Property338 ``property338,
  entry "dictscov-weakdict-l346" "get!(default::Callable, h::WeakValueIdDict{K,V}, key) where {K,V}" "Callable get! returns a live V or calls and stores the default before enforcing the V cast." "get! invariant; base/weakdict.jl:346-354" ``Property346 ``property346,
  entry "dictscov-weakdict-l356" "getkey(h::WeakValueIdDict{K}, kk, default) where {K}" "getkey returns default for nothing or a dead value and casts the live key to K." "getkey invariant; base/weakdict.jl:356-362" ``Property356 ``property356,
  entry "dictscov-weakdict-l364" "getindex(h::WeakValueIdDict{K,V}, key) where {K,V}" "Indexing rejects nothing and missing or dead values, otherwise returning V." "KeyError invariant; base/weakdict.jl:364-371" ``Property364 ``property364,
  entry "dictscov-weakdict-l373" "haskey(h::WeakValueIdDict, key)" "haskey is false for nothing and true exactly for a live value." "haskey invariant; base/weakdict.jl:373-378" ``Property373 ``property373,
  entry "dictscov-weakdict-l380" "delete!(h::WeakValueIdDict, key)" "delete! ignores nothing and otherwise removes the identity key while locked." "delete! invariant; base/weakdict.jl:380-386" ``Property380 ``property380,
  entry "dictscov-weakdict-l388" "pop!(h::WeakValueIdDict{K,V}, key) where {K,V}" "pop! rejects nothing and missing or dead values, otherwise deleting and returning V." "pop! invariant; base/weakdict.jl:388-396" ``Property388 ``property388,
  entry "dictscov-weakdict-l397" "pop!(h::WeakValueIdDict{K,V}, key, default) where {K,V}" "Defaulted pop returns default for nothing or no live value and otherwise returns V, deleting non-nothing keys." "pop! invariant; base/weakdict.jl:397-404" ``Property397 ``property397,
  entry "dictscov-weakdict-l406" "empty!(h::WeakValueIdDict)" "empty! clears the underlying table and dirty flag while locked." "empty! invariant; base/weakdict.jl:406-412" ``Property406 ``property406,
  entry "dictscov-weakdict-l414" "length(h::WeakValueIdDict)" "length counts exactly the stored wrappers whose values remain live." "iterator invariant; base/weakdict.jl:414-422" ``Property414 ``property414,
  entry "dictscov-weakdict-l423" "isempty(h::WeakValueIdDict)" "WeakValueIdDict is empty exactly when its live length is zero." "iterator invariant; base/weakdict.jl:423" ``Property423 ``property423,
  entry "dictscov-weakdict-l425" "iterate(h::WeakValueIdDict{K,V}, snapshot::Union{Nothing,Tuple{Vector{Pair{K,V}},Int}}=nothing) where {K,V}" "Iteration snapshots live pairs under the lock and resumes by one-based snapshot index." "iterator invariant; base/weakdict.jl:425-444" ``Property425 ``property425
]

end JuliaLean.DictsCov.WeakDictRows
