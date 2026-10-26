import JuliaLean.Registry.Types

/-!
# Method-specific models for `base/hamt.jl`

The bitmap is represented by a natural number reduced to 32 bits after each
write. List positions are zero based in Lean, so `entryIndex - 1` is the Julia
array position. The fuel arguments make the source `while` loops total; every
iteration preserves the source order of bitmap calculation, lookup, optional
copy, descent, and hash advancement.
-/

namespace JuliaLean.DictsCov.HamtRows

open JuliaLean.Registry

abbrev R (α : Type) := Except String α

inductive Tree (K V : Type) where
  | leaf (key : K) (value : V)
  | branch (data : List (Tree K V)) (bitmap : Nat)
  deriving Repr

def mask32 : Nat := 2 ^ 32 - 1
def levelMask : Nat := 31
def bitsPerLevel : Nat := 5
def maxShift : Nat := 55

def u32 (x : Nat) : Nat := x % (2 ^ 32)
def shiftLeft (v n : Nat) : Nat := v * 2 ^ n
def shiftRight (v n : Nat) : Nat := v / 2 ^ n

def bitSet (bitmap i : Nat) : Nat := u32 (Nat.lor bitmap (shiftLeft 1 i))
def bitUnset (bitmap i : Nat) : Nat :=
  Nat.land bitmap (Nat.xor mask32 (shiftLeft 1 i))

def countOnes : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => x % 2 + countOnes n (x / 2)

structure HashState (K : Type) where
  key : K
  hash : Nat
  depth : Nat
  shift : Nat
  deriving Repr, DecidableEq

structure BitmapIndex where
  x : Nat
  deriving Repr, DecidableEq

/-- Inner HAMT constructor, `base/hamt.jl:65`. -/
def method65 (data : List (Tree K V)) (bitmap : Nat) : Tree K V := .branch data bitmap
def Property65 : Prop := ∀ (K V : Type) data bitmap,
  method65 (K := K) (V := V) data bitmap = .branch data bitmap
theorem property65 : Property65 := by unfold Property65; intros; rfl

/-- Empty HAMT constructor, `base/hamt.jl:66`. -/
def method66 : Tree K V := .branch [] 0
def Property66 : Prop := ∀ (K V : Type), method66 (K := K) (V := V) = .branch [] 0
theorem property66 : Property66 := by unfold Property66; intros; rfl

/-- Allocate a one-element, unset-bitmap HAMT, `base/hamt.jl:69-74`. -/
def method69 (k : K) (v : V) : Tree K V := .branch [.leaf k v] 0
def Property69 : Prop := ∀ (K V : Type) k v,
  method69 (K := K) (V := V) k v = .branch [.leaf k v] 0
theorem property69 : Property69 := by unfold Property69; intros; rfl

/-- Default HashState constructor, `base/hamt.jl:93`. -/
def method93 (objectid : K → Nat) (key : K) : HashState K :=
  { key := key, hash := objectid key, depth := 0, shift := 0 }
def Property93 : Prop := ∀ (K : Type) objectid key,
  method93 (K := K) objectid key =
    { key := key, hash := objectid key, depth := 0, shift := 0 }
theorem property93 : Property93 := by unfold Property93; intros; rfl

/-- Advance a hash state, `base/hamt.jl:103-117`. -/
def method103 (rehash : Nat → Nat → Nat) (h : HashState K) : HashState K :=
  let depth := h.depth + 1
  let shift := h.shift + bitsPerLevel
  if shift > maxShift then
    { key := h.key, hash := rehash h.hash (depth / bitsPerLevel), depth := depth, shift := 0 }
  else
    { key := h.key, hash := h.hash, depth := depth, shift := shift }
def Property103 : Prop := ∀ (K : Type) rehash (h : HashState K),
  method103 rehash h =
    let depth := h.depth + 1
    let shift := h.shift + bitsPerLevel
    if shift > maxShift then
      { key := h.key, hash := rehash h.hash (depth / bitsPerLevel), depth := depth, shift := 0 }
    else { key := h.key, hash := h.hash, depth := depth, shift := shift }
theorem property103 : Property103 := by unfold Property103; intros; rfl

def advanceToDepth (rehash : Nat → Nat → Nat) : Nat → HashState K → HashState K
  | 0, h => h
  | fuel + 1, h => method103 rehash (advanceToDepth rehash fuel h)

/-- Depth-aligning HashState constructor, `base/hamt.jl:94-100`. -/
def method94 (objectid : K → Nat) (rehash : Nat → Nat → Nat)
    (other : HashState Q) (key : K) : HashState K :=
  advanceToDepth rehash other.depth (method93 objectid key)
def Property94 : Prop := ∀ (K Q : Type) objectid rehash (other : HashState Q) key,
  method94 (K := K) objectid rehash other key =
    advanceToDepth rehash other.depth (method93 objectid key)
theorem property94 : Property94 := by unfold Property94; intros; rfl

/-- Type-inferring HashState wrapper, `base/hamt.jl:101`. -/
def method101 (construct : HashState Q → K → HashState K) (other : HashState Q) (key : K) :=
  construct other key
def Property101 : Prop := ∀ (K Q : Type) construct (other : HashState Q) key,
  method101 (K := K) construct other key = construct other key
theorem property101 : Property101 := by unfold Property101; intros; rfl

/-- BitmapIndex constructor, `base/hamt.jl:122`. -/
def method122 (h : HashState K) : BitmapIndex :=
  ⟨Nat.land (shiftRight h.hash h.shift) levelMask⟩
def Property122 : Prop := ∀ (K : Type) (h : HashState K),
  method122 h = ⟨Nat.land (shiftRight h.hash h.shift) levelMask⟩
theorem property122 : Property122 := by unfold Property122; intros; rfl

/-- Bitmap-indexed left shift, `base/hamt.jl:124`. -/
def method124 (v : Nat) (bi : BitmapIndex) : Nat := shiftLeft v bi.x
def Property124 : Prop := ∀ v bi, method124 v bi = shiftLeft v bi.x
theorem property124 : Property124 := by unfold Property124; intros; rfl

/-- Bitmap-indexed right shift, `base/hamt.jl:125`. -/
def method125 (v : Nat) (bi : BitmapIndex) : Nat := shiftRight v bi.x
def Property125 : Prop := ∀ v bi, method125 v bi = shiftRight v bi.x
theorem property125 : Property125 := by unfold Property125; intros; rfl

/-- Test a HAMT bitmap bit, `base/hamt.jl:127`. -/
def method127 : Tree K V → BitmapIndex → Bool
  | .leaf _ _, _ => false
  | .branch _ bitmap, bi => (shiftRight bitmap bi.x) % 2 == 1
def Property127 : Prop := ∀ (K V : Type) data bitmap bi,
  method127 (.branch data bitmap : Tree K V) bi = ((shiftRight bitmap bi.x) % 2 == 1)
theorem property127 : Property127 := by unfold Property127; intros; rfl

/-- Set a HAMT bitmap bit, `base/hamt.jl:128-131`. -/
def method128 : Tree K V → BitmapIndex → Tree K V
  | .leaf k v, _ => .leaf k v
  | .branch data bitmap, bi => .branch data (bitSet bitmap bi.x)
def Property128 : Prop := ∀ (K V : Type) data bitmap bi,
  method128 (.branch data bitmap : Tree K V) bi = .branch data (bitSet bitmap bi.x)
theorem property128 : Property128 := by unfold Property128; intros; rfl

/-- Unset a HAMT bitmap bit, `base/hamt.jl:133-136`. -/
def method133 : Tree K V → BitmapIndex → Tree K V
  | .leaf k v, _ => .leaf k v
  | .branch data bitmap, bi => .branch data (bitUnset bitmap bi.x)
def Property133 : Prop := ∀ (K V : Type) data bitmap bi,
  method133 (.branch data bitmap : Tree K V) bi = .branch data (bitUnset bitmap bi.x)
theorem property133 : Property133 := by unfold Property133; intros; rfl

/-- Sparse-array entry index, `base/hamt.jl:138-141`. -/
def method138 : Tree K V → BitmapIndex → Nat
  | .leaf _ _, _ => 1
  | .branch _ bitmap, bi =>
      let mask := shiftLeft 1 bi.x - 1
      countOnes 32 (Nat.land bitmap mask) + 1
def Property138 : Prop := ∀ (K V : Type) data bitmap bi,
  method138 (.branch data bitmap : Tree K V) bi =
    let mask := shiftLeft 1 bi.x - 1
    countOnes 32 (Nat.land bitmap mask) + 1
theorem property138 : Property138 := by unfold Property138; intros; rfl

/-- HAMT-level emptiness, `base/hamt.jl:143`. -/
def method143 : Tree K V → Bool
  | .leaf _ _ => false
  | .branch _ bitmap => bitmap == 0
def Property143 : Prop := ∀ (K V : Type) data bitmap,
  method143 (.branch data bitmap : Tree K V) = (bitmap == 0)
theorem property143 : Property143 := by unfold Property143; intros; rfl

/-- Leaf-level emptiness, `base/hamt.jl:144`. -/
def method144 (_leaf : K × V) : Bool := false
def Property144 : Prop := ∀ (K V : Type) (leaf : K × V), method144 leaf = false
theorem property144 : Property144 := by unfold Property144; intros; rfl

structure PathResult (K V : Type) where
  found : Bool
  present : Bool
  trie : Tree K V
  index : Nat
  bi : BitmapIndex
  top : Tree K V
  hash : HashState K
  deriving Repr

def replaceAt (xs : List α) (oneBased : Nat) (x : α) : List α :=
  if oneBased == 0 then xs else xs.set (oneBased - 1) x

def pathLoop (same : K → K → Bool) (rehash : Nat → Nat → Nat) (copy : Bool) :
    Nat → Tree K V → Tree K V → HashState K → R (PathResult K V)
  | 0, _, _, _ => .error "path fuel exhausted"
  | fuel + 1, .leaf _ _, _, _ => .error "path expected HAMT"
  | fuel + 1, .branch data bitmap, top, h =>
      let bi := method122 h
      let i := method138 (.branch data bitmap) bi
      if method127 (.branch data bitmap) bi then
        match data[i - 1]? with
        | none => .error "bounds"
        | some (.leaf key value) =>
            .ok ⟨same key h.key, true, .branch data bitmap, i, bi, top, h⟩
        | some (.branch childData childBitmap) =>
            let child := .branch childData childBitmap
            let child := if copy then .branch childData childBitmap else child
            let data := if copy then replaceAt data i child else data
            pathLoop same rehash copy fuel child top (method103 rehash h)
      else .ok ⟨true, false, .branch data bitmap, i, bi, top, h⟩

/-- HAMT path search and optional copy, `base/hamt.jl:158-186`. -/
def method158 (same : K → K → Bool) (rehash : Nat → Nat → Nat) (fuel : Nat)
    (trie : Tree K V) (h : HashState K) (copy : Bool) : R (PathResult K V) :=
  let top := match trie with
    | .leaf k v => .leaf k v
    | .branch data bitmap => if copy then .branch data bitmap else trie
  pathLoop same rehash copy fuel top top h
def Property158 : Prop := ∀ (K V : Type) same rehash fuel (trie : Tree K V) h copy,
  method158 same rehash fuel trie h copy =
    let top := match trie with
      | .leaf k v => .leaf k v
      | .branch data bitmap => if copy then .branch data bitmap else trie
    pathLoop same rehash copy fuel top top h
theorem property158 : Property158 := by unfold Property158; intros; rfl

/-- Typed-pair HAMT constructor, `base/hamt.jl:76-81`. -/
def method76 (objectid : K → Nat) (k : K) (v : V) : Tree K V :=
  let trie := method69 k v
  let bi := method122 (method93 objectid k)
  method128 trie bi
def Property76 : Prop := ∀ (K V : Type) objectid k v,
  method76 (K := K) (V := V) objectid k v =
    method128 (method69 k v) (method122 (method93 objectid k))
theorem property76 : Property76 := by unfold Property76; intros; rfl

/-- Converting-pair HAMT constructor, `base/hamt.jl:82`. -/
def method82 {Q : Type} (convert : Q → K × V) (construct : K × V → Tree K V) (kv : Q) : Tree K V :=
  construct (convert kv)
def Property82 : Prop := ∀ (K V Q : Type) (convert : Q → K × V)
    (construct : K × V → Tree K V) (kv : Q),
  method82 (K := K) (V := V) convert construct kv = construct (convert kv)
theorem property82 : Property82 := by unfold Property82; intros; rfl

/-- Type-inferring HAMT constructor, `base/hamt.jl:84`. -/
def method84 (construct : K × V → Tree K V) (pair : K × V) : Tree K V := construct pair
def Property84 : Prop := ∀ (K V : Type) construct pair,
  method84 (K := K) (V := V) construct pair = construct pair
theorem property84 : Property84 := by unfold Property84; intros; rfl

/-- Leaf length, `base/hamt.jl:242`. -/
def method242 (_leaf : K × V) : Nat := 1
def Property242 : Prop := ∀ (K V : Type) (leaf : K × V), method242 leaf = 1
theorem property242 : Property242 := by unfold Property242; intros; rfl

def treeLength : Tree K V → Nat
  | .leaf _ _ => 1
  | .branch data _ => (data.map treeLength).foldl (· + ·) 0

/-- HAMT length, `base/hamt.jl:243`. -/
def method243 : Tree K V → Nat
  | .leaf _ _ => 1
  | .branch data _ => (data.map treeLength).foldl (· + ·) 0
def Property243 : Prop := ∀ (K V : Type) data bitmap,
  method243 (.branch data bitmap : Tree K V) = (data.map treeLength).foldl (· + ·) 0
theorem property243 : Property243 := by unfold Property243; intros; rfl

/-- Leaf isempty, `base/hamt.jl:245`. -/
def method245 (_leaf : K × V) : Bool := false
def Property245 : Prop := ∀ (K V : Type) (leaf : K × V), method245 leaf = false
theorem property245 : Property245 := by unfold Property245; intros; rfl

mutual
  def treeEmpty : Tree K V → Bool
    | .leaf _ _ => false
    | .branch data bitmap => bitmap == 0 || treeListEmpty data

  def treeListEmpty : List (Tree K V) → Bool
    | [] => true
    | tree :: trees => treeEmpty tree && treeListEmpty trees
end

/-- HAMT isempty, `base/hamt.jl:246-251`. -/
def method246 : Tree K V → Bool
  | .leaf _ _ => false
  | .branch data bitmap => if bitmap == 0 then true else treeListEmpty data
def Property246 : Prop := ∀ (K V : Type) data bitmap,
  method246 (.branch data bitmap : Tree K V) =
    if bitmap == 0 then true else treeListEmpty data
theorem property246 : Property246 := by unfold Property246; intros; rfl

abbrev Frame (K V : Type) := List (Tree K V) × Nat
abbrev IterState (K V : Type) := List (Frame K V)

def iterLoop : Nat → IterState K V → Option ((K × V) × IterState K V)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, (data, i) :: parent =>
      if i ≥ data.length then iterLoop fuel parent
      else match data[i]? with
        | none => none
        | some (.leaf key value) => some ((key, value), (data, i + 1) :: parent)
        | some (.branch child _) => iterLoop fuel ((child, 0) :: (data, i + 1) :: parent)

/-- DFS iterator, `base/hamt.jl:254-275`. -/
def method254 (fuel : Nat) (trie : Tree K V) (state : Option (IterState K V)) :
    Option ((K × V) × IterState K V) :=
  let state := match state with
    | some state => state
    | none => match trie with
      | .leaf k v => [([.leaf k v], 0)]
      | .branch data _ => [(data, 0)]
  iterLoop fuel state
def Property254 : Prop := ∀ (K V : Type) fuel (trie : Tree K V) state,
  method254 fuel trie state =
    let state := match state with
      | some state => state
      | none => match trie with
        | .leaf k v => [([.leaf k v], 0)]
        | .branch data _ => [(data, 0)]
    iterLoop fuel state
theorem property254 : Property254 := by unfold Property254; intros; rfl

private def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/hamt.jl", juliaFns := [fn], statement := statement,
    source := source, status := .proven, prop := prop, thm := some thm }

def entries : List Entry := [
  entry "dictscov-hamt-l65" "HAMT{K,V}(data, bitmap) where {K,V}" "The inner constructor stores the supplied sparse data and bitmap." "invariant; base/hamt.jl:65" ``Property65 ``property65,
  entry "dictscov-hamt-l66" "HAMT{K, V}() where {K, V}" "The empty constructor has no children and a zero bitmap." "HAMT invariant; base/hamt.jl:66" ``Property66 ``property66,
  entry "dictscov-hamt-l69" "init_hamt(K, V, k, v)" "A single-entry allocation contains one leaf and an unset bitmap." "HAMT invariant; base/hamt.jl:69-74" ``Property69 ``property69,
  entry "dictscov-hamt-l76" "HAMT{K,V}((k,v)::Pair{K,V}) where {K, V}" "The typed-pair constructor sets the bitmap bit selected by the key hash." "HAMT invariant; base/hamt.jl:76-81" ``Property76 ``property76,
  entry "dictscov-hamt-l82" "HAMT{K,V}(kv::Pair) where {K, V}" "The converting constructor converts the pair before typed construction." "constructor invariant; base/hamt.jl:82" ``Property82 ``property82,
  entry "dictscov-hamt-l84" "HAMT(pair::Pair{K,V}) where {K, V}" "The type-inferring constructor delegates with the pair's key and value types." "constructor invariant; base/hamt.jl:84" ``Property84 ``property84,
  entry "dictscov-hamt-l93" "HashState(key)" "A new hash state uses objectid at depth and shift zero." "invariant; base/hamt.jl:93" ``Property93 ``property93,
  entry "dictscov-hamt-l94" "HashState{K}(@nospecialize(other::HashState), @nospecialize(key)) where {K}" "The derived hash state advances to the other state's depth." "invariant; base/hamt.jl:94-100" ``Property94 ``property94,
  entry "dictscov-hamt-l101" "HashState(other::HashState, key)" "The inferred constructor delegates to the key-typed constructor." "invariant; base/hamt.jl:101" ``Property101 ``property101,
  entry "dictscov-hamt-l103" "next(h::HashState{K}) where {K}" "next increments depth and shift, rehashing and resetting shift after MAX_SHIFT." "HAMT invariant; base/hamt.jl:103-117" ``Property103 ``property103,
  entry "dictscov-hamt-l122" "BitmapIndex(h::HashState)" "BitmapIndex selects the five hash bits at the current shift." "HAMT invariant; base/hamt.jl:122" ``Property122 ``property122,
  entry "dictscov-hamt-l124" "Base.:(<<)(v, bi::BitmapIndex)" "A BitmapIndex shifts left by its stored index." "invariant; base/hamt.jl:124" ``Property124 ``property124,
  entry "dictscov-hamt-l125" "Base.:(>>)(v, bi::BitmapIndex)" "A BitmapIndex shifts right by its stored index." "invariant; base/hamt.jl:125" ``Property125 ``property125,
  entry "dictscov-hamt-l127" "isset(trie::HAMT, bi::BitmapIndex)" "isset tests the selected bitmap bit." "HAMT invariant; base/hamt.jl:127" ``Property127 ``property127,
  entry "dictscov-hamt-l128" "set!(trie::HAMT, bi::BitmapIndex)" "set! sets exactly the selected bitmap bit." "HAMT invariant; base/hamt.jl:128-131" ``Property128 ``property128,
  entry "dictscov-hamt-l133" "unset!(trie::HAMT, bi::BitmapIndex)" "unset! clears exactly the selected bitmap bit." "HAMT invariant; base/hamt.jl:133-136" ``Property133 ``property133,
  entry "dictscov-hamt-l138" "entry_index(trie::HAMT, bi::BitmapIndex)" "entry_index is one plus the number of lower occupied bits." "HAMT invariant; base/hamt.jl:138-141" ``Property138 ``property138,
  entry "dictscov-hamt-l143" "islevel_empty(trie::HAMT)" "A HAMT level is empty exactly when its bitmap is zero." "HAMT invariant; base/hamt.jl:143" ``Property143 ``property143,
  entry "dictscov-hamt-l144" "islevel_empty(::Leaf)" "A leaf level is never empty." "HAMT invariant; base/hamt.jl:144" ``Property144 ``property144,
  entry "dictscov-hamt-l158" "path(trie::HAMT{K,V}, h::HashState, copy=false) where {K, V}" "path follows occupied bitmap entries, optionally copying each branch, until it finds a leaf or empty slot." "path docstring and invariant; base/hamt.jl:147-186" ``Property158 ``property158,
  entry "dictscov-hamt-l242" "Base.length(::Leaf)" "Every leaf contributes one entry." "HAMT invariant; base/hamt.jl:242" ``Property242 ``property242,
  entry "dictscov-hamt-l243" "Base.length(trie::HAMT)" "HAMT length is the recursive sum of child lengths." "HAMT invariant; base/hamt.jl:243" ``Property243 ``property243,
  entry "dictscov-hamt-l245" "Base.isempty(::Leaf)" "A leaf is not empty." "HAMT invariant; base/hamt.jl:245" ``Property245 ``property245,
  entry "dictscov-hamt-l246" "Base.isempty(trie::HAMT)" "A HAMT is empty when its level is empty or every child is empty." "HAMT invariant; base/hamt.jl:246-251" ``Property246 ``property246,
  entry "dictscov-hamt-l254" "Base.iterate(trie::HAMT, state=nothing)" "The iterator performs depth-first traversal and returns every leaf pair with resumable state." "HAMT invariant; base/hamt.jl:253-275" ``Property254 ``property254
]

end JuliaLean.DictsCov.HamtRows
