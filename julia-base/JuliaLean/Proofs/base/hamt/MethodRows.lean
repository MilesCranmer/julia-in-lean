import JuliaLean.base.hamt
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









def Property65 : Prop := ∀ (K V : Type) data bitmap,
  method65 (K := K) (V := V) data bitmap = .branch data bitmap
theorem property65 : Property65 := by unfold Property65; intros; rfl

def Property66 : Prop := ∀ (K V : Type), method66 (K := K) (V := V) = .branch [] 0
theorem property66 : Property66 := by unfold Property66; intros; rfl

def Property69 : Prop := ∀ (K V : Type) k v,
  method69 (K := K) (V := V) k v = .branch [.leaf k v] 0
theorem property69 : Property69 := by unfold Property69; intros; rfl

def Property93 : Prop := ∀ (K : Type) objectid key,
  method93 (K := K) objectid key =
    { key := key, hash := objectid key, depth := 0, shift := 0 }
theorem property93 : Property93 := by unfold Property93; intros; rfl

def Property103 : Prop := ∀ (K : Type) rehash (h : HashState K),
  method103 rehash h =
    let depth := h.depth + 1
    let shift := h.shift + bitsPerLevel
    if shift > maxShift then
      { key := h.key, hash := rehash h.hash (depth / bitsPerLevel), depth := depth, shift := 0 }
    else { key := h.key, hash := h.hash, depth := depth, shift := shift }
theorem property103 : Property103 := by unfold Property103; intros; rfl


def Property94 : Prop := ∀ (K Q : Type) objectid rehash (other : HashState Q) key,
  method94 (K := K) objectid rehash other key =
    advanceToDepth rehash other.depth (method93 objectid key)
theorem property94 : Property94 := by unfold Property94; intros; rfl

def Property101 : Prop := ∀ (K Q : Type) construct (other : HashState Q) key,
  method101 (K := K) construct other key = construct other key
theorem property101 : Property101 := by unfold Property101; intros; rfl

def Property122 : Prop := ∀ (K : Type) (h : HashState K),
  method122 h = ⟨Nat.land (shiftRight h.hash h.shift) levelMask⟩
theorem property122 : Property122 := by unfold Property122; intros; rfl

def Property124 : Prop := ∀ v bi, method124 v bi = shiftLeft v bi.x
theorem property124 : Property124 := by unfold Property124; intros; rfl

def Property125 : Prop := ∀ v bi, method125 v bi = shiftRight v bi.x
theorem property125 : Property125 := by unfold Property125; intros; rfl

def Property127 : Prop := ∀ (K V : Type) data bitmap bi,
  method127 (.branch data bitmap : Tree K V) bi = ((shiftRight bitmap bi.x) % 2 == 1)
theorem property127 : Property127 := by unfold Property127; intros; rfl

def Property128 : Prop := ∀ (K V : Type) data bitmap bi,
  method128 (.branch data bitmap : Tree K V) bi = .branch data (bitSet bitmap bi.x)
theorem property128 : Property128 := by unfold Property128; intros; rfl

def Property133 : Prop := ∀ (K V : Type) data bitmap bi,
  method133 (.branch data bitmap : Tree K V) bi = .branch data (bitUnset bitmap bi.x)
theorem property133 : Property133 := by unfold Property133; intros; rfl

def Property138 : Prop := ∀ (K V : Type) data bitmap bi,
  method138 (.branch data bitmap : Tree K V) bi =
    let mask := shiftLeft 1 bi.x - 1
    countOnes 32 (Nat.land bitmap mask) + 1
theorem property138 : Property138 := by unfold Property138; intros; rfl

def Property143 : Prop := ∀ (K V : Type) data bitmap,
  method143 (.branch data bitmap : Tree K V) = (bitmap == 0)
theorem property143 : Property143 := by unfold Property143; intros; rfl

def Property144 : Prop := ∀ (K V : Type) (leaf : K × V), method144 leaf = false
theorem property144 : Property144 := by unfold Property144; intros; rfl




def Property158 : Prop := ∀ (K V : Type) same rehash fuel (trie : Tree K V) h copy,
  method158 same rehash fuel trie h copy =
    let top := match trie with
      | .leaf k v => .leaf k v
      | .branch data bitmap => if copy then .branch data bitmap else trie
    pathLoop same rehash copy fuel top top h
theorem property158 : Property158 := by unfold Property158; intros; rfl

def Property76 : Prop := ∀ (K V : Type) objectid k v,
  method76 (K := K) (V := V) objectid k v =
    method128 (method69 k v) (method122 (method93 objectid k))
theorem property76 : Property76 := by unfold Property76; intros; rfl

def Property82 : Prop := ∀ (K V Q : Type) (convert : Q → K × V)
    (construct : K × V → Tree K V) (kv : Q),
  method82 (K := K) (V := V) convert construct kv = construct (convert kv)
theorem property82 : Property82 := by unfold Property82; intros; rfl

def Property84 : Prop := ∀ (K V : Type) construct pair,
  method84 (K := K) (V := V) construct pair = construct pair
theorem property84 : Property84 := by unfold Property84; intros; rfl

def Property242 : Prop := ∀ (K V : Type) (leaf : K × V), method242 leaf = 1
theorem property242 : Property242 := by unfold Property242; intros; rfl


def Property243 : Prop := ∀ (K V : Type) data bitmap,
  method243 (.branch data bitmap : Tree K V) = (data.map treeLength).foldl (· + ·) 0
theorem property243 : Property243 := by unfold Property243; intros; rfl

def Property245 : Prop := ∀ (K V : Type) (leaf : K × V), method245 leaf = false
theorem property245 : Property245 := by unfold Property245; intros; rfl


def Property246 : Prop := ∀ (K V : Type) data bitmap,
  method246 (.branch data bitmap : Tree K V) =
    if bitmap == 0 then true else treeListEmpty data
theorem property246 : Property246 := by unfold Property246; intros; rfl



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

def entries : List Entry := []

end JuliaLean.DictsCov.HamtRows
