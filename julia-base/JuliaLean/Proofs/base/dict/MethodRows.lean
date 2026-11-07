import JuliaLean.base.dict
import JuliaLean.Registry.Types

/-!
# Remaining method-specific models for `base/dict.jl`

The hash-table methods already covered by `JuliaLean.Dicts` and the earlier
`DictsCov` modules are reused. This file covers the remaining constructors,
`ImmutableDict`, and `PersistentDict`. An immutable dictionary is its newest-
first linked-list spine. Persistent HAMT operations are explicit callbacks,
so each method controls the source order of hashing, path copying, insertion,
deletion, lookup, and conversion.
-/

namespace JuliaLean.DictsCov.DictRows

open JuliaLean.Registry


def Property116 : Prop := ∀ (K V D : Type) construct pairs,
  method116 (K := K) (V := V) (D := D) construct pairs = construct pairs
theorem property116 : Property116 := by unfold Property116; intros; rfl

def Property118 : Prop := ∀ (I T D : Type) eltype dictWithEltype kv,
  method118 (I := I) (T := T) (D := D) eltype dictWithEltype kv =
    dictWithEltype kv (eltype kv)
theorem property118 : Property118 := by unfold Property118; intros; rfl

def Property120 : Prop := ∀ (D : Type) emptyDict, method120 (D := D) emptyDict = emptyDict ()
theorem property120 : Property120 := by unfold Property120; intros; rfl

/-! ## `ImmutableDict` -/


def Property780 : Prop := ∀ (K V : Type), method780 (K := K) (V := V) = []
theorem property780 : Property780 := by unfold Property780; intros; rfl

def Property781 : Prop := ∀ (K V : Type) key value,
  method781 (K := K) (V := V) key value = [(key, value)]
theorem property781 : Property781 := by unfold Property781; intros; rfl

def Property782 : Prop := ∀ (K V : Type) parent key value,
  method782 (K := K) (V := V) parent key value = (key, value) :: parent
theorem property782 : Property782 := by unfold Property782; intros; rfl

def Property811 : Prop := ∀ (K V : Type) pair,
  method811 (K := K) (V := V) pair = method781 pair.1 pair.2
theorem property811 : Property811 := by unfold Property811; intros; rfl

def Property812 : Prop := ∀ (K V Q W : Type) (convertKey : Q → R K)
    (convertValue : W → R V) (dict : Imm K V) (pair : Q × W),
  method812 (K := K) (V := V) convertKey convertValue dict pair = do
    let key ← convertKey pair.1
    let value ← convertValue pair.2
    return method782 dict key value
theorem property812 : Property812 := by unfold Property812; intros; rfl


def Property813 : Prop := ∀ (K V Q W : Type)
    (add : Imm K V → Q × W → R (Imm K V))
    (dict : Imm K V) (pair : Q × W) (rest : List (Q × W)),
  method813 (K := K) (V := V) add dict pair rest = do
    let dict ← add dict pair
    immAppend add dict rest
theorem property813 : Property813 := by unfold Property813; intros; rfl

def Property815 : Prop := ∀ (K V Q W : Type)
    (first : Q × W → R (Imm K V))
    (add : Imm K V → Q × W → R (Imm K V))
    (pair : Q × W) (rest : List (Q × W)),
  method815 (K := K) (V := V) first add pair rest = do
    let dict ← first pair
    immAppend add dict rest
theorem property815 : Property815 := by unfold Property815; intros; rfl

def Property828 : Prop := ∀ (K V Q : Type) (isequal : K → Q → Bool)
    (dict : Imm K V) (query : Q),
  method828 isequal dict query = match dict with
    | [] => false
    | (key, _) :: parent => if isequal key query then true else method828 isequal parent query
theorem property828 : Property828 := by
  unfold Property828; intro K V Q eq dict query; cases dict <;> rfl

def Property836 : Prop := ∀ (K V Q : Type) (isequal : K → Q → Bool)
    (dict : Imm K V) (query : Q),
  method836 isequal dict query = match dict with
    | [] => .error "KeyError"
    | (key, value) :: parent =>
        if isequal key query then .ok value else method836 isequal parent query
theorem property836 : Property836 := by
  unfold Property836; intro K V Q eq dict query; cases dict <;> rfl

def Property843 : Prop := ∀ (K V Q : Type) (isequal : K → Q → Bool)
    (dict : Imm K V) (query : Q) (default : V),
  method843 isequal dict query default = match dict with
    | [] => default
    | (key, value) :: parent =>
        if isequal key query then value else method843 isequal parent query default
theorem property843 : Property843 := by
  unfold Property843; intro K V Q eq dict query default; cases dict <;> rfl

def Property851 : Prop := ∀ (K V Q : Type) (isequal : K → Q → Bool)
    (dict : Imm K V) (query : Q) (default : Unit → R V),
  method851 isequal dict query default = match dict with
    | [] => default ()
    | (key, value) :: parent =>
        if isequal key query then .ok value else method851 isequal parent query default
theorem property851 : Property851 := by
  unfold Property851; intro K V Q eq dict query default; cases dict <;> rfl

def Property860 : Prop := ∀ (K V : Type) (dict state : Imm K V),
  method860 state = match state with | [] => none | pair :: parent => some (pair, parent)
theorem property860 : Property860 := by unfold Property860; intros; rfl

def Property864 : Prop := ∀ (K V : Type) (dict : Imm K V), method864 dict = dict.length
theorem property864 : Property864 := by unfold Property864; intros; rfl

def Property865 : Prop := ∀ (K V : Type) (dict : Imm K V), method865 dict = dict.isEmpty
theorem property865 : Property865 := by unfold Property865; intros; rfl

def Property866 : Prop := ∀ (K V : Type), method866 (K := K) (V := V) = []
theorem property866 : Property866 := by unfold Property866; intros; rfl

def Property890 : Prop := ∀ (D T : Type) empty dict keyType valueType,
  method890 (D := D) (T := T) empty dict keyType valueType = empty dict keyType valueType
theorem property890 : Property890 := by unfold Property890; intros; rfl

def Property891 : Prop := ∀ (D T : Type) dict elementType,
  method891 (D := D) (T := T) dict elementType =
    .error "for AbstractDicts, similar requires an element type of Pair;\n  if calling map, consider a comprehension instead"
theorem property891 : Property891 := by unfold Property891; intros; rfl

/-! ## `PersistentDict` -/



def Property903 : Prop := ∀ (H : Type) emptyHamt,
  method903 (H := H) emptyHamt = ⟨emptyHamt ()⟩
theorem property903 : Property903 := by unfold Property903; intros; rfl

def Property906 : Prop := ∀ (H K V : Type) (singleton : K → V → H) (key : K) (value : V),
  method906 (H := H) singleton key value = ⟨singleton key value⟩
theorem property906 : Property906 := by unfold Property906; intros; rfl

def Property909 : Prop := ∀ (H K V : Type) set dict key value,
  method909 (H := H) (K := K) (V := V) set dict key value = set dict key value
theorem property909 : Property909 := by unfold Property909; intros; rfl

def Property913 : Prop := ∀ (H K V S I B : Type) hashState path insert dict key value,
  method913 (H := H) (K := K) (V := V) (S := S) (I := I) (B := B)
      hashState path insert dict key value =
    let result := path dict.trie (hashState key) true
    ⟨insert result.found result.present result.trie result.index result.bitmap
      result.state value⟩
theorem property913 : Property913 := by unfold Property913; intros; rfl

def Property920 : Prop := ∀ (H K : Type) delete dict key,
  method920 (H := H) (K := K) delete dict key = delete dict key
theorem property920 : Property920 := by unfold Property920; intros; rfl

def Property922 : Prop := ∀ (H K : Type) delete dict key,
  method922 (H := H) (K := K) delete dict key = delete dict key
theorem property922 : Property922 := by unfold Property922; intros; rfl

def Property924 : Prop := ∀ (H K S I B : Type) hashState path deleteAt unset dict key,
  method924 (H := H) (K := K) (S := S) (I := I) (B := B)
      hashState path deleteAt unset dict key =
    let result := path dict.trie (hashState key) true
    if result.found && result.present then
      ⟨unset (deleteAt result.top result.index) result.bitmap⟩
    else ⟨result.top⟩
theorem property924 : Property924 := by unfold Property924; intros; rfl

def Property969 : Prop := ∀ (H : Type) set,
  method969 (H := H) set = set ()
theorem property969 : Property969 := by unfold Property969; intros; rfl

def Property970 : Prop := ∀ (H K V : Type) set pair,
  method970 (H := H) (K := K) (V := V) set pair = set pair.1 pair.2
theorem property970 : Property970 := by unfold Property970; intros; rfl

def Property976 : Prop := ∀ (H K V : Type) set pair,
  method976 (H := H) (K := K) (V := V) set pair = set pair.1 pair.2
theorem property976 : Property976 := by unfold Property976; intros; rfl

def Property982 : Prop := ∀ (H K V : Type) construct dict pair,
  method982 (H := H) (K := K) (V := V) construct dict pair = construct dict pair.1 pair.2
theorem property982 : Property982 := by unfold Property982; intros; rfl

def Property983 : Prop := ∀ (H K V : Type) construct dict pair,
  method983 (H := H) (K := K) (V := V) construct dict pair = construct dict pair.1 pair.2
theorem property983 : Property983 := by unfold Property983; intros; rfl

def Property986 : Prop := ∀ (H K V Q W : Type) (convertKey : Q → R K)
    (convertValue : W → R V) (set : Persistent H → K → V → Persistent H)
    (dict : Persistent H) (key : Q) (value : W),
  method986 (H := H) (K := K) (V := V) convertKey convertValue set dict key value = do
    let key ← convertKey key
    let value ← convertValue value
    return set dict key value
theorem property986 : Property986 := by unfold Property986; intros; rfl


def Property992 : Prop := ∀ (H K V : Type) first add pair rest,
  method992 (H := H) (K := K) (V := V) first add pair rest = do
    let dict ← first pair
    persistentFold add dict rest
theorem property992 : Property992 := by unfold Property992; intros; rfl

def Property1000 : Prop := ∀ (H K V : Type) first add pair rest,
  method1000 (H := H) (K := K) (V := V) first add pair rest = do
    let dict ← first pair
    persistentFold add dict rest
theorem property1000 : Property1000 := by unfold Property1000; intros; rfl

def Property1008 : Prop := ∀ (K V : Type), method1008 (K := K) (V := V) = ⟨⟩
theorem property1008 : Property1008 := by unfold Property1008; intros; rfl

def Property1010 : Prop := ∀ (H K V : Type) (get : Persistent H → K → Option V)
    (valcmp : V → V → Bool) (dict : Persistent H) (pair : K × V),
  method1010 (H := H) get valcmp dict pair = match get dict pair.1 with
    | none => false | some value => valcmp pair.2 value
theorem property1010 : Property1010 := by unfold Property1010; intros; rfl

def Property1017 : Prop := ∀ (H K V : Type) (get : Persistent H → K → Option V)
    (dict : Persistent H) (key : K),
  method1017 (H := H) (V := V) get dict key = (get dict key).isSome
theorem property1017 : Property1017 := by unfold Property1017; intros; rfl

def Property1021 : Prop := ∀ (H K V : Type) (get : Persistent H → K → Option V)
    (dict : Persistent H) (key : K),
  method1021 (H := H) get dict key = match get dict key with
    | none => .error "KeyError" | some value => .ok value
theorem property1021 : Property1021 := by unfold Property1021; intros; rfl

def Property1027 : Prop := ∀ (H K V : Type) (get : Persistent H → K → Option V)
    (dict : Persistent H) (key : K) (default : V),
  method1027 (H := H) get dict key default = match get dict key with
    | none => default | some value => value
theorem property1027 : Property1027 := by unfold Property1027; intros; rfl

def Property1033 : Prop := ∀ (H K V S I B : Type) empty hashState path leafAt dict key,
  method1033 (H := H) (K := K) (V := V) (S := S) (I := I) (B := B)
      empty hashState path leafAt dict key =
    if empty dict.trie then none else
      let result := path dict.trie (hashState key)
      if result.found && result.present then leafAt result.trie result.index else none
theorem property1033 : Property1033 := by unfold Property1033; intros; rfl

def Property1047 : Prop := ∀ (H K V : Type) (get : Persistent H → K → Option V)
    (default : Unit → R V) (dict : Persistent H) (key : K),
  method1047 (H := H) get default dict key = match get dict key with
    | none => default () | some value => .ok value
theorem property1047 : Property1047 := by unfold Property1047; intros; rfl

def Property1053 : Prop := ∀ (H K V : Type) (get : Persistent H → K → Option V)
    (default : Unit → R V) (dict : Persistent H) (key : K),
  method1053 (H := H) get default dict key = match get dict key with
    | none => default () | some value => .ok value
theorem property1053 : Property1053 := by unfold Property1053; intros; rfl

def Property1059 : Prop := ∀ (H K : Type) delete dict key,
  method1059 (H := H) (K := K) delete dict key = delete dict key
theorem property1059 : Property1059 := by unfold Property1059; intros; rfl

def Property1063 : Prop := ∀ (H S P : Type) iterateHamt dict state,
  method1063 (H := H) (S := S) (P := P) iterateHamt dict state = iterateHamt dict.trie state
theorem property1063 : Property1063 := by unfold Property1063; intros; rfl

def Property1065 : Prop := ∀ (H : Type) lengthHamt dict,
  method1065 (H := H) lengthHamt dict = lengthHamt dict.trie
theorem property1065 : Property1065 := by unfold Property1065; intros; rfl

def Property1066 : Prop := ∀ (H : Type) emptyHamt dict,
  method1066 (H := H) emptyHamt dict = emptyHamt dict.trie
theorem property1066 : Property1066 := by unfold Property1066; intros; rfl

def Property1067 : Prop := ∀ (H : Type) emptyPersistent,
  method1067 (H := H) emptyPersistent = emptyPersistent ()
theorem property1067 : Property1067 := by unfold Property1067; intros; rfl

def Property1069 : Prop := ∀ (H K V : Type) only first dict,
  method1069 (H := H) (K := K) (V := V) only first dict = only dict first
theorem property1069 : Property1069 := by unfold Property1069; intros; rfl

private def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/dict.jl", juliaFns := [fn], statement := statement,
    source := source, status := .proven, prop := prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.DictsCov.DictRows
