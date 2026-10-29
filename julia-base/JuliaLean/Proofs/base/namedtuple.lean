import JuliaLean.base.namedtuple
import JuliaLean.Registry.Types

/-!
# Properties of `base/namedtuple.jl`

These specifications describe named-tuple values, field order, conversion, iteration, comparison,
and construction. Core operations and functions from other Base files remain typed parameters where
this model's heterogeneous field representation cannot use their existing Lean model directly.
-/

namespace JuliaLean.Proofs.base.namedtuple

open JuliaLean JuliaLean.base.namedtuple JuliaLean.Registry

/-- The first occurrence determines field position in a sequence of key-value pairs. -/
def firstSymbolKeysLoop (seen : List String) : List KV → List String
  | [] => seen
  | pair :: rest =>
      match pair.key with
      | .symbol key => firstSymbolKeysLoop (if seen.contains key then seen else seen ++ [key]) rest
      | _ => firstSymbolKeysLoop seen rest

def firstSymbolKeys (pairs : List KV) : List String := firstSymbolKeysLoop [] pairs

/-- The value of a key is taken from its final occurrence. -/
def lastSymbolValue : List KV → String → Option Value
  | [], _ => none
  | pair :: rest, key =>
      match lastSymbolValue rest key with
      | some value => some value
      | none =>
          match pair.key with
          | .symbol name => if name = key then some pair.value else none
          | _ => none

def namedTupleFields (nt : ModelNT) : List KV :=
  (nt.type.names.zip nt.values).map fun (name, value) => ⟨.symbol name, value⟩

def namedTupleFieldsMany (nts : List ModelNT) : List KV := nts.flatMap namedTupleFields

def outputMatchesFields (out : ModelNT) (fields : List KV) : Prop :=
  out.type.names = firstSymbolKeys fields ∧
  ∀ key, key ∈ out.type.names →
    match lastSymbolValue fields key with
    | some value => getfield out key = .ok value
    | none => False

def selectedNamedTupleFields (nt : ModelNT) (names : List String) : List KV :=
  names.filterMap fun name =>
    match getfield nt name with
    | .ok value => some ⟨.symbol name, value⟩
    | .error _ => none

/-- An integer key should address the corresponding one-based field. -/
def HaskeyInteger : Prop :=
  ∀ (native : Bool) (nt : ModelNT) (i : Int) (default : Value) (fallback : Unit → Value),
    nt.values.length = nt.type.names.length →
    let key := if native then Key.nativeInteger i else Key.integer i
    let inBounds := 1 ≤ i ∧ i ≤ Int.ofNat nt.values.length
    haskey nt key = .ok (decide inBounds) ∧
    getDefault nt key default =
      (if inBounds then getfieldIndex nt i else .ok default) ∧
    getDefaultFunction fallback nt key =
      (if inBounds then getfieldIndex nt i else .ok (fallback ()))

/-- Merging preserves first field positions and takes each field's final supplied value;
structdiff and selection retain the requested fields. -/
def NamedTupleCorrect : Prop :=
  ∀ (generated : Bool) (a b : ModelNT),
    a.type.names.Nodup → b.type.names.Nodup →
    a.values.length = a.type.names.length → b.values.length = b.type.names.length →
    (∀ out, mergeNamed generated a b = .ok out →
      outputMatchesFields out (namedTupleFields a ++ namedTupleFields b)) ∧
    (∀ out, merge_fallback a b a.type.names b.type.names = .ok out →
      outputMatchesFields out (namedTupleFields a ++ namedTupleFields b)) ∧
    (∀ out, structdiffNamed generated a b = .ok out →
      outputMatchesFields out ((namedTupleFields a).filter fun pair =>
        match pair.key with
        | .symbol key => !(b.type.names.contains key)
        | _ => true)) ∧
    (∀ (typeofValue : Value → TypeTag) (value : Value) (key : String) out,
      setindexNamed generated typeofValue a value key = .ok out →
      outputMatchesFields out (namedTupleFields a ++ [⟨.symbol key, value⟩])) ∧
    (∀ (idxs : List String), idxs.Nodup →
      (∀ key, key ∈ idxs → ∃ value, getfield a key = .ok value) →
      ∃ out, getindexSymbols generated a idxs = .ok out ∧
        out.type.names = idxs ∧
        ∀ key, key ∈ idxs → getfield out key = getfield a key) ∧
    (∀ (idxs : List String) out, idxs.Nodup →
      (∀ key, key ∈ idxs → ∃ value, getfield a key = .ok value) →
      getindexSymbolVector generated a idxs = .ok out →
      outputMatchesFields out (selectedNamedTupleFields a idxs))

/-- Constructors reject a count mismatch, preserve the requested field names, and retain fields in
source order after conversion. -/
def NTConstructCorrect : Prop :=
  ∀ (convert : TypeTag → Value → Result Value) (target : NTType) (args : List Value),
    (args.length ≠ target.names.length →
      constructTyped convert target args =
        .error (.argumentError "Wrong number of arguments to named tuple constructor.")) ∧
    (target.names.Nodup → target.fieldTypes.length = target.names.length →
      args.length = target.names.length →
      ∀ out, constructTyped convert target args = .ok out →
        out.type = target ∧ out.values.length = target.names.length) ∧
    (∀ (generated : Bool) (isA : Value → TypeTag → Bool) (nt : ModelNT) out,
      nt.type.names.Nodup → nt.values.length = nt.type.names.length →
      nt.type.fieldTypes.length = nt.type.names.length →
      constructFromNamedTuple generated convert isA nt.type nt = .ok out →
      out.type.names = nt.type.names ∧ out.values.length = nt.type.names.length) ∧
    (∀ (generated : Bool) (nt : ModelNT) (names : List String) out,
      names.Nodup → (∀ name, name ∈ names → ∃ value, getfield nt name = .ok value) →
      constructNamesFromNamedTuple generated nt names = .ok out →
      outputMatchesFields out (selectedNamedTupleFields nt names)) ∧
    (∀ (generated : Bool) (isA : Value → TypeTag → Bool) (nt : ModelNT) out,
      convertMatchingNames generated convert isA nt.type nt = .ok out →
      out.type.names = nt.type.names) ∧
    (∀ (target : NTType) (nt out : ModelNT),
      convertAbstractTarget convert target nt = .ok out → out.type.names = target.names) ∧
    (∀ (target : NTType) (values : List Value) out,
      convertTupleToNamedTuple convert target values = .ok out →
      out.type.names = target.names) ∧
    (∀ (target : NTType) (args : List Value),
      (new_NamedTuple target args).type = target ∧ (new_NamedTuple target args).values = args) ∧
    (∀ (nt : ModelNT), Tuple nt = nt.values ∧ valuesNamedTuple nt = nt.values) ∧
    (∀ {α : Type} (target : α) (nt : α),
      convertSameNames target nt = nt ∧ convertSameConcreteType target nt = nt) ∧
    (∀ (isT : List Value → Bool) (convert : List Value → Result (List Value)) (nt : ModelNT),
      isT (Tuple nt) = true → convertToTuple isT convert nt = .ok (Tuple nt)) ∧
    (∀ {I : Type 1} (toValues : I → Result (List Value))
      (convert : TypeTag → Value → Result Value) (target : NTType) (itr : I) out,
      target.names.Nodup → target.fieldTypes.length = target.names.length →
      constructTypedFromIterator toValues convert target itr = .ok out →
      out.type.names = target.names) ∧
    (∀ {I : Type 1} (toValues : I → Result (List Value))
      (fromTuple : NTType → List Value → Result ModelNT) (typeofValue : Value → TypeTag)
      (names : List String) (itr : I) (values : List Value) out,
      names.Nodup → toValues itr = .ok values →
      (∀ ty vals result, fromTuple ty vals = .ok result →
        result.type = ty ∧ result.values = vals) →
      constructNamesFromIterator toValues fromTuple typeofValue names itr = .ok out →
      out.type.names = names ∧ out.values = values) ∧
    (∀ {I : Type 1} (toPairs : I → Result (List KV))
      (fromTuple : NTType → List Value → Result ModelNT) (typeofValue : Value → TypeTag)
      (itr : I) pairs out,
      toPairs itr = .ok pairs →
      (∀ pair, pair ∈ pairs → ∃ key, pair.key = .symbol key) →
      (∀ ty vals result, fromTuple ty vals = .ok result →
        result.type = ty ∧ result.values = vals) →
      namedTupleFromIterator toPairs fromTuple typeofValue itr = .ok out →
      outputMatchesFields out pairs)

/-- Named tuples iterate and index their values in field order, expose keys and values separately,
and trim or reverse the corresponding fields. -/
def NTAccessCorrect : Prop :=
  ∀ (nfields : ModelNT → JInt .i64) (nt : ModelNT),
    nt.type.names.Nodup → nt.values.length = nt.type.names.length →
    (nfields nt).val = Int.ofNat nt.type.names.length →
    length nfields nt = nfields nt ∧ firstindex nt = JuliaLean.base.int.lit .i64 1 ∧
    lastindex nfields nt = nfields nt ∧ keysNamedTuple nt = nt.type.names ∧
    valuesNamedTuple nt = nt.values ∧ getindexColon nt = nt ∧ restAll nt = nt ∧
    (∀ (i : JInt .i64), 1 ≤ i.val → i.val ≤ Int.ofNat nt.type.names.length →
      ∃ name value,
        nt.type.names[i.val.toNat - 1]? = some name ∧
        nt.values[i.val.toNat - 1]? = some value ∧
        getindexInt nt i = .ok value ∧ getindexSymbol nt name = .ok value) ∧
    isEmptyEmpty emptyNamedTuple = true ∧
    (nt.type.names ≠ [] → isEmptyNamedTuple nt = false) ∧
    emptyNamedTuple.type.names = [] ∧ emptyNamedTuple.values = [] ∧
(∀ {I : Type} (greater : I → JInt .i64 → Bool)
      (getfieldAt : ModelNT → I → Result Value) (increment : I → I) (one iter : I),
      greater iter (nfields nt) = false →
      iterate nfields greater getfieldAt increment one nt iter =
        some ((getfieldAt nt iter).map (fun value => (value, increment iter)))) ∧
    (∀ {I : Type} (greater : I → JInt .i64 → Bool)
      (getfieldAt : ModelNT → I → Result Value) (increment : I → I) (one iter : I),
      greater iter (nfields nt) = true →
      iterate nfields greater getfieldAt increment one nt iter = none) ∧
    (∀ (i : JInt .i64) (value : Value),
      getfieldIndex nt i.val = .ok value →
      indexed_iterate nt i = .ok (value, JuliaLean.base.int.add i (JuliaLean.base.int.lit .i64 1))) ∧
    (∀ (tailNames frontNames : List String → Result (List String)),
      (∀ names, names ≠ [] → tailNames names = .ok (names.drop 1)) →
      (∀ names, names ≠ [] → frontNames names = .ok names.dropLast) →
      (∀ out, tailNamed tailNames nt = .ok out →
        outputMatchesFields out (selectedNamedTupleFields nt (nt.type.names.drop 1))) ∧
      (∀ out, frontNamed frontNames nt = .ok out →
        outputMatchesFields out (selectedNamedTupleFields nt nt.type.names.dropLast))) ∧
    (∀ (namesAfter : List String → Int → Result (List String)) (i : JInt .i64) (out : ModelNT),
      0 ≤ i.val → i.val ≤ Int.ofNat nt.type.names.length →
      namesAfter nt.type.names i.val = .ok (nt.type.names.drop i.val.toNat) →
      restAfter namesAfter nt i = .ok out →
      outputMatchesFields out (selectedNamedTupleFields nt (nt.type.names.drop i.val.toNat))) ∧
    (∀ (fromTuple : NTType → List Value → Result ModelNT)
      (typeofValue : Value → TypeTag) out,
      (∀ ty vals result, fromTuple ty vals = .ok result →
        result.type = ty ∧ result.values = vals) →
      reverseNamedTuple fromTuple typeofValue nt = .ok out →
      out.type.names = nt.type.names.reverse ∧ out.values = nt.values.reverse) ∧
    (∀ {I : Type} (convertInt : I → Result (JInt .i64)) (i : I) (x : JInt .i64),
      convertInt i = .ok x →
      prevind nt convertInt i = .ok (JuliaLean.base.int.sub x (JuliaLean.base.int.lit .i64 1)) ∧
      nextind nt convertInt i = .ok (JuliaLean.base.int.add x (JuliaLean.base.int.lit .i64 1)))

/-- Equal field-name types compare and order their value tuples; mismatched equality is false. -/
def NTCompareCorrect : Prop :=
  ∀ (eqTuple isequalTuple : List Value → List Value → Bool)
    (ltTuple : List Value → List Value → Result Bool) (a b : ModelNT),
    (a.type.names = b.type.names →
      equalSameNames eqTuple a b = eqTuple (Tuple a) (Tuple b) ∧
      isequalSameNames isequalTuple a b = isequalTuple (Tuple a) (Tuple b) ∧
      lessSameNames ltTuple a b = ltTuple (Tuple a) (Tuple b) ∧
      islessSameNames ltTuple a b = ltTuple (Tuple a) (Tuple b)) ∧
    (a.type.names ≠ b.type.names →
      equalDifferentNames a b = false ∧ isequalDifferentNames a b = false) ∧
    nt_namesValue a = a.type.names ∧ nt_namesType a.type = a.type.names ∧
    (∀ nts, same_namesSpecialized nts = true ∧ same_namesFallback nts = false)

/-- `map` applies its function across corresponding fields only for matching names; `filter`
retains exactly the fields accepted by its predicate. -/
def mapRowsSpec (f : List Value → Value) (columns : List (List Value)) (n : Nat) : List Value :=
  (List.range n).map fun i => f (columns.filterMap fun column => column[i]?)

def NTMapFilterCorrect : Prop :=
  ∀ (mapValues : (List Value → Value) → List (List Value) → List Value)
    (fromTuple : NTType → List Value → Result ModelNT) (typeofValue : Value → TypeTag)
    (f : List Value → Value) (pred : Value → Bool) (nt : ModelNT) (nts : List ModelNT),
    nt.type.names.Nodup → nt.values.length = nt.type.names.length →
    (∀ other, other ∈ nts → other.type.names = nt.type.names ∧ other.values.length = nt.type.names.length) →
    (∀ ty vals out, fromTuple ty vals = .ok out → out.type = ty ∧ out.values = vals) →
    (∀ columns, (∀ column, column ∈ columns → column.length = nt.type.names.length) →
      mapValues f columns = mapRowsSpec f columns nt.type.names.length) →
    (sameNamesDispatch nt nts = false →
      mapNamed mapValues fromTuple typeofValue f nt nts =
        .error (.argumentError "Named tuple names do not match.")) ∧
    (sameNamesDispatch nt nts = true →
      ∀ out, mapNamed mapValues fromTuple typeofValue f nt nts = .ok out →
        out.type.names = nt.type.names ∧
        out.values = mapRowsSpec f ((nt :: nts).map Tuple) nt.type.names.length) ∧
    (∀ out, filterNamed keysNamedTuple true pred nt = .ok out →
      out.type.names.Nodup ∧
      (∀ key, key ∈ nt.type.names →
        (key ∈ out.type.names ↔ ∃ value, getfield nt key = .ok value ∧ pred value = true)) ∧
      ∀ key, key ∈ out.type.names → getfield out key = getfield nt key)

/-- The first position of each key is kept and the last value wins across iterator and
left-associative named-tuple merges. -/
def NTMergeItrCorrect : Prop :=
  ∀ (generated : Bool) (fromTuple : NTType → List Value → Result ModelNT)
    (typeofValue : Value → TypeTag) (a b : ModelNT) (cs : List ModelNT) (itr : List KV),
    a.type.names.Nodup → a.values.length = a.type.names.length →
    b.type.names.Nodup → b.values.length = b.type.names.length →
    (∀ c, c ∈ cs → c.type.names.Nodup ∧ c.values.length = c.type.names.length) →
    (∀ pair, pair ∈ itr → ∃ key, pair.key = .symbol key) →
    (∀ ty vals out, fromTuple ty vals = .ok out → out.type = ty ∧ out.values = vals) →
    (∀ out, mergeIterator generated fromTuple typeofValue a itr = .ok out →
      outputMatchesFields out (namedTupleFields a ++ itr)) ∧
    (∀ out, mergePairs generated a b = .ok out →
      outputMatchesFields out (namedTupleFields a ++ namedTupleFields b)) ∧
    (mergeOne a = a) ∧
    (∀ out, mergeMany generated a b cs = .ok out →
      outputMatchesFields out (namedTupleFieldsMany (a :: b :: cs))) ∧
    (∀ field out, deleteNamed generated a field = .ok out →
      outputMatchesFields out ((namedTupleFields a).filter fun pair => pair.key ≠ .symbol field)) ∧
(∀ (emptyB : ModelNT) (hEmpty : emptyB.type.names = []),
      mergeEmptyRight a emptyB hEmpty = a) ∧
    (∀ (emptyA emptyB : ModelNT) (hA : emptyA.type.names = []) (hB : emptyB.type.names = []),
      mergeEmptyBoth emptyA emptyB hA hB = emptyA) ∧
    (∀ (emptyA : ModelNT) (hA : emptyA.type.names = []),
      mergeEmptyLeft emptyA b hA = b)

/-- The zip overload agrees with merging its iterated key-value pairs. -/
def MergeZipAgrees : Prop :=
  ∀ (generated : Bool) (typeofValue : Value → TypeTag) (a : ModelNT)
    (keys : List String) (values : List Value),
    mergeZip generated typeofValue a keys values =
      mergeIterator generated tupleToNamedTuple typeofValue a
        ((keys.zip values).map fun (key, value) => ⟨.symbol key, value⟩)

/-- Display uses the full type when a value does not match its declared field type, the empty form
for zero fields, and ordered name-value pairs otherwise. -/
def NamedTupleShowCorrect : Prop :=
  ∀ (ops : ShowOps) (nt : ModelNT),
    nt.type.names.Nodup → nt.values.length = nt.type.names.length →
    (ops.nfields nt).val = Int.ofNat nt.type.names.length →
    let n := (ops.nfields nt).val.toNat
    let indices := (List.range n).map (· + 1)
    (showScan ops nt indices = .ok false →
      showNamedTuple ops nt =
        .ok (ops.showType (ops.typeOfTuple nt) ++ ["("] ++ ops.showTuple (Tuple nt) ++ [")"])) ∧
    (n = 0 → showNamedTuple ops nt = .ok ["NamedTuple()"]) ∧
    (n > 0 → showScan ops nt indices = .ok true →
      ∃ fields, showFields ops nt n indices = .ok fields ∧
        showNamedTuple ops nt = .ok (["("] ++ fields ++ [")"]))

/-- Named-tuple key types are Symbol; value and element types follow the declared tuple type. -/
def NamedTupleTypeMethodsCorrect : Prop :=
  ∀ (nt : ModelNT) (t : TypeTag) (eltype : TypeTag → TypeTag),
    keytypeType t = .named "Symbol" ∧
    keytypeValue keytypeType nt = .named "Symbol" ∧
    eltypeNamedTuple (nteltypeDispatch eltype) t = nteltypeDispatch eltype t ∧
    valtypeValue (valtypeType eltype) nt =
      valtypeType eltype (.namedTuple nt.type.names nt.type.fieldTypes) ∧
    valtypeType eltype (.namedTuple nt.type.names nt.type.fieldTypes) =
      eltype (.tuple nt.type.fieldTypes) ∧
    nteltypeFallback t = .any ∧ nt_namesValue nt = nt.type.names ∧
    nt_namesType nt.type = nt.type.names

/-- Merge retains the rightmost type of duplicate fields; differences retain the original type and
value of each remaining field. -/
def NamedTupleTypeHelpersCorrect : Prop :=
  ∀ (names : List String) (a b : NTType) (nt : ModelNT) (excluded : List String),
    names.Nodup → a.names.Nodup → b.names.Nodup → nt.type.names.Nodup →
    (∀ key, key ∈ names →
      fieldType ⟨names, merge_types names a b⟩ key =
        fieldType (if b.names.contains key then b else a) key) ∧
    (∀ key, key ∈ diff_names nt.type.names excluded →
      fieldType ⟨diff_names nt.type.names excluded,
        diff_types nt (diff_names nt.type.names excluded)⟩ key = fieldType nt.type key) ∧
    (∀ out, diff_fallback nt nt.type.names excluded = .ok out →
      outputMatchesFields out (selectedNamedTupleFields nt (diff_names nt.type.names excluded)))

/-- `@NamedTuple` preserves declaration order, defaults omitted types to Any, ignores line nodes,
rejects malformed declarations, and gives keyword arguments the Symbol key type. -/
def NamedTupleMacrosCorrect : Prop :=
  (∀ (fields : List (String × Option TypeTag)),
    let decls := fields.map fun field =>
      match field.2 with | none => MacroExpr.symbol field.1 | some ty => MacroExpr.typed field.1 ty
    namedTupleMacro (.braces decls) =
      .ok ⟨fields.map Prod.fst, fields.map (fun field => field.2.getD .any)⟩ ∧
    namedTupleMacro (.block (decls ++ [.line])) =
      .ok ⟨fields.map Prod.fst, fields.map (fun field => field.2.getD .any)⟩) ∧
(∀ (tupleEltype : TypeTag → TypeTag) (expr : MacroExpr) result,
  kwargsMacro tupleEltype expr = .ok result →
  result.keyType = .named "Symbol" ∧
    result.valueType = eltypeNamedTuple (nteltypeDispatch tupleEltype)
      (.namedTuple result.namedTuple.names result.namedTuple.fieldTypes))

/-- Equal named tuples have equal hashes for every seed when their value tuple's hash respects
isequal. -/
def NamedTupleHashCorrect : Prop :=
  ∀ (objectid : List String → Nat) (hashTuples : List Value → Nat → Nat)
    (xor : Nat → Nat → Nat) (isequalTuples : List Value → List Value → Bool)
    (a b : ModelNT) (seed : Nat),
    a.type.names = b.type.names →
    (∀ xs ys h, isequalTuples xs ys = true → hashTuples xs h = hashTuples ys h) →
    isequalSameNames isequalTuples a b = true →
    hashNamedTuple objectid hashTuples xor a seed = hashNamedTuple objectid hashTuples xor b seed

/-- `split_rest` returns the leading and trailing fields in the requested order. -/
def NamedTupleSplitRestDelegates : Prop :=
  ∀ (nfields : ModelNT → JInt .i64) (checkLength : Nat → Int → Result Unit)
    (splitNames : List String → Int → List Value → Result (List String × List String))
    (generated : Bool) (t first last : ModelNT) (n : JInt .i64) (state : List Value),
    t.type.names.Nodup → t.values.length = t.type.names.length →
    (nfields t).val = Int.ofNat t.type.names.length →
    0 ≤ n.val → n.val ≤ Int.ofNat t.type.names.length →
    checkLength t.type.names.length n.val = .ok () →
    splitNames t.type.names n.val state = .ok (first.type.names, last.type.names) →
    first.type.names ++ last.type.names = t.type.names →
    split_rest nfields checkLength splitNames generated t n state = .ok (first, last) →
    first.values ++ last.values = t.values


theorem ntCompareCorrect_proven : NTCompareCorrect := by
  intro eqTuple isequalTuple ltTuple a b
  exact ⟨fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem namedTupleTypeMethodsCorrect_proven : NamedTupleTypeMethodsCorrect := by
  intro nt t eltype
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem namedTupleHashCorrect_proven : NamedTupleHashCorrect := by
  intro objectid hashTuples xor isequalTuples a b seed hn hh he
  simp only [hashNamedTuple, nt_namesValue, hn, hh _ _ seed he]

theorem haskeyInteger_refuted : ¬ HaskeyInteger := by
  intro h
  have h1 := h false ⟨⟨["a"], [.any]⟩, [Value.box ()]⟩ 1 (Value.box ()) (fun _ => Value.box ()) rfl
  cases h1.1

theorem mergeZipAgrees_refuted : ¬ MergeZipAgrees := by
  intro h
  have hc := h true (fun _ => .any) ⟨⟨["x"], [.any]⟩, [Value.box ()]⟩ ["x", "x"]
    [Value.box (), Value.box ()]
  have hl : mergeZip true (fun _ => .any) ⟨⟨["x"], [.any]⟩, [Value.box ()]⟩
      ["x", "x"] [Value.box (), Value.box ()] = .error .errorException := by rfl
  have hr : mergeIterator true tupleToNamedTuple (fun _ => .any) ⟨⟨["x"], [.any]⟩, [Value.box ()]⟩
      ((["x", "x"].zip [Value.box (), Value.box ()]).map fun (key, value) => ⟨.symbol key, value⟩)
      = .ok ⟨⟨["x"], [.any]⟩, [Value.box ()]⟩ := by rfl
  rw [hl, hr] at hc
  contradiction

/-! ## Added proofs -/
universe u v

private theorem mapM_length_ok {α : Type v} {β : Type u} (f : α → Result β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys → ys.length = xs.length := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    have he : ([] : List β) = ys := by simpa [List.mapM_nil, pure, Except.pure] using h
    subst ys
    rfl
  | cons x xs ih =>
    intro ys h
    cases hx : f x with
    | error e => simp [List.mapM_cons, hx, bind, Except.bind] at h
    | ok y =>
      cases hs : xs.mapM f with
      | error e => simp [List.mapM_cons, hx, hs, bind, Except.bind] at h
      | ok zs =>
        simp [List.mapM_cons, hx, hs, bind, Except.bind, pure, Except.pure] at h
        subst ys
        simpa using congrArg Nat.succ (ih zs hs)

private def declaration (field : String × Option TypeTag) : MacroExpr :=
  match field.2 with
  | none => .symbol field.1
  | some ty => .typed field.1 ty

private theorem declarations_filter (fields : List (String × Option TypeTag)) :
    macroDeclarations (fields.map declaration) = fields.map declaration := by
  apply List.filter_eq_self.mpr
  intro e he
  obtain ⟨⟨name, ty⟩, _, rfl⟩ := List.mem_map.mp he
  cases ty <;> rfl

private theorem declarations_all (fields : List (String × Option TypeTag)) :
    (fields.map declaration).all (fun e => (macroDeclaration e).isSome) = true := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    rcases field with ⟨name, ty⟩
    cases ty <;> simp_all [declaration, macroDeclaration]

private theorem declarations_names (fields : List (String × Option TypeTag)) :
    ((fields.map declaration).filterMap macroDeclaration).map Prod.fst = fields.map Prod.fst := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    rcases field with ⟨name, ty⟩
    cases ty <;> simp_all [declaration, macroDeclaration]

private theorem declarations_types (fields : List (String × Option TypeTag)) :
    ((fields.map declaration).filterMap macroDeclaration).map Prod.snd =
      fields.map (fun field => field.2.getD .any) := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    rcases field with ⟨name, ty⟩
    cases ty <;> simp_all [declaration, macroDeclaration]

theorem namedTupleMacrosCorrect_proven : NamedTupleMacrosCorrect := by
  constructor
  · intro fields
    change namedTupleMacro (.braces (fields.map declaration)) = _ ∧
      namedTupleMacro (.block (fields.map declaration ++ [.line])) = _
    have hf := declarations_filter fields
    have ha := declarations_all fields
    have hn := declarations_names fields
    have ht := declarations_types fields
    have hb : macroDeclarations (fields.map declaration ++ [.line]) = fields.map declaration := by
      simp only [macroDeclarations, List.filter_append]
      simpa [macroDeclarations] using hf
    constructor <;>
      simpa [namedTupleMacro, bind, Except.bind, pure, Except.pure, hf, hb, ha] using (And.intro hn ht)
  · intro tupleEltype expr result h
    cases hm : namedTupleMacro expr with
    | error e => simp [kwargsMacro, hm, bind, Except.bind] at h
    | ok nt =>
      simp [kwargsMacro, hm, bind, Except.bind, pure, Except.pure] at h
      subst result
      exact ⟨rfl, rfl⟩

private theorem showFields_success (ops : ShowOps) (nt : ModelNT) (n : Nat) :
    ∀ indices, showScan ops nt indices = .ok true → ∃ fields, showFields ops nt n indices = .ok fields := by
  intro indices
  induction indices with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons i rest ih =>
    intro h
    simp only [showScan] at h
    cases hg : getfieldIndex nt (Int.ofNat i) with
    | error e => rw [hg] at h; contradiction
    | ok value =>
      rw [hg] at h
      by_cases ht : ops.sameType (ops.typeOfValue value) (ops.fieldTypeAt (ops.typeOfTuple nt) i) = true
      · have hs : showScan ops nt rest = .ok true := by simpa only [if_pos ht] using h
        obtain ⟨later, hl⟩ := ih hs
        let ti := if ops.isNamedTupleSubtype ops.typeinfo then ops.fieldTypeAt ops.typeinfo i else .any
        let sep := if n == 1 then [","] else if i < n then [", "] else []
        refine ⟨ops.showSymbol (ops.fieldName nt i) ++ [" = "] ++ ops.showValue ti value ++ sep ++ later, ?_⟩
        simp only [showFields]
        rw [hg, hl]
      · simp only [if_neg ht] at h
        have hb : (false : Bool) = true := Except.ok.inj h
        cases hb

theorem namedTupleShowCorrect_proven : NamedTupleShowCorrect := by
  intro ops nt _ _ _
  dsimp only
  constructor
  · intro hs
    simp [showNamedTuple, hs, bind, Except.bind, pure, Except.pure]
  constructor
  · intro hn
    simp [showNamedTuple, hn, showScan, bind, Except.bind, pure, Except.pure]
  · intro hp hs
    obtain ⟨fields, hf⟩ := showFields_success ops nt (ops.nfields nt).val.toNat _ hs
    refine ⟨fields, hf, ?_⟩
    have hv : 0 < (ops.nfields nt).val := by omega
    simp [showNamedTuple, hs, hf, Nat.ne_of_gt hp, hv, bind, Except.bind, pure, Except.pure]

private def fields (names : List String) (values : List Value) : List KV :=
  (names.zip values).map fun (name, value) => ⟨.symbol name, value⟩

private theorem first_fields_loop : ∀ (names : List String) (values : List Value) (seen : List String),
    values.length = names.length → (seen ++ names).Nodup →
    firstSymbolKeysLoop seen (fields names values) = seen ++ names := by
  intro names
  induction names with
  | nil => intro values seen _ _; simp [fields, firstSymbolKeysLoop]
  | cons name names ih =>
    intro values seen hl hn
    cases values with
    | nil => simp at hl
    | cons value values =>
      have htail : values.length = names.length := by simpa using hl
      have hnot : name ∉ seen := by
        intro hm
        exact (List.nodup_append.mp hn).2.2 name hm name (by simp) rfl
      have hb : ¬seen.contains name = true := fun h => hnot (List.contains_iff_mem.mp h)
      have hn' : ((seen ++ [name]) ++ names).Nodup := by simpa [List.append_assoc] using hn
      change firstSymbolKeysLoop (if seen.contains name then seen else seen ++ [name])
        (fields names values) = seen ++ (name :: names)
      rw [if_neg hb, ih values (seen ++ [name]) htail hn']
      simp [List.append_assoc]

private theorem first_fields (names : List String) (values : List Value)
    (hl : values.length = names.length) (hn : names.Nodup) :
    firstSymbolKeys (fields names values) = names := by
  exact first_fields_loop names values [] hl (by simpa using hn)

private theorem last_fields : ∀ (names : List String) (values : List Value),
    values.length = names.length → names.Nodup → ∀ key,
    lastSymbolValue (fields names values) key = values[names.idxOf key]? := by
  intro names
  induction names with
  | nil =>
    intro values hl _ key
    cases values with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons name names ih =>
    intro values hl hn key
    cases values with
    | nil => simp at hl
    | cons value values =>
      have htail : values.length = names.length := by simpa using hl
      have hnd := (List.nodup_cons.mp hn).2
      by_cases he : name = key
      · subst key
        have hnone : lastSymbolValue (fields names values) name = none := by
          rw [ih values htail hnd name, List.idxOf_eq_length (List.nodup_cons.mp hn).1]
          apply List.getElem?_eq_none_iff.mpr
          omega
        change (match lastSymbolValue (fields names values) name with
          | some v => some v
          | none => if name = name then some value else none) = _
        rw [hnone]
        simp [List.idxOf, List.findIdx_cons]
      · have hieq : (name :: names).idxOf key = names.idxOf key + 1 := by
          simp [List.idxOf, List.findIdx_cons, he]
        change (match lastSymbolValue (fields names values) key with
          | some v => some v
          | none => if name = key then some value else none) = _
        rw [ih values htail hnd key, hieq, List.getElem?_cons_succ]
        cases hv : values[names.idxOf key]? <;> simp [he]

private theorem fields_match (nt : ModelNT) (hn : nt.type.names.Nodup)
    (hl : nt.values.length = nt.type.names.length) : outputMatchesFields nt (fields nt.type.names nt.values) := by
  constructor
  · exact (first_fields _ _ hl hn).symm
  · intro key hmem
    rw [last_fields _ _ hl hn key]
    cases hv : nt.values[nt.type.names.idxOf key]? with
    | some v => simp only [getfield, hv]
    | none =>
      have hi := List.idxOf_lt_length_iff.mpr hmem
      have hb := List.getElem?_eq_none_iff.mp hv
      omega

private theorem selected_fields (nt : ModelNT) : ∀ (names : List String) (values : List Value),
    names.mapM (getfield nt) = .ok values → selectedNamedTupleFields nt names = fields names values := by
  intro names
  induction names with
  | nil =>
    intro values h
    have he : ([] : List Value) = values := by simpa [List.mapM_nil, pure, Except.pure] using h
    subst values
    rfl
  | cons name names ih =>
    intro values h
    cases hg : getfield nt name with
    | error e => simp [List.mapM_cons, hg, bind, Except.bind] at h
    | ok value =>
      cases hs : names.mapM (getfield nt) with
      | error e => simp [List.mapM_cons, hg, hs, bind, Except.bind] at h
      | ok vs =>
        simp [List.mapM_cons, hg, hs, bind, Except.bind, pure, Except.pure] at h
        subst values
        have ht := ih vs hs
        simpa [selectedNamedTupleFields, fields, hg] using congrArg (fun rest => (⟨.symbol name, value⟩ : KV) :: rest) ht

private theorem constructNames_shape (generated : Bool) (nt : ModelNT) (names : List String) (out : ModelNT)
    (h : constructNamesFromNamedTuple generated nt names = .ok out) :
    out.type.names = names ∧ names.mapM (getfield nt) = .ok out.values := by
  cases generated <;> cases hm : names.mapM (getfield nt) with
  | error e => simp [constructNamesFromNamedTuple, hm, bind, Except.bind] at h
  | ok values =>
    simp [constructNamesFromNamedTuple, hm, bind, Except.bind, pure, Except.pure] at h
    subst out
    exact ⟨rfl, rfl⟩

private theorem constructNames_selected (generated : Bool) (nt : ModelNT) (names : List String) (out : ModelNT)
    (hn : names.Nodup) (h : constructNamesFromNamedTuple generated nt names = .ok out) :
    outputMatchesFields out (selectedNamedTupleFields nt names) := by
  obtain ⟨he, hm⟩ := constructNames_shape generated nt names out h
  have hl := mapM_length_ok (getfield nt) names out.values hm
  have hs := selected_fields nt names out.values hm
  rw [hs, ← he]
  apply fields_match
  · rwa [he]
  · rwa [he]

private theorem mapM_lookup (nt : ModelNT) : ∀ (names : List String) (values : List Value),
    names.mapM (getfield nt) = .ok values → ∀ key, key ∈ names →
    ∃ value, values[names.idxOf key]? = some value ∧ getfield nt key = .ok value := by
  intro names
  induction names with
  | nil => intro _ _ key hk; simp at hk
  | cons name names ih =>
    intro values h key hk
    cases hg : getfield nt name with
    | error e => simp [List.mapM_cons, hg, bind, Except.bind] at h
    | ok value =>
      cases hs : names.mapM (getfield nt) with
      | error e => simp [List.mapM_cons, hg, hs, bind, Except.bind] at h
      | ok vs =>
        simp [List.mapM_cons, hg, hs, bind, Except.bind, pure, Except.pure] at h
        subst values
        by_cases he : name = key
        · subst key
          exact ⟨value, by simp [List.idxOf, List.findIdx_cons], hg⟩
        · have hk' : key ∈ names := (List.mem_cons.mp hk).resolve_left (Ne.symm he)
          obtain ⟨v, hv, hf⟩ := ih vs hs key hk'
          refine ⟨v, ?_, hf⟩
          simpa [List.idxOf, List.findIdx_cons, he] using hv

private theorem constructNames_getfield (generated : Bool) (nt : ModelNT) (names : List String) (out : ModelNT)
    (h : constructNamesFromNamedTuple generated nt names = .ok out) {key : String} (hk : key ∈ names) :
    getfield out key = getfield nt key := by
  obtain ⟨he, hm⟩ := constructNames_shape generated nt names out h
  obtain ⟨v, hv, hf⟩ := mapM_lookup nt names out.values hm key hk
  simp only [getfield, he, hv]
  exact hf.symm

private theorem diff_loop_mapM (nt : ModelNT) : ∀ names, diffValuesLoop nt names = names.mapM (getfield nt) := by
  intro names
  induction names with
  | nil => rfl
  | cons name names ih =>
    simp only [diffValuesLoop, List.mapM_cons, ih]

private theorem fieldType_map (names : List String) (f : String → TypeTag) (key : String)
    (hk : key ∈ names) : fieldType ⟨names, names.map f⟩ key = f key := by
  have hi := List.idxOf_lt_length_iff.mpr hk
  simp only [fieldType]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem_idxOf hi]
  rfl

theorem namedTupleTypeHelpersCorrect_proven : NamedTupleTypeHelpersCorrect := by
  intro names a b nt excluded _ _ _ hn
  constructor
  · intro key hk
    exact fieldType_map names (fun name => fieldType (if b.names.contains name then b else a) name) key hk
  constructor
  · intro key hk
    exact fieldType_map _ (fieldType nt.type) key hk
  · intro out h
    cases hnames : diff_names nt.type.names excluded with
    | nil =>
      simp [diff_fallback, hnames, pure, Except.pure] at h
      subst out
      simp [hnames, selectedNamedTupleFields, outputMatchesFields, firstSymbolKeys, firstSymbolKeysLoop, emptyNamedTuple, newNamedTuple]
    | cons name names =>
      have hd : (name :: names).Nodup := by
        rw [← hnames]
        exact hn.filter _
      cases hm : diffValuesLoop nt (name :: names) with
      | error e => simp [diff_fallback, hnames, hm, bind, Except.bind] at h
      | ok values =>
        simp [diff_fallback, hnames, hm, bind, Except.bind, pure, Except.pure] at h
        subst out
        have hmap : (name :: names).mapM (getfield nt) = .ok values := by rwa [← diff_loop_mapM]
        have hl := mapM_length_ok (getfield nt) _ _ hmap
        rw [selected_fields nt _ _ hmap]
        exact fields_match _ hd hl

private theorem mapM_from_positions {α : Type v} {β : Type u} (f : α → Result β) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
    (∀ (i : Nat) (hi : i < xs.length) (hj : i < ys.length), f xs[i] = .ok ys[i]) → xs.mapM f = .ok ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys hl _
    cases ys with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons x xs ih =>
    intro ys hl hp
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have hl' : xs.length = ys.length := by simpa using hl
      have hp' : ∀ i (hi : i < xs.length) (hj : i < ys.length), f xs[i] = .ok ys[i] := by
        intro i hi hj
        exact hp (i + 1) (by simpa using hi) (by simpa using hj)
      have hx := hp 0 (by simp) (by simp)
      change f x = .ok y at hx
      rw [List.mapM_cons, hx, ih ys hl' hp']
      rfl

private theorem own_mapM (nt : ModelNT) (hn : nt.type.names.Nodup)
    (hl : nt.values.length = nt.type.names.length) : nt.type.names.mapM (getfield nt) = .ok nt.values := by
  apply mapM_from_positions
  · exact hl.symm
  · intro i hi hj
    simp only [getfield]
    rw [hn.idxOf_getElem i hi, List.getElem?_eq_getElem hj]

theorem namedTupleSplitRestDelegates_proven : NamedTupleSplitRestDelegates := by
  intro nfields checkLength splitNames generated t first last n state hn hl hfields _ _ hc hs hcat h
  have hlen : (length nfields t).val.toNat = t.type.names.length := by
    change (nfields t).val.toNat = _
    rw [hfields]
    rfl
  simp only [split_rest, hlen, hc, hs] at h
  cases hf : constructNamesFromNamedTuple generated t first.type.names with
  | error e => rw [hf] at h; contradiction
  | ok fst =>
    rw [hf] at h
    cases hb : constructNamesFromNamedTuple generated t last.type.names with
    | error e => rw [hb] at h; contradiction
    | ok lst =>
      rw [hb] at h
      have he : (fst, lst) = (first, last) := Except.ok.inj h
      have he1 := congrArg Prod.fst he
      have he2 := congrArg Prod.snd he
      dsimp only at he1 he2
      subst fst
      subst lst
      have hfm := (constructNames_shape generated t first.type.names first hf).2
      have hlm := (constructNames_shape generated t last.type.names last hb).2
      have hm : (first.type.names ++ last.type.names).mapM (getfield t) = .ok (first.values ++ last.values) := by
        rw [List.mapM_append, hfm, hlm]
        rfl
      rw [hcat, own_mapM t hn hl] at hm
      exact (Except.ok.inj hm).symm

private theorem getfield_exists (nt : ModelNT) (hl : nt.values.length = nt.type.names.length)
    (key : String) (hk : key ∈ nt.type.names) : ∃ value, getfield nt key = .ok value := by
  have hi : nt.type.names.idxOf key < nt.values.length := by
    rw [hl]
    exact List.idxOf_lt_length_iff.mpr hk
  refine ⟨nt.values[nt.type.names.idxOf key], ?_⟩
  simp only [getfield]
  rw [List.getElem?_eq_getElem hi]

private theorem construct_empty_input (nt : ModelNT) (hl : nt.values.length = nt.type.names.length)
    (hn : nt.type.names = []) (generated : Bool) (names : List String) (out : ModelNT)
    (h : constructNamesFromNamedTuple generated nt names = .ok out) :
    outputMatchesFields out [] := by
  have hv : nt.values = [] := by
    cases hh : nt.values with
    | nil => rfl
    | cons _ _ => simp [hn, hh] at hl
  have hnames : names = [] := by
    cases names with
    | nil => rfl
    | cons key rest =>
      have hm := (constructNames_shape generated nt (key :: rest) out h).2
      have hf : getfield nt key = .error (.fieldError key) := by simp [getfield, hn, hv, List.idxOf]
      simp [List.mapM_cons, hf, bind, Except.bind] at hm
  subst names
  exact constructNames_selected generated nt [] out (by simp) h

private theorem reverse_tuple_eq {α : Type} (xs : List α) :
    JuliaLean.base.tuple.reverseTuple xs = xs.reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [JuliaLean.base.tuple.reverseTuple, JuliaLean.base.tuple.revargs, List.reverse_cons] using congrArg (fun ys => ys ++ [x]) ih

theorem ntAccessCorrect_proven : NTAccessCorrect := by
  intro nfields nt hn hl hf
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, (fun _ => rfl), rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hj
    simp only [Int.ofNat_eq_coe] at hj
    have hb : i.val.toNat - 1 < nt.type.names.length := by omega
    have hc : i.val.toNat - 1 < nt.values.length := by omega
    have he : (i.val - 1).toNat = i.val.toNat - 1 := by omega
    refine ⟨nt.type.names[i.val.toNat - 1], nt.values[i.val.toNat - 1],
      List.getElem?_eq_getElem hb, List.getElem?_eq_getElem hc, ?_, ?_⟩
    · simp only [getindexInt, getfieldIndex]
      rw [if_neg (by omega), he, List.getElem?_eq_getElem hc]
    · simp only [getindexSymbol, getfield]
      rw [hn.idxOf_getElem _ hb, List.getElem?_eq_getElem hc]
  · intro I greater getfieldAt increment one iter h
    simp [iterate, h]
  · intro I greater getfieldAt increment one iter h
    simp [iterate, h]
  · intro i value h
    simp [indexed_iterate, h, bind, Except.bind, pure, Except.pure]
  · intro tailNames frontNames ht hb
    constructor
    · intro out h
      by_cases he : nt.type.names = []
      · cases hx : tailNames nt.type.names with
        | error e => simp [tailNamed, hx] at h
        | ok names =>
          have hc : constructNamesFromNamedTuple false nt names = .ok out := by simpa [tailNamed, hx] using h
          have hh := construct_empty_input nt hl he false names out hc
          simpa [he, selectedNamedTupleFields] using hh
      · have hx := ht nt.type.names he
        have hc : constructNamesFromNamedTuple false nt (nt.type.names.drop 1) = .ok out := by
          simpa [tailNamed, hx] using h
        exact constructNames_selected false nt _ out hn.drop hc
    · intro out h
      by_cases he : nt.type.names = []
      · cases hx : frontNames nt.type.names with
        | error e => simp [frontNamed, hx] at h
        | ok names =>
          have hc : constructNamesFromNamedTuple false nt names = .ok out := by simpa [frontNamed, hx] using h
          have hh := construct_empty_input nt hl he false names out hc
          simpa [he, selectedNamedTupleFields] using hh
      · have hx := hb nt.type.names he
        have hc : constructNamesFromNamedTuple false nt nt.type.names.dropLast = .ok out := by
          simpa [frontNamed, hx] using h
        exact constructNames_selected false nt _ out (List.Pairwise.sublist (List.dropLast_sublist _) hn) hc
  · intro namesAfter i out _ _ hx h
    have hc : constructNamesFromNamedTuple false nt (nt.type.names.drop i.val.toNat) = .ok out := by
      simpa [restAfter, hx] using h
    exact constructNames_selected false nt _ out hn.drop hc
  · intro fromTuple typeofValue out hfrom h
    have hh : fromTuple ⟨JuliaLean.base.tuple.reverseTuple (keysNamedTuple nt),
        (valuesNamedTuple nt).reverse.map typeofValue⟩ (valuesNamedTuple nt).reverse = .ok out := by
      simpa [reverseNamedTuple, constructNamesFromIterator, bind, Except.bind, pure, Except.pure] using h
    obtain ⟨ht, hv⟩ := hfrom _ _ _ hh
    constructor
    · rw [ht]
      exact reverse_tuple_eq _
    · exact hv
  · intro I convertInt i x hx
    constructor <;> simp [prevind, nextind, hx, bind, Except.bind, pure, Except.pure]

theorem ntMapFilterCorrect_proven : NTMapFilterCorrect := by
  intro mapValues fromTuple typeofValue f pred nt nts hn hl hnts hfrom hmap
  constructor
  · intro hs
    simp [mapNamed, hs, bind, Except.bind] <;> rfl
  constructor
  · intro hs out h
    let values := mapValues f ((nt :: nts).map Tuple)
    have hc : fromTuple ⟨nt.type.names, values.map typeofValue⟩ values = .ok out := by
      simpa [mapNamed, hs, constructNamesFromIterator, values, bind, Except.bind, pure, Except.pure] using h
    obtain ⟨ht, hv⟩ := hfrom _ _ _ hc
    constructor
    · rw [ht]
    · rw [hv]
      apply hmap
      intro column hc
      obtain ⟨other, hm, he⟩ := List.mem_map.mp hc
      subst column
      cases List.mem_cons.mp hm with
      | inl he => subst other; exact hl
      | inr he => exact (hnts other he).2
  · intro out h
    let selected := nt.type.names.filter (fun key =>
      match getfield nt key with | .ok value => pred value | .error _ => false)
    have hc : constructNamesFromNamedTuple true nt selected = .ok out := h
    obtain ⟨he, hm⟩ := constructNames_shape true nt selected out hc
    constructor
    · rw [he]
      exact hn.filter _
    constructor
    · intro key hk
      rw [he]
      change key ∈ nt.type.names.filter _ ↔ _
      rw [List.mem_filter]
      constructor
      · intro hp
        obtain ⟨v, hg⟩ := getfield_exists nt hl key hk
        refine ⟨v, hg, ?_⟩
        simpa only [hg] using hp.2
      · rintro ⟨v, hg, hp⟩
        exact ⟨hk, by simpa only [hg] using hp⟩
    · intro key hk
      apply constructNames_getfield true nt selected out hc
      rwa [← he]

private def lookup (names : List String) (values : List Value) (key : String) : Option Value :=
  values[names.idxOf key]?

private theorem setAt_set (values : List Value) (i : Nat) (v : Value) :
    setAt values i v = values.set i v := by
  induction values generalizing i with
  | nil => simp [setAt]
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ j => simp [setAt, ih]

private theorem lookup_set (names : List String) (values : List Value) (name : String) (v : Value)
    (hl : values.length = names.length) (hm : name ∈ names) (key : String) :
    lookup names (setAt values (names.idxOf name) v) key =
      if key = name then some v else lookup names values key := by
  have hi : names.idxOf name < names.length := List.idxOf_lt_length_iff.mpr hm
  have hiv : names.idxOf name < values.length := by omega
  by_cases he : key = name
  · subst key
    simp [lookup, setAt_set, List.getElem?_set, hiv]
  · have hne : names.idxOf name ≠ names.idxOf key := by
      intro heq
      have hj : names.idxOf key < names.length := by omega
      have hh := congrArg (fun i : Nat => names[i]?) heq
      rw [List.getElem?_eq_getElem hi, List.getElem_idxOf hi,
        List.getElem?_eq_getElem hj, List.getElem_idxOf hj] at hh
      exact he (Option.some.inj hh).symm
    simp only [lookup, setAt_set, List.getElem?_set, if_neg hne, if_neg he]

private theorem lookup_append (names : List String) (values : List Value) (name : String) (v : Value)
    (hl : values.length = names.length) (hm : name ∉ names) (key : String) :
    lookup (names ++ [name]) (values ++ [v]) key =
      if key = name then some v else lookup names values key := by
  by_cases he : key = name
  · subst key
    simp only [lookup, List.idxOf_append, if_neg hm]
    have hid : [name].idxOf name = 0 := by simp [List.idxOf, List.findIdx_cons]
    rw [hid, Nat.zero_add, List.getElem?_append_right (by omega)]
    simp [hl]
  · by_cases hk : key ∈ names
    · have hi : names.idxOf key < values.length := by
        rw [hl]
        exact List.idxOf_lt_length_iff.mpr hk
      simp only [lookup, List.idxOf_append, if_pos hk, if_neg he]
      exact List.getElem?_append_left hi
    · have hkn : key ∉ names ++ [name] := by simp [hk, he]
      simp only [lookup, if_neg he, List.idxOf_eq_length hk, List.idxOf_eq_length hkn]
      rw [List.getElem?_eq_none_iff.mpr (by simp [hl]), List.getElem?_eq_none_iff.mpr (by omega)]

private theorem pairFields_invariant : ∀ (pairs : List KV) (names : List String) (values : List Value)
    (outNames : List String) (outValues : List Value),
    names.Nodup → values.length = names.length →
    pairFieldsLoop pairs names values = .ok (outNames, outValues) →
    outNames.Nodup ∧ outValues.length = outNames.length ∧
    outNames = firstSymbolKeysLoop names pairs ∧
    ∀ key, lookup outNames outValues key =
      match lastSymbolValue pairs key with | some v => some v | none => lookup names values key := by
  intro pairs
  induction pairs with
  | nil =>
    intro names values outNames outValues hn hl h
    have he : (names, values) = (outNames, outValues) := Except.ok.inj h
    cases he
    exact ⟨hn, hl, rfl, fun _ => rfl⟩
  | cons pair rest ih =>
    intro names values outNames outValues hn hl h
    rcases pair with ⟨kind, value⟩
    cases kind with
    | symbol name =>
      by_cases hm : name ∈ names
      · have hb : names.contains name = true := List.contains_iff_mem.mpr hm
        have hc : pairFieldsLoop rest names (setAt values (names.idxOf name) value) = .ok (outNames, outValues) := by
          simpa only [pairFieldsLoop, if_pos hb] using h
        have hl' : (setAt values (names.idxOf name) value).length = names.length := by
          simpa [setAt_set] using hl
        obtain ⟨hnd, hlen, hnames, hlookup⟩ := ih names _ outNames outValues hn hl' hc
        refine ⟨hnd, hlen, ?_, ?_⟩
        · simpa only [firstSymbolKeysLoop, if_pos hb] using hnames
        · intro key
          rw [hlookup key, lookup_set names values name value hl hm key]
          simp only [lastSymbolValue]
          cases hv : lastSymbolValue rest key with
          | some v => rfl
          | none =>
            by_cases he : key = name
            · subst key; simp
            · simp only [if_neg he, if_neg (Ne.symm he)]
      · have hb : ¬names.contains name = true := fun hh => hm (List.contains_iff_mem.mp hh)
        have hc : pairFieldsLoop rest (names ++ [name]) (values ++ [value]) = .ok (outNames, outValues) := by
          simpa only [pairFieldsLoop, if_neg hb] using h
        have hn' : (names ++ [name]).Nodup := by
          rw [List.nodup_append]
          refine ⟨hn, by simp, ?_⟩
          intro x hx y hy hxy
          have hy' := List.mem_singleton.mp hy
          rw [hxy, hy'] at hx
          exact hm hx
        have hl' : (values ++ [value]).length = (names ++ [name]).length := by simpa using congrArg Nat.succ hl
        obtain ⟨hnd, hlen, hnames, hlookup⟩ := ih _ _ outNames outValues hn' hl' hc
        refine ⟨hnd, hlen, ?_, ?_⟩
        · simpa only [firstSymbolKeysLoop, if_neg hb] using hnames
        · intro key
          rw [hlookup key, lookup_append names values name value hl hm key]
          simp only [lastSymbolValue]
          cases hv : lastSymbolValue rest key with
          | some v => rfl
          | none =>
            by_cases he : key = name
            · subst key; simp
            · simp only [if_neg he, if_neg (Ne.symm he)]
    | nativeInteger _ | integer _ | other => simp [pairFieldsLoop] at h

private theorem pairFields_properties (pairs : List KV) (names : List String) (values : List Value)
    (h : pairFields pairs = .ok (names, values)) :
    names.Nodup ∧ values.length = names.length ∧ names = firstSymbolKeys pairs ∧
    ∀ key, lookup names values key = lastSymbolValue pairs key := by
  obtain ⟨hn, hl, hs, hv⟩ := pairFields_invariant pairs [] [] names values (by simp) rfl h
  refine ⟨hn, hl, hs, ?_⟩
  intro key
  rw [hv key]
  cases hx : lastSymbolValue pairs key <;> rfl

private theorem pairFields_matches (pairs : List KV) (names : List String) (values : List Value)
    (out : ModelNT) (h : pairFields pairs = .ok (names, values))
    (hn : out.type.names = names) (hv : out.values = values) : outputMatchesFields out pairs := by
  obtain ⟨hnd, hl, hs, hk⟩ := pairFields_properties pairs names values h
  constructor
  · exact hn.trans hs
  · intro key hmem
    have hmem' : key ∈ names := by rwa [← hn]
    rw [← hk key]
    cases hx : lookup names values key with
    | some v => simp only [getfield, hn, hv, lookup] at hx ⊢; rw [hx]
    | none =>
      have hi := List.idxOf_lt_length_iff.mpr hmem'
      have hb := List.getElem?_eq_none_iff.mp hx
      omega

private theorem typed_mismatch (convert : TypeTag → Value → Result Value) (target : NTType)
    (args : List Value) (h : args.length ≠ target.names.length) :
    constructTyped convert target args = .error (.argumentError "Wrong number of arguments to named tuple constructor.") := by
  simp [constructTyped, h, bind, Except.bind] <;> rfl

private theorem typed_info (convert : TypeTag → Value → Result Value) (target : NTType)
    (args : List Value) (out : ModelNT) (h : constructTyped convert target args = .ok out) :
    out.type = target ∧ out.values.length = min target.fieldTypes.length args.length ∧
      args.length = target.names.length := by
  by_cases he : args.length = target.names.length
  · cases hc : convertTupleFields convert target.fieldTypes args with
    | error err => simp [constructTyped, he, hc, bind, Except.bind] at h
    | ok values =>
      have hout : newNamedTuple target values = out := by
        simpa [constructTyped, he, hc, bind, Except.bind, pure, Except.pure] using h
      subst out
      refine ⟨rfl, ?_, he⟩
      have hv := mapM_length_ok (fun pair : TypeTag × Value => convert pair.1 pair.2)
        (target.fieldTypes.zip args) values hc
      simpa [List.length_zip, newNamedTuple] using hv
  · rw [typed_mismatch convert target args he] at h
    cases h

private theorem from_named_info (generated : Bool) (convert : TypeTag → Value → Result Value)
    (isA : Value → TypeTag → Bool) (target : NTType) (nt out : ModelNT)
    (h : constructFromNamedTuple generated convert isA target nt = .ok out) :
    out.type = target ∧ (target.fieldTypes.length = target.names.length →
      out.values.length = target.names.length) := by
  cases generated with
  | false =>
    cases hm : target.names.mapM (getfield nt) with
    | error err => simp [constructFromNamedTuple, hm, bind, Except.bind] at h
    | ok args =>
      have hc : constructTyped convert target args = .ok out := by
        simpa [constructFromNamedTuple, hm, bind, Except.bind] using h
      obtain ⟨ht, hv, _⟩ := typed_info convert target args out hc
      refine ⟨ht, ?_⟩
      intro hf
      have hl := mapM_length_ok (getfield nt) target.names args hm
      rw [hv, hf, hl, Nat.min_self]
  | true =>
    let field : String → Result Value := fun name => do
      let value ← getfield nt name
      let ty := fieldType target name
      if isA value ty then pure value else convert ty value
    change (do let values ← target.names.mapM field
               pure (newNamedTuple target values)) = .ok out at h
    cases hm : target.names.mapM field with
    | error err => simp [hm, bind, Except.bind] at h
    | ok values =>
      have hout : newNamedTuple target values = out := by
        simpa [hm, bind, Except.bind, pure, Except.pure] using h
      subst out
      exact ⟨rfl, fun _ => mapM_length_ok field target.names values hm⟩

private theorem typed_names (convert : TypeTag → Value → Result Value) (target : NTType)
    (args : List Value) (out : ModelNT) (h : constructTyped convert target args = .ok out) :
    out.type.names = target.names := congrArg NTType.names (typed_info convert target args out h).1

 theorem ntConstructCorrect_proven : NTConstructCorrect := by
  intro convert target args
  refine ⟨typed_mismatch convert target args, ?_, ?_, ?_, ?_, ?_, ?_,
    (fun _ _ => ⟨rfl, rfl⟩), (fun _ => ⟨rfl, rfl⟩),
    (fun {_} _ _ => ⟨rfl, rfl⟩), ?_, ?_, ?_, ?_⟩
  · intro _ hf hl out h
    obtain ⟨ht, hv, _⟩ := typed_info convert target args out h
    exact ⟨ht, by rw [hv, hf, hl, Nat.min_self]⟩
  · intro generated isA nt out _ _ hf h
    obtain ⟨ht, hv⟩ := from_named_info generated convert isA nt.type nt out h
    exact ⟨congrArg NTType.names ht, hv hf⟩
  · intro generated nt names out hn _ h
    exact constructNames_selected generated nt names out hn h
  · intro generated isA nt out h
    exact congrArg NTType.names (from_named_info generated convert isA nt.type nt out h).1
  · intro target nt out h
    change (do
      let values ← convertTupleFields convert
        ((List.range target.names.length).map (fun i => target.fieldTypes.getD i .any)) nt.values
      constructTyped convert
        ⟨target.names, (List.range target.names.length).map (fun i => target.fieldTypes.getD i .any)⟩ values) = .ok out at h
    cases hc : convertTupleFields convert ((List.range target.names.length).map (fun i => target.fieldTypes.getD i .any)) nt.values with
    | error err =>
      simp only [hc, bind, Except.bind] at h
      cases h
    | ok values =>
      have ht : constructTyped convert ⟨target.names, (List.range target.names.length).map (fun i => target.fieldTypes.getD i .any)⟩ values = .ok out := by
        simpa only [hc, bind, Except.bind] using h
      exact typed_names convert ⟨target.names, (List.range target.names.length).map (fun i => target.fieldTypes.getD i .any)⟩ values out ht
  · intro target values out h
    exact typed_names _ _ _ _ h
  · intro isT cv nt h
    simp [convertToTuple, h, pure, Except.pure]
  · intro I toValues cv target itr out _ _ h
    cases hv : toValues itr with
    | error err => simp [constructTypedFromIterator, hv, bind, Except.bind] at h
    | ok values =>
      cases hc : convertTupleFields cv target.fieldTypes values with
      | error err => simp [constructTypedFromIterator, hv, hc, bind, Except.bind] at h
      | ok converted =>
        have ht : constructTyped cv target converted = .ok out := by
          simpa [constructTypedFromIterator, hv, hc, bind, Except.bind] using h
        exact typed_names _ _ _ _ ht
  · intro I toValues fromTuple typeofValue names itr values out _ hv hfrom h
    have hc : fromTuple ⟨names, values.map typeofValue⟩ values = .ok out := by
      simpa [constructNamesFromIterator, hv, bind, Except.bind] using h
    obtain ⟨ht, hv⟩ := hfrom _ _ _ hc
    exact ⟨congrArg NTType.names ht, hv⟩
  · intro I toPairs fromTuple typeofValue itr pairs out hp _ hfrom h
    cases hc : pairFields pairs with
    | error err => simp [namedTupleFromIterator, hp, hc, bind, Except.bind] at h
    | ok state =>
      rcases state with ⟨names, values⟩
      have hf : fromTuple ⟨names, values.map typeofValue⟩ values = .ok out := by
        simpa [namedTupleFromIterator, hp, hc, bind, Except.bind] using h
      obtain ⟨ht, hv⟩ := hfrom _ _ _ hf
      exact pairFields_matches pairs names values out hc (congrArg NTType.names ht) hv

private theorem nodup_snoc (seen : List String) (name : String) (hn : seen.Nodup) (hm : name ∉ seen) :
    (seen ++ [name]).Nodup := by
  rw [List.nodup_append]
  refine ⟨hn, by simp, ?_⟩
  intro x hx y hy hxy
  rw [hxy, List.mem_singleton.mp hy] at hx
  exact hm hx

private theorem first_loop_nodup : ∀ (pairs : List KV) (seen : List String),
    seen.Nodup → (firstSymbolKeysLoop seen pairs).Nodup := by
  intro pairs
  induction pairs with
  | nil => intro seen hn; exact hn
  | cons pair rest ih =>
    intro seen hn
    rcases pair with ⟨key, value⟩
    cases key with
    | symbol name =>
      change (firstSymbolKeysLoop (if seen.contains name then seen else seen ++ [name]) rest).Nodup
      by_cases hm : name ∈ seen
      · rw [if_pos (List.contains_iff_mem.mpr hm)]
        exact ih seen hn
      · rw [if_neg (fun h => hm (List.contains_iff_mem.mp h))]
        exact ih _ (nodup_snoc seen name hn hm)
    | nativeInteger _ | integer _ | other => exact ih seen hn

private theorem first_loop_append : ∀ (pairs later : List KV) (seen : List String),
    firstSymbolKeysLoop seen (pairs ++ later) = firstSymbolKeysLoop (firstSymbolKeysLoop seen pairs) later := by
  intro pairs
  induction pairs with
  | nil => intros; rfl
  | cons pair rest ih =>
    intro later seen
    rcases pair with ⟨key, value⟩
    cases key <;> exact ih later _

private theorem first_loop_formula : ∀ (pairs : List KV) (seen : List String),
    seen.Nodup → firstSymbolKeysLoop seen pairs =
      seen ++ (firstSymbolKeys pairs).filter (fun key => !seen.contains key) := by
  intro pairs
  induction pairs with
  | nil => intro seen _; simp [firstSymbolKeys, firstSymbolKeysLoop]
  | cons pair rest ih =>
    intro seen hn
    rcases pair with ⟨key, value⟩
    cases key with
    | symbol name =>
      change firstSymbolKeysLoop (if seen.contains name then seen else seen ++ [name]) rest =
        seen ++ (firstSymbolKeysLoop [name] rest).filter (fun key => !seen.contains key)
      rw [ih [name] (by simp)]
      by_cases hm : name ∈ seen
      · have hb := List.contains_iff_mem.mpr hm
        rw [if_pos hb, ih seen hn]
        simp only [List.filter_append, List.filter_cons, hb, Bool.not_true, Bool.false_eq_true,
          ite_false, List.filter_nil, List.nil_append]
        congr 1
        rw [List.filter_filter]
        apply List.filter_congr
        intro key _
        by_cases he : name = key
        · subst key; simp [hb, hm]
        · simp [List.contains_cons, he, Ne.symm he]
      · have hb : seen.contains name = false := by
          cases hx : seen.contains name with
          | false => rfl
          | true => exact False.elim (hm (List.contains_iff_mem.mp hx))
        rw [if_neg (fun h => hm (List.contains_iff_mem.mp h)), ih (seen ++ [name]) (nodup_snoc seen name hn hm)]
        simp only [List.filter_append, List.filter_cons, hb, Bool.not_false, ite_true,
          List.filter_nil, List.append_assoc, List.filter_filter]
        congr 1
        apply congrArg (fun tail => [name] ++ tail)
        apply List.filter_congr
        intro key _
        rw [List.contains_append]
        cases seen.contains key <;> cases [name].contains key <;> rfl
    | nativeInteger _ | integer _ | other => exact ih seen hn

private theorem first_append (left right : List KV) :
    firstSymbolKeys (left ++ right) = firstSymbolKeys left ++
      (firstSymbolKeys right).filter (fun key => !(firstSymbolKeys left).contains key) := by
  rw [show firstSymbolKeys (left ++ right) = firstSymbolKeysLoop (firstSymbolKeys left) right from
    first_loop_append left right []]
  exact first_loop_formula right _ (first_loop_nodup left [] (by simp))

private theorem last_append : ∀ (left right : List KV) (key : String),
    lastSymbolValue (left ++ right) key =
      match lastSymbolValue right key with | some v => some v | none => lastSymbolValue left key := by
  intro left
  induction left with
  | nil =>
    intro right key
    simp only [List.nil_append]
    cases hx : lastSymbolValue right key <;> rfl
  | cons pair rest ih =>
    intro right key
    simp only [List.cons_append, lastSymbolValue, ih]
    cases hx : lastSymbolValue right key <;> rfl

private theorem mapM_at {α : Type u} (f : String → Result α) :
    ∀ (names : List String) (values : List α), names.mapM f = .ok values →
      ∀ key, key ∈ names → ∃ value, values[names.idxOf key]? = some value ∧ f key = .ok value := by
  intro names
  induction names with
  | nil => intro _ _ _ hk; simp at hk
  | cons name names ih =>
    intro values h key hk
    cases hf : f name with
    | error err => simp [List.mapM_cons, hf, bind, Except.bind] at h
    | ok value =>
      cases ht : names.mapM f with
      | error err => simp [List.mapM_cons, hf, ht, bind, Except.bind] at h
      | ok tail =>
        have he : value :: tail = values := by
          simpa [List.mapM_cons, hf, ht, bind, Except.bind, pure, Except.pure] using h
        subst values
        by_cases hkey : name = key
        · subst key
          refine ⟨value, ?_, hf⟩
          simp [List.idxOf, List.findIdx_cons]
        · have hk' : key ∈ names := (List.mem_cons.mp hk).resolve_left (Ne.symm hkey)
          obtain ⟨v, hv, hg⟩ := ih tail ht key hk'
          refine ⟨v, ?_, hg⟩
          simpa [List.idxOf, List.findIdx_cons, hkey] using hv

private theorem lookup_none (names : List String) (values : List Value) (hl : values.length = names.length)
    (key : String) (hk : key ∉ names) : lookup names values key = none := by
  simp only [lookup, List.idxOf_eq_length hk]
  exact List.getElem?_eq_none_iff.mpr (by omega)

private theorem lookup_getfield (nt : ModelNT) (key : String) :
    getfield nt key = match lookup nt.type.names nt.values key with
      | some value => .ok value | none => .error (.fieldError key) := rfl

private theorem merge_values_mapM (bn : List String) (a b : ModelNT) : ∀ names,
    mergeValuesLoop bn a b names = names.mapM (fun name => getfield (if bn.contains name then b else a) name) := by
  intro names
  induction names with
  | nil => rfl
  | cons name names ih => simp [mergeValuesLoop, List.mapM_cons, ih]

private theorem last_named (nt : ModelNT) (hn : nt.type.names.Nodup)
    (hl : nt.values.length = nt.type.names.length) (key : String) :
    lastSymbolValue (namedTupleFields nt) key = lookup nt.type.names nt.values key := by
  exact last_fields nt.type.names nt.values hl hn key

private theorem first_named (nt : ModelNT) (hn : nt.type.names.Nodup)
    (hl : nt.values.length = nt.type.names.length) : firstSymbolKeys (namedTupleFields nt) = nt.type.names :=
  first_fields nt.type.names nt.values hl hn

private abbrev WF (nt : ModelNT) := nt.type.names.Nodup ∧ nt.values.length = nt.type.names.length
private def FieldsEq (left right : List KV) : Prop :=
  firstSymbolKeys left = firstSymbolKeys right ∧ ∀ key, lastSymbolValue left key = lastSymbolValue right key

private theorem fieldsEq_refl (fields : List KV) : FieldsEq fields fields := ⟨rfl, fun _ => rfl⟩
private theorem fieldsEq_trans {a b c : List KV} (hab : FieldsEq a b) (hbc : FieldsEq b c) : FieldsEq a c :=
  ⟨hab.1.trans hbc.1, fun key => (hab.2 key).trans (hbc.2 key)⟩
private theorem fieldsEq_append {a b c d : List KV} (hab : FieldsEq a b) (hcd : FieldsEq c d) :
    FieldsEq (a ++ c) (b ++ d) := by
  constructor
  · rw [first_append, first_append, hab.1, hcd.1]
  · intro key
    rw [last_append, last_append, hab.2 key, hcd.2 key]

private theorem matches_equiv (out : ModelNT) {left right : List KV} (he : FieldsEq left right)
    (hm : outputMatchesFields out left) : outputMatchesFields out right := by
  refine ⟨hm.1.trans he.1, ?_⟩
  intro key hk
  rw [← he.2 key]
  exact hm.2 key hk

private theorem getfield_some (nt : ModelNT) (key : String) (value : Value) :
    getfield nt key = .ok value ↔ lookup nt.type.names nt.values key = some value := by
  rw [lookup_getfield]
  cases hx : lookup nt.type.names nt.values key <;> simp

private theorem merge_names_nodup (an bn : List String) (ha : an.Nodup) (hb : bn.Nodup) :
    (merge_names an bn).Nodup := by
  rw [merge_names, List.nodup_append]
  refine ⟨ha, hb.filter _, ?_⟩
  intro x hx y hy hxy
  have hy' := (List.mem_filter.mp hy).2
  have hyes := List.contains_iff_mem.mpr (hxy ▸ hx)
  rw [hyes] at hy'
  cases hy'

private theorem merge_as_fallback (generated : Bool) (a b : ModelNT) :
    mergeNamed generated a b = merge_fallback a b a.type.names b.type.names := by
  cases generated <;> rfl

private theorem merge_shape (a b out : ModelNT)
    (h : merge_fallback a b a.type.names b.type.names = .ok out) :
    out.type.names = merge_names a.type.names b.type.names ∧
    (merge_names a.type.names b.type.names).mapM
      (fun key => getfield (if b.type.names.contains key then b else a) key) = .ok out.values := by
  cases hv : mergeValuesLoop b.type.names a b (merge_names a.type.names b.type.names) with
  | error err => simp [merge_fallback, hv, bind, Except.bind] at h
  | ok values =>
    have he : new_NamedTuple
        ⟨merge_names a.type.names b.type.names,
          merge_types (merge_names a.type.names b.type.names) a.type b.type⟩ values = out := by
      simpa [merge_fallback, hv, bind, Except.bind, pure, Except.pure] using h
    subst out
    constructor
    · rfl
    · rw [← merge_values_mapM]
      exact hv

private theorem merge_core (generated : Bool) (a b out : ModelNT) (ha : WF a) (hb : WF b)
    (h : mergeNamed generated a b = .ok out) :
    WF out ∧ FieldsEq (namedTupleFields out) (namedTupleFields a ++ namedTupleFields b) := by
  rw [merge_as_fallback] at h
  obtain ⟨hnames, hvalues⟩ := merge_shape a b out h
  have hnd : out.type.names.Nodup := by rw [hnames]; exact merge_names_nodup _ _ ha.1 hb.1
  have hlen : out.values.length = out.type.names.length := by
    rw [hnames]
    exact mapM_length_ok _ _ _ hvalues
  have hfirst : out.type.names = firstSymbolKeys (namedTupleFields a ++ namedTupleFields b) := by
    rw [first_append, first_named a ha.1 ha.2, first_named b hb.1 hb.2]
    exact hnames
  have hlookup : ∀ key, lookup out.type.names out.values key =
      lastSymbolValue (namedTupleFields a ++ namedTupleFields b) key := by
    intro key
    rw [last_append, last_named a ha.1 ha.2, last_named b hb.1 hb.2]
    by_cases hk : key ∈ out.type.names
    · have hm : key ∈ merge_names a.type.names b.type.names := by rwa [← hnames]
      obtain ⟨value, hv, hg⟩ := mapM_at _ _ _ hvalues key hm
      have hout : lookup out.type.names out.values key = some value := by simpa only [lookup, hnames] using hv
      by_cases hkb : key ∈ b.type.names
      · have hbkey := List.contains_iff_mem.mpr hkb
        rw [if_pos hbkey] at hg
        rw [(getfield_some b key value).mp hg]
        exact hout
      · have hbkey : ¬b.type.names.contains key = true := fun hh => hkb (List.contains_iff_mem.mp hh)
        rw [if_neg hbkey] at hg
        rw [lookup_none b.type.names b.values hb.2 key hkb]
        rw [(getfield_some a key value).mp hg]
        exact hout
    · have hka : key ∉ a.type.names := by
        intro hm
        apply hk
        rw [hnames, merge_names]
        exact List.mem_append_left _ hm
      have hkb : key ∉ b.type.names := by
        intro hm
        apply hk
        rw [hnames, merge_names]
        apply List.mem_append_right
        exact List.mem_filter.mpr ⟨hm, by simpa using hka⟩
      rw [lookup_none out.type.names out.values hlen key hk,
        lookup_none a.type.names a.values ha.2 key hka,
        lookup_none b.type.names b.values hb.2 key hkb]
  refine ⟨⟨hnd, hlen⟩, ?_, ?_⟩
  · exact (first_named out hnd hlen).trans hfirst
  · intro key
    exact (last_named out hnd hlen key).trans (hlookup key)

private theorem merged_matches (generated : Bool) (a b out : ModelNT) (ha : WF a) (hb : WF b)
    (h : mergeNamed generated a b = .ok out) :
    outputMatchesFields out (namedTupleFields a ++ namedTupleFields b) := by
  obtain ⟨hw, he⟩ := merge_core generated a b out ha hb h
  exact matches_equiv out he (fields_match out hw.1 hw.2)

private theorem merge_loop_core (generated : Bool) : ∀ (cs : List ModelNT) (a out : ModelNT),
    WF a → (∀ c, c ∈ cs → WF c) → mergeManyLoop generated a cs = .ok out →
    WF out ∧ FieldsEq (namedTupleFields out) (namedTupleFields a ++ namedTupleFieldsMany cs) := by
  intro cs
  induction cs with
  | nil =>
    intro a out ha _ h
    have he : a = out := Except.ok.inj h
    subst out
    exact ⟨ha, by simpa [namedTupleFieldsMany] using fieldsEq_refl (namedTupleFields a)⟩
  | cons b cs ih =>
    intro a out ha hall h
    cases hm : mergeNamed generated a b with
    | error err => simp [mergeManyLoop, hm, bind, Except.bind] at h
    | ok merged =>
      have ht : mergeManyLoop generated merged cs = .ok out := by
        simpa [mergeManyLoop, hm, bind, Except.bind] using h
      obtain ⟨hw, he⟩ := merge_core generated a b merged ha (hall b (by simp)) hm
      obtain ⟨hout, hfinal⟩ := ih merged out hw (fun c hc => hall c (by simp [hc])) ht
      refine ⟨hout, ?_⟩
      have hshift := fieldsEq_append he (fieldsEq_refl (namedTupleFieldsMany cs))
      have hh := fieldsEq_trans hfinal hshift
      simpa [namedTupleFieldsMany, List.append_assoc] using hh

private theorem many_matches (generated : Bool) (a b : ModelNT) (cs : List ModelNT) (out : ModelNT)
    (ha : WF a) (hb : WF b) (hall : ∀ c, c ∈ cs → WF c)
    (h : mergeMany generated a b cs = .ok out) :
    outputMatchesFields out (namedTupleFieldsMany (a :: b :: cs)) := by
  cases hm : mergeNamed generated a b with
  | error err => simp [mergeMany, hm, bind, Except.bind] at h
  | ok merged =>
    have ht : mergeManyLoop generated merged cs = .ok out := by
      simpa [mergeMany, hm, bind, Except.bind] using h
    obtain ⟨hw, he⟩ := merge_core generated a b merged ha hb hm
    obtain ⟨hout, hfinal⟩ := merge_loop_core generated cs merged out hw hall ht
    have hshift := fieldsEq_append he (fieldsEq_refl (namedTupleFieldsMany cs))
    have hh := fieldsEq_trans hfinal hshift
    apply matches_equiv out _ (fields_match out hout.1 hout.2)
    simpa [namedTupleFieldsMany, namedTupleFields, fields, List.append_assoc] using hh

private theorem iterator_matches (generated : Bool) (fromTuple : NTType → List Value → Result ModelNT)
    (typeofValue : Value → TypeTag) (a : ModelNT) (itr : List KV) (out : ModelNT)
    (ha : WF a)
    (hfrom : ∀ ty vals result, fromTuple ty vals = .ok result → result.type = ty ∧ result.values = vals)
    (h : mergeIterator generated fromTuple typeofValue a itr = .ok out) :
    outputMatchesFields out (namedTupleFields a ++ itr) := by
  cases hp : pairFields itr with
  | error err => simp [mergeIterator, hp, bind, Except.bind] at h
  | ok state =>
    rcases state with ⟨names, values⟩
    obtain ⟨hn, hl, hs, hv⟩ := pairFields_properties itr names values hp
    cases hf : fromTuple ⟨names, values.map typeofValue⟩ values with
    | error err => simp [mergeIterator, hp, constructNamesFromIterator, hf, bind, Except.bind] at h
    | ok b =>
      have hm : mergeNamed generated a b = .ok out := by
        simpa [mergeIterator, hp, constructNamesFromIterator, hf, bind, Except.bind] using h
      obtain ⟨ht, hvals⟩ := hfrom _ _ _ hf
      have hbn : b.type.names = names := congrArg NTType.names ht
      have hb : WF b := ⟨by rwa [hbn], by rwa [hbn, hvals]⟩
      have he : FieldsEq (namedTupleFields b) itr := by
        constructor
        · exact (first_named b hb.1 hb.2).trans (hbn.trans hs)
        · intro key
          rw [last_named b hb.1 hb.2, lookup, hbn, hvals]
          exact hv key
      exact matches_equiv out (fieldsEq_append (fieldsEq_refl _) he)
        (merged_matches generated a b out ha hb hm)

private theorem selected_filter (nt : ModelNT) (keep : String → Bool) : ∀ names,
    selectedNamedTupleFields nt (names.filter keep) =
      (selectedNamedTupleFields nt names).filter (fun pair =>
        match pair.key with | .symbol key => keep key | _ => true) := by
  intro names
  induction names with
  | nil => rfl
  | cons name names ih =>
    unfold selectedNamedTupleFields at ih ⊢
    cases hg : getfield nt name <;> cases hk : keep name <;>
      simp [List.filter_cons, hg, hk, ih]

private theorem own_selected (nt : ModelNT) (hw : WF nt) :
    selectedNamedTupleFields nt nt.type.names = namedTupleFields nt :=
  selected_fields nt nt.type.names nt.values (own_mapM nt hw.1 hw.2)

private theorem diff_as_fallback (generated : Bool) (a b : ModelNT) :
    structdiffNamed generated a b = diff_fallback a a.type.names b.type.names := by
  cases generated <;> rfl

private theorem difference_matches (generated : Bool) (a b out : ModelNT) (ha : WF a) (hb : WF b)
    (h : structdiffNamed generated a b = .ok out) :
    outputMatchesFields out ((namedTupleFields a).filter (fun pair =>
      match pair.key with | .symbol key => !b.type.names.contains key | _ => true)) := by
  rw [diff_as_fallback] at h
  have hm := (namedTupleTypeHelpersCorrect_proven [] a.type b.type a b.type.names
    (by simp) ha.1 hb.1 ha.1).2.2 out h
  change outputMatchesFields out
    (selectedNamedTupleFields a (a.type.names.filter (fun key => !b.type.names.contains key))) at hm
  rw [selected_filter, own_selected a ha] at hm
  exact hm

private theorem delete_matches (generated : Bool) (a out : ModelNT) (field : String) (ha : WF a)
    (h : deleteNamed generated a field = .ok out) :
    outputMatchesFields out ((namedTupleFields a).filter fun pair => pair.key ≠ .symbol field) := by
  have hn : (diff_names a.type.names [field]).Nodup := ha.1.filter _
  have hm := constructNames_selected generated a _ out hn h
  change outputMatchesFields out
    (selectedNamedTupleFields a (a.type.names.filter (fun key => ![field].contains key))) at hm
  rw [selected_filter, own_selected a ha] at hm
  have heq :
      ((namedTupleFields a).filter fun pair =>
        match pair.key with | .symbol key => ![field].contains key | _ => true) =
      ((namedTupleFields a).filter fun pair => pair.key ≠ .symbol field) := by
    apply List.filter_congr
    intro pair _
    cases hk : pair.key with
    | symbol name =>
      by_cases he : name = field
      · subst name; simp [hk]
      · simp [hk, he, Ne.symm he]
    | nativeInteger _ | integer _ | other => simp [hk]
  rwa [heq] at hm

private theorem mapM_exists {α : Type u} (f : String → Result α) : ∀ (names : List String),
    (∀ key, key ∈ names → ∃ value, f key = .ok value) → ∃ values, names.mapM f = .ok values := by
  intro names
  induction names with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons name names ih =>
    intro hall
    obtain ⟨value, hv⟩ := hall name (by simp)
    obtain ⟨values, hs⟩ := ih (fun key hk => hall key (by simp [hk]))
    exact ⟨value :: values, by simp [List.mapM_cons, hv, hs, bind, Except.bind, pure, Except.pure]⟩

private theorem selection_exists (generated : Bool) (nt : ModelNT) (names : List String)
    (hn : names.Nodup) (hall : ∀ key, key ∈ names → ∃ value, getfield nt key = .ok value) :
    ∃ out, getindexSymbols generated nt names = .ok out ∧ out.type.names = names ∧
      ∀ key, key ∈ names → getfield out key = getfield nt key := by
  obtain ⟨values, hv⟩ := mapM_exists (getfield nt) names hall
  have hex : ∃ out, constructNamesFromNamedTuple generated nt names = .ok out := by
    cases generated <;> simp [constructNamesFromNamedTuple, hv, bind, Except.bind, pure, Except.pure]
  obtain ⟨out, hc⟩ := hex
  refine ⟨out, hc, (constructNames_shape generated nt names out hc).1, ?_⟩
  intro key hk
  exact constructNames_getfield generated nt names out hc hk

 theorem namedTupleCorrect_proven : NamedTupleCorrect := by
  intro generated a b han hbn hal hbl
  have ha : WF a := ⟨han, hal⟩
  have hb : WF b := ⟨hbn, hbl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro out h
    exact merged_matches generated a b out ha hb h
  · intro out h
    exact merged_matches false a b out ha hb h
  · intro out h
    exact difference_matches generated a b out ha hb h
  · intro typeofValue value key out h
    exact merged_matches generated a (newNamedTuple ⟨[key], [typeofValue value]⟩ [value]) out
      ha ⟨by simp [newNamedTuple], rfl⟩ h
  · intro names hn hall
    exact selection_exists generated a names hn hall
  · intro names out hn _ h
    exact constructNames_selected generated a names out hn h

 theorem ntMergeItrCorrect_proven : NTMergeItrCorrect := by
  intro generated fromTuple typeofValue a b cs itr han hal hbn hbl hall _ hfrom
  have ha : WF a := ⟨han, hal⟩
  have hb : WF b := ⟨hbn, hbl⟩
  refine ⟨?_, ?_, rfl, ?_, ?_, (fun _ _ => rfl), (fun _ _ _ _ => rfl), (fun _ _ => rfl)⟩
  · intro out h
    exact iterator_matches generated fromTuple typeofValue a itr out ha hfrom h
  · intro out h
    exact merged_matches generated a b out ha hb h
  · intro out h
    exact many_matches generated a b cs out ha hb hall h
  · intro field out h
    exact delete_matches generated a out field ha h

/-! ## Registry entries -/

def entries : List Entry := [
  { id := "tuples-namedtuple-haskey-integer", juliaFile := "base/namedtuple.jl"
    juliaFns := ["haskey(nt::NamedTuple, key::Union{Integer,Symbol})", "get(nt::NamedTuple, key::Union{Integer,Symbol}, default)", "get(f, nt::NamedTuple, key)"]
    statement := "Integer keys address the corresponding one-based named-tuple field; missing integer keys use the supplied default."
    source := "base/namedtuple.jl:384-386 (integer and symbol key methods)"
    status := .refuted, prop := ``HaskeyInteger, thm := some ``haskeyInteger_refuted,
    notes := "Non-native integer keys throw TypeError in isdefined; repro/tuples-namedtuple-haskey-integer.jl."
    issue := "none found (queries: haskey NamedTuple, NamedTuple get Integer, isdefined Int32)" },
  { id := "tuples-namedtuple-merge", juliaFile := "base/namedtuple.jl"
    juliaFns := ["merge(a::NamedTuple, b::NamedTuple)", "merge_names", "merge_fallback", "structdiff", "diff_names", "setindex(nt::NamedTuple, v, idx::Symbol)", "getindex(t::NamedTuple, idxs::Tuple{Vararg{Symbol}})"]
    statement := "Merge preserves first field positions and takes values from the rightmost matching tuple; structdiff and setindex retain the requested fields and values, and symbol selection preserves requested order."
    source := "base/namedtuple.jl:306-340 (merge docstring and method), 442-485 (structdiff and setindex docstrings)"
    status := .proven, prop := ``NamedTupleCorrect, thm := some ``namedTupleCorrect_proven },
  { id := "sorttuplescov-nt-construct", juliaFile := "base/namedtuple.jl"
    juliaFns := ["NamedTuple{names,T}(args::Tuple)", "NamedTuple{names,T}(nt::NamedTuple)", "NamedTuple{names}(nt::NamedTuple)", "NamedTuple{names,T}(itr)", "NamedTuple{names}(itr)", "NamedTuple(itr)", "_new_NamedTuple", "convert(::Type{NT}, nt::NT)", "Tuple(nt::NamedTuple)", "(::Type{T})(nt::NamedTuple)"]
    statement := "Named-tuple constructors reject a value-count mismatch, preserve requested field names, and convert supplied values to their declared field types; tuple conversion retains the values in order."
    source := "base/namedtuple.jl:6-112 (NamedTuple docstring), 115-196"
    status := .proven, prop := ``NTConstructCorrect, thm := some ``ntConstructCorrect_proven,
    notes := "Constructor preservation assumes the documented equal arity of field names and declared field types." },
  { id := "sorttuplescov-nt-access", juliaFile := "base/namedtuple.jl"
    juliaFns := ["length(t::NamedTuple)", "iterate(t::NamedTuple, iter)", "rest(t::NamedTuple)", "firstindex", "lastindex", "getindex(t::NamedTuple, i::Int)", "getindex(t::NamedTuple, i::Symbol)", "getindex(t::NamedTuple, ::Colon)", "indexed_iterate(t::NamedTuple, i, state)", "isempty", "empty", "keys", "values", "tail", "front", "reverse(nt::NamedTuple)", "prevind", "nextind"]
    statement := "Named tuples iterate and index their values in field order, expose names and values separately, and tail, front, or reverse the corresponding fields."
    source := "base/namedtuple.jl:159-176,382-389"
    status := .proven, prop := ``NTAccessCorrect, thm := some ``ntAccessCorrect_proven,
    notes := "The rest field-partition contract requires an index between zero and the field count." },
  { id := "sorttuplescov-nt-compare", juliaFile := "base/namedtuple.jl"
    juliaFns := ["==(a::NamedTuple{n}, b::NamedTuple{n})", "==(a::NamedTuple, b::NamedTuple)", "isequal", "_nt_names", "<(a::NamedTuple{n}, b::NamedTuple{n})", "isless(a::NamedTuple{n}, b::NamedTuple)", "same_names"]
    statement := "Named tuples with the same names compare and order their value tuples; equality and isequal are false when names differ."
    source := "base/namedtuple.jl:241-256"
    status := .proven, prop := ``NTCompareCorrect, thm := some ``ntCompareCorrect_proven },
  { id := "sorttuplescov-nt-map-filter", juliaFile := "base/namedtuple.jl"
    juliaFns := ["map(f, nt::NamedTuple{names}, nts::NamedTuple...)", "filter(f, xs::NamedTuple)"]
    statement := "Named-tuple map rejects mismatched names and applies the function to corresponding values; filter keeps exactly the fields accepted by its predicate."
    source := "base/namedtuple.jl:258-266"
    status := .proven, prop := ``NTMapFilterCorrect, thm := some ``ntMapFilterCorrect_proven },
  { id := "sorttuplescov-nt-merge-itr", juliaFile := "base/namedtuple.jl"
    juliaFns := ["merge(a::NamedTuple, itr)", "merge(a::NamedTuple, b::Iterators.Pairs)", "merge(a, b, cs...)", "merge(a::NamedTuple)", "delete(a::NamedTuple, field::Symbol)"]
    statement := "Iterator merges retain a key's first position and last value, multiple named tuples merge left-to-right, one-argument merge is identity, and delete removes the selected field."
    source := "base/namedtuple.jl:307-380 (merge docstrings and iterator method), 437-440 (delete docstring)"
    status := .proven, prop := ``NTMergeItrCorrect, thm := some ``ntMergeItrCorrect_proven },
  { id := "sorttuplescov-merge-zip", juliaFile := "base/namedtuple.jl"
    juliaFns := ["merge(a::NamedTuple, b::Iterators.Zip{<:Tuple{Any,Any}})"]
    statement := "Merging a zip of key and value iterators agrees with merging the iterator's key-value pairs."
    source := "base/namedtuple.jl:354-357 (merge iterator contract)"
    status := .refuted, prop := ``MergeZipAgrees, thm := some ``mergeZipAgrees_refuted,
    notes := "Duplicate-key zip merging throws while collected-pair merging succeeds; repro/sorttuplescov-merge-zip.jl."
    issue := "none found (queries: merge NamedTuple zip, merge zip duplicate, NamedTuple merge iterator)" },
  { id := "sorttuplescov-namedtuple-show", juliaFile := "base/namedtuple.jl"
    juliaFns := ["show(io::IO, t::NamedTuple)"]
    statement := "Display uses the full type if a field value does not match its declared type, `NamedTuple()` for no fields, and ordered name-value pairs otherwise."
    source := "base/namedtuple.jl:198-229; Base show contract"
    status := .proven, prop := ``NamedTupleShowCorrect, thm := some ``namedTupleShowCorrect_proven },
  { id := "sorttuplescov-namedtuple-type-methods", juliaFile := "base/namedtuple.jl"
    juliaFns := ["eltype(::Type{T})", "nteltype", "keytype(::NamedTuple)", "keytype(::Type{<:NamedTuple})", "valtype(::NamedTuple)", "valtype(::Type{<:NamedTuple})", "_nt_names(::Type)"]
    statement := "NamedTuple key types are Symbol, and value and element types follow the declared tuple type."
    source := "base/namedtuple.jl:231-248"
    status := .proven, prop := ``NamedTupleTypeMethodsCorrect, thm := some ``namedTupleTypeMethodsCorrect_proven },
  { id := "sorttuplescov-namedtuple-type-helpers", juliaFile := "base/namedtuple.jl"
    juliaFns := ["merge_types", "diff_types", "diff_fallback"]
    statement := "Merged fields keep the rightmost declared type, while a difference keeps each retained field's original type and value."
    source := "base/namedtuple.jl:280-285,403-422"
    status := .proven, prop := ``NamedTupleTypeHelpersCorrect, thm := some ``namedTupleTypeHelpersCorrect_proven },
  { id := "sorttuplescov-namedtuple-macros", juliaFile := "base/namedtuple.jl"
    juliaFns := ["@NamedTuple", "@Kwargs"]
    statement := "The macros preserve declaration order, use Any for omitted field types, ignore line nodes, reject malformed declarations, and give keyword arguments a Symbol key type."
    source := "base/namedtuple.jl:487-523,525-583"
    status := .proven, prop := ``NamedTupleMacrosCorrect, thm := some ``namedTupleMacrosCorrect_proven },
  { id := "sorttuplescov-namedtuple-hash", juliaFile := "base/namedtuple.jl"
    juliaFns := ["hash(x::NamedTuple,h::UInt)"]
    statement := "Equal named tuples have equal hashes for every seed when their value tuple's hash respects isequal."
    source := "base/namedtuple.jl:250; hash contract"
    status := .proven, prop := ``NamedTupleHashCorrect, thm := some ``namedTupleHashCorrect_proven },
  { id := "sorttuplescov-namedtuple-split-rest", juliaFile := "base/namedtuple.jl"
    juliaFns := ["split_rest(t::NamedTuple,n,st...)"]
    statement := "Named-tuple split_rest partitions field names and values into the requested leading and trailing portions."
    source := "base/namedtuple.jl:585-589; tuple split_rest contract"
    status := .proven, prop := ``NamedTupleSplitRestDelegates, thm := some ``namedTupleSplitRestDelegates_proven }
]

/-! ## Method-to-property coverage

The method names below use their Julia source signatures. -/

def methodProperties : List (String × String) := [
  ("NamedTuple{names,T}(args::Tuple)@115", "sorttuplescov-nt-construct"),
  ("NamedTuple{names,T}(nt::NamedTuple)@124", "sorttuplescov-nt-construct"),
  ("NamedTuple{names}(nt::NamedTuple)@136", "sorttuplescov-nt-construct"),
  ("NamedTuple{names,T}(itr)@148", "sorttuplescov-nt-construct"),
  ("NamedTuple{names}(itr)@149", "sorttuplescov-nt-construct"),
  ("NamedTuple(itr)@151", "sorttuplescov-nt-construct"),
  ("_new_NamedTuple@155", "sorttuplescov-nt-construct"),
  ("length(t::NamedTuple)@159", "sorttuplescov-nt-access"),
  ("iterate(t::NamedTuple)@160", "sorttuplescov-nt-access"),
  ("rest(t::NamedTuple)@161", "sorttuplescov-nt-access"),
  ("rest(t::NamedTuple{names}, i)@162", "sorttuplescov-nt-access"),
  ("firstindex(t::NamedTuple)@163", "sorttuplescov-nt-access"),
  ("lastindex(t::NamedTuple)@164", "sorttuplescov-nt-access"),
  ("getindex(t::NamedTuple, i::Int)@165", "sorttuplescov-nt-access"),
  ("getindex(t::NamedTuple, i::Symbol)@166", "sorttuplescov-nt-access"),
  ("getindex(t::NamedTuple, ::Colon)@167", "sorttuplescov-nt-access"),
  ("getindex(t::NamedTuple, idxs::Tuple{Vararg{Symbol}})@168", "tuples-namedtuple-merge"),
  ("getindex(t::NamedTuple, idxs::AbstractVector{Symbol})@169", "sorttuplescov-nt-access"),
  ("indexed_iterate(t::NamedTuple, i::Int)@170", "sorttuplescov-nt-access"),
  ("isempty(::NamedTuple{()})@171", "sorttuplescov-nt-access"),
  ("isempty(::NamedTuple)@172", "sorttuplescov-nt-access"),
  ("empty(::NamedTuple)@173", "sorttuplescov-nt-access"),
  ("prevind(t::NamedTuple, i::Integer)@175", "sorttuplescov-nt-access"),
  ("nextind(t::NamedTuple, i::Integer)@176", "sorttuplescov-nt-access"),
  ("convert(::Type{NT}, nt::NT) where NT<:NamedTuple{names}@178", "sorttuplescov-nt-construct"),
  ("convert(::Type{NT}, nt::NT) where NT<:NamedTuple{names,T}@179", "sorttuplescov-nt-construct"),
  ("convert(::Type{NT}, t::Tuple)@180", "sorttuplescov-nt-construct"),
  ("convert(::Type{NamedTuple{names,T}}, nt::NamedTuple{names})@182", "sorttuplescov-nt-construct"),
  ("convert(::Type{NT}, nt::NamedTuple{names})@187", "sorttuplescov-nt-construct"),
  ("Tuple(nt::NamedTuple)@195", "sorttuplescov-nt-construct"),
  ("(::Type{T})(nt::NamedTuple) where T<:Tuple@196", "sorttuplescov-nt-construct"),
  ("show(io::IO, t::NamedTuple)@198", "sorttuplescov-namedtuple-show"),
  ("eltype(::Type{T})@231", "sorttuplescov-namedtuple-type-methods"),
  ("nteltype(::Type)@232", "sorttuplescov-namedtuple-type-methods"),
  ("nteltype(::Type{NamedTuple{names,T}})@233", "sorttuplescov-namedtuple-type-methods"),
  ("keytype(nt::NamedTuple)@235", "sorttuplescov-namedtuple-type-methods"),
  ("keytype(T::Type{<:NamedTuple})@236", "sorttuplescov-namedtuple-type-methods"),
  ("valtype(nt::NamedTuple)@238", "sorttuplescov-namedtuple-type-methods"),
  ("valtype(T::Type{<:NamedTuple})@239", "sorttuplescov-namedtuple-type-methods"),
  ("==(a::NamedTuple{n}, b::NamedTuple{n})@241", "sorttuplescov-nt-compare"),
  ("==(a::NamedTuple, b::NamedTuple)@242", "sorttuplescov-nt-compare"),
  ("isequal(a::NamedTuple{n}, b::NamedTuple{n})@244", "sorttuplescov-nt-compare"),
  ("isequal(a::NamedTuple, b::NamedTuple)@245", "sorttuplescov-nt-compare"),
  ("_nt_names(nt::NamedTuple{names})@247", "sorttuplescov-nt-compare"),
  ("_nt_names(::Type{T})@248", "sorttuplescov-namedtuple-type-methods"),
  ("hash(x::NamedTuple, h::UInt)@250", "sorttuplescov-namedtuple-hash"),
  ("<(a::NamedTuple{n}, b::NamedTuple{n})@252", "sorttuplescov-nt-compare"),
  ("isless(a::NamedTuple{n}, b::NamedTuple{n})@253", "sorttuplescov-nt-compare"),
  ("same_names(::NamedTuple{names}...)@255", "sorttuplescov-nt-compare"),
  ("same_names(::NamedTuple...)@256", "sorttuplescov-nt-compare"),
  ("map(f, nt::NamedTuple{names}, nts::NamedTuple...)@259", "sorttuplescov-nt-map-filter"),
  ("filter(f, xs::NamedTuple)@266", "sorttuplescov-nt-map-filter"),
  ("merge_names(an::Tuple{Vararg{Symbol}}, bn::Tuple{Vararg{Symbol}})@268", "tuples-namedtuple-merge"),
  ("merge_types(names::Tuple{Vararg{Symbol}}, a, b)@280", "sorttuplescov-namedtuple-type-helpers"),
  ("merge_fallback(a::NamedTuple, b::NamedTuple, an, bn)@287", "tuples-namedtuple-merge"),
  ("merge(a::NamedTuple{an}, b::NamedTuple{bn})@331", "tuples-namedtuple-merge"),
  ("merge(a::NamedTuple, b::NamedTuple{()})@342", "sorttuplescov-nt-merge-itr"),
  ("merge(a::NamedTuple{()}, b::NamedTuple{()})@343", "sorttuplescov-nt-merge-itr"),
  ("merge(a::NamedTuple{()}, b::NamedTuple)@344", "sorttuplescov-nt-merge-itr"),
  ("merge(a::NamedTuple, b::Iterators.Pairs)@346", "sorttuplescov-nt-merge-itr"),
  ("merge(a::NamedTuple, b::Iterators.Zip)@348", "sorttuplescov-merge-zip"),
  ("merge(a::NamedTuple, b::NamedTuple, cs::NamedTuple...)@350", "sorttuplescov-nt-merge-itr"),
  ("merge(a::NamedTuple)@352", "sorttuplescov-nt-merge-itr"),
  ("merge(a::NamedTuple, itr)@364", "sorttuplescov-nt-merge-itr"),
  ("keys(nt::NamedTuple{names})@382", "sorttuplescov-nt-access"),
  ("values(nt::NamedTuple)@383", "sorttuplescov-nt-access"),
  ("haskey(nt::NamedTuple, key::Union{Integer,Symbol})@384", "tuples-namedtuple-haskey-integer"),
  ("get(nt::NamedTuple, key::Union{Integer,Symbol}, default)@385", "tuples-namedtuple-haskey-integer"),
  ("get(f, nt::NamedTuple, key::Union{Integer,Symbol})@386", "tuples-namedtuple-haskey-integer"),
  ("tail(t::NamedTuple{names})@387", "sorttuplescov-nt-access"),
  ("front(t::NamedTuple{names})@388", "sorttuplescov-nt-access"),
  ("reverse(nt::NamedTuple)@389", "sorttuplescov-nt-access"),
  ("diff_names(an::Tuple{Vararg{Symbol}}, bn::Tuple{Vararg{Symbol}})@391", "tuples-namedtuple-merge"),
  ("diff_types(a::NamedTuple, names::Tuple{Vararg{Symbol}})@403", "sorttuplescov-namedtuple-type-helpers"),
  ("diff_fallback(a::NamedTuple, an, bn)@409", "sorttuplescov-namedtuple-type-helpers"),
  ("delete(a::NamedTuple{an}, field::Symbol)@437", "sorttuplescov-nt-merge-itr"),
  ("structdiff(a::NamedTuple{an}, b::Union{NamedTuple{bn}, Type{NamedTuple{bn}}})@448", "tuples-namedtuple-merge"),
  ("structdiff(a::NamedTuple{an}, b::Union{NamedTuple{an}, Type{NamedTuple{an}}})@461", "tuples-namedtuple-merge"),
  ("setindex(nt::NamedTuple, v, idx::Symbol)@483", "tuples-namedtuple-merge"),
  ("@NamedTuple(ex)@514", "sorttuplescov-namedtuple-macros"),
  ("@Kwargs(ex)@578", "sorttuplescov-namedtuple-macros"),
  ("split_rest(t::NamedTuple{names}, n::Int, st...)@585", "sorttuplescov-namedtuple-split-rest")
]

end JuliaLean.Proofs.base.namedtuple
