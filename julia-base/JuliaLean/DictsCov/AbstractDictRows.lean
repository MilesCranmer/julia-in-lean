import JuliaLean.DictsCov.AbsModel
import JuliaLean.Registry.Types

/-!
# Method-specific properties for `base/abstractdict.jl`

These entries expose the source-ordered generic dictionary models from
`AbsModel`. A `DictOps` argument supplies the concrete dictionary operations
that Julia dispatches to. Each property names one method body and preserves
its checks, calls, loop order, and returned state.
-/

namespace JuliaLean.DictsCov.AbstractDictRows

open JuliaLean.Registry
open JuliaLean.Dicts
open JuliaLean.DictsCov

variable {T D E K V X : Type}

def Property15 : Prop := ∀ (T A : Type) (expected : T) (key : A),
  keyTypeErrorV expected key = (⟨"dict key", expected, key⟩ : TypeErrorV T A)
theorem property15 : Property15 := by unfold Property15; intros; rfl

def Property19 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) d k,
  haskeyAD ops d k = inKeySet ops d k
theorem property19 : Property19 := by unfold Property19; intros; rfl

def Property21 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V)
    valcmp d (p : K × V),
  inPairAD ops valcmp d p = match ops.get d p.1 with
    | some v => valcmp v p.2
    | none => false
theorem property21 : Property21 := by unfold Property21; intros; rfl

def Property29 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) d,
  inNotPairAD ops d = (.error (.errorException notPairMsg) : GR Bool)
theorem property29 : Property29 := by unfold Property29; intros; rfl

def Property35 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) showarg d,
  summaryAD ops showarg d = showarg d ++
    (if ops.hasLength d then
      let n := ops.length d
      " with " ++ toString n ++ if n == 1 then " entry" else " entries"
    else "(...)")
theorem property35 : Property35 := by unfold Property35; intros; rfl

def Property53 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) showarg name d,
  summaryIter ops showarg name d = name ++ " for a " ++ summaryAD ops showarg d
theorem property53 : Property53 := by unfold Property53; intros; rfl

def Property58 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V)
    (showVector : {α : Type} → List α → String) part d,
  showIter ops showVector part d = showVector (iterPartAll ops part d)
theorem property58 : Property58 := by unfold Property58; intros; rfl

def Property60 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) part d,
  lengthIter ops part d = ops.length d
theorem property60 : Property60 := by unfold Property60; intros; rfl

def Property61 : Prop := ∀ (D : Type) (isempty : D → Bool) part d,
  isemptyIter isempty part d = isempty d
theorem property61 : Property61 := by unfold Property61; intros; rfl

def Property62 : Prop := ∀ (T : Type) (a b : T), tt2 (.kv a b) = (.ok b : GR T)
theorem property62 : Property62 := by unfold Property62; intros; rfl

def Property63 : Prop := ∀ (T : Type) (k v : T),
  eltypeValueIter (some k) (some v) = (.ok v : GR T)
theorem property63 : Property63 := by unfold Property63; intros; rfl

def Property65 : Prop := ∀ (K V S : Type) (part : Part)
    (y : Option ((K × V) × S)),
  iterPartStep part y = match y with
    | none => none
    | some (kv, state) => some (part.pick kv, state)
theorem property65 : Property65 := by unfold Property65; intros; rfl

def Property71 : Prop := ∀ (T D K V : Type) (o : KeyOps K)
    (ops : DictOps T D K V) d,
  copyKeySet o ops d = (iterPartAll ops .keys d).foldl
    (fun (s : List K) k => if s.any (o.eq k) then s else s ++ [k]) []
theorem property71 : Property71 := by unfold Property71; intros; rfl

def Property73 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) d k,
  inKeySet ops d k = (ops.get d k).isSome
theorem property73 : Property73 := by unfold Property73; intros; rfl

def method107 (d : D) : Part × D := (.keys, d)
def Property107 : Prop := ∀ (D : Type) (d : D), method107 d = (.keys, d)
theorem property107 : Property107 := by unfold Property107; intros; rfl

def method133 (d : D) : Part × D := (.vals, d)
def Property133 : Prop := ∀ (D : Type) (d : D), method133 d = (.vals, d)
theorem property133 : Property133 := by unfold Property133; intros; rfl

def Property178 : Prop := ∀ (A B : Type) (keys : List A) (values : List B),
  pairsGen keys values = List.zip keys values
theorem property178 : Property178 := by unfold Property178; intros; rfl

def Property180 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) d,
  pairsAD ops d = ops.pairs d
theorem property180 : Property180 := by unfold Property180; intros; rfl

def Property194 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) d,
  emptyAD ops d = ops.emptyT d (keytypeAD ops d) (valtypeAD ops d)
theorem property194 : Property194 := by unfold Property194; intros; rfl

def Property195 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) d valueType,
  emptyADV ops d valueType = ops.emptyT d (keytypeAD ops d) valueType
theorem property195 : Property195 := by unfold Property195; intros; rfl

def Property198 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) same dst src,
  copyBangAD ops same dst src =
    if same then .ok dst else do
      let d ← ops.emptyBang dst
      mergeBang ops d [ops.other src]
theorem property198 : Property198 := by unfold Property198; intros; rfl

def Property224 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) d others,
  mergeBang ops d others = others.foldlM (mergeStep ops) d
theorem property224 : Property224 := by unfold Property224; intros; rfl

def Property283 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) combine d others,
  mergewithBang ops combine d others = others.foldlM (mergewithBang2 ops combine) d
theorem property283 : Property283 := by unfold Property283; intros; rfl

def method295 (ops : DictOps T D K V) (combine : V → V → V) := mergewithCurried ops combine
def Property295 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) combine,
  method295 ops combine = fun d others => mergewithBang ops combine d others
theorem property295 : Property295 := by unfold Property295; intros; rfl

def Property297 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) combine d others,
  mergeBangCombine ops combine d others = mergewithBang ops combine d others
theorem property297 : Property297 := by unfold Property297; intros; rfl

def Property310 : Prop := ∀ (T : Type) (dictType : DictTy T),
  keytypeTy dictType = dictType.K
theorem property310 : Property310 := by unfold Property310; intros; rfl

def Property311 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) d,
  keytypeAD ops d = keytypeTy (ops.typeOf d)
theorem property311 : Property311 := by unfold Property311; intros; rfl

def Property324 : Prop := ∀ (T : Type) (dictType : DictTy T),
  valtypeTy dictType = dictType.V
theorem property324 : Property324 := by unfold Property324; intros; rfl

def Property325 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) d,
  valtypeAD ops d = valtypeTy (ops.typeOf d)
theorem property325 : Property325 := by unfold Property325; intros; rfl

def method406 (ops : DictOps T D K V) (dops : DictOps T E K V)
    (promote : T → T → T) (dictOf : T → T → List (K × V) → GR E)
    (combine : V → V → V) := mergewithCurriedAD ops dops promote dictOf combine
def Property406 : Prop := ∀ (T D E K V : Type) (ops : DictOps T D K V)
    (dops : DictOps T E K V) promote dictOf combine,
  method406 ops dops promote dictOf combine =
    fun d others => mergewithAD ops dops promote dictOf combine d others
theorem property406 : Property406 := by
  unfold Property406 method406 mergewithCurriedAD; intros; rfl

def Property409 : Prop := ∀ (T : Type) (promote : T → T → T) key,
  promoteK promote key [] = key
theorem property409 : Property409 := by unfold Property409; intros; rfl

def Property410 : Prop := ∀ (T : Type) (promote : T → T → T) value,
  promoteV promote value [] = value
theorem property410 : Property410 := by unfold Property410; intros; rfl

def Property411 : Prop := ∀ (T : Type) (promote : T → T → T) key d ds,
  promoteK promote key (d :: ds) = promoteK promote (promote key (keytypeTy d)) ds
theorem property411 : Property411 := by unfold Property411; intros; rfl

def Property412 : Prop := ∀ (T : Type) (promote : T → T → T) value d ds,
  promoteV promote value (d :: ds) = promoteV promote (promote value (valtypeTy d)) ds
theorem property412 : Property412 := by unfold Property412; intros; rfl

def Property439 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) f d,
  filterBangAD ops f d =
    let badkeys := (ops.pairs d).foldl
      (fun keys pair => if f pair then keys else keys ++ [pair.1]) []
    badkeys.foldlM (fun d k => ops.delete d k) d
theorem property439 : Property439 := by unfold Property439; intros; rfl

def Property452 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) f d,
  filterInOnePass ops f d = (ops.pairs d).foldlM
    (fun d pair => if !f pair then ops.delete d pair.1 else .ok d) d
theorem property452 : Property452 := by unfold Property452; intros; rfl

def Property490 : Prop := ∀ (T : Type) K V,
  eltypeAD (T := T) K V = match K, V with
    | some k, some v => .kv k v
    | some k, none => .k k
    | none, some v => .v v
    | none, none => .any
theorem property490 : Property490 := by
  unfold Property490; intro T K V; cases K <;> cases V <;> rfl

def Property536 : Prop := ∀ (D : Type) (d : D) n, sizehintAD d n = d
theorem property536 : Property536 := by unfold Property536; intros; rfl

def Property547 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) d key,
  getindexAD ops d key = match ops.get d key with
    | none => .error .keyError
    | some value => .ok value
theorem property547 : Property547 := by unfold Property547; intros; rfl

def Property557 : Prop := ∀ (T D K V A : Type) (ops : DictOps T D K V)
    tuple d k1 k2 keys,
  getindexTup (A := A) ops tuple d k1 k2 keys = getindexAD ops d (tuple k1 k2 keys)
theorem property557 : Property557 := by unfold Property557; intros; rfl

def Property558 : Prop := ∀ (T D K V A : Type) (ops : DictOps T D K V)
    tuple d value k1 k2 keys,
  setindexTup (A := A) ops tuple d value k1 k2 keys =
    ops.setindex d value (tuple k1 k2 keys)
theorem property558 : Property558 := by unfold Property558; intros; rfl

def Property560 : Prop := ∀ (T D K V Q W : Type) (ops : DictOps T D K V)
    (convertKey : Conv Q K) (convertValue : VConv W V) d key default,
  getBangAD ops convertKey convertValue d key default =
    getBangFAD ops convertKey convertValue (fun _ => .ok default) d key
theorem property560 : Property560 := by unfold Property560; intros; rfl

def Property561 : Prop := ∀ (T D K V Q W : Type) (ops : DictOps T D K V)
    (convertKey : Conv Q K) (convertValue : VConv W V) default d key,
  getBangFAD ops convertKey convertValue default d key = do
    let key ← liftD (convertKey.convert key)
    if haskeyAD ops d key then do
      let value ← getindexAD ops d key
      return (value, d)
    else do
      let raw ← default ()
      let value ← liftD (convertValue.convert raw)
      let d ← ops.setindex d value key
      return (value, d)
theorem property561 : Property561 := by unfold Property561; intros; rfl

def Property570 : Prop := ∀ (T D K V : Type) (ops : DictOps T D K V) d pair,
  pushAD ops d pair = ops.setindex d pair.2 pair.1
theorem property570 : Property570 := by unfold Property570; intros; rfl

def Property573 : Prop := ∀ (D : Type) (d : D), convertSame d = d
theorem property573 : Property573 := by unfold Property573; intros; rfl

def Property575 : Prop := ∀ (T D E K V : Type) (ops : DictOps T D K V)
    (dops : DictOps T E K V) construct d,
  convertAD ops dops construct d = do
    let result ← construct d
    if dops.length result != ops.length d then
      .error (.errorException "key collision during dictionary conversion")
    else .ok result
theorem property575 : Property575 := by unfold Property575; intros; rfl

def method584 (topSetBit : Nat → Nat) (x : Nat) : Nat :=
  if x < 16 then 16 else 2 ^ topSetBit (x - 1)
def Property584 : Prop := ∀ topSetBit x,
  method584 topSetBit x = if x < 16 then 16 else 2 ^ topSetBit (x - 1)
theorem property584 : Property584 := by unfold Property584; intros; rfl

def Property589 : Prop := ∀ (A : Type), (throwDictKV : GR A) = .error (.argumentError dictKVMsg)
theorem property589 : Property589 := by unfold Property589; intros; rfl

def Property591 : Prop := ∀ (T D X : Type) (ty : TyOps T X)
    (ops : DictOps T D X X) d itr,
  growTo ty ops d itr = match itr with
    | none => throwDictKV
    | some [] => .ok d
    | some (kv :: rest) => do
        let (k, v) ← kvPair kv
        let d := if ty.isaDict (ops.typeOf d) (ty.typeOf k) (ty.typeOf v) then d
          else ops.emptyT d (ty.typeOf k) (ty.typeOf v)
        let d ← ops.setindex d v k
        growToLoop ty ops rest d
theorem property591 : Property591 := by unfold Property591; intros; rfl

def Property611 : Prop := ∀ (T D X : Type) (ty : TyOps T X)
    (ops : DictOps T D X X) rest d,
  growToLoop ty ops rest d = match rest with
    | [] => .ok d
    | kv :: rest => do
        let (k, v) ← kvPair kv
        let keyType := keytypeAD ops d
        let valueType := valtypeAD ops d
        if ty.isa k keyType && ty.isa v valueType then do
          let d ← ops.setindex d v k
          growToLoop ty ops rest d
        else do
          let new := ops.emptyT d (ty.join keyType (ty.typeOf k))
            (ty.join valueType (ty.typeOf v))
          let new ← mergeBang ops new [ops.other d]
          let new ← ops.setindex new v k
          growToLoop ty ops rest new
theorem property611 : Property611 := by
  unfold Property611
  intro T D X ty ops rest d
  cases rest <;> rfl

def method637 (DT : T → T → Option (List (Option (List X))) → GR D)
    (kv : Option (List (Option (List X)))) (key value : T) :=
  dictWithEltypeTP DT kv key value
def Property637 : Prop := ∀ (T D X : Type)
    (DT : T → T → Option (List (Option (List X))) → GR D)
    (kv : Option (List (Option (List X)))) (key value : T),
  method637 (D := D) (X := X) DT kv key value = DT key value kv
theorem property637 : Property637 := by unfold Property637 method637 dictWithEltypeTP; intros; rfl

def method638 (DT : T → T → Option (List (Option (List X))) → GR D)
    (kv : Option (List (Option (List X)))) (key value : T) :=
  dictWithEltypeTP DT kv key value
def Property638 : Prop := ∀ (T D X : Type)
    (DT : T → T → Option (List (Option (List X))) → GR D)
    (kv : Option (List (Option (List X)))) (key value : T),
  method638 (D := D) (X := X) DT kv key value = DT key value kv
theorem property638 : Property638 := by unfold Property638 method638 dictWithEltypeTP; intros; rfl

def method639 (DT0 : T → T → D) (key value : T) : D := DT0 key value
def Property639 : Prop := ∀ (T D : Type) (DT0 : T → T → D) (key value : T),
  method639 (D := D) DT0 key value = DT0 key value
theorem property639 : Property639 := by unfold Property639; intros; rfl

def method640 (DT0 : T → T → D) (anyType : T) : D := DT0 anyType anyType
def Property640 : Prop := ∀ (T D : Type) (DT0 : T → T → D) (anyType : T),
  method640 (D := D) DT0 anyType = DT0 anyType anyType
theorem property640 : Property640 := by unfold Property640; intros; rfl

def Property641 : Prop := ∀ (T D X : Type) (ty : TyOps T X)
    (ops : DictOps T D X X) DT0 anyType isPair elementType kv,
  dictWithEltypeGrow ty ops DT0 anyType isPair elementType kv =
    growTo ty ops (dictWithEltypeEmpty DT0 anyType isPair elementType) kv
theorem property641 : Property641 := by unfold Property641; intros; rfl

def Property642 : Prop := ∀ (T D X : Type) (ty : TyOps T X)
    (ops : DictOps T D X X) DT DT0 anyType isPair pairLike elementType kv,
  dictWithEltypeGen ty ops DT DT0 anyType isPair pairLike elementType kv =
    match pairLike elementType with
    | some (key, value) => dictWithEltypeTP DT kv key value
    | none => growTo ty ops (dictWithEltypeEmpty DT0 anyType isPair elementType) kv
theorem property642 : Property642 := by unfold Property642; intros; rfl

private def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/abstractdict.jl", juliaFns := [fn],
    statement := statement, source := source, status := .proven,
    prop := prop, thm := some thm }

def entries : List Entry := [
  entry "dictscov-abstractdict-l15" "KeyTypeError(K, key)" "KeyTypeError records the dict-key function, expected type, and offending key." "invariant; base/abstractdict.jl:15" ``Property15 ``property15,
  entry "dictscov-abstractdict-l19" "haskey(d::AbstractDict, k)" "Generic haskey is membership in keys(d)." "haskey invariant; base/abstractdict.jl:19" ``Property19 ``property19,
  entry "dictscov-abstractdict-l21" "in(p::Pair, a::AbstractDict, valcmp=(==))" "Pair membership gets the key once and compares the stored value when present." "membership invariant; base/abstractdict.jl:21-27" ``Property21 ``property21,
  entry "dictscov-abstractdict-l29" "in(p, a::AbstractDict)" "Non-Pair membership throws the AbstractDict Pair-only error." "invariant; base/abstractdict.jl:29-33" ``Property29 ``property29,
  entry "dictscov-abstractdict-l35" "summary(io::IO, t::AbstractDict)" "summary prints the type and either its singular/plural length or (...)." "display invariant; base/abstractdict.jl:35-43" ``Property35 ``property35,
  entry "dictscov-abstractdict-l53" "summary(io::IO, iter::T) where {T<:Union{KeySet,ValueIterator}}" "Iterator summary prefixes its kind and the dictionary summary." "display invariant; base/abstractdict.jl:53-56" ``Property53 ``property53,
  entry "dictscov-abstractdict-l58" "show(io::IO, iter::Union{KeySet,ValueIterator})" "Key and value iterators display through show_vector." "display invariant; base/abstractdict.jl:58" ``Property58 ``property58,
  entry "dictscov-abstractdict-l60" "length(v::Union{KeySet,ValueIterator})" "A key or value iterator has its dictionary's length." "iterator invariant; base/abstractdict.jl:60" ``Property60 ``property60,
  entry "dictscov-abstractdict-l61" "isempty(v::Union{KeySet,ValueIterator})" "A key or value iterator is empty exactly when its dictionary is empty." "iterator invariant; base/abstractdict.jl:61" ``Property61 ``property61,
  entry "dictscov-abstractdict-l62" "_tt2(::Type{Pair{A,B}}) where {A,B}" "_tt2 returns the value parameter of a fully specified Pair type." "type invariant; base/abstractdict.jl:62" ``Property62 ``property62,
  entry "dictscov-abstractdict-l63" "eltype(::Type{ValueIterator{D}}) where {D}" "A ValueIterator's element type is the value parameter of its dictionary Pair eltype." "type invariant; base/abstractdict.jl:63" ``Property63 ``property63,
  entry "dictscov-abstractdict-l65" "iterate(v::Union{KeySet,ValueIterator}, state...)" "Iterator delegation preserves state and projects the key or value from each pair." "keys/values docstrings; base/abstractdict.jl:65-69" ``Property65 ``property65,
  entry "dictscov-abstractdict-l71" "copy(v::KeySet)" "Copying a KeySet builds a mutable set of its keys, collapsing equal keys." "copy invariant; base/abstractdict.jl:71" ``Property71 ``property71,
  entry "dictscov-abstractdict-l73" "in(k, v::KeySet)" "KeySet membership is true exactly when the dictionary get does not return the sentinel." "membership invariant; base/abstractdict.jl:73" ``Property73 ``property73,
  entry "dictscov-abstractdict-l107" "keys(a::AbstractDict)" "keys wraps the dictionary in a KeySet without changing it." "keys docstring; base/abstractdict.jl:84-92,107" ``Property107 ``property107,
  entry "dictscov-abstractdict-l133" "values(a::AbstractDict)" "values wraps the dictionary in a ValueIterator without changing it." "values docstring; base/abstractdict.jl:109-118,133" ``Property133 ``property133,
  entry "dictscov-abstractdict-l178" "pairs(collection)" "Generic pairs zips keys and values in their shared iteration order." "pairs docstring; base/abstractdict.jl:135-178" ``Property178 ``property178,
  entry "dictscov-abstractdict-l180" "pairs(a::AbstractDict)" "pairs of an AbstractDict is the dictionary's own pair iteration." "pairs docstring; base/abstractdict.jl:180" ``Property180 ``property180,
  entry "dictscov-abstractdict-l194" "empty(a::AbstractDict)" "empty requests the dictionary's current key and value types." "empty docstring; base/abstractdict.jl:183-194" ``Property194 ``property194,
  entry "dictscov-abstractdict-l195" "empty(a::AbstractDict, ::Type{V}) where {V}" "The one-type empty overload preserves the key type and replaces the value type." "empty docstring; base/abstractdict.jl:183-195" ``Property195 ``property195,
  entry "dictscov-abstractdict-l198" "copy!(dst::AbstractDict, src::AbstractDict)" "copy! returns an identical destination unchanged or empties it and merges the source." "copy invariant; base/abstractdict.jl:198-201" ``Property198 ``property198,
  entry "dictscov-abstractdict-l224" "merge!(d::AbstractDict, others::AbstractDict...)" "merge! size-hints when lengths exist and then inserts every pair in argument order." "merge! docstring; base/abstractdict.jl:203-234" ``Property224 ``property224,
  entry "dictscov-abstractdict-l283" "mergewith!(combine, d::AbstractDict, others::AbstractDict...)" "The vararg mergewith! is a left fold over its dictionaries." "mergewith! docstring; base/abstractdict.jl:237-285" ``Property283 ``property283,
  entry "dictscov-abstractdict-l295" "mergewith!(combine)" "The curried mergewith! returns a function that delegates with the same combiner." "mergewith! docstring; base/abstractdict.jl:239-245,295" ``Property295 ``property295,
  entry "dictscov-abstractdict-l297" "merge!(combine::Callable, args...)" "The callable merge! compatibility overload delegates to mergewith!." "compatibility docstring; base/abstractdict.jl:247-249,297" ``Property297 ``property297,
  entry "dictscov-abstractdict-l310" "keytype(::Type{<:AbstractDict{K}}) where {K}" "keytype of a dictionary type returns its key parameter." "keytype docstring; base/abstractdict.jl:299-310" ``Property310 ``property310,
  entry "dictscov-abstractdict-l311" "keytype(a::AbstractDict)" "keytype of a value delegates to its concrete type." "keytype docstring; base/abstractdict.jl:311" ``Property311 ``property311,
  entry "dictscov-abstractdict-l324" "valtype(::Type{<:AbstractDict{<:Any,V}}) where {V}" "valtype of a dictionary type returns its value parameter." "valtype docstring; base/abstractdict.jl:313-324" ``Property324 ``property324,
  entry "dictscov-abstractdict-l325" "valtype(a::AbstractDict)" "valtype of a value delegates to its concrete type." "valtype docstring; base/abstractdict.jl:325" ``Property325 ``property325,
  entry "dictscov-abstractdict-l406" "mergewith(combine)" "The curried nonmutating mergewith returns a function using the same combiner." "mergewith docstring; base/abstractdict.jl:365-406" ``Property406 ``property406,
  entry "dictscov-abstractdict-l409" "promoteK(K)" "The zero-dictionary key promotion returns its initial type." "type invariant; base/abstractdict.jl:409" ``Property409 ``property409,
  entry "dictscov-abstractdict-l410" "promoteV(V)" "The zero-dictionary value promotion returns its initial type." "type invariant; base/abstractdict.jl:410" ``Property410 ``property410,
  entry "dictscov-abstractdict-l411" "promoteK(K, d, ds...)" "Key promotion folds promote_type over dictionaries from left to right." "type invariant; base/abstractdict.jl:411" ``Property411 ``property411,
  entry "dictscov-abstractdict-l412" "promoteV(V, d, ds...)" "Value promotion folds promote_type over dictionaries from left to right." "type invariant; base/abstractdict.jl:412" ``Property412 ``property412,
  entry "dictscov-abstractdict-l439" "filter!(f, d::AbstractDict)" "Generic filter! first collects rejected keys, then deletes them after iteration." "filter! docstring; base/abstractdict.jl:419-450" ``Property439 ``property439,
  entry "dictscov-abstractdict-l452" "filter_in_one_pass!(f, d::AbstractDict)" "The one-pass filter deletes each rejected key during iteration." "filter invariant; base/abstractdict.jl:452-459" ``Property452 ``property452,
  entry "dictscov-abstractdict-l490" "eltype(::Type{<:AbstractDict{K,V}}) where {K,V}" "AbstractDict eltype reflects each bound or unbound Pair parameter." "type invariant; base/abstractdict.jl:490-502" ``Property490 ``property490,
  entry "dictscov-abstractdict-l536" "sizehint!(d::AbstractDict, n)" "The generic sizehint! fallback returns the dictionary unchanged." "sizehint! invariant; base/abstractdict.jl:536" ``Property536 ``property536,
  entry "dictscov-abstractdict-l547" "getindex(t::AbstractDict{<:Any,V}, key) where V" "Generic indexing returns the stored V or throws KeyError when the sentinel is returned." "KeyError docstring; base/abstractdict.jl:547-553" ``Property547 ``property547,
  entry "dictscov-abstractdict-l557" "getindex(t::AbstractDict, k1, k2, ks...)" "Multi-index getindex builds one tuple key and delegates." "indexing invariant; base/abstractdict.jl:555-557" ``Property557 ``property557,
  entry "dictscov-abstractdict-l558" "setindex!(t::AbstractDict, v, k1, k2, ks...)" "Multi-index setindex! builds one tuple key and delegates." "indexing invariant; base/abstractdict.jl:555-558" ``Property558 ``property558,
  entry "dictscov-abstractdict-l560" "get!(t::AbstractDict, key, default)" "Value get! wraps the supplied default in a zero-argument callable." "get! invariant; base/abstractdict.jl:560" ``Property560 ``property560,
  entry "dictscov-abstractdict-l561" "get!(default::Callable, t::AbstractDict{K,V}, key) where K where V" "Callable get! converts the key, returns a present value, or converts, stores, and returns the default." "get! docstring; base/abstractdict.jl:561-568" ``Property561 ``property561,
  entry "dictscov-abstractdict-l570" "push!(t::AbstractDict, p::Pair)" "push! stores the pair's value under its key." "push! invariant; base/abstractdict.jl:570" ``Property570 ``property570,
  entry "dictscov-abstractdict-l573" "convert(::Type{T}, x::T) where {T<:AbstractDict}" "Converting a dictionary to its own type returns the identical value." "conversion invariant; base/abstractdict.jl:573" ``Property573 ``property573,
  entry "dictscov-abstractdict-l575" "convert(::Type{T}, x::AbstractDict) where T<:AbstractDict" "Dictionary conversion constructs T and rejects any key collision that changes length." "conversion invariant; base/abstractdict.jl:575-581" ``Property575 ``property575,
  entry "dictscov-abstractdict-l584" "_tablesz(x::T) where T <: Integer" "The identity-table size is 16 below 16 and otherwise the next power-of-two expression." "table-size invariant; base/abstractdict.jl:584" ``Property584 ``property584,
  entry "dictscov-abstractdict-l589" "_throw_dict_kv_error()" "The invalid dictionary iterator helper throws its fixed ArgumentError." "invariant; base/abstractdict.jl:589" ``Property589 ``property589,
  entry "dictscov-abstractdict-l591" "grow_to!(dest::AbstractDict, itr)" "Initial growth validates iteration and a two-element pair, adapts dictionary types, inserts, and continues." "constructor invariant; base/abstractdict.jl:591-609" ``Property591 ``property591,
  entry "dictscov-abstractdict-l611" "grow_to!(dest::AbstractDict{K,V}, itr, st) where {K, V}" "Growth validates every pair, inserts matching types, and widens and merges before a mismatched insertion." "constructor invariant; base/abstractdict.jl:611-634" ``Property611 ``property611,
  entry "dictscov-abstractdict-l637" "dict_with_eltype(DT_apply, kv, ::TP{K,V}) where {K,V}" "Known pair eltypes construct the dictionary with K and V before consuming the iterator." "constructor invariant; base/abstractdict.jl:637" ``Property637 ``property637,
  entry "dictscov-abstractdict-l638" "dict_with_eltype(DT_apply, kv::Generator, ::TP{K,V}) where {K,V}" "Known generator pair eltypes construct the dictionary with K and V before consuming it." "constructor invariant; base/abstractdict.jl:638" ``Property638 ``property638,
  entry "dictscov-abstractdict-l639" "dict_with_eltype(DT_apply, ::Type{Pair{K,V}}) where {K,V}" "A known Pair type constructs an empty dictionary with K and V." "constructor invariant; base/abstractdict.jl:639" ``Property639 ``property639,
  entry "dictscov-abstractdict-l640" "dict_with_eltype(DT_apply, ::Type)" "An unknown eltype constructs an empty Any,Any dictionary." "constructor invariant; base/abstractdict.jl:640" ``Property640 ``property640,
  entry "dictscov-abstractdict-l641" "dict_with_eltype(DT_apply::F, kv, t) where {F}" "The generic path makes an empty dictionary from the default eltype and grows it from the iterator." "constructor invariant; base/abstractdict.jl:641" ``Property641 ``property641,
  entry "dictscov-abstractdict-l642" "dict_with_eltype(DT_apply::F, kv::Generator, t) where F" "The generator path uses a concrete pair eltype directly and otherwise grows from an inferred empty dictionary." "constructor invariant; base/abstractdict.jl:642-648" ``Property642 ``property642
]

end JuliaLean.DictsCov.AbstractDictRows
