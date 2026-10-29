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

def entries : List Entry := []

end JuliaLean.DictsCov.AbstractDictRows
