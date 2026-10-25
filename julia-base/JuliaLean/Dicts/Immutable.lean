import JuliaLean.Dicts.Bugs

/-!
# `ImmutableDict` and the generic `AbstractDict` comparisons

`ImmutableDict` (`base/dict.jl:776-866`) is a linked list of pairs; setting an
existing key adds a new pair that shadows the old one, and iteration yields
every pair, most recent first. The generic `==`, `isequal` and `hash` of
`base/abstractdict.jl` apply to it unchanged.
-/

namespace JuliaLean.Dicts

variable {K V : Type}

/-- The chain of an `ImmutableDict`, most recent pair first
(`iterate`, `base/dict.jl:860-863`). -/
abbrev IDict (K V : Type) := List (K × V)

/-- `get(dict::ImmutableDict, key, default)`, `base/dict.jl:843-849`:
`isequal(dict.key, key)` on the chain. -/
def idGet (eq : K → K → Bool) : IDict K V → K → Option V
  | [], _ => none
  | (k, v) :: d, q => if eq k q then some v else idGet eq d q

/-- `in(key_value::Pair, dict::ImmutableDict, valcmp)`, `base/dict.jl:817-826`. -/
def idIn (eq : K → K → Bool) (valcmp : V → V → Bool) : IDict K V → K × V → Bool
  | [], _ => false
  | (k, v) :: d, (q, w) => if eq k q && valcmp w v then true else idIn eq valcmp d (q, w)

/-- `length(t::ImmutableDict) = count(Returns(true), t)`, `base/dict.jl:864`. -/
def idLength (d : IDict K V) : Nat := d.length

/-- The loop `for pair in l; in(pair, r, valcmp) || return false; end`. -/
def idAllIn (eq : K → K → Bool) (valcmp : V → V → Bool) (r : IDict K V) : IDict K V → Bool
  | [] => true
  | p :: l => if idIn eq valcmp r p then idAllIn eq valcmp r l else false

/-- `==(l::AbstractDict, r::AbstractDict)`, `base/abstractdict.jl:518-533`, for two
`ImmutableDict`s (neither is an `IdDict`; values compare to `Bool`). -/
def idEq (eq : K → K → Bool) (veq : V → V → Bool) (l r : IDict K V) : Bool :=
  if idLength l != idLength r then false else idAllIn eq veq r l

/-- `isequal(l::AbstractDict, r::AbstractDict)`, `base/abstractdict.jl:504-516`,
for two distinct `ImmutableDict` objects (`l === r` is false). -/
def idIsequal (eq : K → K → Bool) (visequal : V → V → Bool) (l r : IDict K V) : Bool :=
  if idLength l != idLength r then false else idAllIn eq visequal r l

/-- `xor` of two `UInt64`s. -/
def xor64 (a b : JInt .u64) : JInt .u64 := JInt.wrap .u64 (Int.ofNat (Nat.xor a.val.toNat b.val.toNat))

/-- `hasha_seed`, `base/abstractdict.jl:538`. -/
def hashaSeed : JInt .u64 := JInt.lit .u64 0x6d35bb51952d5539

/-- `hash(a::AbstractDict, h)`, `base/abstractdict.jl:539-545`, with the hash
methods `hk = hash(::K, ::UInt)`, `hv = hash(::V)` and `hu = hash(::UInt, ::UInt)`. -/
def idHash (hk : K → JInt .u64 → JInt .u64) (hv : V → JInt .u64)
    (hu : JInt .u64 → JInt .u64 → JInt .u64) (d : IDict K V) (h : JInt .u64) : JInt .u64 :=
  hu (d.foldl (fun acc kv => xor64 acc (hk kv.1 (hv kv.2))) hashaSeed) h

/-- `isequal` is symmetric ("`isequal` is an equivalence relation",
`base/operators.jl:152`) and so is `==` (`base/operators.jl:116`: collections
compare their key sets, then the values for each key), for every key
`isequal` and value comparison that are. -/
def ImmutableDictEqSymmetric : Prop :=
  ∀ (K V : Type) (o : KeyOps K) (veq : V → V → Bool), o.Lawful →
  (∀ a, veq a a = true) → (∀ a b, veq a b = veq b a) →
  ∀ l r : IDict K V, idIsequal o.eq veq l r = idIsequal o.eq veq r l ∧
    idEq o.eq veq l r = idEq o.eq veq r l

/-- `isequal(x, y)` implies `hash(x) == hash(y)` (`hash` docstring,
`base/hashing.jl:14`, `base/operators.jl:134`), for every element hash
consistent with `isequal`. -/
def ImmutableDictHashIsequal : Prop :=
  ∀ (K V : Type) (o : KeyOps K) (visequal : V → V → Bool), o.Lawful →
  ∀ (hk : K → JInt .u64 → JInt .u64) (hv : V → JInt .u64) (hu : JInt .u64 → JInt .u64 → JInt .u64),
    (∀ a b h, o.eq a b = true → hk a h = hk b h) → (∀ a b, visequal a b = true → hv a = hv b) →
  ∀ l r : IDict K V, idIsequal o.eq visequal l r = true → ∀ h, idHash hk hv hu l h = idHash hk hv hu r h

/-- `X = ImmutableDict(:a => 1, :a => 1)` and `Y = ImmutableDict(:a => 1, :b => 2)`
(keys `:a = 0`, `:b = 1`): `isequal(X, Y)` and `X == Y`, but not `Y == X`. -/
theorem immutableDictEqSymmetric_refuted : ¬ ImmutableDictEqSymmetric := by
  intro h
  have hp := h Nat Nat natOps (fun a b => a == b) natOps_lawful (by intro a; simp)
    (by intro a b; exact Bool.beq_comm) [(0, 1), (0, 1)] [(1, 2), (0, 1)]
  revert hp
  decide

/-- `A = ImmutableDict(:b => 2, :a => 1, :a => 1)` and
`B = ImmutableDict(:a => 1, :b => 2, :b => 2)` are `isequal` but their hashes
differ: the duplicate pairs cancel in the `xor`. -/
theorem immutableDictHashIsequal_refuted : ¬ ImmutableDictHashIsequal := by
  intro h
  have hp := h Nat Nat natOps (fun a b => a == b) natOps_lawful
    (fun k x => JInt.wrap .u64 (k * 1000 + x.val)) (fun v => JInt.wrap .u64 v) (fun x _ => x)
    (by intro a b x hab; simp [natOps] at hab; rw [hab]) (by intro a b hab; simp at hab; rw [hab])
    [(0, 1), (0, 1), (1, 2)] [(1, 2), (1, 2), (0, 1)] (by decide) (JInt.lit .u64 0)
  revert hp
  decide

/-! ## `PersistentDict` against `Dict`

`PersistentDict` "behaves like an IdDict" (`base/dict.jl:945-946`): its
lookups compare keys with `===` (`KeyValue.get`, `base/dict.jl:1033-1045`).
The generic `==` returns `false` when exactly one argument is an `IdDict`
(`base/abstractdict.jl:519-521`) but has no such case for `PersistentDict`. -/

/-- The two keys `1` and `1.0`: `isequal` but not `===`. -/
inductive OneKey where
  | int | float
  deriving DecidableEq

/-- `in(key_val::Pair{K,V}, dict::PersistentDict{K,V})`, `base/dict.jl:1010-1015`:
the pair whose key is `===` to the query. -/
def pdIn {V : Type} (valcmp : V → V → Bool) (pairs : List (OneKey × V)) (kv : OneKey × V) : Bool :=
  match pairs.find? (fun e => decide (e.1 = kv.1)) with
  | some (_, v) => valcmp kv.2 v
  | none => false

/-- `in(p::Pair, a::AbstractDict)` on a `Dict{Any}`, `base/abstractdict.jl:21-27`:
`get` compares keys with `isequal`, under which `1` and `1.0` are one key. -/
def dictAnyIn {V : Type} (valcmp : V → V → Bool) (pairs : List (OneKey × V)) (kv : OneKey × V) : Bool :=
  match pairs.head? with
  | some (_, v) => valcmp v kv.2
  | none => false

/-- The generic `==`, `base/abstractdict.jl:518-533`, given each side's iteration,
`IdDict` test and `in`. -/
def genericDictEq {V : Type} (lpairs : List (OneKey × V)) (lId : Bool)
    (rpairs : List (OneKey × V)) (rId : Bool) (rIn : OneKey × V → Bool) : Bool :=
  if lId != rId then false
  else if lpairs.length != rpairs.length then false
  else lpairs.all rIn

/-- `==` between a `PersistentDict{Any}` and a `Dict{Any}` with at most one key
each is symmetric. -/
def PersistentDictEqSymmetric : Prop :=
  ∀ (V : Type) (veq : V → V → Bool), (∀ a b, veq a b = veq b a) →
  ∀ (pd d : List (OneKey × V)), pd.length ≤ 1 → d.length ≤ 1 →
    genericDictEq pd false d false (dictAnyIn veq d) = genericDictEq d false pd false (pdIn veq pd)

/-- `PersistentDict{Any,Int}(1 => 1) == Dict{Any,Int}(1.0 => 1)` but not the reverse. -/
theorem persistentDictEqSymmetric_refuted : ¬ PersistentDictEqSymmetric := by
  intro h
  have hp := h Nat (fun a b => a == b) (by intro a b; exact Bool.beq_comm)
    [(.int, 1)] [(.float, 1)] (by decide) (by decide)
  revert hp
  decide

/-! ## Converting an `ImmutableDict` to a `Dict`

`iterate(::ImmutableDict)` "actually defines reverse iteration (e.g. it should
not be used for merge/copy/filter type operations)" (`base/dict.jl:859`), yet
`Dict(kv)` and `merge!` consume it: the oldest shadowed pair is stored last. -/

/-- `Dict{K,V}(kv)`, `base/dict.jl:91-98`: `sizehint!(h, length(kv))`, then
`h[k] = v` for each pair in iteration order. -/
def dictOfPairs {K V : Type} (o : KeyOps K) (kv : List (K × V)) : DR (Table K V) := do
  let h ← sizehint o Table.empty (JInt.lit .i64 kv.length) true
  kv.foldlM (fun h p => setindex o h p.2 p.1) h

/-- `Dict(d)` for an `ImmutableDict` `d` maps every key to `d[key]`. -/
def ImmutableDictToDict : Prop :=
  ∀ (K V : Type) (o : KeyOps K), o.Lawful → ∀ d : IDict K V, d.length ≤ 2 ^ 30 →
    ∀ q, (do let h ← dictOfPairs o d; dictGet o h q) = .ok (idGet o.eq d q)

/-- `Dict(ImmutableDict(:a => 1, :a => 2))` maps `:a` to `1`, although `d[:a] == 2`. -/
theorem immutableDictToDict_refuted : ¬ ImmutableDictToDict := by
  intro h
  have hp := congrArg (fun r : DR (Option Nat) => match r with | .ok v => v | .error _ => none)
    (h Nat Nat natOps natOps_lawful [(0, 2), (0, 1)] (by decide) 0)
  revert hp
  decide +kernel

/-! ## `in(pair, ::ImmutableDict)` with a `missing` comparison -/

/-- `in(key_value::Pair, dict::ImmutableDict, valcmp)`, `base/dict.jl:817-826`,
with a three-valued `valcmp` (`none` is `missing`): `valcmp(value, dict.value)
&& return true` throws `TypeError` on `missing`. The result is `in`'s value,
`some b` or `missing`. -/
def idIn3 {K V : Type} (eq : K → K → Bool) (valcmp : V → V → Option Bool) :
    IDict K V → K × V → Except String (Option Bool)
  | [], _ => .ok (some false)
  | (k, v) :: d, (q, w) =>
    if eq k q then
      match valcmp w v with
      | some true => .ok (some true)
      | some false => idIn3 eq valcmp d (q, w)
      | none => .error "TypeError: non-boolean (Missing) used in boolean context"
    else idIn3 eq valcmp d (q, w)

/-- `in(pair, d)` with `valcmp = (==)` follows three-valued logic like
`in(p::Pair, a::AbstractDict)` (`base/abstractdict.jl:21-27`, which returns
`valcmp(v, p.second)`), so that `==` on collections can return `missing`
(`base/operators.jl:126-127`): it never throws. -/
def ImmutableDictInMissing : Prop :=
  ∀ (K V : Type) (o : KeyOps K) (valcmp : V → V → Option Bool), o.Lawful →
  ∀ (d : IDict K V) (p : K × V), okB (idIn3 o.eq valcmp d p) = true

/-- `==` on `Union{Int, Missing}` values: `missing` if either side is. -/
def eqMissing : Option Nat → Option Nat → Option Bool
  | some x, some y => some (x == y)
  | _, _ => none

/-- `(:a => missing) in ImmutableDict(:a => 1)` throws `TypeError`. -/
theorem immutableDictInMissing_refuted : ¬ ImmutableDictInMissing := by
  intro h
  have hp := h Nat (Option Nat) natOps eqMissing natOps_lawful [(0, some 1)] (0, none)
  revert hp
  decide

end JuliaLean.Dicts
