import JuliaLean.Proofs.base.dict.Bugs
import JuliaLean.base.dict
import JuliaLean.base.abstractdict

/-!
# `ImmutableDict` and the generic `AbstractDict` comparisons

`ImmutableDict` (`base/dict.jl:776-866`) is a linked list of pairs; setting an
existing key adds a new pair that shadows the old one, and iteration yields
every pair, most recent first. The generic `==`, `isequal` and `hash` of
`base/abstractdict.jl` apply to it unchanged.
-/

namespace JuliaLean.Dicts

variable {K V : Type}



/-- `isequal` is symmetric ("`isequal` is an equivalence relation",
`base/operators.jl:152`) and so is `==` (`base/operators.jl:116`: collections
compare their key sets, then the values for each key), for every key
`isequal` and value comparison that are. -/
def ImmutableDictEqSymmetric : Prop :=
  ∀ (K V : Type) (o : KeyOps K) (veq : V → V → Bool), o.Lawful →
  (∀ a, veq a a = true) → (∀ a b, veq a b = veq b a) →
  ∀ l r : IDict K V, idIsequal idIn idLength o.eq veq l r = idIsequal idIn idLength o.eq veq r l ∧
    idEq idIn idLength o.eq veq l r = idEq idIn idLength o.eq veq r l

/-- `isequal(x, y)` implies `hash(x) == hash(y)` (`hash` docstring,
`base/hashing.jl:14`, `base/operators.jl:134`), for every element hash
consistent with `isequal`. -/
def ImmutableDictHashIsequal : Prop :=
  ∀ (K V : Type) (o : KeyOps K) (visequal : V → V → Bool), o.Lawful →
  ∀ (hk : K → JInt .u64 → JInt .u64) (hv : V → JInt .u64) (hu : JInt .u64 → JInt .u64 → JInt .u64),
    (∀ a b h, o.eq a b = true → hk a h = hk b h) → (∀ a b, visequal a b = true → hv a = hv b) →
  ∀ l r : IDict K V, idIsequal idIn idLength o.eq visequal l r = true → ∀ h, idHash hk hv hu l h = idHash hk hv hu r h

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
