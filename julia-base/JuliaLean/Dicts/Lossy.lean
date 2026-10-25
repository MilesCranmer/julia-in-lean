import JuliaLean.Dicts.Immutable

/-!
# Key conversions that skip the `isequal` check

`setindex!(h::Dict{K,V}, v0, key0)` (`base/dict.jl:347-357`) converts a key of
another type and throws `KeyTypeError` unless `isequal(convert(K, key0), key0)`.
Two other ways of storing a key convert without that check:

* `replace!(new, ::Dict)` and `replace!(new, ::Set)` (`base/set.jl:980-1019`)
  collect the replacement pairs in a `Vector{Pair{K,V}}`, which converts them;
* `ImmutableDict{K,V}(parent, key, value) = new(parent, key, value)`
  (`base/dict.jl:782`) converts the key field, reached from
  `ImmutableDict(d, key => value)` and `Base.setindex(d, value, key)`.
-/

namespace JuliaLean.Dicts

variable {K Q V : Type}

/-! ## `replace!(new, ::Dict)` -/

/-- The loop of `_replace!(new, t::Dict{K,V}, A, count)`, `base/set.jl:986-1005`.
`new k v` is `new(Pair{K,V}(k, v))`: `none` when it returns its argument
(`x1 === x2`), otherwise the new pair, whose key has type `Q`. `fuel` bounds the
slot scan (`skip_deleted` strictly increases `i`). -/
def replaceLoop (c : Conv Q K) (new : K → V → Option (Q × V)) (count : Nat) :
    Nat → Table K V → Nat → Nat → List (K × V) → DR (Table K V × List (K × V))
  | 0, _, _, _, _ => throw .diverges
  | fuel + 1, t, i, cnt, news =>
    -- `while i != 0`
    if i == 0 then pure (t, news) else do
    let (k1, v1) ← entryAt t i
    let (t, cnt, news, stop) ← match new k1 v1 with
      | none => pure (t, cnt, news, false)
      | some (k2, v2) => do
        let (t, news) ←
          -- `if isequal(k1, k2)`: overwrite in place; `t.keys[i] = k2` converts
          if c.iseq k2 k1 then do
            let k ← c.convert k2
            pure ({ t with keys := upd t.keys i (some k), vals := upd t.vals i (some v2),
                           age := bump t.age }, news)
          -- `_delete!(t, i); push!(news, x2)`: `push!` into `Pair{K,V}[]` converts
          else do
            let t := deleteAt t i
            let k ← c.convert k2
            pure (t, news ++ [(k, v2)])
        -- `c += 1; c == count && break`
        pure (t, cnt + 1, news, cnt + 1 == count)
    if stop then pure (t, news) else
    -- `i = i == typemax(Int) ? 0 : skip_deleted(t, i+1)`
    let i := if i == 2 ^ 63 - 1 then 0 else skipDeleted t (i + 1)
    replaceLoop c new count fuel t i cnt news

/-- `_replace!(new, t::Dict{K,V}, A::AbstractDict, count)`, `base/set.jl:980-1010`:
`count == 0 && return t`; `i = skip_deleted_floor!(t)`; the loop; then
`push!(t, n)` (a `Pair{K,V}`, so no further conversion) for every collected pair. -/
def replaceDict (o : KeyOps K) (c : Conv Q K) (new : K → V → Option (Q × V))
    (t : Table K V) (count : Nat) : DR (Table K V) := do
  if count == 0 then return t
  -- `skip_deleted_floor!`, `base/dict.jl:698-704`
  let i := skipDeleted t t.idxfloor
  let t := if i != 0 then { t with idxfloor := i } else t
  let (t, news) ← replaceLoop c new count (t.size + 1) t i 0 []
  news.foldlM (fun t kv => setindex o t kv.2 kv.1) t

/-- `haskey(t, q)` for a key of type `Q` (`base/dict.jl:553`). -/
def haskeyConv (c : Conv Q K) (t : Table K V) (q : Q) : DR Bool := do
  let index ← htKeyindex t (c.hash q) (c.iseq q)
  pure (index ≥ 0)

/-- `replace!(new, d)` (docstring `base/set.jl:776-780`, "Replace each element
`x` in collection `A` by `new(x)`"): when the call returns, the key of every
replacement pair is a key of `d`. -/
def ReplaceKeepsReplacements : Prop :=
  ∀ (K Q V : Type) (o : KeyOps K) (c : Conv Q K), o.Lawful → ConvLawful o c → GenericMax o →
  ∀ (t : Table K V) m, Reach o t m → ∀ (new : K → V → Option (Q × V)) t',
    replaceDict o c new t (2 ^ 63 - 1) = .ok t' →
    ∀ e ∈ m, ∀ q w, new e.1 e.2 = some (q, w) → haskeyConv c t' q = .ok true

/-- `d = Dict{Float32,Int}(2 => 5)` (in the model, `roundConv` rounds to even). -/
def opsReplace : List (DOp Nat Nat) := [.base (.set 2 5)]

/-- `p -> 0.1 => 7` (`1` here: odd, so not representable). -/
def newReplace : Nat → Nat → Option (Nat × Nat) := fun _ _ => some (1, 7)

theorem replaceKeepsReplacements_refuted : ¬ ReplaceKeepsReplacements := by
  intro h
  have hr := reach_of_ok natOps opsReplace ⟨by decide, by decide⟩ (by decide +kernel)
    (by decide +kernel)
  have hok : okB (replaceDict natOps roundConv newReplace
      (getOkD (runOps natOps opsReplace) Table.empty) (2 ^ 63 - 1)) = true := by decide +kernel
  have hm : ((2, 5) : Nat × Nat) ∈ getOkD (rrun natOps opsReplace) [] := by decide +kernel
  have hk := h Nat Nat Nat natOps roundConv natOps_lawful roundConv_lawful natOps_generic _ _ hr
    newReplace (getOkD (replaceDict natOps roundConv newReplace
      (getOkD (runOps natOps opsReplace) Table.empty) (2 ^ 63 - 1)) Table.empty)
    (eq_ok_of_okB _ _ hok) _ hm 1 7 rfl
  have hf : okB (haskeyConv roundConv (getOkD (replaceDict natOps roundConv newReplace
      (getOkD (runOps natOps opsReplace) Table.empty) (2 ^ 63 - 1)) Table.empty) 1 >>= fun b =>
        if b then throw .argumentError else pure ()) = true := by decide +kernel
  rw [hk] at hf
  simp [okB, bind, Except.bind] at hf

/-! ## `ImmutableDict(d, key => value)` and `Base.setindex(d, value, key)` -/

/-- `ImmutableDict{K,V}(parent, key, value) = new(parent, key, value)`
(`base/dict.jl:782`): `new` converts the key field with `convert(K, key)`.
`ImmutableDict(t, KV::Pair)` (`base/dict.jl:812`) and `setindex(d, value, key)`
(`base/dict.jl:886-888`) call it. -/
def idSetConv (c : Conv Q K) (d : IDict K V) (key : Q) (value : V) : DR (IDict K V) := do
  let k ← c.convert key
  pure ((k, value) :: d)

/-- `get(dict::ImmutableDict, key, default)` for a key of type `Q`,
`base/dict.jl:843-849`. -/
def idGetConv (c : Conv Q K) : IDict K V → Q → Option V
  | [], _ => none
  | (k, v) :: d, q => if c.iseq q k then some v else idGetConv c d q

/-- After `d2 = ImmutableDict(d, key => value)`, `d2[key] == value`: the
`ImmutableDict` docstring (`base/dict.jl:790-792`, "Calling `getindex` will
return the most recent value for a particular key") and the `setindex`
docstring (`base/dict.jl:871-872`, "with the most recent value of the key `key`
set to `value`"). -/
def ImmutableDictSetGet : Prop :=
  ∀ (K Q V : Type) (o : KeyOps K) (c : Conv Q K), o.Lawful → ConvLawful o c →
  ∀ (d : IDict K V) (q : Q) (v : V) d', idSetConv c d q v = .ok d' → idGetConv c d' q = some v

theorem immutableDictSetGet_refuted : ¬ ImmutableDictSetGet := by
  intro h
  have hk := h Nat Nat Nat natOps roundConv natOps_lawful roundConv_lawful [] 1 1 [(0, 1)] rfl
  revert hk
  decide

end JuliaLean.Dicts
