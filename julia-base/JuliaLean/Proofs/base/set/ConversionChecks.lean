import JuliaLean.Proofs.base.dict.ImmutableClaims
import JuliaLean.Proofs.base.dict.ProofReach
import JuliaLean.base.set
import JuliaLean.Proofs.base.set.Bugs

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
