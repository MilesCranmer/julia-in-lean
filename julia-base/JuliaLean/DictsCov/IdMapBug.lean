import JuliaLean.DictsCov.EqTable

/-!
# `map!(f, values(d))` and `mergewith!(f, d, d)` on an `IdDict`

Both generic methods (`base/abstractdict.jl:673-681`, `288-293`) assign
`d[key] = ...` while iterating `d`. `setindex!(::IdDict)` rehashes when
`d.ndel >= 3*length(d.ht)>>2` (`base/iddict.jl:84-87`), which moves the pairs
not yet visited.
-/

namespace JuliaLean.DictsCov

open EqTable

/-- `map!(f, values(d))` replaces every value `v` of `d` by `f(v)` (docstring
`base/abstractdict.jl:653`), and `mergewith!(+, d, d)` doubles every value
(docstring `base/abstractdict.jl:243-244`), for every `IdDict{Int,Int}` built
by `setindex!`/`delete!` and every `objectid`. -/
def IdDictMapOnce : Prop :=
  ∀ (keyhash : Int → Nat) (ops : List Op) (f : Int → Int) (k v : Int),
    (k, v) ∈ pairsOf (run keyhash ops) →
    (mapValues keyhash f ((run keyhash ops).ht.length + 1) (run keyhash ops) 0).get keyhash k =
        some (f v) ∧
      (mergewithSelf keyhash (· + ·) ((run keyhash ops).ht.length + 1) (run keyhash ops) 0).get
        keyhash k = some (v + v)

/-- `objectid` on the keys of the reproducer: `2`, `11` and `25` fall in pair
slot 0 of the 16-slot table (as `objectid(k) & 15 == 0` in Julia); the junk
keys `-1, ..., -23` anywhere else. -/
def exHash (k : Int) : Nat := if k = 2 ∨ k = 11 ∨ k = 25 then 0 else k.natAbs % 16

/-- `d[2] = 0; d[11] = 1; d[25] = 2; delete!(d, 2)`, then 23 insert/delete
pairs of junk keys: `ndel = 24 = 3*32>>2`. -/
def exOps : List Op :=
  [.set 2 0, .set 11 1, .set 25 2, .del 2] ++
    (List.range 23).flatMap (fun j => [.set (-((j : Int) + 1)) 0, .del (-((j : Int) + 1))])

theorem ex_ndel : (run exHash exOps).ndel = 24 := by decide +kernel

theorem ex_pairs : pairsOf (run exHash exOps) = [(11, 1), (25, 2)] := by decide +kernel

theorem ex_map : (mapValues exHash (· + 10) ((run exHash exOps).ht.length + 1)
    (run exHash exOps) 0).get exHash 25 = some 2 := by decide +kernel

theorem ex_merge : (mergewithSelf exHash (· + ·) ((run exHash exOps).ht.length + 1)
    (run exHash exOps) 0).get exHash 25 = some 2 := by decide +kernel

theorem idDictMapOnce_refuted : ¬ IdDictMapOnce := by
  intro h
  have h1 := (h exHash exOps (· + 10) 25 2 (by rw [ex_pairs]; decide)).1
  rw [ex_map] at h1
  exact absurd h1 (by decide)

end JuliaLean.DictsCov
