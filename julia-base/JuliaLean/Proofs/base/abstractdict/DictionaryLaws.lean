import JuliaLean.base.abstractdict

namespace JuliaLean.DictsCov
open JuliaLean.Dicts
variable {T D E K V X : Type}
/-! ## Reference semantics -/

/-- `d[k] = v` on a lookup function. -/
def gset (o : KeyOps K) (g : K → Option V) (k : K) (v : V) : K → Option V :=
  fun q => if o.eq q k then some v else g q

/-- `delete!(d, k)` on a lookup function. -/
def gdel (o : KeyOps K) (g : K → Option V) (k : K) : K → Option V :=
  fun q => if o.eq q k then none else g q

/-- The lookup function of a list of distinct pairs. -/
def gOf (o : KeyOps K) (ps : List (K × V)) : K → Option V :=
  fun q => (ps.find? (fun e => o.eq q e.1)).map Prod.snd

/-- A concrete type whose methods behave like a finite map under the key
comparison `o`: lookups agree with the iterated pairs, which are distinct;
`setindex!`/`delete!`/`empty`/`empty!`/`sizehint!` update the lookups and
keep the type. -/
structure DictOps.Lawful (o : KeyOps K) (ops : DictOps T D K V) : Prop where
  get_pairs : ∀ d, ops.get d = gOf o (ops.pairs d)
  distinct : ∀ d, (ops.pairs d).Pairwise (fun a b => o.eq a.1 b.1 = false)
  length : ∀ d, ops.length d = (ops.pairs d).length
  set : ∀ d v k, ∃ d', ops.setindex d v k = .ok d' ∧ ops.get d' = gset o (ops.get d) k v ∧
    ops.typeOf d' = ops.typeOf d
  del : ∀ d k, ∃ d', ops.delete d k = .ok d' ∧ ops.get d' = gdel o (ops.get d) k
  emptyT : ∀ d K V, ops.get (ops.emptyT d K V) = (fun _ => none) ∧
    (ops.typeOf (ops.emptyT d K V)).K = K ∧ (ops.typeOf (ops.emptyT d K V)).V = V
  emptyBang : ∀ d, ∃ d', ops.emptyBang d = .ok d' ∧ ops.get d' = (fun _ => none)
  sizehint : ∀ d n, ops.get (ops.sizehint d n) = ops.get d ∧ ops.typeOf (ops.sizehint d n) = ops.typeOf d

end JuliaLean.DictsCov
