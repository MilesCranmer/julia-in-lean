import JuliaLean.base.iddict
import JuliaLean.Proofs.base.iddict.OperationHistories

/-!
# Properties of the identity collections
-/

namespace JuliaLean.IdDicts

/-! ## `IdDict` -/

/-- Call sequences of `setindex!`, `delete!`, `pop!`, `empty!` and
`sizehint!` move an `IdDict{K,V}` exactly like a reference `===` map with the
documented type rules: `get(d, q, default)` returns the reference value or
`default`, `length` is the number of reference keys, and iteration yields
pairs with pairwise non-`===` keys and the reference lookups. -/
def IdDictOpsAgree : Prop :=
  ∀ (K V : JTy) (ops : List DOp), (∀ op ∈ ops, op.mutator = true) →
    let d := runD K V ops
    let m := refD K V ops
    (∀ q dflt, d.get q dflt = .ok ((rLookup m q).getD dflt)) ∧
    d.length = m.length ∧
    ∃ t, d.iterate = .ok t ∧ keysDistinct t ∧ (∀ q, rLookup t q = rLookup m q)

/-- For every call sequence (including `get!` and `pop!` on stored
sentinels), `length(d)` equals the number of pairs iteration yields, the
yielded keys are pairwise non-`===`, and iteration does not throw. -/
def IdDictLengthLive : Prop :=
  ∀ (K V : JTy) (ops : List DOp),
    let d := runD K V ops
    ∃ t, d.iterate = .ok t ∧ d.length = t.length ∧ keysDistinct t

/-- `get!(d, k, default)` on an absent key of type `K` whose default converts
to `w`: stores `k => w`, returns `w`, and grows `length` by one. -/
def IdDictGetBangAbsent : Prop :=
  ∀ (K V : JTy) (ops : List DOp) (k dflt w : JVal),
    let d := runD K V ops
    rLookup d.ht k = none → isa k K = true → convert V dflt = .ok w →
    let r := d.getBang k dflt
    r.2 = .ok w ∧ r.1.get k token = .ok w ∧ r.1.length = d.length + 1

/-- `haskey(d, k)` is true and `d[k]` returns the stored value for every key
present in the dictionary (iteration yields `k => v`). -/
def LookupFindsPresent : Prop :=
  ∀ (K V : JTy) (ops : List DOp) (k v : JVal),
    let d := runD K V ops
    (∃ t, d.iterate = .ok t ∧ rLookup t k = some v) →
    d.haskey k = .ok true ∧ d.getindex k = .ok v

/-- `pop!(d, k)` returns the stored value of a present key. -/
def PopReturnsPresent : Prop :=
  ∀ (K V : JTy) (ops : List DOp) (k v : JVal),
    let d := runD K V ops
    (∃ t, d.iterate = .ok t ∧ rLookup t k = some v) →
    (d.pop k).2 = .ok v

/-- `get!(d, k, default)` on a present key returns the stored value and
leaves the dictionary's contents unchanged. -/
def GetBangKeepsPresent : Prop :=
  ∀ (K V : JTy) (ops : List DOp) (k v dflt : JVal),
    let d := runD K V ops
    (∃ t, d.iterate = .ok t ∧ rLookup t k = some v) →
    let r := d.getBang k dflt
    r.2 = .ok v ∧ r.1.iterate = d.iterate



end JuliaLean.IdDicts
