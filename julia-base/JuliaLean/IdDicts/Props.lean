import JuliaLean.IdDicts.IdDict
import JuliaLean.IdDicts.IdSet
import JuliaLean.IdDicts.Weak

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

/-! ## `IdSet` -/

/-- Call sequences on an `IdSet{Any}` (with fewer than `2^62` mentioned
elements, so `union!`'s `max_values` exit cannot fire) agree with a reference
`===` set: iteration yields the reference elements, each once, in insertion
order, `length` is their number, and no internal `@assert` fails. -/
def IdSetOpsAgree : Prop :=
  ∀ ops : List SOp, (ops.map SOp.size).sum < 2 ^ 62 →
    let s := runS .any ops
    s.iterate = .ok (refS ops) ∧ s.length = (refS ops).length ∧ (refS ops).Nodup ∧
    ∀ x, s.mem x = decide (x ∈ refS ops)

/-- Every element of an `IdSet{T}` has type `T`, so iteration (`collect`)
never throws. -/
def IdSetElemsHaveEltype : Prop :=
  ∀ (T : JTy) (ops : List SOp), ∃ xs, (runS T ops).iterate = .ok xs

/-- `symdiff!(s, itr)` on an `IdSet{Any}`: `x` is in the result exactly when
it is in `s` or `===` an element of `itr`, but not both. -/
def IdSetSymdiffIdentity : Prop :=
  ∀ (ops : List SOp) (itr : List JVal) (x : JVal),
    let s := runS .any ops
    (s.symdiffVec itr).mem x = (s.mem x != decide (x ∈ itr))

/-- `issetequal(a, b) == (a ⊆ b && b ⊆ a)` for an `IdSet{Any}` `a` and a
vector `b`, in both argument orders. -/
def IdSetIssetequalSubsets : Prop :=
  ∀ (ops : List SOp) (b : List JVal),
    let a := Coll.ids (runS .any ops)
    issetequal a (.vec b) = (issubset a (.vec b) && issubset (.vec b) a) ∧
    issetequal (.vec b) a = (issubset (.vec b) a && issubset a (.vec b))

/-- `issubset(a, b) == all(x -> x in b, a)` for an `IdSet{Any}` `a` and a
`Set` or vector `b`. -/
def IdSetIssubsetIn : Prop :=
  ∀ (ops : List SOp) (b : List JVal),
    let a := Coll.ids (runS .any ops)
    issubset a (.set (jsetOf b)) = a.elems.all (Coll.set (jsetOf b)).mem ∧
    issubset a (.vec b) = a.elems.all (Coll.vec b).mem

/-! ## `WeakKeyDict` and `WeakValueIdDict` -/

/-- After any realistic sequence of `setindex!`, `delete!` and garbage
collections, `length(wkh)` equals the number of pairs iteration yields. -/
def WeakKeyLengthLive : Prop :=
  ∀ (K : JTy) (ops : List WOp), Realistic ops → NoValueFreed ops →
    let w := runW K ops
    (w.length).2 = .ok (w.length).1.iterate.length

/-- After `h[k] = v` succeeds on a `WeakValueIdDict{K,V}()`, `h[k]`,
`get(h, k, default)` and `get!(h, k, default)` do not throw `TypeError`. -/
def WeakValueReadsTyped : Prop :=
  ∀ (K V : JTy) (k v dflt : JVal),
    let r := (WVID.new K V).setindex v k
    r.2 = .ok () →
    r.1.getindex k ≠ .error .typeError ∧ r.1.get k dflt ≠ .error .typeError ∧
    (r.1.getBang k dflt).2 ≠ .error .typeError

end JuliaLean.IdDicts
