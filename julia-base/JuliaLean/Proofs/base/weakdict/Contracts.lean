import JuliaLean.base.weakdict
import JuliaLean.Proofs.base.weakdict.OperationHistories

namespace JuliaLean.IdDicts
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
