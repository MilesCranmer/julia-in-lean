import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.IdDicts.Value
import JuliaLean.IdDicts.IdDict
import JuliaLean.IdDicts.IdSet
import JuliaLean.IdDicts.Weak
import JuliaLean.IdDicts.Props
import JuliaLean.IdDicts.ProofTable
import JuliaLean.IdDicts.ProofIdDict
import JuliaLean.IdDicts.ProofIdSet
import JuliaLean.IdDicts.Refutations

namespace JuliaLean.IdDicts

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  -- proven
  -- refuted
  { id := "iddicts-weakkeydict-length", juliaFile := "base/weakdict.jl"
    juliaFns := ["setindex!(::WeakKeyDict, v, k)", "length(::WeakKeyDict)", "iterate(::WeakKeyDict)"]
    statement := "After any realistic sequence of setindex!, delete! and garbage collections, length(wkh) equals the number of pairs iteration yields."
    source := "invariant; WeakKeyDict docstring base/weakdict.jl:14-16; length base/weakdict.jl:190-195", status := .refuted
    prop := ``WeakKeyLengthLive, thm := some ``weakKeyLengthLive_refuted
    issue := "related #24721 (closed); none found (queries: WeakKeyDict finalizer, WeakKeyDict length, WeakKeyDict isequal key, WeakKeyDict replace key, WeakKeyDict dirty, WeakKeyDict stale entry)"
    notes := "Re-setting an isequal key retargets the WeakRef without registering a finalizer (base/weakdict.jl:97-103); once the new key is collected, length counts a dead entry. 1.13.2 has the same code in base/weakkeydict.jl. P2." },
  { id := "iddicts-weakvalue-eltype", juliaFile := "base/weakdict.jl"
    juliaFns := ["setindex!(::WeakValueIdDict, v, k)", "getindex(::WeakValueIdDict, k)", "get(::WeakValueIdDict, k, default)", "get!(::WeakValueIdDict, k, default)"]
    statement := "After h[k] = v succeeds on a WeakValueIdDict{K,V}(), h[k], get(h, k, default) and get!(h, k, default) do not throw TypeError."
    source := "WeakValueIdDict docstring base/weakdict.jl:227 (like IdDict); IdDict setindex! converts values base/iddict.jl:81-83", status := .refuted
    prop := ``WeakValueReadsTyped, thm := some ``weakValueReadsTyped_refuted
    issue := "related #62831 (merged, adds the type); none found (queries: WeakValueIdDict, WeakValueIdDict TypeError, weak value dict convert)"
    notes := "Master only (the type is not in 1.13.2). WeakValueIdDict{Any,Vector{Int}}()[:k] = [1.0] is accepted; every read throws TypeError. P2." }
]

end JuliaLean.IdDicts
