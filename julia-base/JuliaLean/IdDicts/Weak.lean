import JuliaLean.IdDicts.IdDict

/-!
# `WeakKeyDict` and `WeakValueIdDict`, base/weakdict.jl (master `bbfa0ce4150`)

`WeakKeyDict{K,V}` wraps `ht::Dict{WeakRef,V}`. A `Dict` key `WeakRef` hashes
and compares through its referent (`hash(w::WeakRef, h) = hash(w.value, h)`,
`isequal(w::WeakRef, v) = isequal(w.value, v)`, base/hashing.jl and
base/gcutils.jl), so the inner table is an `isequal`-keyed map from referents;
a collected referent is `nothing` and matches no key. The model keeps, per
entry, the referent (`none` once collected) and the value.

Garbage collection is an explicit event `gc dead`: every referent in `dead`
becomes `nothing`, and every object in `dead` with a pending finalizer runs
it (`WeakKeyDictFinalizer` sets `dirty`, base/weakdict.jl:8). The values
(`V` is `Any` in this model) are held strongly, so a realistic `dead` list
holds no stored value.

`WeakValueIdDict{K,V}` (master only) wraps `ht::IdDict{K,WeakRef}`. Its
properties here are about type checks, so its values are all alive and the
inner `IdDict{K,WeakRef}` is the eqtable map of `JuliaLean.IdDicts.IdDict`
holding the referents.
-/

namespace JuliaLean.IdDicts

/-! ## `WeakKeyDict{K,Any}` -/

structure WKD where
  K : JTy
  /-- inner `Dict{WeakRef,V}`: (referent or collected, value), insertion order -/
  ht : List (Option JVal × JVal)
  /-- objects on which `finalizer(wkh.finalizer, key)` is pending -/
  fins : List JVal
  dirty : Bool

def WKD.new (K : JTy) : WKD := ⟨K, [], [], false⟩

/-- `_cleanup_locked(h)`, base/weakdict.jl:65-77. -/
def WKD.cleanup (w : WKD) : WKD :=
  if w.dirty then { w with dirty := false, ht := w.ht.filter fun e => e.1.isSome } else w

/-- Inner-`Dict` key match of a lookup key against a stored `WeakRef`. -/
def wrMatch (key : JVal) (e : Option JVal × JVal) : Bool :=
  match e.1 with
  | some y => isequal y key
  | none => false

/-- `setindex!(wkh, v, key)`, base/weakdict.jl:90-107. -/
def WKD.setindex (w : WKD) (v key : JVal) : Out WKD Unit :=
  if !isa key w.K then (w, .error .argumentError)
  else if key == .nothing then (w, .error .argumentError)
  else
    let w := w.cleanup
    -- `k = getkey(wkh.ht, key, nothing)`
    if w.ht.any (wrMatch key) then
      -- `k.value = key; wkh.ht[k] = v`
      ({ w with ht := w.ht.map fun e => if wrMatch key e then (some key, v) else e }, .ok ())
    else if !finalizable key then (w, .error .errorException)
    else
      -- `finalizer(wkh.finalizer, key); k = WeakRef(key); wkh.ht[k] = v`
      ({ w with fins := key :: w.fins, ht := w.ht ++ [(some key, v)] }, .ok ())

/-- `delete!(wkh, key)`, base/weakdict.jl:164-170. -/
def WKD.delete (w : WKD) (key : JVal) : WKD :=
  if key == .nothing then w else
  match w.ht.findIdx? (wrMatch key) with
  | some i => { w with ht := w.ht.eraseIdx i }
  | none => w

/-- `haskey(wkh, key)`, base/weakdict.jl:177-182. -/
def WKD.haskey (w : WKD) (key : JVal) : Bool := key != .nothing && w.ht.any (wrMatch key)

/-- `length(t)`, base/weakdict.jl:190-195: sweeps when dirty. -/
def WKD.length (w : WKD) : Out WKD Nat := let w := w.cleanup; (w, .ok w.ht.length)

/-- `iterate(t)` to exhaustion, base/weakdict.jl:197-210: entries whose key
was collected are skipped. -/
def WKD.iterate (w : WKD) : List (JVal × JVal) :=
  w.ht.filterMap fun e => e.1.map fun k => (k, e.2)

/-- A garbage collection that frees the objects `dead`. -/
def WKD.gc (w : WKD) (dead : List JVal) : WKD :=
  let ran := w.fins.any (· ∈ dead)
  { w with
    ht := w.ht.map fun e => (e.1.bind fun k => if k ∈ dead then none else some k, e.2)
    fins := w.fins.filter (· ∉ dead)
    dirty := w.dirty || ran }

inductive WOp where
  | set (k v : JVal)
  | delete (k : JVal)
  | gc (dead : List JVal)

def WOp.run (w : WKD) : WOp → WKD
  | .set k v => (w.setindex v k).1
  | .delete k => w.delete k
  | .gc dead => w.gc dead

def runW (K : JTy) (ops : List WOp) : WKD := ops.foldl WOp.run (WKD.new K)

/-- Values and keys a call mentions. -/
def WOp.mentions : WOp → List JVal
  | .set k v => [k, v]
  | .delete k => [k]
  | .gc _ => []

/-- A call sequence a program can produce: a collection frees only mutable
objects, never a value stored in the dictionary (values are strong
references; this is approximated by: never a value of any `set`), and a freed
object is not used by a later call. -/
def Realistic : List WOp → Prop
  | [] => True
  | .gc dead :: rest =>
      (∀ x ∈ dead, finalizable x = true) ∧
      (∀ x ∈ dead, ∀ op ∈ rest, x ∉ op.mentions) ∧ Realistic rest
  | _ :: rest => Realistic rest

/-- `dead` contains no value stored by any `set` of the sequence. -/
def NoValueFreed (ops : List WOp) : Prop :=
  ∀ op ∈ ops, ∀ dead, op = .gc dead → ∀ op' ∈ ops, ∀ k v, op' = .set k v → v ∉ dead

/-! ## `WeakValueIdDict{K,V}` -/

structure WVID where
  K : JTy
  V : JTy
  /-- inner `IdDict{K,WeakRef}`: keys and live referents -/
  ht : Tab
  dirty : Bool

def WVID.new (K V : JTy) : WVID := ⟨K, V, [], false⟩

/-- `setindex!(h, v, key)`, base/weakdict.jl:302-315 (with all values alive,
`_cleanup_locked` sweeps nothing). -/
def WVID.setindex (h : WVID) (v key : JVal) : Out WVID Unit :=
  if !isa key h.K then (h, .error .argumentError)
  else if key == .nothing then (h, .error .argumentError)
  else if v == .nothing then (h, .error .argumentError)
  else if !finalizable v then (h, .error .errorException)
  else ({ h with ht := (eqtablePut h.ht key v).1 }, .ok ())

/-- `_getvalue(h, key)`, base/weakdict.jl:318-322: `get(h.ht, key, nothing)`
then `.value`; `nothing` is never a stored referent. -/
def WVID.getvalue (h : WVID) (key : JVal) : JVal := eqtableGet h.ht key .nothing

/-- `getindex(h, key)`, base/weakdict.jl:364-371. -/
def WVID.getindex (h : WVID) (key : JVal) : Except IErr JVal :=
  if key == .nothing then .error .keyError else
  let v := h.getvalue key
  if v == .nothing then .error .keyError else cast v h.V

/-- `get(h, key, default)`, base/weakdict.jl:324-330. -/
def WVID.get (h : WVID) (key default : JVal) : Except IErr JVal :=
  if key == .nothing then .error .keyError else
  let v := h.getvalue key
  if v == .nothing then .ok default else cast v h.V

/-- `get!(h, key, default)`, base/weakdict.jl:338-345. -/
def WVID.getBang (h : WVID) (key default : JVal) : Out WVID JVal :=
  let v := h.getvalue key
  if v != .nothing then (h, cast v h.V) else
  let r := h.setindex default key
  match r.2 with
  | .error e => (r.1, .error e)
  | .ok () => (r.1, cast default h.V)

end JuliaLean.IdDicts
