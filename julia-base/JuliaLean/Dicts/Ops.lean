import JuliaLean.Dicts.Sets

/-!
# Operation sequences and their reference semantics

Properties quantify over every `Dict` reachable from `Dict()` by a sequence of
API calls (`runOps`) and compare the table with an association list built by
the same calls on a mathematical finite map (`rrun`).
-/

namespace JuliaLean.Dicts

variable {K V : Type}

/-- One mutating `Dict` API call. `merge`/`mergewith` take the pairs of the other
dictionary, built as `d2 = Dict{K,V}(); for (k, v) in ps; d2[k] = v; end`. -/
inductive BaseOp (K V : Type) where
  /-- `d[k] = v` -/
  | set (k : K) (v : V)
  /-- `delete!(d, k)` -/
  | del (k : K)
  /-- `pop!(d, k)` -/
  | pop (k : K)
  /-- `pop!(d, k, default)` -/
  | popd (k : K) (dflt : V)
  /-- `get!(d, k, v)` -/
  | getv (k : K) (v : V)
  /-- `sizehint!(d, n; shrink)` -/
  | hint (n : JInt .i64) (shrink : Bool)
  /-- `empty!(d)` -/
  | empty
  /-- `filter!(p -> pred(p.first, p.second), d)` -/
  | filter (pred : K → V → Bool)
  /-- `merge!(d, d2)` -/
  | merge (ps : List (K × V))
  /-- `mergewith!(f, d, d2)` -/
  | mergewith (f : V → V → V) (ps : List (K × V))

/-- A call, or `get!(d, k) do; <inner calls on d>; v; end`. -/
inductive DOp (K V : Type) where
  | base (b : BaseOp K V)
  | getf (k : K) (v : V) (inner : List (BaseOp K V))

/-- The dictionary `d2` of `merge`/`mergewith`. -/
def buildDict (o : KeyOps K) (ps : List (K × V)) : DR (Table K V) :=
  ps.foldlM (fun t kv => setindex o t kv.2 kv.1) Table.empty

def runBase (o : KeyOps K) (t : Table K V) : BaseOp K V → DR (Table K V)
  | .set k v => setindex o t v k
  | .del k => dictDelete o t k
  | .pop k => do let r ← popKey o t k; pure r.2
  | .popd k d => do let r ← popKeyDefault o t k d; pure r.2
  | .getv k v => do let r ← getBangVal o t k v; pure r.2
  | .hint n s => sizehint o t n s
  | .empty => pure (emptyBang t)
  | .filter p => filterBang t p
  | .merge ps => do dictMerge o t (← buildDict o ps)
  | .mergewith f ps => do mergewith o f t (← buildDict o ps)

def runBaseList (o : KeyOps K) (t : Table K V) (l : List (BaseOp K V)) : DR (Table K V) :=
  l.foldlM (runBase o) t

/-- The `default` closure of `get!(d, k) do ... end`: run `inner` on `d`, return `v`. -/
def innerDefault (o : KeyOps K) (v : V) (inner : List (BaseOp K V)) (t : Table K V) :
    DR (V × Table K V) := do
  let t ← runBaseList o t inner
  pure (v, t)

def runOp (o : KeyOps K) (t : Table K V) : DOp K V → DR (Table K V)
  | .base b => runBase o t b
  | .getf k v inner => do let r ← getBang o t k (innerDefault o v inner); pure r.2

/-- The table after the calls `ops`, starting from `Dict{K,V}()`. -/
def runOps (o : KeyOps K) (ops : List (DOp K V)) : DR (Table K V) :=
  ops.foldlM (runOp o) Table.empty

/-! ## Reference semantics: association lists with pairwise non-`isequal` keys -/

abbrev RMap (K V : Type) := List (K × V)

def rdel (o : KeyOps K) (m : RMap K V) (k : K) : RMap K V := m.filter (fun e => !o.eq k e.1)
/-- Setting a key stores the new key object (`h.keys[index] = key`, `base/dict.jl:365`). -/
def rset (o : KeyOps K) (m : RMap K V) (k : K) (v : V) : RMap K V := (k, v) :: rdel o m k
def rfind (o : KeyOps K) (m : RMap K V) (q : K) : Option (K × V) := m.find? (fun e => o.eq q e.1)
def rlookup (o : KeyOps K) (m : RMap K V) (q : K) : Option V := (rfind o m q).map (·.2)
def rbuild (o : KeyOps K) (ps : List (K × V)) : RMap K V :=
  ps.foldl (fun m kv => rset o m kv.1 kv.2) []

/-- `mergewith!`: an existing key keeps its key object and combines the values. -/
def rcombine (o : KeyOps K) (f : V → V → V) (m : RMap K V) (kv : K × V) : RMap K V :=
  match rfind o m kv.1 with
  | some (k0, w) => (k0, f w kv.2) :: rdel o m kv.1
  | none => rset o m kv.1 kv.2

def rbase (o : KeyOps K) (m : RMap K V) : BaseOp K V → DR (RMap K V)
  | .set k v => pure (rset o m k v)
  | .del k => pure (rdel o m k)
  | .pop k => match rfind o m k with
    | some _ => pure (rdel o m k)
    | none => throw .keyError
  | .popd k _ => pure (rdel o m k)
  | .getv k v => match rfind o m k with
    | some _ => pure m
    | none => pure (rset o m k v)
  | .hint _ _ => pure m
  | .empty => pure []
  | .filter p => pure (m.filter fun e => p e.1 e.2)
  | .merge ps => pure ((rbuild o ps).foldl (fun m kv => rset o m kv.1 kv.2) m)
  | .mergewith f ps => pure ((rbuild o ps).foldl (rcombine o f) m)

def rbaseList (o : KeyOps K) (m : RMap K V) (l : List (BaseOp K V)) : DR (RMap K V) :=
  l.foldlM (rbase o) m

def rop (o : KeyOps K) (m : RMap K V) : DOp K V → DR (RMap K V)
  | .base b => rbase o m b
  | .getf k v inner => match rfind o m k with
    | some _ => pure m
    | none => do let m ← rbaseList o m inner; pure (rset o m k v)

def rrun (o : KeyOps K) (ops : List (DOp K V)) : DR (RMap K V) := ops.foldlM (rop o) []

/-! ## Size bounds of the calls -/

/-- Calls weighted by the pairs they insert. -/
def baseWeight : BaseOp K V → Nat
  | .merge ps => 1 + ps.length
  | .mergewith _ ps => 1 + ps.length
  | _ => 1

def baseListWeight (l : List (BaseOp K V)) : Nat := (l.map baseWeight).sum

def opWeight : DOp K V → Nat
  | .base b => baseWeight b
  | .getf _ _ inner => 1 + baseListWeight inner

/-- A size hint whose `3 * n` does not overflow `Int`. -/
def baseHintSmall : BaseOp K V → Bool
  | .hint n _ => decide (n.val ≤ 2 ^ 61)
  | _ => true

def opHintSmall : DOp K V → Bool
  | .base b => baseHintSmall b
  | .getf _ _ inner => inner.all baseHintSmall

/-- The bound used by the properties: at most `2^30` inserted pairs (a few
gigabytes of table) and no size hint that overflows `Int` arithmetic. With it
no `Int` count wraps and `age::UInt` cannot return to an earlier value. -/
def OpsSmall (ops : List (DOp K V)) : Prop :=
  (ops.map opWeight).sum ≤ 2 ^ 30 ∧ ops.all opHintSmall = true

def InnerSmall (inner : List (BaseOp K V)) : Prop :=
  baseListWeight inner ≤ 2 ^ 30 ∧ inner.all baseHintSmall = true

/-- `max_values(K)` is an upper bound on the number of pairwise non-`isequal`
keys, or large enough that no reachable table gets near it. -/
def MaxValuesOK (o : KeyOps K) : Prop :=
  2 ^ 62 ≤ o.maxValues.val ∨
  ∀ xs : List K, xs.Pairwise (fun a b => o.eq a b = false) → (xs.length : Int) ≤ o.maxValues.val

/-! ## Agreement of a table with a reference map -/

/-- `t` represents `m`: `m` has pairwise non-`isequal` keys, every lookup
agrees, iteration yields exactly the pairs of `m` (each key once) and
`length(t)` is the number of keys. -/
def Agrees (o : KeyOps K) (t : Table K V) (m : RMap K V) : Prop :=
  m.Pairwise (fun a b => o.eq a.1 b.1 = false) ∧
  (∀ q, dictGet o t q = .ok (rlookup o m q)) ∧
  (∃ xs, iterList t = .ok xs ∧ (∀ e, e ∈ xs ↔ e ∈ m) ∧ xs.length = m.length) ∧
  dictLength t = m.length

/-- `t` is reachable from `Dict()` by small call sequences whose reference result is `m`. -/
def Reach (o : KeyOps K) (t : Table K V) (m : RMap K V) : Prop :=
  ∃ ops : List (DOp K V), OpsSmall ops ∧ runOps o ops = .ok t ∧ rrun o ops = .ok m

/-- `Except.isOk` as a `Bool`, for refutations by evaluation. -/
def okB {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

end JuliaLean.Dicts
