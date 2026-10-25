import DynExpr.EvalCache.Core

/-!
Specifications and property statements for the unary feature cache of PR #219.
-/

namespace DynExpr.EvalCache
open DynExpr.Eval

section spec
variable {T : Type} [JlScalar T]

/-- The cache agrees with the input behind its identity: its entry matrix has
the size a reset for `X` and `o` would give, and every stored entry `(i, f)` is
in range and equals unary operator `i` applied to row `f` of `X`, as
`deg1_eval` computes it; under `early_exit` the row and the entry are valid. -/
def Consistent (ee : Bool) (szT : Nat) (X : JMat T) (o : OpEnum T) (c : UCache T) : Prop :=
  (c.nu, c.nf) = resetDims szT o X ∧
  ∀ i f v, c.get i f = some v →
    1 ≤ i ∧ i ≤ c.nu ∧ 1 ≤ f ∧ f ≤ c.nf ∧
    ∃ g row, o.lookup 1 i = some g ∧ X.row f = .ok row ∧ degnEval g [row] = .ok v ∧
      (ee = true → isValidArray row = true ∧ isValidArray v = true)

/-- A cache whose identities are those of `X` (`xid`) and `o` (`oid`) is
consistent with them. A cache recorded for other identities is unconstrained:
it is reset before use. A fresh `UnaryFeatureCache` satisfies this. -/
def CacheOK (ee : Bool) (szT xid oid : Nat) (X : JMat T) (o : OpEnum T) (c : UCache T) : Prop :=
  c.key = some (xid, oid) → Consistent ee szT X o c

/-- No in-place mutation of inputs: calls with the same identity of `X` see the
same contents. -/
def XStable (ks : List (Call T)) : Prop :=
  ∀ k ∈ ks, ∀ k' ∈ ks, k.xid = k'.xid → k.X = k'.X

/-- Operators keep their behaviour: calls with the same identity of the
operators see the same functions. -/
def OpsStable (ks : List (Call T)) : Prop :=
  ∀ k ∈ ks, ∀ k' ∈ ks, k.oid = k'.oid → k.o = k'.o

/-- A thread's job is well formed: its node `op(x_feat)` is well formed and
`sizeof(T) > 0`. -/
def Job.WF (j : Job T) : Prop :=
  (Tree.branch j.op [.feature j.feat] : Tree T).WF j.cx.D j.o.nops j.X.nrows ∧ 0 < j.ce.szT

/-- Both threads finish with the uncached result of their own node. -/
def RaceOK (ja jb : Job T) : TState T × TState T × UCache T → Prop
  | (.done ra, .done rb, _) => ra = ja.plain ∧ rb = jb.plain
  | _ => True

end spec

/-- evalcache-single: with a cache that is fresh or consistent with the current
`X` and operators, the cached `eval_tree_array` returns exactly the uncached
result (value array, flag, or the same error) for every early_exit, use_fused,
bumper, turbo and buffer setting. -/
def evalCacheSingle : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (t : Tree T)
    (X : JMat T) (o : OpEnum T) (ec : EvalContext T) (xid oid szT : Nat) (c : UCache T),
    0 < szT → t.WF D o.nops X.nrows → CacheOK ec.earlyExit szT xid oid X o c →
    ∃ c', evalTreeArrayC ext impl D t X o ec xid oid szT c =
      (evalTreeArray ext impl D t X o ec).map (fun r => (r, c'))

/-- evalcache-node: inside the evaluator, every cached step returns the same
`ResultOk` as the uncached one (array, flag and array identity: fresh or the
same buffer slot) and leaves the buffer in the same state. -/
def evalCacheNode : Prop :=
  ∀ (T : Type) [JlScalar T] (cx : Ctx) (ce : CEnv) (o : OpEnum T) (X : JMat T) (t : Tree T)
    (b : Buf T) (c : UCache T),
    0 < ce.szT → t.WF cx.D o.nops X.nrows → CacheOK cx.earlyExit ce.szT ce.xid ce.oid X o c →
    ∃ c', evalTC cx ce o X t (b, c) = (evalT cx o X t b).map (emb c')

/-- evalcache-stored: after a call, the cache is still consistent with the
input: every stored entry is unary operator `i` applied to row `f` of `X`;
under early_exit the row and the entry are finite, without early_exit the
entry is the operator output as is (NaN/Inf included). The cache either is
unchanged or carries the identities of this call. -/
def evalCacheStored : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (t : Tree T)
    (X : JMat T) (o : OpEnum T) (ec : EvalContext T) (xid oid szT : Nat) (c : UCache T),
    0 < szT → t.WF D o.nops X.nrows → CacheOK ec.earlyExit szT xid oid X o c →
    ∀ r c', evalTreeArrayC ext impl D t X o ec xid oid szT c = .ok (r, c') →
      CacheOK ec.earlyExit szT xid oid X o c' ∧ (c' = c ∨ c'.key = some (xid, oid))

/-- evalcache-store-rule: for a node `op(x_f)` on a fresh cache within the
size limit (turbo and bumper off), a successful call stores `op.(X[f, :])`
exactly when early_exit is off, or the row and the output are both finite. -/
def evalCacheStoreRule : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (op f : Nat)
    (X : JMat T) (o : OpEnum T) (ec : EvalContext T) (xid oid szT : Nat),
    0 < szT → (Tree.branch op [.feature f] : Tree T).WF D o.nops X.nrows →
    ec.turbo = false → ec.bumper = false →
    (opsOf o 1).length * X.nrows ≤ maxEntries szT X.ncols →
    ∃ g row out, o.lookup 1 op = some g ∧ X.row f = .ok row ∧ degnEval g [row] = .ok out ∧
      ∀ r c', evalTreeArrayC ext impl D (.branch op [.feature f]) X o ec xid oid szT
          UCache.empty = .ok (r, c') →
        c'.get op f = if !ec.earlyExit || (isValidArray row && isValidArray out)
          then some out else none

/-- evalcache-sequence: a cache shared by any sequence of calls (different
trees; any identities of X and operators, which trigger resets; any
use_fused, bumper, turbo and buffer per call) gives every call its uncached
result, provided contents never change behind an identity and all calls use
the same early_exit. -/
def evalCacheSequence : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D szT : Nat) (ee : Bool)
    (ks : List (Call T)),
    0 < szT → (∀ k ∈ ks, k.t.WF D k.o.nops k.X.nrows ∧ k.ec.earlyExit = ee) →
    XStable ks → OpsStable ks →
    runCached ext impl D szT ks UCache.empty = runPlain ext impl D ks

/-- evalcache-mutate-x: as evalcache-sequence, but X may change contents while
keeping its identity (in-place mutation, or a view whose index vector changed). -/
def evalCacheMutateX : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D szT : Nat) (ee : Bool)
    (ks : List (Call T)),
    0 < szT → (∀ k ∈ ks, k.t.WF D k.o.nops k.X.nrows ∧ k.ec.earlyExit = ee) →
    OpsStable ks →
    runCached ext impl D szT ks UCache.empty = runPlain ext impl D ks

/-- evalcache-mutate-op: as evalcache-sequence, but an operator may change
behaviour while the operators keep their identity (a closure over mutable
state, a mutable callable struct). -/
def evalCacheMutateOp : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D szT : Nat) (ee : Bool)
    (ks : List (Call T)),
    0 < szT → (∀ k ∈ ks, k.t.WF D k.o.nops k.X.nrows ∧ k.ec.earlyExit = ee) →
    XStable ks →
    runCached ext impl D szT ks UCache.empty = runPlain ext impl D ks

/-- evalcache-shared-early-exit: as evalcache-sequence, but the contexts sharing
the cache may differ in early_exit. -/
def evalCacheSharedEarly : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D szT : Nat) (ks : List (Call T)),
    0 < szT → (∀ k ∈ ks, k.t.WF D k.o.nops k.X.nrows) → XStable ks → OpsStable ks →
    runCached ext impl D szT ks UCache.empty = runPlain ext impl D ks

/-- evalcache-limit: when a full entry matrix would exceed 16 MiB, the result
is the uncached one and the cache, once reset for this input, stores nothing. -/
def evalCacheLimit : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (t : Tree T)
    (X : JMat T) (o : OpEnum T) (ec : EvalContext T) (xid oid szT : Nat) (c : UCache T),
    0 < szT → t.WF D o.nops X.nrows → CacheOK ec.earlyExit szT xid oid X o c →
    maxEntries szT X.ncols < (opsOf o 1).length * X.nrows →
    ∃ c', evalTreeArrayC ext impl D t X o ec xid oid szT c =
        (evalTreeArray ext impl D t X o ec).map (fun r => (r, c')) ∧
      (c'.key = some (xid, oid) → c'.isEmpty = true ∧ ∀ i f, c'.get i f = none)

/-- evalcache-turbo: with turbo=true the cache is never read or written: the
result is the uncached turbo result and the cache is unchanged. -/
def evalCacheTurbo : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (t : Tree T)
    (X : JMat T) (o : OpEnum T) (ec : EvalContext T) (xid oid szT : Nat) (c : UCache T),
    ec.turbo = true →
    evalTreeArrayC ext impl D t X o ec xid oid szT c =
      (evalTreeArray ext impl D t X o ec).map (fun r => (r, c))

/-- evalcache-copy: `copy(eval_context)` starts from a fresh cache, so it gives
uncached results whatever state (even stale) the original cache is in. -/
def evalCacheCopy : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (t : Tree T)
    (X : JMat T) (o : OpEnum T) (ec : EvalContext T) (xid oid szT : Nat) (c : UCache T),
    0 < szT → t.WF D o.nops X.nrows →
    (copyContext ec c).2.key = none ∧
    ∃ c', evalTreeArrayC ext impl D t X o (copyContext ec c).1 xid oid szT (copyContext ec c).2 =
      (evalTreeArray ext impl D t X o ec).map (fun r => (r, c'))

/-- evalcache-threads: two threads that share one cache, each evaluating a
unary feature node on its own input, finish with their uncached results under
every interleaving of the cache accesses. -/
def evalCacheRace : Prop :=
  ∀ (T : Type) [JlScalar T] (ja jb : Job T) (sched : List Bool) (c : UCache T),
    ja.WF → jb.WF → ja.ce.szT = jb.ce.szT →
    (ja.ce.xid = jb.ce.xid → ja.X = jb.X) → (ja.ce.oid = jb.ce.oid → ja.o = jb.o) →
    CacheOK ja.cx.earlyExit ja.ce.szT ja.ce.xid ja.ce.oid ja.X ja.o c →
    CacheOK jb.cx.earlyExit jb.ce.szT jb.ce.xid jb.ce.oid jb.X jb.o c →
    RaceOK ja jb (race ja jb sched (.start, .start, c))

/-- evalcache-threads-same: two threads that share one cache and the same
input (identities, contents, early_exit), evaluating any unary feature nodes,
finish with their uncached results under every interleaving. -/
def evalCacheRaceSame : Prop :=
  ∀ (T : Type) [JlScalar T] (ja jb : Job T) (sched : List Bool) (c : UCache T),
    ja.WF → jb.WF → ja.ce.szT = jb.ce.szT → ja.ce.xid = jb.ce.xid → ja.ce.oid = jb.ce.oid →
    ja.X = jb.X → ja.o = jb.o → ja.cx.earlyExit = jb.cx.earlyExit →
    CacheOK ja.cx.earlyExit ja.ce.szT ja.ce.xid ja.ce.oid ja.X ja.o c →
    RaceOK ja jb (race ja jb sched (.start, .start, c))

end DynExpr.EvalCache
