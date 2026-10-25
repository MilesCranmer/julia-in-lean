import DynExpr.Eval.Core

/-!
Mirror of the unary feature cache added by DynamicExpressions.jl PR #219
(branch `perf/unary-feature-cache`, head 5e2f3b8c, not on master):
`UnaryFeatureCache`, `cached_deg1_eval`, the cache branches of
`dispatch_deg1_eval`, the `unary_cache` field of `EvalContext`, and
`Base.copy(::EvalContext)`. Line numbers below refer to `src/Evaluate.jl` at
that head. Everything else the PR leaves unchanged and is reused from the
master mirror `DynExpr.Eval.Core` (leaves, kernels, constant shortcut).

Modelling choices:
* The cache is the state of the mutable `UnaryFeatureCache`: the cached
  evaluator threads it next to the `ArrayBuffer` state and returns it.
* Object identity (`===`) of `X` and of `operators` is an explicit number
  (`xid`, `oid`) next to their contents. Julia compares identities only;
  whether the contents behind an identity stayed the same is a hypothesis of
  the properties. The cache holds a strong reference to `X`, so an identity
  cannot be recycled for another object while it is cached.
* `entries` is an `nu × nf` matrix of optional vectors, given as a function
  plus its size. Stored vectors are `copy`s (line 639), so, arrays being values
  here, they never share storage with evaluation outputs.
* `sizeof(T)` is the parameter `szT`.
* `turbo=true` contexts return before touching the cache (lines 606-607);
  they are evaluated by the opaque extension evaluator, as on master.
-/

namespace DynExpr.EvalCache
open DynExpr.Eval

/-- State of `UnaryFeatureCache{T}` (src/Evaluate.jl:115-123). `key` is the
identity pair `(X, operators)` recorded at the last reset, `none` for the
initial `nothing` fields; `get i f` is `entries[i, f]` for `1 ≤ i ≤ nu`,
`1 ≤ f ≤ nf`. -/
structure UCache (T : Type) where
  key : Option (Nat × Nat)
  nu : Nat
  nf : Nat
  get : Nat → Nat → Option (JVec T)

variable {T : Type} [JlScalar T]

/-- `UnaryFeatureCache(T)` (src/Evaluate.jl:120-122), also the result of
`copy(::UnaryFeatureCache)` (src/Evaluate.jl:125): no identities and a
`0 × 0` entry matrix. -/
def UCache.empty : UCache T := ⟨none, 0, 0, fun _ _ => none⟩

/-- `isempty(cache.entries)` (src/Evaluate.jl:623). -/
def UCache.isEmpty (c : UCache T) : Bool := c.nu == 0 || c.nf == 0

/-- `cache.entries[i, f] = v` (src/Evaluate.jl:639), after the bounds check of
line 625. -/
def UCache.store (c : UCache T) (i f : Nat) (v : JVec T) : UCache T :=
  { c with get := fun i' f' => if i' = i ∧ f' = f then some v else c.get i' f' }

/-- Identities of `cX` and `operators`, `sizeof(T)`, and the context's
`bumper` flag, as read by `cached_deg1_eval` (src/Evaluate.jl:596-622). -/
structure CEnv where
  xid : Nat
  oid : Nat
  szT : Nat
  bumper : Bool := false

/-- The 16 MiB limit (src/Evaluate.jl:616). -/
def limitBytes : Nat := 16 * 1024 ^ 2

/-- `max_entries = (16 * 1024^2) ÷ sizeof(T) ÷ max(nrows, 1)` (src/Evaluate.jl:616),
for `sizeof(T) > 0` (`cachedDeg1` raises `DivideError` otherwise). -/
def maxEntries (szT nrows : Nat) : Nat := limitBytes / szT / max nrows 1

/-- Entry matrix size chosen at a reset (src/Evaluate.jl:617-621):
`nunary × nfeatures` within the limit, otherwise `0 × 0`. -/
def resetDims (szT : Nat) (o : OpEnum T) (X : JMat T) : Nat × Nat :=
  if (opsOf o 1).length * X.nrows ≤ maxEntries szT X.ncols then
    ((opsOf o 1).length, X.nrows)
  else (0, 0)

/-- Identity check and reset (src/Evaluate.jl:613-622). -/
def resetIfNew (ce : CEnv) (o : OpEnum T) (X : JMat T) (c : UCache T) : UCache T :=
  if c.key = some (ce.xid, ce.oid) then c
  else ⟨some (ce.xid, ce.oid), (resetDims ce.szT o X).1, (resetDims ce.szT o X).2,
    fun _ _ => none⟩

/-- `copyto!(output, cached)` (src/Evaluate.jl:628). -/
def copyTo (dst src : JVec T) : Jl (JVec T) :=
  if src.size ≤ dst.size then .ok (src ++ dst.extract src.size dst.size)
  else .error .boundsError

/-- Evaluator state: `ArrayBuffer` state and cache state. -/
abbrev St (T : Type) := Buf T × UCache T

/-- Attach a cache state to an uncached result. -/
def emb (c : UCache T) (p : ResultOk T × Buf T) : ResultOk T × St T := (p.1, (p.2, c))

/-- A step that does not touch the cache (leaves, fused kernels, the constant
shortcut: code the PR leaves unchanged). -/
def liftB (k : Buf T → Jl (ResultOk T × Buf T)) (s : St T) : Jl (ResultOk T × St T) := (k s.1).map (emb s.2)

/-- `cached_deg1_eval` (src/Evaluate.jl:596-642) for a node `op(x_feat)` whose
operator `f` the caller looked up, with `turbo` off (the evaluator below is
the non-turbo one). `none` means "evaluate without the cache", returned with
the possibly reset cache. The miss path evaluates the leaf with `deg0_eval`,
which is the leaf case of `evalT`. -/
def cachedDeg1 (cx : Ctx) (ce : CEnv) (o : OpEnum T) (X : JMat T) (op : Nat)
    (f : List T → T) (feat : Nat) (s : St T) :
    Jl (Option (ResultOk T × Buf T) × UCache T) :=
  if s.2.key ≠ some (ce.xid, ce.oid) ∧ ce.szT = 0 then
    .error (.errorException "DivideError: integer division error")
  else
    let c := resetIfNew ce o X s.2
    if c.isEmpty then .ok (none, c)
    else if ¬ (1 ≤ op ∧ op ≤ c.nu ∧ 1 ≤ feat ∧ feat ≤ c.nf) then .error .boundsError
    else match c.get op feat with
      | some v => do
        let (a, b') ← getArray s.1 X.ncols
        let out ← copyTo a v
        pure (some (⟨out, true, nextId s.1⟩, b'), c)
      | none => do
        let (r, b1) ← evalT cx o X (.feature feat) s.1
        if !r.ok then pure (some (r, b1), c)
        else if cx.earlyExit && !isValidArray r.x then pure (some (⟨r.x, false, r.id⟩, b1), c)
        else do
          let out ← degnEval f [r.x]
          let c' := if !cx.earlyExit || isValidArray out then c.store op feat out else c
          pure (some (⟨out, true, r.id⟩, b1), c')

/-- The call site `cached = cached_deg1_eval(...); cached === nothing || return cached`
followed by the uncached code `fallback` (src/Evaluate.jl:656-667, 697-706).
`bumper=true` returns `nothing` before the cache is read (line 606). -/
def viaCache (cx : Ctx) (ce : CEnv) (o : OpEnum T) (X : JMat T) (op : Nat)
    (f : List T → T) (feat : Nat) (fallback : St T → Jl (ResultOk T × St T)) (s : St T) : Jl (ResultOk T × St T) :=
  if ce.bumper then fallback s
  else do
    let (res, c) ← cachedDeg1 cx ce o X op f feat s
    match res with
    | some p => pure (emb c p)
    | none => fallback (s.1, c)

/-- `checked` with the cache state threaded through the child. -/
def checkedC (cx : Ctx) (ev : St T → Jl (ResultOk T × St T)) (k : JVec T → Ident → St T → Jl (ResultOk T × St T))
    (s : St T) : Jl (ResultOk T × St T) := do
  let (r, s) ← ev s
  if !r.ok then pure (r, s)
  else if cx.earlyExit && !isValidArray r.x then pure (⟨r.x, false, r.id⟩, s)
  else k r.x r.id s

/-- `unfused1` (src/Evaluate.jl:664-667, 701-706) with the cache threaded
through the child. -/
def unfused1C (cx : Ctx) (fop : Jl (List T → T)) (evC : St T → Jl (ResultOk T × St T)) (s : St T) : Jl (ResultOk T × St T) :=
  checkedC cx evC (fun x cid => liftB (fun b => do
    let f ← fop
    let out ← degnEval f [x]
    pure (⟨out, true, cid⟩, b))) s

/-- `unfused2` with the cache threaded through both children. -/
def unfused2C (cx : Ctx) (fop : Jl (List T → T)) (evL evR : St T → Jl (ResultOk T × St T)) (s : St T) : Jl (ResultOk T × St T) :=
  checkedC cx evL (fun xl cid => checkedC cx evR (fun xr _ => liftB (fun b => do
    let f ← fop
    let out ← degnEval f [xl, xr]
    pure (⟨out, true, cid⟩, b)))) s

/-- `dispatch_deg1_eval` of PR #219 (src/Evaluate.jl:644-711). Over 15 unary
operators the cache is tried for a feature child, with the operator looked up
first as the call's argument (lines 656-663). Otherwise the cache is tried in
the final `else` branch (lines 697-700); `cached_deg1_eval` returns `nothing`
without touching the cache unless the child is a feature (line 609), so a
non-feature child goes straight to the uncached code. -/
def deg1DispatchC (cx : Ctx) (ce : CEnv) (o : OpEnum T) (X : JMat T) (op : Nat)
    (c : Tree T) (evC : St T → Jl (ResultOk T × St T)) (s : St T) : Jl (ResultOk T × St T) :=
  let unaops := opsOf o 1
  if operatorLimit < unaops.length then
    match c with
    | .feature feat => do
      let f ← idxOp unaops op
      viaCache cx ce o X op f feat (unfused1C cx (idxOp unaops op) evC) s
    | _ => unfused1C cx (idxOp unaops op) evC s
  else do
    let f ← nifOp unaops op
    match c with
    | .branch lop [ll, lr] =>
      if cx.useFused && isLeaf ll && isLeaf lr then do
        let fl ← nifOp (opsOf o 2) lop
        liftB (deg1L2 cx X f fl ll lr) s
      else unfused1C cx (pure f) evC s
    | .branch lop [ll] =>
      if cx.useFused && isLeaf ll then do
        let fl ← nifOp unaops lop
        liftB (deg1L1 cx X f fl ll) s
      else unfused1C cx (pure f) evC s
    | .feature feat => viaCache cx ce o X op f feat (unfused1C cx (pure f) evC) s
    | _ => unfused1C cx (pure f) evC s

/-- `dispatch_deg2_eval` (src/Evaluate.jl:484-573, unchanged by the PR) with
the cache threaded through the children. -/
def deg2DispatchC (cx : Ctx) (o : OpEnum T) (X : JMat T) (op : Nat) (l r : Tree T)
    (evL evR : St T → Jl (ResultOk T × St T)) (s : St T) : Jl (ResultOk T × St T) :=
  let binops := opsOf o 2
  if operatorLimit < binops.length then unfused2C cx (idxOp binops op) evL evR s
  else do
    let f ← nifOp binops op
    let r0path := checkedC cx evL (fun xl cid => liftB (deg2R0 cx X f r xl cid)) s
    let l0path := checkedC cx evR (fun xr cid => liftB (deg2L0 cx X f l xr cid)) s
    if cx.useFused && isLeaf l && isLeaf r then liftB (deg2L0R0 cx X f l r) s
    else if cx.useFused && isLeaf r then
      match l with
      | .branch lop [ll, lr] =>
        if isNum T && isLeaf ll && isLeaf lr then do
          let g ← nifOp binops lop
          liftB (branch0 cx X f g .left ll lr r) s
        else r0path
      | _ => r0path
    else if cx.useFused && isLeaf l then
      match r with
      | .branch rop [rl, rr] =>
        if isNum T && isLeaf rl && isLeaf rr then do
          let g ← nifOp binops rop
          liftB (branch0 cx X f g .right l rl rr) s
        else l0path
      | _ => l0path
    else unfused2C cx (pure f) evL evR s

/-- `degnFinish` with the cache state carried along. -/
def degnFinishC (o : OpEnum T) (d op : Nat) :
    (ResultOk T × St T) ⊕ (List (JVec T × Ident) × St T) → Jl (ResultOk T × St T)
  | .inl r => pure r
  | .inr (xs, s) => (degnFinish o d op (.inr (xs, s.1))).map (emb s.2)

mutual
/-- `_eval_tree_array` (src/Evaluate.jl:331-358) with a `UnaryFeatureCache`:
as `evalT`, but unary nodes go through `deg1DispatchC`. -/
def evalTC (cx : Ctx) (ce : CEnv) (o : OpEnum T) (X : JMat T) : Tree T → St T → Jl (ResultOk T × St T)
  | .const v, s => liftB (evalT cx o X (.const v)) s
  | .feature f, s => liftB (evalT cx o X (.feature f)) s
  | .branch op cs, s =>
    if isConstantL cs then liftB (constPath o X (.branch op cs)) s
    else match cs with
      | [c] => deg1DispatchC cx ce o X op c (evalTC cx ce o X c) s
      | [l, r] => deg2DispatchC cx o X op l r (evalTC cx ce o X l) (evalTC cx ce o X r) s
      | l :: r :: rest =>
        if cx.D = 2 then deg2DispatchC cx o X op l r (evalTC cx ce o X l) (evalTC cx ce o X r) s
        else do
          let res ← evalChildrenC cx ce o X (l :: r :: rest) s
          degnFinishC o (rest.length + 2) op res
      | [] => .error (.undefinedBehavior "branch without children")
/-- The children loop of `inner_dispatch_degn_eval` with the cache threaded. -/
def evalChildrenC (cx : Ctx) (ce : CEnv) (o : OpEnum T) (X : JMat T) :
    List (Tree T) → St T → Jl ((ResultOk T × St T) ⊕ (List (JVec T × Ident) × St T))
  | [], s => .ok (.inr ([], s))
  | c :: cs, s => do
    let (r, s) ← evalTC cx ce o X c s
    if !r.ok then pure (.inl (r, s))
    else if cx.earlyExit && !isValidArray r.x then pure (.inl (⟨r.x, false, r.id⟩, s))
    else do
      match ← evalChildrenC cx ce o X cs s with
      | .inl e => pure (.inl e)
      | .inr (xs, s') => pure (.inr ((r.x, r.id) :: xs, s'))
end

/-- `eval_tree_array` return statement with the cache (src/Evaluate.jl:298-302). -/
def evalArrC (cx : Ctx) (ce : CEnv) (o : OpEnum T) (X : JMat T) (t : Tree T) (b : Buf T)
    (c : UCache T) : Jl ((JVec T × Bool) × UCache T) := do
  let (r, s) ← evalTC cx ce o X t (b, c)
  pure ((r.x, r.ok && (!cx.earlyExit || isValidArray r.x)), s.2)

/-- `eval_tree_array(tree, X, ::OperatorEnum; eval_context)` (src/Evaluate.jl:282-303)
for a context whose `unary_cache` is a `UnaryFeatureCache{T}` in state `c`;
`xid`, `oid` are the identities of `X` and `operators`, `szT` is `sizeof(T)`.
Returns the result and the new cache state. -/
def evalTreeArrayC (ext : Ext) (impl : ExtImpl T) (D : Nat) (t : Tree T) (X : JMat T)
    (o : OpEnum T) (ec : EvalContext T) (xid oid szT : Nat) (c : UCache T) :
    Jl ((JVec T × Bool) × UCache T) :=
  if ec.turbo && !JlScalar.isFloat (T := T) then
    .error (.assertionError "T in (Float32, Float64)")
  else if ec.turbo && !ext.loopVectorization then
    .error (.errorException "Please load the LoopVectorization.jl package to use this feature.")
  else if ec.turbo then do
    let r ← impl.turboEval t X
    pure ((r.x, r.ok && (!ec.earlyExit || isValidArray r.x)), c)
  else evalArrC ⟨ec.earlyExit, ec.useFused, D⟩ ⟨xid, oid, szT, ec.bumper⟩ o X t ec.buffer c

/-- `Base.copy(::EvalContext)` (src/Evaluate.jl:192-203): the same policy, a
copy of the buffer (equal as a value), and `copy(cache)`, a fresh cache. -/
def copyContext (ec : EvalContext T) (_c : UCache T) : EvalContext T × UCache T :=
  (ec, UCache.empty)

/-! Sequences of calls sharing one cache. -/

/-- One `eval_tree_array` call: tree, input contents and identity, operator
contents and identity, context policy and buffer state. -/
structure Call (T : Type) where
  t : Tree T
  X : JMat T
  xid : Nat
  o : OpEnum T
  oid : Nat
  ec : EvalContext T

/-- Run the calls in order with one shared `UnaryFeatureCache`. -/
def runCached (ext : Ext) (impl : ExtImpl T) (D szT : Nat) :
    List (Call T) → UCache T → Jl (List (JVec T × Bool))
  | [], _ => .ok []
  | k :: ks, c => do
    let (r, c') ← evalTreeArrayC ext impl D k.t k.X k.o k.ec k.xid k.oid szT c
    let rs ← runCached ext impl D szT ks c'
    pure (r :: rs)

/-- Run the same calls without a cache. -/
def runPlain (ext : Ext) (impl : ExtImpl T) (D : Nat) : List (Call T) → Jl (List (JVec T × Bool))
  | [] => .ok []
  | k :: ks => do
    let r ← evalTreeArray ext impl D k.t k.X k.o k.ec
    let rs ← runPlain ext impl D ks
    pure (r :: rs)

/-! Two threads sharing one cache.

Each thread runs `cached_deg1_eval` for a root node `op(x_feat)` with no buffer
and at most 15 unary operators, split into the steps that touch the shared
cache: the identity check and reset (lines 613-622), the entry read
(lines 623-630), and, after a miss, the store (line 639). Each step is atomic
here; a real schedule may interleave even finer, so any bad interleaving of
these steps is also a real execution. -/

/-- Thread-local state. `pending out` holds a computed miss result before
its store. -/
inductive TState (T : Type) where
  | start
  | checked
  | pending (r : ResultOk T)
  | done (r : Jl (ResultOk T))

/-- Work of one thread: input and operator identities and contents, the node
`op(x_feat)` and the context policy. -/
structure Job (T : Type) where
  ce : CEnv
  X : JMat T
  o : OpEnum T
  op : Nat
  feat : Nat
  cx : Ctx

/-- Uncached node result `op(x_feat)` for a job (the reference). -/
def Job.plain (j : Job T) : Jl (ResultOk T) :=
  (evalT j.cx j.o j.X (.branch j.op [.feature j.feat]) .none).map Prod.fst

/-- One atomic step of a thread on the shared cache. -/
def tstep (j : Job T) : TState T × UCache T → TState T × UCache T
  | (.start, c) =>
    if c.key ≠ some (j.ce.xid, j.ce.oid) ∧ j.ce.szT = 0 then
      (.done (.error (.errorException "DivideError: integer division error")), c)
    else (.checked, resetIfNew j.ce j.o j.X c)
  | (.checked, c) =>
    match nifOp (opsOf j.o 1) j.op with
    | .error e => (.done (.error e), c)
    | .ok f =>
      if c.isEmpty then (.done j.plain, c)
      else if ¬ (1 ≤ j.op ∧ j.op ≤ c.nu ∧ 1 ≤ j.feat ∧ j.feat ≤ c.nf) then
        (.done (.error .boundsError), c)
      else match c.get j.op j.feat with
        | some v => (.done ((copyTo (JVec.fill j.X.ncols JlScalar.undef) v).map
            fun out => ⟨out, true, .fresh⟩), c)
        | none =>
          match evalT j.cx j.o j.X (.feature j.feat) .none with
          | .error e => (.done (.error e), c)
          | .ok (r, _) =>
            if !r.ok then (.done (.ok r), c)
            else if j.cx.earlyExit && !isValidArray r.x then (.done (.ok ⟨r.x, false, r.id⟩), c)
            else match degnEval f [r.x] with
              | .error e => (.done (.error e), c)
              | .ok out =>
                if !j.cx.earlyExit || isValidArray out then (.pending ⟨out, true, r.id⟩, c)
                else (.done (.ok ⟨out, true, r.id⟩), c)
  | (.pending r, c) =>
    if 1 ≤ j.op ∧ j.op ≤ c.nu ∧ 1 ≤ j.feat ∧ j.feat ≤ c.nf then
      (.done (.ok r), c.store j.op j.feat r.x)
    else (.done (.error .boundsError), c)
  | (.done r, c) => (.done r, c)

/-- Run a schedule (`true`: thread A takes a step, `false`: thread B). -/
def race (ja jb : Job T) : List Bool → TState T × TState T × UCache T →
    TState T × TState T × UCache T
  | [], st => st
  | true :: rest, (a, b, c) =>
    let (a', c') := tstep ja (a, c)
    race ja jb rest (a', b, c')
  | false :: rest, (a, b, c) =>
    let (b', c') := tstep jb (b, c)
    race ja jb rest (a, b', c')

end DynExpr.EvalCache
