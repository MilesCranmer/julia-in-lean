import JuliaLean.Proofs.base.loading.cachefile

/-!
Acceptance and exact specifications for the cache-file checks of `base/loading.jl` (pinned master
f755f49a9e41). `cachefile.lean` shows that each check rejects; this file shows the other
direction: when every check passes, `stale_cachefile` returns a fresh verdict, and
`any_includes_stale` returns false on unchanged includes. These use `OkRun` (every run returns
normally with the stated value), so a function that always rejects, always throws or never
returns does not satisfy them.

The `walk_ok` tactic follows the function body like `walk_step`, but it must prove that each
callee returns. It takes that from a hypothesis in the context (`apply_assumption`), pushes the
rest of the body into the postcondition when the first action is not a callee (`okRun_bind'`),
and closes branches the hypotheses rule out with `simp_all`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace JuliaLean.Proofs.base.loading.Cachefile
open JuliaLean JuliaLean.base.loading

section
variable {X Y E D CI CF V : Type}

theorem okRun_forIn {σ β : Type} (o : LOps X Y E D CI CF V) (xs : List σ) (init : β)
    (f : σ → β → LM o (ForInStep β)) (Inv : β → Prop) (h0 : Inv init)
    (hf : ∀ x ∈ xs, ∀ b, Inv b → OkRun o (f x b) (fun r => Inv r.value)) :
    OkRun o (forIn xs init f) Inv := by
  induction xs generalizing init with
  | nil => simp only [List.forIn_nil]; exact okRun_pure o h0
  | cons x rest ih =>
    simp only [List.forIn_cons]
    refine okRun_bind o (hf x (by simp) init h0) ?_
    intro r hr
    cases r with
    | done b' => exact okRun_pure o hr
    | yield b' => exact ih b' hr (fun y hy => hf y (by simp [hy]))

theorem okRun_tryFinally (o : LOps X Y E D CI CF V) {α : Type} {body : LM o α} {c : LM o Unit}
    {Q : α → Prop} (h : OkRun o body Q) (hc : OkRun o c (fun _ => True)) :
    OkRun o (tryFinallyL o body c) Q := by
  intro s
  obtain ⟨a, s1, h1, hq⟩ := h s
  obtain ⟨u, s2, h2, -⟩ := hc s1
  refine ⟨a, s2, ?_, hq⟩
  unfold tryFinallyL
  simp only [ExceptT.run_mk]
  simp only [StateT.run] at h1 h2
  simp [bind, StateT.bind, h1, h2, StateT.run, pure, StateT.pure]

theorem okRun_tryCatch (o : LOps X Y E D CI CF V) {α : Type} {body : LM o α}
    {handler : LErr E → LM o α} {Q : α → Prop} (h : OkRun o body Q) :
    OkRun o (tryCatchL o body handler) Q := by
  intro s
  obtain ⟨a, s1, h1, hq⟩ := h s
  refine ⟨a, s1, ?_, hq⟩
  unfold tryCatchL
  simp only [ExceptT.run_mk]
  simp only [StateT.run] at h1
  simp [bind, StateT.bind, h1, StateT.run, pure, StateT.pure]

theorem okRun_withLock (o : LOps X Y E D CI CF V) {α : Type} {body : LM o α} {Q : α → Prop}
    (h : OkRun o body Q) : OkRun o (withLock o body) Q := by
  intro s
  obtain ⟨a, s1, h1, hq⟩ := h { s with require_lock := s.require_lock + 1 }
  refine ⟨a, { s1 with require_lock := s1.require_lock - 1 }, ?_, hq⟩
  have h1' : body { s with require_lock := s.require_lock + 1 } = some (.ok a, s1) := h1
  simp [withLock, ExceptT.run, ExceptT.mk, StateT.run, bind, StateT.bind, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, h1']

theorem okRun_map (o : LOps X Y E D CI CF V) {α β : Type} {m : LM o α} {f : α → β}
    {P : α → Prop} {Q : β → Prop} (hm : OkRun o m P) (hk : ∀ a, P a → Q (f a)) :
    OkRun o (f <$> m) Q := by
  rw [map_eq_pure_bind]
  exact okRun_bind o hm fun a h => okRun_pure o (hk a h)

theorem okRun_of_eq (o : LOps X Y E D CI CF V) {α : Type} {m : LM o α} {a : α} {Q : α → Prop}
    (h : m = pure a) (hq : Q a) : OkRun o m Q := by
  rw [h]; exact okRun_pure o hq

end

open Lean Meta Elab Tactic in
/-- Close an `OkRun` goal with a local hypothesis whose conclusion is an `OkRun` statement
(a callee hint), instantiating its arguments. Side premises must be closed by `assumption`. -/
elab "apply_hint" : tactic => do
  let g ← getMainGoal
  g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let isHint ← forallTelescope ty fun _ c => pure (c.isAppOf ``OkRun)
    unless isHint do continue
    let saved ← saveState
    try
      let gs ← g.apply (mkFVar d.fvarId)
      for sg in gs do
        sg.assumption
      replaceMainGoal []
      return
    catch _ =>
      restoreState saved
  throwError "apply_hint: no hint"

macro "walk_ok_leaf" : tactic => `(tactic| first | rfl | (simp_all; done))

/-- One step of the `OkRun` walk. `hloop1` and `hloop2`, when present, give the per-element
facts of a loop: they are instantiated with the loop's membership hypothesis. -/
syntax "walk_ok" : tactic
macro_rules | `(tactic| walk_ok) => `(tactic| first
  | with_reducible (intro _ h; (try dsimp only at h); subst h)
  | with_reducible intro _
  | (jp_step; next => (repeat' walk_ok) <;> fail "jp spec failed")
  | jp_step inline
  | ((with_reducible_and_instances apply okRun_throw); simp_all; done)
  | ((with_reducible_and_instances apply okRun_throwL); simp_all; done)
  | ((with_reducible_and_instances apply okRun_pure); walk_ok_leaf)
  | ((with_reducible_and_instances apply okRun_pure); (try dsimp only); show OkRun _ _ _)
  | (with_reducible_and_instances apply okRun_tryFinally)
  | (with_reducible_and_instances apply okRun_tryCatch)
  | (with_reducible_and_instances apply okRun_withLock)
  | ((with_reducible_and_instances refine okRun_bind _ (okRun_forIn _ _ _ _ (fun b => b.1 = none) rfl ?_) ?_);
      intro _ _ _ _;
      (try have := $(Lean.mkIdent `hloop1) _ ‹_›);
      (try have := $(Lean.mkIdent `hloop2) _ ‹_›);
      try (simp_all; done))
  | ((with_reducible_and_instances apply okRun_bind); apply_hint)
  | apply_hint
  | ((with_reducible_and_instances apply okRun_map); apply_hint)
  | ((with_reducible_and_instances apply okRun_ite) <;> intro _)
  | match_step
  | (with_reducible_and_instances apply okRun_bind')
  | (simp_all; done)
  | fail "walk_ok stuck")

/-! ## `any_includes_stale`: unchanged includes are accepted -/

section
variable {X Y E D CI CF V : Type}

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem precise_ok (o : LOps X Y E D CI CF V) {Stream : Type} (ops : IncludeStalenessOps o Stream)
    st fixup isFile fileHash dirHash (hfs : PureIncludeFs o ops st fixup isFile fileHash dirHash)
    (hstore : ∀ p, OkRun o (in_package_store o p) (fun _ => True))
    (includes : List CacheHeaderIncludes) (cachefile : Bytes) (reasons : Option (AMap Bytes base.loading.JInt64))
    (hun : ∀ inc ∈ includes, IncludeUnchanged o ops.io st fileHash dirHash inc) :
    OkRun o (any_includes_stale o ops includes cachefile reasons) (fun r => r.1 = false) := by
  have hloop1 := hun
  unfold IncludeUnchanged at hloop1
  have h5 := mtime_not_stale_self
  have h1 : ∀ p, OkRun o (ops.io.statPath p) (· = st p) := fun p => okRun_of_eq o (hfs.stat p) rfl
  have h2 : ∀ p, OkRun o (ops.fileHash p) (· = fileHash p) := fun p => okRun_of_eq o (hfs.fileHash p) rfl
  have h3 : ∀ p, OkRun o (ops.directoryHash p) (· = dirHash p) := fun p => okRun_of_eq o (hfs.dirHash p) rfl
  have h4 : ∀ m, OkRun o (ops.io.logDebug m) (fun _ => True) := fun m => okRun_of_eq o (hfs.log m) trivial
  clear hun
  unfold any_includes_stale
  repeat' walk_ok

/-! ## `_include_dependency!`: what is recorded -/

/-- `-1.0`, the mtime `_include_dependency!` records for a content-tracked dependency. -/
abbrev minusOneMtime : base.float.FV .f64 := JuliaLean.Promotion.Fl.ofBits 0xBFF0000000000000

theorem minusOne_not_recorded : include_mtime_recorded minusOneMtime = false := by decide +kernel

theorem include_dependency_tracked {Mod DepList : Type} (o : LOps X Y E D CI CF V)
    (ops : IncludeDependencyOps o Mod DepList) (dl : DepList) (mod : Mod) (p : Bytes) (tc pmd : Bool)
    (prev : Option Bytes) (path : Bytes) (stt : StatStruct) (sz : CacheU64) (isd : Bool)
    (names : List Bytes) (fh : U32)
    (hsrc : source_path o ops.sourcePath none = pure prev)
    (habs : prev = none → abspath o p = pure path)
    (hrel : ∀ q, prev = some q → ∃ dq jq, dirname o q = pure dq ∧ joinpath o [dq, p] = pure jq ∧
      normpath o jq = pure path)
    (hstat : o.fs.stat path = .ok stt) (hsz : ops.toUInt64 stt.size = pure sz)
    (hisdir : o.fs.isdir path = .ok isd) (hrd : ops.readDirectory path = pure names)
    (hfh : ops.hashFile path = pure fh) :
    _include_dependency_record o ops dl true mod p tc pmd =
      (withLock o (if tc then
          ops.recordDependency dl mod path sz (if isd then ops.hashBytes (ops.joinNames names) else fh)
            minusOneMtime
        else ops.recordDependency dl mod path (JInt.lit .u64 0) (JInt.lit .u32 0) stt.mtime)) >>=
        fun _ => pure (path, prev) := by
  unfold _include_dependency_record
  cases prev with
  | none =>
    simp only [hsrc, habs rfl, pure_bind, Bool.not_true, Bool.false_eq_true, ite_false, liftL, hstat, hisdir,
      hrd, hfh, hsz]
    cases tc <;> cases isd <;> simp
  | some q =>
    obtain ⟨dq, jq, h1, h2, h3⟩ := hrel q rfl
    simp only [hsrc, h1, h2, h3, pure_bind, Bool.not_true, Bool.false_eq_true, ite_false, liftL, hstat, hisdir,
      hrd, hfh, hsz]
    cases tc <;> cases isd <;> simp

theorem include_dependency_untracked {Mod DepList : Type} (o : LOps X Y E D CI CF V)
    (ops : IncludeDependencyOps o Mod DepList) (dl : DepList) (mod : Mod) (p : Bytes) (tc pmd : Bool)
    (prev : Option Bytes) (path : Bytes) (isf rd : Bool)
    (hsrc : source_path o ops.sourcePath none = pure prev)
    (habs : prev = none → abspath o p = pure path)
    (hrel : ∀ q, prev = some q → ∃ dq jq, dirname o q = pure dq ∧ joinpath o [dq, p] = pure jq ∧
      normpath o jq = pure path)
    (hisf : o.fs.isfile path = .ok isf) (hrd : ops.isReadable path = pure rd) :
    _include_dependency_record o ops dl false mod p tc pmd =
      if pmd = false ∧ isf = false then throwL o (ops.systemError (lit "opening file") path)
      else if pmd = true ∧ rd = false then throwL o (ops.systemError (lit "opening file or folder") path)
      else pure (path, prev) := by
  unfold _include_dependency_record
  cases prev with
  | none =>
    simp only [hsrc, habs rfl, pure_bind, liftL, hisf, hrd]
    cases pmd <;> cases isf <;> cases rd <;> simp [throwL]
  | some q =>
    obtain ⟨dq, jq, h1, h2, h3⟩ := hrel q rfl
    simp only [hsrc, h1, h2, h3, pure_bind, liftL, hisf, hrd]
    cases pmd <;> cases isf <;> cases rd <;> simp [throwL]

/-! ## `stale_cachefile`: a cache that passes every check is accepted -/

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem t_accept {Stream Mod Reason PrefValue : Type} (o : LOps X Y E D CI CF V)
    (ops : CacheStalenessOps o Stream Mod Reason PrefValue) (modkey : base.pkgid.PkgId) (wanted : CacheU128)
    (modspec : PkgLoadSpec) (cachefile : Bytes) (ig : Bool) (rf : CacheFlags)
    (reasons : Option (AMap Bytes base.loading.JInt64)) (sc vc spl : Bool)
    (ck : CacheU32) (hdr : ParsedCacheHeader) (pkg : base.pkgid.PkgId) (low : CacheU128) (mrest : List (base.pkgid.PkgId × CacheU128))
    (inc0 : CacheHeaderIncludes) (irest : List CacheHeaderIncludes)
    (root : base.pkgid.PkgId → Option Mod) (bid : Mod → CacheU128) (img : base.pkgid.PkgId → Bool) (loc : base.pkgid.PkgId → Option PkgLoadSpec)
    (sf : Bytes → Bytes → Bool) (idp : base.pkgid.PkgId → Bytes → Option base.pkgid.PkgId)
    (hopen : ∀ p, OkRun o (ops.io.openRead p) (fun _ => True))
    (hclose : ∀ st, OkRun o (ops.io.close st) (fun _ => True))
    (hlog : ∀ m, OkRun o (ops.io.logDebug m) (fun _ => True))
    (hvalid : ∀ st, OkRun o (isvalid_cache_header o ops.io st) (· = some ck))
    (hpos : ∀ st, OkRun o (ops.io.position st) (fun _ => True))
    (hread : ∀ st, OkRun o (ops.io.readU8 st) (fun _ => True))
    (hseek : ∀ st n, OkRun o (ops.io.seek st n) (fun _ => True))
    (hcov : ∀ f, OkRun o (match_cache_coverage o ops.coverage rf f) (· = true))
    (hreq8 : OkRun o (_cacheflag_to_uint8 o ops.coverage rf) (fun _ => True))
    (hact8 : ∀ b c, OkRun o (_cacheflag_to_uint8 o ops.coverage (CacheFlags_fromUInt8 b c)) (fun _ => True))
    (hmatch : ∀ a b, OkRun o (ops.jlMatchCacheFlags a b) (fun r => r.val ≠ 0))
    (hparse : ∀ st, OkRun o (parse_cache_header o ops.io st cachefile) (· = hdr))
    (hmods : hdr.modules = (pkg, low) :: mrest)
    (hpkg : pkg = modkey ∨ modkey = ⟨none, lit ""⟩)
    (hbid : wanted.val ≠ 0 → JInt.wrap .u128 (ck.val * 2 ^ 64 + low.val % 2 ^ 64) = wanted)
    (hsyn : sc = true → hdr.syntaxVersion = cache_edition modspec.julia_edition)
    (husep : OkRun o ops.usePkgimages (· = true))
    (hclone : ∀ t, OkRun o (check_clone_targets o ops.cloneTargets t) (· = none))
    (hocp : ∀ p, OkRun o (ops.validation.objectCachePath p) (fun _ => True))
    (hisf : ∀ p, OkRun o (ops.io.isFile p) (· = true))
    (hpre : ∀ p b, OkRun o (maybe_loaded_precompile o ops.registry p b) (· = none))
    (hroot : ∀ p, OkRun o (maybe_root_module o ops.registry p) (· = root p))
    (hmb : ∀ m, OkRun o (module_build_id o ops.registry m) (· = bid m))
    (himg : ∀ p, OkRun o (ops.inSysimage p) (· = img p))
    (hloc : ∀ p, OkRun o (ops.locatePackageLoadSpec p) (· = loc p))
    (hloop1 : ∀ x ∈ hdr.requiredModules, (root x.1 = none → (loc x.1).isSome = true) ∧
      ∀ m, root x.1 = some m →
        (root_module_key ops.registry m == x.1 && bid m == x.2 && (!ig || img x.1)) = false →
        ops.registry.sameModule m ops.coreModule = false ∧ (!ig && sc) = false ∧ (loc x.1).isSome = true)
    (hconc : OkRun o ops.concreteDependencies (· = []))
    (hinc : hdr.includes = inc0 :: irest)
    (hsame : ∀ a b, OkRun o (ops.io.sameFile a b) (· = sf a b))
    (hsrc : sc = true → sf inc0.filename modspec.path = true)
    (hid : ∀ k n, OkRun o (ops.identifyPackage k n) (· = idp k n))
    (hloop2 : ∀ x ∈ hdr.requiredPackages, idp x.1 x.2.name = some x.2)
    (hincs : ∀ r, OkRun o (any_includes_stale o ops.includes hdr.includes cachefile r) (·.1 = false))
    (hck : ∀ st oc r, OkRun o (checksums_invalid_io o ops.io st cachefile oc r spl) (·.1 = false))
    (hprefs : OkRun o (stale_prefs o ops.preferences hdr.preferencesBlob) (· = false)) :
    OkRun o (stale_cachefile o ops modkey wanted modspec cachefile ig rf reasons sc vc spl) (·.stale = false) := by
  unfold stale_cachefile
  repeat' walk_ok

/-! ## Helpers for the statements -/

theorem isvalid_ok {Stream : Type} (o : LOps X Y E D CI CF V) (io : CacheIOOps o Stream) (ck : CacheU32)
    (h : ∀ st, OkRun o (io.readVerifyHeader st) (fun hd => hd.status.val = 0 ∧
      base.int.and_int hd.flags JI_FLAG_PKGIMAGE ≠ JInt.lit .u32 0 ∧ hd.checksum = ck)) :
    ∀ st, OkRun o (isvalid_cache_header o io st) (· = some ck) := by
  intro st
  unfold isvalid_cache_header
  refine okRun_bind o (h st) fun hd hh => ?_
  obtain ⟨h1, h2, h3⟩ := hh
  have hc : ¬ ((hd.status.val == 0 && base.int.and_int hd.flags JI_FLAG_PKGIMAGE == JInt.lit .u32 0) = true) := by
    intro hc
    simp at hc
    first | exact h2 hc.2 | exact h2 (Subtype.ext hc.2) | exact h2 (Subtype.ext (hc h1))
  rw [if_neg hc]
  exact okRun_pure o (by simp [h1, h3])

theorem fromUInt8_chain : ∀ n : Fin 256,
    (chain8 (CacheFlags_fromUInt8 (JInt.wrap .u8 n.val) (JInt.wrap .i64 0))).isSome = true := by
  decide +kernel

theorem act8_ok (o : LOps X Y E D CI CF V) (cov : CoverageOps o) (err : LErr E)
    (hconv : ∀ x, cov.convertUInt8 x = conv8 o err x) (b : JInt .u8) (c : base.loading.JInt64) :
    OkRun o (_cacheflag_to_uint8 o cov (CacheFlags_fromUInt8 b c)) (fun _ => True) := by
  rw [cacheflag_chain o cov err hconv]
  have hr : 0 ≤ b.val ∧ b.val < 256 := by
    have h := b.property
    have hmin : IntTy.u8.min = 0 := by decide
    have hmax : IntTy.u8.max = 255 := by decide
    have h1 : 0 ≤ b.val := hmin ▸ h.1
    have h2 : b.val ≤ 255 := hmax ▸ h.2
    omega
  have hb : b = JInt.wrap .u8 ((⟨b.val.toNat, by omega⟩ : Fin 256).val : Int) := by
    apply Subtype.ext
    simp only [JInt.wrap]
    rw [Int.toNat_of_nonneg hr.1]
    exact (wrapInt_of_inRange _ _ b.property).symm
  have hs : (chain8 (CacheFlags_fromUInt8 b c)).isSome = true := by
    have h0 : chain8 (CacheFlags_fromUInt8 b c) = chain8 (CacheFlags_fromUInt8 b (JInt.wrap .i64 0)) := rfl
    rw [h0, hb]
    exact fromUInt8_chain _
  cases h : chain8 (CacheFlags_fromUInt8 b c) with
  | none => rw [h] at hs; cases hs
  | some v => exact okRun_pure o trivial

/-! ## Statements -/

/-- `any_includes_stale` returns false, and always returns, on include dependencies that are
unchanged: same recorded mtime (mtime-tracked), or same size and content hash (content-tracked).
The file-system callees are pure functions of the path, and `in_package_store` returns. -/
def AnyIncludesStalePrecise : Prop :=
  ∀ (X Y E D CI CF V Stream : Type) (o : LOps X Y E D CI CF V) (ops : IncludeStalenessOps o Stream)
    st fixup isFile fileHash dirHash, PureIncludeFs o ops st fixup isFile fileHash dirHash →
    (∀ p, OkRun o (in_package_store o p) (fun _ => True)) →
    ∀ includes cachefile reasons, (∀ inc ∈ includes, IncludeUnchanged o ops.io st fileHash dirHash inc) →
      OkRun o (any_includes_stale o ops includes cachefile reasons) (fun r => r.1 = false)

/-- What `_include_dependency!` records. The path is `abspath(_path)` without a current source
file, else `normpath(joinpath(dirname(prev), _path))`. While dependencies are tracked it records,
under `require_lock`, `(mod, path, UInt64(filesize(path)), hash, -1.0)` with `hash` the CRC of
`join(readdir(path))` for a directory and of the file otherwise (`track_content`), or
`(mod, path, 0, 0, mtime(path))`; the `-1.0` makes the checker compare size and hash instead of
mtime. Otherwise it records nothing and throws `SystemError` for a missing file (or, for
`path_may_be_dir`, an unreadable path). It returns `(path, prev)`. -/
def IncludeDependencyRecord : Prop :=
  ∀ (X Y E D CI CF V Mod DepList : Type) (o : LOps X Y E D CI CF V) (ops : IncludeDependencyOps o Mod DepList)
    (dl : DepList) (mod : Mod) (p : Bytes) (tc pmd : Bool) (prev : Option Bytes) (path : Bytes),
    source_path o ops.sourcePath none = pure prev →
    (prev = none → abspath o p = pure path) →
    (∀ q, prev = some q → ∃ dq jq, dirname o q = pure dq ∧ joinpath o [dq, p] = pure jq ∧
      normpath o jq = pure path) →
    (∀ (stt : StatStruct) (sz : CacheU64) (isd : Bool) (names : List Bytes) (fh : U32),
      o.fs.stat path = .ok stt → ops.toUInt64 stt.size = pure sz → o.fs.isdir path = .ok isd →
      ops.readDirectory path = pure names → ops.hashFile path = pure fh →
      _include_dependency_record o ops dl true mod p tc pmd =
        (withLock o (if tc then
            ops.recordDependency dl mod path sz (if isd then ops.hashBytes (ops.joinNames names) else fh)
              minusOneMtime
          else ops.recordDependency dl mod path (JInt.lit .u64 0) (JInt.lit .u32 0) stt.mtime)) >>=
          fun _ => pure (path, prev)) ∧
    (∀ isf rd, o.fs.isfile path = .ok isf → ops.isReadable path = pure rd →
      _include_dependency_record o ops dl false mod p tc pmd =
        if pmd = false ∧ isf = false then throwL o (ops.systemError (lit "opening file") path)
        else if pmd = true ∧ rd = false then throwL o (ops.systemError (lit "opening file or folder") path)
        else pure (path, prev)) ∧
    include_mtime_recorded minusOneMtime = false

/-- `_cacheflag_to_uint8` packs the flags as the `OOICCDDP` layout of the `CacheFlags` comment
(base/loading.jl:1955): pkgimages in bit 0, debug level in bits 1-2, bounds checking in bits 3-4,
inlining in bit 5 and optimization level in bits 6-7, for fields in `0:3`. -/
def CacheFlagsByteLayout : Prop :=
  ∀ (X Y E D CI CF V : Type) (o : LOps X Y E D CI CF V) (cov : CoverageOps o) (err : LErr E),
    (∀ x, cov.convertUInt8 x = conv8 o err x) → ∀ (b : Bool) (d c : Fin 4) (i : Bool) (p : Fin 4) cov' path,
    _cacheflag_to_uint8 o cov ⟨b, JInt.wrap .i64 d.val, JInt.wrap .i64 c.val, i, JInt.wrap .i64 p.val, cov', path⟩ =
      pure (JInt.wrap .u8 ((if b then 1 else 0) + 2 * d.val + 8 * c.val + 32 * (if i then 1 else 0) + 64 * p.val))

/-- When every check passes, `stale_cachefile` returns a fresh verdict, and it always returns. The
checks: the file opens; `jl_read_verify_header` accepts a package image with checksum `ck`; the
header's flag byte and the requested flags (fields in `0:3`) encode; `jl_match_cache_flags`
matches and the coverage matches; the header has a module list headed by the requested package
(or `PkgId("")` was requested) with the requested build id (or 0), and, with `stalecheck`, the
current syntax version; with a pkgimage, pkgimages are enabled, the CPU targets match and the
object file exists; each required module is either loaded with its recorded identity and build id
(and in the sysimage under `ignore_loaded`), or locatable (when it is not loaded, or loaded at
another version that `ignore_loaded` or `stalecheck = false` lets through, and it is not `Core`);
no concrete dependency is pinned; with `stalecheck`, the first include is the source path,
each required package resolves to the same package, and no include is stale; the checksums are
valid; the preferences are unchanged. `walk_ok` checks each branch of the body. -/
def StaleCachefileAccepts : Prop :=
  ∀ (X Y E D CI CF V Stream Mod Reason PrefValue : Type) (o : LOps X Y E D CI CF V)
    (ops : CacheStalenessOps o Stream Mod Reason PrefValue) (modkey : base.pkgid.PkgId) (wanted : CacheU128)
    (modspec : PkgLoadSpec) (cachefile : Bytes) (ig : Bool) (rf : CacheFlags)
    (reasons : Option (AMap Bytes base.loading.JInt64)) (sc vc spl : Bool)
    (ck : CacheU32) (hdr : ParsedCacheHeader) (pkg : base.pkgid.PkgId) (low : CacheU128)
    (mrest : List (base.pkgid.PkgId × CacheU128)) (inc0 : CacheHeaderIncludes) (irest : List CacheHeaderIncludes)
    (root : base.pkgid.PkgId → Option Mod) (bid : Mod → CacheU128) (img : base.pkgid.PkgId → Bool)
    (loc : base.pkgid.PkgId → Option PkgLoadSpec) (sf : Bytes → Bytes → Bool)
    (idp : base.pkgid.PkgId → Bytes → Option base.pkgid.PkgId) (err : LErr E),
    (∀ p, OkRun o (ops.io.openRead p) (fun _ => True)) →
    (∀ st, OkRun o (ops.io.close st) (fun _ => True)) →
    (∀ m, OkRun o (ops.io.logDebug m) (fun _ => True)) →
    (∀ st, OkRun o (ops.io.readVerifyHeader st) (fun hd => hd.status.val = 0 ∧
      base.int.and_int hd.flags JI_FLAG_PKGIMAGE ≠ JInt.lit .u32 0 ∧ hd.checksum = ck)) →
    (∀ st, OkRun o (ops.io.position st) (fun _ => True)) →
    (∀ st, OkRun o (ops.io.readU8 st) (fun _ => True)) →
    (∀ st n, OkRun o (ops.io.seek st n) (fun _ => True)) →
    (∀ x, ops.coverage.convertUInt8 x = conv8 o err x) →
    (0 ≤ rf.debug_level.val ∧ rf.debug_level.val < 4) → (0 ≤ rf.check_bounds.val ∧ rf.check_bounds.val < 4) →
    (0 ≤ rf.opt_level.val ∧ rf.opt_level.val < 4) →
    (∀ f, OkRun o (match_cache_coverage o ops.coverage rf f) (· = true)) →
    (∀ a b, OkRun o (ops.jlMatchCacheFlags a b) (fun r => r.val ≠ 0)) →
    (∀ st, OkRun o (parse_cache_header o ops.io st cachefile) (· = hdr)) →
    hdr.modules = (pkg, low) :: mrest →
    (pkg = modkey ∨ modkey = ⟨none, lit ""⟩) →
    (wanted.val ≠ 0 → JInt.wrap .u128 (ck.val * 2 ^ 64 + low.val % 2 ^ 64) = wanted) →
    (sc = true → hdr.syntaxVersion = cache_edition modspec.julia_edition) →
    OkRun o ops.usePkgimages (· = true) →
    (∀ t, OkRun o (check_clone_targets o ops.cloneTargets t) (· = none)) →
    (∀ p, OkRun o (ops.validation.objectCachePath p) (fun _ => True)) →
    (∀ p, OkRun o (ops.io.isFile p) (· = true)) →
    (∀ p b, OkRun o (maybe_loaded_precompile o ops.registry p b) (· = none)) →
    (∀ p, OkRun o (maybe_root_module o ops.registry p) (· = root p)) →
    (∀ m, OkRun o (module_build_id o ops.registry m) (· = bid m)) →
    (∀ p, OkRun o (ops.inSysimage p) (· = img p)) →
    (∀ p, OkRun o (ops.locatePackageLoadSpec p) (· = loc p)) →
    (∀ x ∈ hdr.requiredModules, (root x.1 = none → (loc x.1).isSome = true) ∧
      ∀ m, root x.1 = some m →
        (root_module_key ops.registry m = x.1 ∧ bid m = x.2 ∧ (ig = true → img x.1 = true)) ∨
        (ops.registry.sameModule m ops.coreModule = false ∧ (ig = true ∨ sc = false) ∧ (loc x.1).isSome = true)) →
    OkRun o ops.concreteDependencies (· = []) →
    hdr.includes = inc0 :: irest →
    (∀ a b, OkRun o (ops.io.sameFile a b) (· = sf a b)) →
    (sc = true → sf inc0.filename modspec.path = true) →
    (∀ k n, OkRun o (ops.identifyPackage k n) (· = idp k n)) →
    (∀ x ∈ hdr.requiredPackages, idp x.1 x.2.name = some x.2) →
    (∀ r, OkRun o (any_includes_stale o ops.includes hdr.includes cachefile r) (·.1 = false)) →
    (∀ st oc r, OkRun o (checksums_invalid_io o ops.io st cachefile oc r spl) (·.1 = false)) →
    OkRun o (stale_prefs o ops.preferences hdr.preferencesBlob) (· = false) →
    OkRun o (stale_cachefile o ops modkey wanted modspec cachefile ig rf reasons sc vc spl) (·.stale = false)

/-- `stale_cachefile(modspec, cachefile; ...)` accepts every cache that passes the checks, whatever
package and build id the cache holds: it forwards `PkgId("")` and `UInt128(0)`, which turn those two
checks off, with `stalecheck = true`. The requested flags are the given ones, or `CacheFlags()`
(the model of `CacheFlags_withOptions`) when none are given. -/
def StaleCachefileModspecAccepts : Prop :=
  ∀ (X Y E D CI CF V Stream Mod Reason PrefValue : Type) (o : LOps X Y E D CI CF V)
    (ops : CacheStalenessOps o Stream Mod Reason PrefValue)
    (modspec : PkgLoadSpec) (cachefile : Bytes) (ig : Bool) (rf : Option CacheFlags) (f0 : CacheFlags)
    (reasons : Option (AMap Bytes base.loading.JInt64)) (vc : Bool)
    (ck : CacheU32) (hdr : ParsedCacheHeader) (pkg : base.pkgid.PkgId) (low : CacheU128)
    (mrest : List (base.pkgid.PkgId × CacheU128)) (inc0 : CacheHeaderIncludes) (irest : List CacheHeaderIncludes)
    (root : base.pkgid.PkgId → Option Mod) (bid : Mod → CacheU128) (img : base.pkgid.PkgId → Bool)
    (loc : base.pkgid.PkgId → Option PkgLoadSpec) (sf : Bytes → Bytes → Bool)
    (idp : base.pkgid.PkgId → Bytes → Option base.pkgid.PkgId) (err : LErr E),
    (∀ f, rf = some f → f = f0) →
    (rf = none → OkRun o (CacheFlags_withOptions o ops.runtimeFlags ops.coverage) (· = f0)) →
    (∀ p, OkRun o (ops.io.openRead p) (fun _ => True)) →
    (∀ st, OkRun o (ops.io.close st) (fun _ => True)) →
    (∀ m, OkRun o (ops.io.logDebug m) (fun _ => True)) →
    (∀ st, OkRun o (ops.io.readVerifyHeader st) (fun hd => hd.status.val = 0 ∧
      base.int.and_int hd.flags JI_FLAG_PKGIMAGE ≠ JInt.lit .u32 0 ∧ hd.checksum = ck)) →
    (∀ st, OkRun o (ops.io.position st) (fun _ => True)) →
    (∀ st, OkRun o (ops.io.readU8 st) (fun _ => True)) →
    (∀ st n, OkRun o (ops.io.seek st n) (fun _ => True)) →
    (∀ x, ops.coverage.convertUInt8 x = conv8 o err x) →
    (0 ≤ f0.debug_level.val ∧ f0.debug_level.val < 4) → (0 ≤ f0.check_bounds.val ∧ f0.check_bounds.val < 4) →
    (0 ≤ f0.opt_level.val ∧ f0.opt_level.val < 4) →
    (∀ f, OkRun o (match_cache_coverage o ops.coverage f0 f) (· = true)) →
    (∀ a b, OkRun o (ops.jlMatchCacheFlags a b) (fun r => r.val ≠ 0)) →
    (∀ st, OkRun o (parse_cache_header o ops.io st cachefile) (· = hdr)) →
    hdr.modules = (pkg, low) :: mrest →
    hdr.syntaxVersion = cache_edition modspec.julia_edition →
    OkRun o ops.usePkgimages (· = true) →
    (∀ t, OkRun o (check_clone_targets o ops.cloneTargets t) (· = none)) →
    (∀ p, OkRun o (ops.validation.objectCachePath p) (fun _ => True)) →
    (∀ p, OkRun o (ops.io.isFile p) (· = true)) →
    (∀ p b, OkRun o (maybe_loaded_precompile o ops.registry p b) (· = none)) →
    (∀ p, OkRun o (maybe_root_module o ops.registry p) (· = root p)) →
    (∀ m, OkRun o (module_build_id o ops.registry m) (· = bid m)) →
    (∀ p, OkRun o (ops.inSysimage p) (· = img p)) →
    (∀ p, OkRun o (ops.locatePackageLoadSpec p) (· = loc p)) →
    (∀ x ∈ hdr.requiredModules, (root x.1 = none → (loc x.1).isSome = true) ∧
      ∀ m, root x.1 = some m →
        (root_module_key ops.registry m = x.1 ∧ bid m = x.2 ∧ (ig = true → img x.1 = true)) ∨
        (ops.registry.sameModule m ops.coreModule = false ∧ ig = true ∧ (loc x.1).isSome = true)) →
    OkRun o ops.concreteDependencies (· = []) →
    hdr.includes = inc0 :: irest →
    (∀ a b, OkRun o (ops.io.sameFile a b) (· = sf a b)) →
    sf inc0.filename modspec.path = true →
    (∀ k n, OkRun o (ops.identifyPackage k n) (· = idp k n)) →
    (∀ x ∈ hdr.requiredPackages, idp x.1 x.2.name = some x.2) →
    (∀ r, OkRun o (any_includes_stale o ops.includes hdr.includes cachefile r) (·.1 = false)) →
    (∀ st oc r, OkRun o (checksums_invalid_io o ops.io st cachefile oc r true) (·.1 = false)) →
    OkRun o (stale_prefs o ops.preferences hdr.preferencesBlob) (· = false) →
    OkRun o (stale_cachefile_modspec o ops modspec cachefile ig rf reasons vc) (·.stale = false)

/-! ## Proofs -/

theorem anyIncludesStalePrecise_proven : AnyIncludesStalePrecise := by
  intro X Y E D CI CF V Stream o ops st fixup isFile fileHash dirHash hfs hstore includes cachefile reasons hun
  exact precise_ok o ops st fixup isFile fileHash dirHash hfs hstore includes cachefile reasons hun

theorem includeDependencyRecord_proven : IncludeDependencyRecord := by
  intro X Y E D CI CF V Mod DepList o ops dl mod p tc pmd prev path hsrc habs hrel
  refine ⟨fun stt sz isd names fh h1 h2 h3 h4 h5 =>
      include_dependency_tracked o ops dl mod p tc pmd prev path stt sz isd names fh hsrc habs hrel h1 h2 h3 h4 h5,
    fun isf rd h1 h2 => include_dependency_untracked o ops dl mod p tc pmd prev path isf rd hsrc habs hrel h1 h2,
    minusOne_not_recorded⟩

theorem cacheFlagsByteLayout_proven : CacheFlagsByteLayout := by
  intro X Y E D CI CF V o cov err hconv b d c i p cov' path
  rw [cacheflag_chain o cov err hconv]
  have h : chain8 ⟨b, JInt.wrap .i64 d.val, JInt.wrap .i64 c.val, i, JInt.wrap .i64 p.val, cov', path⟩ =
      chain8 (flagsOf b d c i p) := rfl
  rw [h, (layout_table b d c i p).1]
  rfl

theorem req8_ok (o : LOps X Y E D CI CF V) (cov : CoverageOps o) (err : LErr E)
    (hconv : ∀ x, cov.convertUInt8 x = conv8 o err x) (rf : CacheFlags)
    (hd : 0 ≤ rf.debug_level.val ∧ rf.debug_level.val < 4) (hc : 0 ≤ rf.check_bounds.val ∧ rf.check_bounds.val < 4)
    (hp : 0 ≤ rf.opt_level.val ∧ rf.opt_level.val < 4) :
    OkRun o (_cacheflag_to_uint8 o cov rf) (fun _ => True) := by
  obtain ⟨byte, hb, -⟩ := cacheflag_roundtrip o cov err hconv rf hd hc hp (JInt.wrap .i64 0)
  exact okRun_of_eq o hb trivial

theorem staleCachefileAccepts_proven : StaleCachefileAccepts := by
  intro X Y E D CI CF V Stream Mod Reason PrefValue o ops modkey wanted modspec cachefile ig rf reasons sc vc spl
    ck hdr pkg low mrest inc0 irest root bid img loc sf idp err hopen hclose hlog hver hpos hread hseek hconv
    hd hc hp hcov hmatch hparse hmods hpkg hbid hsyn husep hclone hocp hisf hpre hroot hmb himg hloc hdeps hconc
    hinc hsame hsrc hid hreqp hincs hck hprefs
  refine t_accept o ops modkey wanted modspec cachefile ig rf reasons sc vc spl ck hdr pkg low mrest inc0 irest
    root bid img loc sf idp hopen hclose hlog (isvalid_ok o ops.io ck hver) hpos hread hseek hcov
    (req8_ok o ops.coverage err hconv rf hd hc hp) (act8_ok o ops.coverage err hconv) hmatch hparse hmods hpkg hbid
    hsyn husep hclone hocp hisf hpre hroot hmb himg hloc ?_ hconc hinc hsame hsrc hid hreqp hincs hck hprefs
  intro x hx
  refine ⟨(hdeps x hx).1, fun m hm hf => ?_⟩
  have hb : ∀ a b : Bool, (a && b) = false ↔ (a = true → b = false) := by decide
  rcases (hdeps x hx).2 m hm with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exfalso
    simp only [hb, beq_iff_eq] at hf
    cases hig : ig <;> cases himgx : img x.1 <;> simp_all
  · refine ⟨h1, ?_, h3⟩
    cases ig <;> cases sc <;> simp_all

theorem staleCachefileModspecAccepts_proven : StaleCachefileModspecAccepts := by
  intro X Y E D CI CF V Stream Mod Reason PrefValue o ops modspec cachefile ig rf f0 reasons vc
    ck hdr pkg low mrest inc0 irest root bid img loc sf idp err hsome hnone hopen hclose hlog hver hpos hread hseek
    hconv hd hc hp hcov hmatch hparse hmods hsyn husep hclone hocp hisf hpre hroot hmb himg hloc hdeps hconc
    hinc hsame hsrc hid hreqp hincs hck hprefs
  have hacc : OkRun o (stale_cachefile o ops ⟨none, lit ""⟩ (JInt.wrap .u128 0) modspec cachefile ig f0 reasons
      true vc true) (·.stale = false) :=
    staleCachefileAccepts_proven X Y E D CI CF V Stream Mod Reason PrefValue o ops ⟨none, lit ""⟩ (JInt.wrap .u128 0)
      modspec cachefile ig f0 reasons true vc true ck hdr pkg low mrest inc0 irest root bid img loc sf idp err
      hopen hclose hlog hver hpos hread hseek hconv hd hc hp hcov hmatch hparse hmods (Or.inr rfl)
      (fun h => (h (by decide)).elim) (fun _ => hsyn) husep hclone hocp hisf hpre hroot hmb himg hloc
      (fun x hx => ⟨(hdeps x hx).1, fun m hm => by
        rcases (hdeps x hx).2 m hm with h | ⟨h1, h2, h3⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, Or.inl h2, h3⟩⟩)
      hconc hinc hsame (fun _ => hsrc) hid hreqp hincs hck hprefs
  unfold stale_cachefile_modspec
  cases rf with
  | some f =>
    have := hsome f rfl
    subst this
    simpa using hacc
  | none =>
    exact okRun_bind o (hnone rfl) fun f hf => by subst hf; exact hacc

open JuliaLean.Registry

def acceptEntries : List Entry := [
  { id := "compiler-loading-any-includes-stale-precise", juliaFile := "base/loading.jl"
    juliaFns := ["any_includes_stale(includes::Vector{CacheHeaderIncludes}, cachefile::String, reasons)"]
    statement := "any_includes_stale always returns, and returns false, on unchanged include dependencies: same recorded mtime (mtime-tracked), or same size and content hash (content-tracked)."
    source := "base/loading.jl:4802-4857 (identical inputs must not be reported stale)"
    status := .proven, prop := ``AnyIncludesStalePrecise, thm := some ``anyIncludesStalePrecise_proven
    notes := "OkRun: every run returns normally, so a version that throws or loops on unchanged includes fails it. File-system callees are pure functions of the path and in_package_store returns." },
  { id := "compiler-loading-include-dependency-record", juliaFile := "base/loading.jl"
    juliaFns := ["_include_dependency!(dep_list, track_dependencies, mod, _path, track_content, path_may_be_dir)"]
    statement := "_include_dependency! resolves the path against the current source file, records (mod, path, filesize, CRC of the file or of join(readdir(dir)), -1.0) with track_content and (mod, path, 0, 0, mtime) without, under require_lock, while tracking; otherwise it records nothing and throws SystemError for a missing file or unreadable path. The -1.0 sentinel is not a recorded mtime, so the checker compares size and hash."
    source := "base/loading.jl:2682-2709, 4822 (ftime_req >= 0.0)"
    status := .proven, prop := ``IncludeDependencyRecord, thm := some ``includeDependencyRecord_proven
    notes := "The model stats the path once before hashing; the source hashes first and then calls filesize(path) and mtime(path), which stat again. The two differ only if the file changes during the call." },
  { id := "compiler-loading-cacheflags-byte-layout", juliaFile := "base/loading.jl"
    juliaFns := ["_cacheflag_to_uint8(cf::CacheFlags)"]
    statement := "For fields in 0:3, _cacheflag_to_uint8 returns pkgimages + 2*debug_level + 8*check_bounds + 32*inline + 64*opt_level, the OOICCDDP layout of the CacheFlags comment."
    source := "base/loading.jl:1955, 2012-2020"
    status := .proven, prop := ``CacheFlagsByteLayout, thm := some ``cacheFlagsByteLayout_proven },
  { id := "compiler-loading-stale-cachefile-accepts", juliaFile := "base/loading.jl"
    juliaFns := ["stale_cachefile(modkey::PkgId, build_id::UInt128, modspec::PkgLoadSpec, cachefile::String)",
      "isvalid_cache_header(f::IOStream)", "_cacheflag_to_uint8(cf::CacheFlags)"]
    statement := "When every check passes (header, flags, coverage, package id, build id, syntax version, pkgimage, each required module loaded at its recorded identity and build id or locatable, no pinned concrete dependency, source path, package identities, includes, checksums, preferences), stale_cachefile always returns a fresh verdict."
    source := "base/loading.jl:4919-5139 (a cache whose recorded inputs all match is not reported stale)"
    status := .proven, prop := ``StaleCachefileAccepts, thm := some ``staleCachefileAccepts_proven
    notes := "OkRun: the always-stale and always-throwing functions fail it. Callees that are model functions with their own rows (parse_cache_header, match_cache_coverage, check_clone_targets, any_includes_stale, checksums_invalid_io, stale_prefs, maybe_root_module, maybe_loaded_precompile) are hypotheses. Not covered: a pinned concrete dependency (the loop is assumed empty), a source path accepted only after fixup_stdlib_path, a dependency already in loaded_precompiles with stalecheck=false, and a coverage mismatch accepted as a plain cache." },
  { id := "compiler-loading-stale-cachefile-modspec-accepts", juliaFile := "base/loading.jl"
    juliaFns := ["stale_cachefile(modspec::PkgLoadSpec, cachefile::String)"]
    statement := "stale_cachefile(modspec, cachefile) accepts every cache that passes the checks whatever package and build id it holds, with stalecheck on and the given flags or CacheFlags(): it forwards PkgId(\"\") and UInt128(0)."
    source := "base/loading.jl:4916-4918, 5004 (modkey != PkgId(\"\")), 5010 (build_id != UInt128(0))"
    status := .proven, prop := ``StaleCachefileModspecAccepts, thm := some ``staleCachefileModspecAccepts_proven
    notes := "Derived from compiler-loading-stale-cachefile-accepts with no package-id or build-id hypothesis; PkgId(\"\") is now the concrete ⟨none, \"\"⟩ in the model rather than an abstract operation." }
]

end
end JuliaLean.Proofs.base.loading.Cachefile
