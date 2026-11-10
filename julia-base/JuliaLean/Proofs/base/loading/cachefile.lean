import JuliaLean.base.loading
import JuliaLean.Registry.Types

/-!
Properties of the cache-file validation in `base/loading.jl` (pinned master f755f49a9e41):
`stale_cachefile`, `any_includes_stale`, the `CacheFlags` byte encoding, and the small
helpers they call.

The model's callees are abstract operations in the `LM` monad. A property says what every
successful run returns (`AllOk`), under named hypotheses about what the callees return. The
`walk_step` tactic proves such a statement by following the function body: binds, `if`s,
`match`es, `for` loops (whose early returns are rejections) and the `__do_jp` join points the
`do` elaborator introduces.
-/

set_option linter.unusedSimpArgs false
namespace JuliaLean.Proofs.base.loading.Cachefile
open JuliaLean JuliaLean.base.loading

variable {X Y E D CI CF V : Type}

/-- Every successful run of `x` returns a value satisfying `Q`. -/
def AllOk (o : LOps X Y E D CI CF V) {α : Type} (x : LM o α) (Q : α → Prop) : Prop :=
  ∀ s a s', (ExceptT.run x).run s = some (.ok a, s') → Q a

theorem allOk_pure (o : LOps X Y E D CI CF V) {α : Type} {a : α} {Q : α → Prop} (h : Q a) :
    AllOk o (pure a) Q := by
  intro s b s' hr
  simp [ExceptT.run, pure, ExceptT.pure, ExceptT.mk, StateT.run, StateT.pure] at hr
  obtain ⟨rfl, -⟩ := hr
  exact h

theorem run_bind (o : LOps X Y E D CI CF V) {α β : Type} (m : LM o α) (k : α → LM o β) (s) :
    (ExceptT.run (m >>= k)).run s = ((ExceptT.run m).run s).bind fun p => match p.1 with
      | .ok a => (ExceptT.run (k a)).run p.2
      | .error e => some (.error e, p.2) := by
  simp only [bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.run, StateT.bind, ExceptT.bindCont]
  cases (m s) with
  | none => rfl
  | some p => obtain ⟨r, s1⟩ := p; cases r <;> rfl

theorem allOk_bind (o : LOps X Y E D CI CF V) {α β : Type} {m : LM o α} {k : α → LM o β}
    {P : α → Prop} {Q : β → Prop} (hm : AllOk o m P) (hk : ∀ a, P a → AllOk o (k a) Q) :
    AllOk o (m >>= k) Q := by
  intro s b s' hr
  rw [run_bind] at hr
  cases h1 : (ExceptT.run m).run s with
  | none => simp [h1] at hr
  | some p =>
    obtain ⟨r, s1⟩ := p
    cases r with
    | error e => simp [h1] at hr
    | ok a =>
      simp only [h1, Option.bind] at hr
      exact hk a (hm s a s1 h1) s1 b s' hr

theorem allOk_throw (o : LOps X Y E D CI CF V) {α : Type} {e : LErr E} {Q : α → Prop} :
    AllOk o (throw e) Q := by
  intro s b s' hr
  simp [ExceptT.run, throw, throwThe, MonadExceptOf.throw, ExceptT.mk, StateT.run, StateT.pure, pure] at hr

/-- Every run of `x`, from any state, returns normally (no exception, no divergence) with a value
satisfying `Q`. Unlike `AllOk`, a function that throws or diverges does not satisfy it. -/
def OkRun (o : LOps X Y E D CI CF V) {α : Type} (x : LM o α) (Q : α → Prop) : Prop :=
  ∀ s, ∃ a s', (ExceptT.run x).run s = some (.ok a, s') ∧ Q a

theorem okRun_pure (o : LOps X Y E D CI CF V) {α : Type} {a : α} {Q : α → Prop} (h : Q a) :
    OkRun o (pure a) Q := fun s => ⟨a, s, rfl, h⟩

theorem okRun_bind (o : LOps X Y E D CI CF V) {α β : Type} {m : LM o α} {k : α → LM o β}
    {P : α → Prop} {Q : β → Prop} (hm : OkRun o m P) (hk : ∀ a, P a → OkRun o (k a) Q) :
    OkRun o (m >>= k) Q := by
  intro s
  obtain ⟨a, s1, h1, hp⟩ := hm s
  obtain ⟨b, s2, h2, hq⟩ := hk a hp s1
  refine ⟨b, s2, ?_, hq⟩
  rw [run_bind, h1]
  exact h2

theorem okRun_bind' (o : LOps X Y E D CI CF V) {α β : Type} {m : LM o α} {k : α → LM o β}
    {Q : β → Prop} (hm : OkRun o m (fun a => OkRun o (k a) Q)) : OkRun o (m >>= k) Q :=
  okRun_bind o hm fun _ h => h

theorem okRun_mono (o : LOps X Y E D CI CF V) {α : Type} {m : LM o α} {P Q : α → Prop}
    (h : OkRun o m P) (hpq : ∀ a, P a → Q a) : OkRun o m Q := by
  intro s
  obtain ⟨a, s', h1, hp⟩ := h s
  exact ⟨a, s', h1, hpq a hp⟩

theorem okRun_ite (o : LOps X Y E D CI CF V) {α : Type} {c : Prop} [Decidable c] {t e : LM o α}
    {Q : α → Prop} (ht : c → OkRun o t Q) (he : ¬c → OkRun o e Q) : OkRun o (if c then t else e) Q := by
  by_cases h : c
  · rw [if_pos h]; exact ht h
  · rw [if_neg h]; exact he h

theorem okRun_throw (o : LOps X Y E D CI CF V) {α : Type} {e : LErr E} {Q : α → Prop} (h : False) :
    OkRun o (throw e) Q := h.elim

theorem okRun_throwL (o : LOps X Y E D CI CF V) {α : Type} {e : LErr E} {Q : α → Prop} (h : False) :
    OkRun o (throwL o e) Q := h.elim

theorem okRun_allOk (o : LOps X Y E D CI CF V) {α : Type} {m : LM o α} {Q : α → Prop}
    (h : OkRun o m Q) : AllOk o m Q := by
  intro s a s' hr
  obtain ⟨b, s'', h1, hq⟩ := h s
  rw [h1] at hr
  cases hr
  exact hq

end JuliaLean.Proofs.base.loading.Cachefile

namespace JuliaLean.Proofs.base.loading.Cachefile
open JuliaLean JuliaLean.base.loading
variable {X Y E D CI CF V : Type}

theorem allOk_forIn {σ β : Type} (o : LOps X Y E D CI CF V) (xs : List σ) (init : β)
    (f : σ → β → LM o (ForInStep β)) (Inv Done : β → Prop) (Good : σ → Prop)
    (h0 : Inv init)
    (hf : ∀ x ∈ xs, ∀ b, Inv b → AllOk o (f x b) (fun r => match r with
      | .done b' => Done b'
      | .yield b' => Good x ∧ Inv b')) :
    AllOk o (forIn xs init f) (fun r => Done r ∨ ((∀ x ∈ xs, Good x) ∧ Inv r)) := by
  induction xs generalizing init with
  | nil =>
    simp only [List.forIn_nil]
    exact allOk_pure o (Or.inr ⟨by simp, h0⟩)
  | cons x rest ih =>
    simp only [List.forIn_cons]
    refine allOk_bind o (hf x (by simp) init h0) ?_
    intro r hr
    cases r with
    | done b' => exact allOk_pure o (Or.inl hr)
    | yield b' =>
      obtain ⟨hg, hi⟩ := hr
      intro s a s' hrun
      rcases ih b' hi (fun y hy => hf y (by simp [hy])) s a s' hrun with hd | ⟨hall, hinv⟩
      · exact Or.inl hd
      · refine Or.inr ⟨?_, hinv⟩
        intro y hy
        simp at hy
        rcases hy with rfl | hy
        · exact hg
        · exact hall y hy

structure PureIncludeFs (o : LOps X Y E D CI CF V) {Stream : Type} (ops : IncludeStalenessOps o Stream)
    (st : Bytes → CacheFileStat) (fixup : Bytes → Bytes) (isFile : Bytes → Bool)
    (fileHash dirHash : Bytes → CacheU32) : Prop where
  stat : ∀ p, ops.io.statPath p = pure (st p)
  fixup : ∀ p, ops.fixupStdlibPath p = pure (fixup p)
  isFile : ∀ p, ops.io.isFile p = pure (isFile p)
  fileHash : ∀ p, ops.fileHash p = pure (fileHash p)
  dirHash : ∀ p, ops.directoryHash p = pure (dirHash p)
  log : ∀ m, ops.io.logDebug m = pure ()

theorem allOk_any (o : LOps X Y E D CI CF V) {α : Type} (m : LM o α) : AllOk o m (fun _ => True) :=
  fun _ _ _ _ => trivial

theorem mtime_not_stale_self (x : JuliaLean.base.float.FV .f64) (h : include_mtime_recorded x = true) :
    include_mtime_is_stale x x = false := by
  have hn : x.isnan = false := by
    revert h
    simp only [include_mtime_recorded, JuliaLean.base.float.le_float, JuliaLean.C.jlLeFloat, JuliaLean.Promotion.Fl.le,
      JuliaLean.Promotion.Fl.lt, JuliaLean.Promotion.Fl.eq]
    cases x.isnan <;> simp
  simp [include_mtime_is_stale, JuliaLean.base.float.eq_float, JuliaLean.C.jlEqFloat, JuliaLean.Promotion.Fl.eq, hn]

def IncludeUnchanged {Stream : Type} (o : LOps X Y E D CI CF V) (io : CacheIOOps o Stream)
    (st : Bytes → CacheFileStat) (fileHash dirHash : Bytes → CacheU32) (inc : CacheHeaderIncludes) : Prop :=
  ¬ (lit "@depot" ++ io.pathsep).isPrefixOf inc.filename = true ∧ (st inc.filename).isPath = true ∧
  (include_mtime_recorded inc.mtime = true → (st inc.filename).mtime = inc.mtime) ∧
  (include_mtime_recorded inc.mtime = false → (st inc.filename).size.val = inc.fsize.val ∧
    (if (st inc.filename).isDirectory then dirHash inc.filename else fileHash inc.filename) = inc.hash)

theorem precise (o : LOps X Y E D CI CF V) {Stream : Type} (ops : IncludeStalenessOps o Stream)
    st fixup isFile fileHash dirHash (hfs : PureIncludeFs o ops st fixup isFile fileHash dirHash)
    (includes : List CacheHeaderIncludes) (cachefile : Bytes) (reasons : Option (AMap Bytes base.loading.JInt64))
    (hun : ∀ inc ∈ includes, IncludeUnchanged o ops.io st fileHash dirHash inc) :
    AllOk o (any_includes_stale o ops includes cachefile reasons) (fun r => r.1 = false) := by
  unfold any_includes_stale
  refine allOk_bind o (allOk_forIn o includes _ _ (fun b => b.1 = none) (fun _ => False) (fun _ => True) rfl ?_) ?_
  · intro inc hmem b hb
    obtain ⟨hdepot, hpath, hmt, hsz⟩ := hun inc hmem
    simp only [hfs.stat, hfs.log, hfs.fileHash, hfs.dirHash, pure_bind, hdepot, hpath, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true]
    by_cases hr : include_mtime_recorded inc.mtime = true
    · have hm := hmt hr
      simp only [hr, hm, mtime_not_stale_self _ hr, ite_true, ite_false, Bool.false_eq_true]
      exact allOk_pure o ⟨trivial, rfl⟩
    · have hr' : include_mtime_recorded inc.mtime = false := by simpa using hr
      obtain ⟨hs, hh⟩ := hsz hr'
      simp only [hr', hs, bne_self_eq_false, ite_false, Bool.false_eq_true]
      cases hdir : (st inc.filename).isDirectory <;> simp only [hdir, ite_true, ite_false, Bool.false_eq_true] at hh ⊢
      · split
        · refine allOk_bind o (allOk_any o _) fun trusted _ => ?_
          split
          · exact allOk_pure o ⟨trivial, rfl⟩
          · simp only [hfs.fileHash, pure_bind, hh, bne_self_eq_false, ite_false, Bool.false_eq_true]
            exact allOk_pure o ⟨trivial, rfl⟩
        · simp only [hfs.fileHash, pure_bind, hh, bne_self_eq_false, ite_false, Bool.false_eq_true]
          exact allOk_pure o ⟨trivial, rfl⟩
      · simp only [hfs.dirHash, pure_bind, hh, bne_self_eq_false, ite_false, Bool.false_eq_true, Bool.not_true,
          Bool.false_and]
        exact allOk_pure o ⟨trivial, rfl⟩
  · intro b hb
    rcases hb with hb | ⟨-, hb⟩
    · exact hb.elim
    · simp only [hb]
      exact allOk_pure o rfl

def IncludeAccepted {Stream : Type} (o : LOps X Y E D CI CF V) (io : CacheIOOps o Stream)
    (st : Bytes → CacheFileStat) (fixup : Bytes → Bytes) (isFile : Bytes → Bool)
    (fileHash dirHash : Bytes → CacheU32) (Pre : Bytes → Bytes → Prop) (InStore : Bytes → Prop)
    (inc : CacheHeaderIncludes) : Prop :=
  ¬ (lit "@depot" ++ io.pathsep).isPrefixOf inc.filename = true ∧
  (((st inc.filename).isPath = false ∧ fixup inc.filename ≠ inc.filename ∧ isFile (fixup inc.filename) = true ∧
      Pre (fixup inc.filename) o.STDLIB) ∨
   ((st inc.filename).isPath = true ∧
    (include_mtime_recorded inc.mtime = true → include_mtime_is_stale (st inc.filename).mtime inc.mtime = false) ∧
    (include_mtime_recorded inc.mtime = false → (st inc.filename).size.val = inc.fsize.val ∧
      ((((st inc.filename).isDirectory = false ∧
          base.int.and_int (io.fileMode (st inc.filename)) (JInt.wrap .u64 0o222) = JInt.wrap .u64 0) ∧
          InStore inc.filename) ∨
        (if (st inc.filename).isDirectory then dirHash inc.filename else fileHash inc.filename) = inc.hash))))

macro "hash_finish" : tactic => `(tactic| (
  split
  · exact allOk_pure _ ⟨_, rfl, rfl⟩
  · rename_i hne
    refine allOk_pure _ ⟨?_, rfl⟩
    unfold IncludeAccepted
    refine ⟨‹_›, Or.inr ⟨‹_›, fun h => by simp_all, fun _ => ⟨‹_›, Or.inr ?_⟩⟩⟩
    simp_all))

theorem sound (o : LOps X Y E D CI CF V) {Stream : Type} (ops : IncludeStalenessOps o Stream)
    st fixup isFile fileHash dirHash (hfs : PureIncludeFs o ops st fixup isFile fileHash dirHash)
    (Pre : Bytes → Bytes → Prop) (InStore : Bytes → Prop)
    (hsw : ∀ a b, AllOk o (startswith o a b) (fun r => r = true → Pre a b))
    (hstore : ∀ p, AllOk o (in_package_store o p) (fun r => r = true → InStore p))
    (includes : List CacheHeaderIncludes) (cachefile : Bytes) (reasons : Option (AMap Bytes base.loading.JInt64)) :
    AllOk o (any_includes_stale o ops includes cachefile reasons)
      (fun r => r.1 = false → ∀ inc ∈ includes, IncludeAccepted o ops.io st fixup isFile fileHash dirHash Pre InStore inc) := by
  unfold any_includes_stale
  refine allOk_bind o (allOk_forIn o includes _ _ (fun b => b.1 = none) (fun b => ∃ r, b.1 = some r ∧ r.1 = true)
    (IncludeAccepted o ops.io st fixup isFile fileHash dirHash Pre InStore) rfl ?_) ?_
  · intro inc _ b hb
    simp only [hfs.stat, hfs.log, hfs.fileHash, hfs.dirHash, hfs.fixup, hfs.isFile, pure_bind]
    split
    · exact allOk_pure o ⟨_, rfl, rfl⟩
    · rename_i hdepot
      split
      · rename_i hnp
        have hnp' : (st inc.filename).isPath = false := by simpa using hnp
        split
        · rename_i hne
          refine allOk_bind o (P := fun std => std = true → isFile (fixup inc.filename) = true ∧
              Pre (fixup inc.filename) o.STDLIB) ?_ fun std hstdP => ?_
          · split
            · rename_i hc; exact fun s r s' h hr => ⟨hc, hsw _ _ s r s' h hr⟩
            · exact allOk_pure o (fun h => by simp at h)
          split
          · rename_i hstd
            have hstd := hstdP hstd
            refine allOk_pure o ⟨?_, rfl⟩
            unfold IncludeAccepted
            exact ⟨hdepot, Or.inl ⟨hnp', by simpa using hne, hstd.1, hstd.2⟩⟩
          · exact allOk_pure o ⟨_, rfl, rfl⟩
        · simp only [Bool.false_eq_true, ite_false]
          exact allOk_pure o ⟨_, rfl, rfl⟩
      · rename_i hp
        have hp' : (st inc.filename).isPath = true := by simpa using hp
        split
        · rename_i hr
          split
          · exact allOk_pure o ⟨_, rfl, rfl⟩
          · rename_i hm
            refine allOk_pure o ⟨?_, rfl⟩
            unfold IncludeAccepted
            exact ⟨hdepot, Or.inr ⟨hp', fun _ => by simpa using hm, fun h => by simp_all⟩⟩
        · rename_i hr
          have hr' : include_mtime_recorded inc.mtime = false := by simpa using hr
          split
          · exact allOk_pure o ⟨_, rfl, rfl⟩
          · rename_i hs
            have hs' : (st inc.filename).size.val = inc.fsize.val := by simpa using hs
            split
            · rename_i hro
              refine allOk_bind o (P := fun t => t = true → InStore inc.filename) (hstore _) fun trusted htP => ?_
              split
              · rename_i ht
                simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hro
                refine allOk_pure o ⟨?_, rfl⟩
                unfold IncludeAccepted
                exact ⟨hdepot, Or.inr ⟨hp', fun h => by simp_all, fun _ => ⟨hs', Or.inl ⟨hro, htP ht⟩⟩⟩⟩
              · cases hd : (st inc.filename).isDirectory <;>
                  simp only [hd, ite_true, ite_false, Bool.false_eq_true, pure_bind] <;> hash_finish
            · simp only [Bool.false_eq_true, ite_false]
              cases hd : (st inc.filename).isDirectory <;>
                simp only [hd, ite_true, ite_false, Bool.false_eq_true, pure_bind] <;> hash_finish
  · intro b hb
    rcases hb with ⟨r, hr, hr1⟩ | ⟨hall, hb⟩
    · simp only [hr]
      exact allOk_pure o (fun h => by simp_all)
    · simp only [hb]
      exact allOk_pure o (fun _ => hall)
end JuliaLean.Proofs.base.loading.Cachefile

namespace JuliaLean.Proofs.base.loading.Cachefile
open JuliaLean JuliaLean.base.loading
variable {X Y E D CI CF V : Type}

theorem allOk_tryFinally (o : LOps X Y E D CI CF V) {α : Type} {body : LM o α} {c : LM o Unit}
    {Q : α → Prop} (h : AllOk o body Q) : AllOk o (tryFinallyL o body c) Q := by
  intro s a s' hr
  unfold tryFinallyL at hr
  simp only [ExceptT.run_mk] at hr
  revert hr
  cases h1 : ExceptT.run body s with
  | none => simp [bind, StateT.bind, h1, StateT.run]
  | some p =>
    obtain ⟨r, s1⟩ := p
    cases h2 : ExceptT.run c s1 with
    | none => simp [bind, StateT.bind, h1, h2, StateT.run]
    | some q =>
      obtain ⟨rc, s2⟩ := q
      cases rc <;> cases r <;> simp [bind, StateT.bind, h1, h2, StateT.run, pure, StateT.pure]
      intro ha _
      subst ha
      exact h _ _ _ h1

theorem allOk_tryCatch (o : LOps X Y E D CI CF V) {α : Type} {body : LM o α} {handler : LErr E → LM o α}
    {Q : α → Prop} (h : AllOk o body Q) (hh : ∀ e, AllOk o (handler e) Q) :
    AllOk o (tryCatchL o body handler) Q := by
  intro s a s' hr
  unfold tryCatchL at hr
  simp only [ExceptT.run_mk] at hr
  revert hr
  cases h1 : ExceptT.run body s with
  | none => simp [bind, StateT.bind, h1, StateT.run]
  | some p =>
    obtain ⟨r, s1⟩ := p
    cases r with
    | ok v =>
      simp [bind, StateT.bind, h1, StateT.run, pure, StateT.pure]
      intro ha _
      subst ha
      exact h _ _ _ h1
    | error e =>
      simp [bind, StateT.bind, h1, StateT.run]
      exact hh e s1 a s'

theorem allOk_forIn_early {σ R S : Type} (o : LOps X Y E D CI CF V) (xs : List σ) (init : Option R × S)
    (f : σ → Option R × S → LM o (ForInStep (Option R × S))) (QR : R → Prop)
    (h0 : ∀ r, init.1 = some r → QR r)
    (hf : ∀ x ∈ xs, ∀ b : Option R × S, (∀ r, b.1 = some r → QR r) →
      AllOk o (f x b) (fun st => ∀ r, st.value.1 = some r → QR r)) :
    AllOk o (forIn xs init f) (fun b => (∀ r, b.1 = some r → QR r) ∧ (xs = [] → b = init)) := by
  intro s a s' hr
  refine ⟨?_, fun hxs => ?_⟩
  · have := allOk_forIn o xs init f (fun b => ∀ r, b.1 = some r → QR r) (fun b => ∀ r, b.1 = some r → QR r)
      (fun _ => True) h0 (fun x hx b hb => by
        intro s1 a1 s2 h1
        have := hf x hx b hb s1 a1 s2 h1
        cases a1 <;> simp_all [ForInStep.value]) s a s' hr
    rcases this with h | ⟨_, h⟩ <;> exact h
  · subst hxs
    simp [List.forIn_nil, pure, ExceptT.run, ExceptT.pure, ExceptT.mk, StateT.run, StateT.pure] at hr
    exact hr.1.symm

theorem allOk_bind_and (o : LOps X Y E D CI CF V) {α β : Type} {m : LM o α} {k : α → LM o β}
    {P1 P2 : α → Prop} {Q : β → Prop} (hm : AllOk o m (fun a => P1 a ∧ P2 a))
    (hk : ∀ a, P1 a → P2 a → AllOk o (k a) Q) : AllOk o (m >>= k) Q :=
  allOk_bind o hm fun a h => hk a h.1 h.2

theorem allOk_ite (o : LOps X Y E D CI CF V) {α : Type} {c : Prop} [Decidable c] {t e : LM o α}
    {Q : α → Prop} (ht : c → AllOk o t Q) (he : ¬c → AllOk o e Q) : AllOk o (if c then t else e) Q := by
  by_cases h : c
  · rw [if_pos h]; exact ht h
  · rw [if_neg h]; exact he h

macro "walk_leaf" : tactic => `(tactic| first
  | rfl
  | (intro r hr; cases hr; done)
  | (intro r hr; cases hr; rfl)
  | (intro h; cases h; done)
  | (simp_all; done)
  | (intros; simp_all; done)
  | (intro _ hw; revert ‹¬(($(Lean.mkIdent `wanted)).val != 0 && _ != $(Lean.mkIdent `wanted)) = true›;
      simp only [hw, bne_iff_ne, ne_eq, decide_true, Bool.true_and, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not, Classical.not_not]; exact id))

/-- Wrapper for join-point lemmas in the context, so that `simp_all` leaves them alone. -/
def JpSpec (p : Prop) : Prop := p

open Lean Meta Elab Tactic in
/-- Handle a `have x := v; body` at the head of an `AllOk` goal. A function-valued monadic
join point gets a lemma `∀ args, AllOk o (x args) Q`, proved once; any other value is inlined.
A goal whose monadic action is a call of a local join point is closed by its lemma. -/
elab "jp_step" inl:("inline")? : tactic => do
  let inline := inl.isSome
  let g ← getMainGoal
  g.withContext do
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  let some (m, Q, mk) ← (do
      let args := tgt.getAppArgs
      if (tgt.isAppOfArity ``AllOk 11 || tgt.isAppOfArity ``OkRun 11) then
        let f := tgt.getAppFn
        pure (some (args[9]!, args[10]!, fun (m' : Expr) => mkAppN f (args.set! 9 m')))
      else pure none) | throwError "jp_step: not an AllOk goal"
  let m := match m with
    | .app (.lam n t b bi) v => if t.isForall then Expr.letE n t v b true else (Expr.app (.lam n t b bi) v)
    | m => m
  if m.getAppFn.isLambda then
    let g' ← g.replaceTargetDefEq (mk m.headBeta)
    replaceMainGoal [g']
    return
  match m with
  | .letE n t v b _ =>
    let isJp ← forallTelescope t fun _ ret => do
      let ret ← whnfR ret
      pure (ret.getAppFn.isConstOf ``LM || ret.isAppOf ``ExceptT)
    if !isJp || !t.isForall then
      let g' ← g.replaceTargetDefEq (mk (b.instantiate1 v))
      replaceMainGoal [g']
    else if inline then
      let g' ← g.replaceTargetDefEq (.letE n t v (mk b) false)
      let (_, g'') ← g'.intro1P
      replaceMainGoal [g'']
    else
      let H ← withLocalDeclD n t fun jp => do
        let body ← forallTelescope t fun xs _ => do
          mkForallFVars xs (mk (mkAppN jp xs))
        mkLambdaFVars #[jp] body
      let hvTy ← forallTelescope t fun xs _ => do mkForallFVars xs (mk (v.beta xs))
      let hv ← mkFreshExprSyntheticOpaqueMVar hvTy (n.appendAfter "_def")
      let hbTy ← withLocalDeclD n t fun jp => do
        let hyp := mkApp (mkConst ``JpSpec) (H.beta #[jp])
        withLocalDeclD (n.appendAfter "_spec") hyp fun h => do
          mkForallFVars #[jp, h] (mk (b.instantiate1 jp))
      let hb ← mkFreshExprSyntheticOpaqueMVar hbTy
      g.assign (mkAppN hb #[v, hv])
      replaceMainGoal [hv.mvarId!, hb.mvarId!]
  | _ =>
    let fn := m.getAppFn
    if !fn.isFVar then throwError "jp_step: no join point"
    if let some val ← fn.fvarId!.getValue? then
      let g' ← g.replaceTargetDefEq (mk (val.beta m.getAppArgs))
      replaceMainGoal [g']
      return
    let lctx ← getLCtx
    for d in lctx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      unless ty.isAppOf ``JpSpec do continue
      let concl ← forallTelescope ty.appArg! fun _ c => pure c
      if (concl.isAppOfArity ``AllOk 11 || concl.isAppOfArity ``OkRun 11) && (concl.getAppArgs[9]!).getAppFn == fn then
        let gs ← g.apply (mkFVar d.fvarId)
        replaceMainGoal gs
        return
    throwError "jp_step: no lemma for the join point"

open Lean Meta Elab Tactic in
/-- Case-split the `match` at the head of an `AllOk` goal: generalize the discriminants (keeping
equations), case on the first, and reduce the matcher. -/
elab "match_step" : tactic => do
  let g ← getMainGoal
  g.withContext do
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  unless (tgt.isAppOfArity ``AllOk 11 || tgt.isAppOfArity ``OkRun 11) do throwError "match_step: not an AllOk goal"
  let m := tgt.getAppArgs[9]!
  let some app ← matchMatcherApp? m | throwError "match_step: not a match"
  let discrs := app.discrs
  let args : Array GeneralizeArg := discrs.map fun d =>
    { expr := d, xName? := some `d, hName? := some `hd }
  let (fvars, g) ← g.generalize args
  let subs ← g.cases fvars[0]!
  let mut out := []
  for sg in subs do
    let g := sg.mvarId
    let g' ← g.withContext do
      let t ← whnfR (← instantiateMVars (← g.getType))
      if (t.isAppOfArity ``AllOk 11 || t.isAppOfArity ``OkRun 11) then
        let a := t.getAppArgs
        match ← reduceMatcher? a[9]! with
        | ReduceMatcherResult.reduced e => g.replaceTargetDefEq (mkAppN t.getAppFn (a.set! 9 e))
        | _ => pure g
      else pure g
    out := out ++ [g']
  replaceMainGoal out

syntax "walk_step" : tactic
macro_rules | `(tactic| walk_step) => `(tactic| first
  | with_reducible intro _
  | (jp_step; next => (repeat' walk_step) <;> fail "jp spec failed")
  | jp_step inline
  | with_reducible_and_instances exact allOk_throw _
  | (with_reducible_and_instances apply allOk_pure); walk_leaf
  | with_reducible_and_instances apply allOk_tryFinally
  | ((with_reducible_and_instances apply allOk_tryCatch); intro _)
  | with_reducible_and_instances refine allOk_bind_and _ (allOk_forIn_early _ _ _ _ (fun (r : CacheStaleDecision _) => r.stale = true) (by simp) ?_) ?_
  | ((with_reducible_and_instances apply allOk_bind); first
      | with_reducible_and_instances apply $(Lean.mkIdent `hint1)
      | with_reducible_and_instances apply $(Lean.mkIdent `hint2)
      | with_reducible_and_instances apply $(Lean.mkIdent `hint3)
      | with_reducible_and_instances apply $(Lean.mkIdent `hint4)
      | exact allOk_any _ _)
  | ((with_reducible_and_instances apply allOk_ite) <;> intro _)
  | match_step
  | fail "walk stuck")

theorem isvalid_none {Stream : Type} (o : LOps X Y E D CI CF V) (io : CacheIOOps o Stream) (st : Stream)
    (h : AllOk o (io.readVerifyHeader st) (fun h => h.status.val ≠ 0)) :
    AllOk o (isvalid_cache_header o io st) (· = none) := by
  unfold isvalid_cache_header
  refine allOk_bind o h fun hd hs => ?_
  refine allOk_ite o (fun c => ?_) (fun c => ?_)
  · exact allOk_bind o (allOk_any o _) fun _ _ => allOk_pure o rfl
  · exact allOk_pure o (by simp [hs])

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem t_flags {Stream Mod Reason PrefValue : Type} (o : LOps X Y E D CI CF V)
    (ops : CacheStalenessOps o Stream Mod Reason PrefValue) modkey wanted modspec cachefile ig rf reasons sc vc spl
    (hint1 : ∀ a b, AllOk o (ops.jlMatchCacheFlags a b) (fun r => r.val = 0)) :
    AllOk o (stale_cachefile o ops modkey wanted modspec cachefile ig rf reasons sc vc spl) (fun d => d.stale = true) := by
  unfold stale_cachefile
  repeat' walk_step

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem t_header {Stream Mod Reason PrefValue : Type} (o : LOps X Y E D CI CF V)
    (ops : CacheStalenessOps o Stream Mod Reason PrefValue) modkey wanted modspec cachefile ig rf reasons sc vc spl
    (hint1 : ∀ st, AllOk o (isvalid_cache_header o ops.io st) (· = none)) :
    AllOk o (stale_cachefile o ops modkey wanted modspec cachefile ig rf reasons sc vc spl) (fun d => d.stale = true) := by
  unfold stale_cachefile
  repeat' walk_step

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem t_prefs {Stream Mod Reason PrefValue : Type} (o : LOps X Y E D CI CF V)
    (ops : CacheStalenessOps o Stream Mod Reason PrefValue) modkey wanted modspec cachefile ig rf reasons sc vc spl
    (hint1 : ∀ blob, AllOk o (stale_prefs o ops.preferences blob) (· = true)) :
    AllOk o (stale_cachefile o ops modkey wanted modspec cachefile ig rf reasons sc vc spl) (fun d => d.stale = true) := by
  unfold stale_cachefile
  repeat' walk_step

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem t_checksums {Stream Mod Reason PrefValue : Type} (o : LOps X Y E D CI CF V)
    (ops : CacheStalenessOps o Stream Mod Reason PrefValue) modkey wanted modspec cachefile ig rf reasons sc vc spl (hvc : vc = true)
    (hint1 : ∀ st cf oc r spl, AllOk o (checksums_invalid_io o ops.io st cf oc r spl) (·.1 = true)) :
    AllOk o (stale_cachefile o ops modkey wanted modspec cachefile ig rf reasons sc vc spl) (fun d => d.stale = true) := by
  unfold stale_cachefile
  repeat' walk_step

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem t_includes {Stream Mod Reason PrefValue : Type} (o : LOps X Y E D CI CF V)
    (ops : CacheStalenessOps o Stream Mod Reason PrefValue) modkey wanted modspec cachefile ig rf reasons sc vc spl (hsc : sc = true)
    (hint1 : AllOk o ops.concreteDependencies (· = []))
    (hint2 : ∀ incs cf r, AllOk o (any_includes_stale o ops.includes incs cf r) (·.1 = true)) :
    AllOk o (stale_cachefile o ops modkey wanted modspec cachefile ig rf reasons sc vc spl) (fun d => d.stale = true) := by
  unfold stale_cachefile
  repeat' walk_step

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem t_srcpath {Stream Mod Reason PrefValue : Type} (o : LOps X Y E D CI CF V)
    (ops : CacheStalenessOps o Stream Mod Reason PrefValue) modkey wanted modspec cachefile ig rf reasons sc vc spl (hsc : sc = true)
    (hint1 : AllOk o ops.concreteDependencies (· = []))
    (hint2 : ∀ a b, AllOk o (ops.io.sameFile a b) (· = false)) :
    AllOk o (stale_cachefile o ops modkey wanted modspec cachefile ig rf reasons sc vc spl) (fun d => d.stale = true) := by
  unfold stale_cachefile
  repeat' walk_step

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem t_syntax {Stream Mod Reason PrefValue : Type} (o : LOps X Y E D CI CF V)
    (ops : CacheStalenessOps o Stream Mod Reason PrefValue) modkey wanted modspec cachefile ig rf reasons sc vc spl (hsc : sc = true)
    (hint1 : ∀ st cf, AllOk o (parse_cache_header o ops.io st cf) (·.syntaxVersion ≠ cache_edition modspec.julia_edition)) :
    AllOk o (stale_cachefile o ops modkey wanted modspec cachefile ig rf reasons sc vc spl) (fun d => d.stale = true) := by
  unfold stale_cachefile
  repeat' walk_step

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem t_buildid {Stream Mod Reason PrefValue : Type} (o : LOps X Y E D CI CF V)
    (ops : CacheStalenessOps o Stream Mod Reason PrefValue) modkey wanted modspec cachefile ig rf reasons sc vc spl :
    AllOk o (stale_cachefile o ops modkey wanted modspec cachefile ig rf reasons sc vc spl)
      (fun d => d.stale = false → wanted.val ≠ 0 → d.buildId = wanted) := by
  unfold stale_cachefile
  repeat' walk_step
end JuliaLean.Proofs.base.loading.Cachefile

namespace JuliaLean.Proofs.base.loading.Cachefile
open JuliaLean JuliaLean.base.loading
variable {X Y E D CI CF V : Type}

/-! ## Small helpers -/

theorem allOk_withLock (o : LOps X Y E D CI CF V) {α : Type} {body : LM o α} {Q : α → Prop}
    (h : AllOk o body Q) : AllOk o (withLock o body) Q := by
  intro s a s' hr
  unfold withLock at hr
  simp only [ExceptT.run_mk] at hr
  revert hr
  simp only [bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure,
    StateT.pure, StateT.run, Option.bind]
  cases h1 : ExceptT.run body { s with require_lock := s.require_lock + 1 } with
  | none => simp
  | some p =>
    obtain ⟨r, s1⟩ := p
    simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro hra _
    subst hra
    exact h _ _ _ h1

theorem withLock_pure_run (o : LOps X Y E D CI CF V) {α : Type} (a : α) (s : World X D CI CF) :
    (ExceptT.run (withLock o (pure a : LM o α))).run s = some (.ok a, s) := by
  simp [withLock, ExceptT.run, ExceptT.mk, StateT.run, bind, StateT.bind, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, ExceptT.pure, Option.bind]

/-- `maybe_loaded_precompile` returns a module of `loaded_precompiles[key]` whose build id is the
requested one, and it returns one whenever such a module exists (base/loading.jl:3041-3049). -/
theorem maybeLoaded_loop (o : LOps X Y E D CI CF V) {Mod : Type} (ops : ModuleRegistryOps o Mod)
    (w : Mod → JInt .u64 × JInt .u64) (hw : ∀ m, ops.moduleBuildIdWords m = pure (w m)) (buildid : JInt .u128) :
    ∀ mods : List Mod, maybeLoadedPrecompileLoop o ops buildid mods =
      pure (mods.find? (fun m => JInt.wrap .u128 ((w m).1.val * (2 ^ 64 : Int) + (w m).2.val) == buildid)) := by
  intro mods
  induction mods with
  | nil => rfl
  | cons m rest ih =>
    simp only [maybeLoadedPrecompileLoop, module_build_id, hw, pure_bind, List.find?_cons]
    cases hb : (JInt.wrap .u128 ((w m).1.val * (2 ^ 64 : Int) + (w m).2.val) == buildid) with
    | true => simp
    | false => simpa using ih


/-! ## `CacheFlags` byte encoding -/

/-- `UInt8(x)`: exact conversion, throwing `err` (an `InexactError`) outside `0:255`. -/
def conv8 (o : LOps X Y E D CI CF V) (err : LErr E) (x : base.loading.JInt64) : LM o (JInt .u8) :=
  if 0 ≤ x.val ∧ x.val < 256 then pure (JInt.wrap .u8 x.val) else throwL o err

def c8 (x : base.loading.JInt64) : Option (JInt .u8) :=
  if 0 ≤ x.val ∧ x.val < 256 then some (JInt.wrap .u8 x.val) else none

/-- The `Int` that `_cacheflag_to_uint8` computes before its one `UInt8` conversion. -/
def orChain (cf : CacheFlags) : base.loading.JInt64 :=
  base.int.or_int (base.int.or_int (base.int.or_int (base.int.or_int
    (base.int.or_int (JInt.wrap .i64 (JInt.wrap .u8 0 : JInt .u8).val)
      (base.int.shl_int (i64 (if cf.use_pkgimages then 1 else 0)) (i64 0)))
    (base.int.shl_int cf.debug_level (i64 1)))
    (base.int.shl_int cf.check_bounds (i64 3)))
    (base.int.shl_int (i64 (if cf.inline then 1 else 0)) (i64 5)))
    (base.int.shl_int cf.opt_level (i64 6))

/-- The byte `_cacheflag_to_uint8` returns, with `UInt8(x)` as a partial function. -/
def chain8 (cf : CacheFlags) : Option (JInt .u8) := c8 (orChain cf)

theorem cacheflag_chain (o : LOps X Y E D CI CF V) (cov : CoverageOps o) (err : LErr E) (hconv : ∀ x, cov.convertUInt8 x = conv8 o err x)
    (cf : CacheFlags) :
    _cacheflag_to_uint8 o cov cf = match chain8 cf with | some b => pure b | none => throwL o err := by
  have h : _cacheflag_to_uint8 o cov cf = conv8 o err (orChain cf) := by
    simp only [_cacheflag_to_uint8, hconv]; rfl
  rw [h]
  unfold conv8 chain8 c8
  split <;> rfl

abbrev flagsOf (b : Bool) (d c : Fin 4) (i : Bool) (p : Fin 4) : CacheFlags :=
  CacheFlags.mk b (JInt.wrap .i64 d.val) (JInt.wrap .i64 c.val) i (JInt.wrap .i64 p.val) (JInt.wrap .i64 0) none

/-- The byte layout `OOICCDDP` of the `CacheFlags` comment (base/loading.jl:1955), as arithmetic. -/
def layoutByte (b : Bool) (d c : Fin 4) (i : Bool) (p : Fin 4) : Int :=
  (if b then 1 else 0) + 2 * d.val + 8 * c.val + 32 * (if i then 1 else 0) + 64 * p.val

theorem layout_table : ∀ (b : Bool) (d c : Fin 4) (i : Bool) (p : Fin 4),
    chain8 (flagsOf b d c i p) = some (JInt.wrap .u8 (layoutByte b d c i p)) ∧
    CacheFlags_fromUInt8 (JInt.wrap .u8 (layoutByte b d c i p)) (JInt.wrap .i64 0) = flagsOf b d c i p := by
  decide +kernel

theorem roundtrip_table : ∀ (b : Bool) (d c : Fin 4) (i : Bool) (p : Fin 4),
    (chain8 (flagsOf b d c i p)).map (CacheFlags_fromUInt8 · (JInt.wrap .i64 0)) = some (flagsOf b d c i p) := by
  intro b d c i p
  rw [(layout_table b d c i p).1]
  exact congrArg some (layout_table b d c i p).2

theorem cacheflag_roundtrip (o : LOps X Y E D CI CF V) (cov : CoverageOps o) (err : LErr E)
    (hconv : ∀ x, cov.convertUInt8 x = conv8 o err x) (cf : CacheFlags)
    (hd : 0 ≤ cf.debug_level.val ∧ cf.debug_level.val < 4)
    (hc : 0 ≤ cf.check_bounds.val ∧ cf.check_bounds.val < 4)
    (hp : 0 ≤ cf.opt_level.val ∧ cf.opt_level.val < 4) (coverage : base.loading.JInt64) :
    ∃ byte, _cacheflag_to_uint8 o cov cf = pure byte ∧
      CacheFlags_fromUInt8 byte coverage = { cf with coverage := coverage, coverage_path := none } := by
  have wrapEq : ∀ (x : base.loading.JInt64), 0 ≤ x.val → x.val < 4 →
      ∃ k : Fin 4, x = JInt.wrap .i64 (k.val : Int) := by
    intro x h0 h4
    refine ⟨⟨x.val.toNat, by omega⟩, ?_⟩
    apply Subtype.ext
    simp only [JInt.wrap]
    rw [Int.toNat_of_nonneg h0]
    exact (wrapInt_of_inRange _ _ x.property).symm
  obtain ⟨b, dl, cb, il, ol, cv, cp⟩ := cf
  obtain ⟨d, rfl⟩ := wrapEq dl hd.1 hd.2
  obtain ⟨c, rfl⟩ := wrapEq cb hc.1 hc.2
  obtain ⟨p, rfl⟩ := wrapEq ol hp.1 hp.2
  have hcf : chain8 ⟨b, JInt.wrap .i64 d.val, JInt.wrap .i64 c.val, il, JInt.wrap .i64 p.val, cv, cp⟩ =
      chain8 (flagsOf b d c il p) := rfl
  have ht := roundtrip_table b d c il p
  rw [← hcf] at ht
  cases hch : chain8 ⟨b, JInt.wrap .i64 d.val, JInt.wrap .i64 c.val, il, JInt.wrap .i64 p.val, cv, cp⟩ with
  | none => rw [hch] at ht; cases ht
  | some byte =>
    refine ⟨byte, by rw [cacheflag_chain o cov err hconv, hch], ?_⟩
    rw [hch] at ht
    have ht' : CacheFlags_fromUInt8 byte (JInt.wrap .i64 0) = flagsOf b d c il p := Option.some.inj ht
    have := congrArg (fun f : CacheFlags => { f with coverage := coverage }) ht'
    exact this

/-! ## Directory include dependencies -/

/-- A directory include whose recorded size differs from its current `st_size` is stale, whatever
its listing hash. -/
theorem dir_size_stale (o : LOps X Y E D CI CF V) {Stream : Type} (ops : IncludeStalenessOps o Stream)
    st fixup isFile fileHash dirHash (hfs : PureIncludeFs o ops st fixup isFile fileHash dirHash)
    (inc : CacheHeaderIncludes) (cachefile : Bytes) (reasons : Option (AMap Bytes base.loading.JInt64))
    (hdepot : ¬ (lit "@depot" ++ ops.io.pathsep).isPrefixOf inc.filename = true)
    (hpath : (st inc.filename).isPath = true) (hrec : include_mtime_recorded inc.mtime = false)
    (hsize : (st inc.filename).size.val ≠ inc.fsize.val) :
    any_includes_stale o ops [inc] cachefile reasons =
      pure (true, recordReasonMaybe reasons (lit "fsize_changed")) := by
  have hd' : ¬ (lit "@depot" ++ ops.io.pathsep <+: inc.filename) := by simpa using hdepot
  unfold any_includes_stale
  simp [List.forIn_cons, hfs.stat, hfs.log, hd', hpath, hrec, hsize]

end JuliaLean.Proofs.base.loading.Cachefile

namespace JuliaLean.Proofs.base.loading.Cachefile.Concrete
open JuliaLean JuliaLean.base.loading JuliaLean.Proofs.base.loading.Cachefile

abbrev U := Unit
abbrev W := World U U U U

set_option maxHeartbeats 2000000 in
def files0 : JuliaLean.base.path.FileBindings W :=
  { Handle := Unit, CString := Unit, StatMemory := Unit, IOBuf := Unit, User := Unit,
    Group := Unit, Req := Unit, StrBuf := Unit, SizeRef := Unit, Dirent := Unit, Stream := Unit,
    WString := Unit, Chan := Unit, Cmd := Unit, Pipe := Unit, IterObj := Unit, DirPtr := Unit,
    DiskBuf := Unit, DiskStatRaw := Unit, PathVal := Unit
    ops := by repeat (first | exact default | intro _ | constructor) }

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
def ops0 : LOps U U U U U U U := by
  constructor
  case pathFiles => exact files0
  all_goals repeat (first | exact default | intro _ | constructor)

set_option maxHeartbeats 2000000 in
def world0 : W := by
  repeat (first | exact default | intro _ | exact Unit | constructor)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
def io0 : CacheIOOps ops0 Unit := by
  constructor
  all_goals repeat (first | exact default | intro _ | exact throwL ops0 .boundsError | constructor)


def dirStat (size : Int) : CacheFileStat :=
  { device := JInt.wrap .u64 0, inode := JInt.wrap .u64 0, mode := JInt.wrap .u64 0o40755
    size := JInt.wrap .i64 size, mtime := JuliaLean.Promotion.Fl.ofBits 0
    ctime := JuliaLean.Promotion.Fl.ofBits 0, isPath := true, isDirectory := true }

def incOps (size : Int) (h : CacheU32) : IncludeStalenessOps ops0 Unit :=
  { io := { io0 with statPath := fun _ => pure (dirStat size), logDebug := fun _ => pure (),
                     fileMode := fun _ => JInt.wrap .u64 0o40755, pathsep := [47] }
    fixupStdlibPath := fun p => pure p, directoryHash := fun _ => pure h, fileHash := fun _ => pure h }

def dirInc (size : Int) (h : CacheU32) : CacheHeaderIncludes :=
  { id := ⟨none, []⟩, filename := [47, 100], fsize := JInt.wrap .u64 size, hash := h
    mtime := JuliaLean.Promotion.Fl.ofBits 0xBFF0000000000000, modpath := [] }


theorem dirInc_run :
    (ExceptT.run (any_includes_stale ops0 (incOps 20480 (JInt.wrap .u32 7)) [dirInc 4096 (JInt.wrap .u32 7)] [] none)).run
      world0 = some (.ok (true, none), world0) := by
  rw [dir_size_stale ops0 (incOps 20480 (JInt.wrap .u32 7)) (fun _ => dirStat 20480) id (fun _ => false)
    (fun _ => JInt.wrap .u32 7) (fun _ => JInt.wrap .u32 7)
    ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
    (dirInc 4096 (JInt.wrap .u32 7)) [] none (by decide +kernel) rfl (by decide) (by decide)]
  rfl

end JuliaLean.Proofs.base.loading.Cachefile.Concrete

namespace JuliaLean.Proofs.base.loading.Cachefile
open JuliaLean JuliaLean.base.loading

/-! ## Further helpers -/

section
variable {X Y E D CI CF V : Type}

theorem modspec_stale {Stream Mod Reason PrefValue : Type} (o : LOps X Y E D CI CF V)
    (ops : CacheStalenessOps o Stream Mod Reason PrefValue) (modspec : PkgLoadSpec) (cachefile : Bytes)
    (ig : Bool) (rf : Option CacheFlags) (reasons : Option (AMap Bytes base.loading.JInt64)) (vc : Bool)
    (h : ∀ flags, AllOk o (stale_cachefile o ops ⟨none, lit ""⟩ (JInt.wrap .u128 0) modspec cachefile ig
      flags reasons true vc true) (fun d => d.stale = true)) :
    AllOk o (stale_cachefile_modspec o ops modspec cachefile ig rf reasons vc) (fun d => d.stale = true) := by
  unfold stale_cachefile_modspec
  cases rf with
  | some f => exact h f
  | none => exact allOk_bind o (allOk_any o _) fun flags _ => h flags

theorem object_build_id_spec {Object Module : Type} (o : LOps X Y E D CI CF V)
    (ops : ObjectBuildIdOps o Object Module) (top : Object → Option Module)
    (w : Module → JInt .u64 × JInt .u64)
    (htop : ∀ x, ops.objectTopModule x = pure (top x)) (hw : ∀ m, ops.registry.moduleBuildIdWords m = pure (w m))
    (x : Object) :
    object_build_id o ops x =
      pure ((top x).map fun m => JInt.wrap .u128 ((w m).1.val * (2 ^ 64 : Int) + (w m).2.val)) := by
  unfold object_build_id
  simp only [htop, pure_bind]
  cases top x <;> simp [module_build_id, hw]

end

/-! ## Statements -/

/-- `any_includes_stale` accepts an include only if its recorded inputs match: the path is not an
unresolved `@depot` path, and either it is a relocated stdlib file under `Sys.STDLIB`, or it exists
and its mtime is within the tolerance (mtime-tracked) or its size matches and its content hash
matches or it is a read-only file in a depot's package store (content-tracked). The file-system
callees are pure functions of the path. `Pre a b` is whatever `startswith(a, b)` guarantees when it
answers true, and `InStore p` whatever `in_package_store(p)` guarantees. -/
def AnyIncludesStaleSound : Prop :=
  ∀ (X Y E D CI CF V Stream : Type) (o : LOps X Y E D CI CF V) (ops : IncludeStalenessOps o Stream)
    st fixup isFile fileHash dirHash, PureIncludeFs o ops st fixup isFile fileHash dirHash →
    ∀ (Pre : Bytes → Bytes → Prop) (InStore : Bytes → Prop),
    (∀ a b, AllOk o (startswith o a b) (fun r => r = true → Pre a b)) →
    (∀ p, AllOk o (in_package_store o p) (fun r => r = true → InStore p)) →
    ∀ includes cachefile reasons,
      AllOk o (any_includes_stale o ops includes cachefile reasons)
        (fun r => r.1 = false → ∀ inc ∈ includes, IncludeAccepted o ops.io st fixup isFile fileHash dirHash Pre InStore inc)

/-- Each check of `stale_cachefile` is effective: when the callee behind it reports a mismatch
on every call, every verdict is stale. The checks are the header (`jl_read_verify_header`), the
flags (`jl_match_cache_flags`), the preferences, the checksums (when verified), the include
dependencies and the source path (when `stalecheck` is on and no concrete dependency is pinned),
and the syntax version (with `stalecheck`). -/
def StaleCachefileRejects : Prop :=
  ∀ (X Y E D CI CF V Stream Mod Reason PrefValue : Type) (o : LOps X Y E D CI CF V)
    (ops : CacheStalenessOps o Stream Mod Reason PrefValue) modkey wanted modspec cachefile ig rf reasons sc vc spl,
    let run := stale_cachefile o ops modkey wanted modspec cachefile ig rf reasons sc vc spl
    ((∀ st, AllOk o (ops.io.readVerifyHeader st) (fun h => h.status.val ≠ 0)) → AllOk o run (·.stale = true)) ∧
    ((∀ a b, AllOk o (ops.jlMatchCacheFlags a b) (·.val = 0)) → AllOk o run (·.stale = true)) ∧
    ((∀ blob, AllOk o (stale_prefs o ops.preferences blob) (· = true)) → AllOk o run (·.stale = true)) ∧
    (vc = true → (∀ st cf oc r spl, AllOk o (checksums_invalid_io o ops.io st cf oc r spl) (·.1 = true)) →
      AllOk o run (·.stale = true)) ∧
    (sc = true → AllOk o ops.concreteDependencies (· = []) →
      (∀ incs cf r, AllOk o (any_includes_stale o ops.includes incs cf r) (·.1 = true)) → AllOk o run (·.stale = true)) ∧
    (sc = true → AllOk o ops.concreteDependencies (· = []) →
      (∀ a b, AllOk o (ops.io.sameFile a b) (· = false)) → AllOk o run (·.stale = true)) ∧
    ((∀ st, AllOk o (ops.io.readVerifyHeader st) (fun h => h.status.val ≠ 0)) →
      ∀ rf' vc', AllOk o (stale_cachefile_modspec o ops modspec cachefile ig rf' reasons vc') (·.stale = true)) ∧
    (sc = true → (∀ st cf, AllOk o (parse_cache_header o ops.io st cf)
      (·.syntaxVersion ≠ cache_edition modspec.julia_edition)) → AllOk o run (·.stale = true))

/-- A fresh verdict carries the requested build id whenever one was requested. -/
def StaleCachefileBuildId : Prop :=
  ∀ (X Y E D CI CF V Stream Mod Reason PrefValue : Type) (o : LOps X Y E D CI CF V)
    (ops : CacheStalenessOps o Stream Mod Reason PrefValue) modkey wanted modspec cachefile ig rf reasons sc vc spl,
    AllOk o (stale_cachefile o ops modkey wanted modspec cachefile ig rf reasons sc vc spl)
      (fun d => d.stale = false → wanted.val ≠ 0 → d.buildId = wanted)

/-- The flag byte written by `_cacheflag_to_uint8` is read back by `CacheFlags(::UInt8, coverage)`
as the same flags, for the field ranges Julia's options produce (`-g0`..`-g3` is not needed:
debug level, bounds checking and optimization level each fit two bits). `UInt8(x)` is the exact
conversion. -/
def CacheFlagsRoundTrip : Prop :=
  ∀ (X Y E D CI CF V : Type) (o : LOps X Y E D CI CF V) (cov : CoverageOps o) (err : LErr E),
    (∀ x, cov.convertUInt8 x = conv8 o err x) → ∀ cf : CacheFlags,
    (0 ≤ cf.debug_level.val ∧ cf.debug_level.val < 4) → (0 ≤ cf.check_bounds.val ∧ cf.check_bounds.val < 4) →
    (0 ≤ cf.opt_level.val ∧ cf.opt_level.val < 4) → ∀ coverage,
    ∃ byte, _cacheflag_to_uint8 o cov cf = pure byte ∧
      CacheFlags_fromUInt8 byte coverage = { cf with coverage := coverage, coverage_path := none }

/-- `maybe_loaded_precompile(key, buildid)` returns the first module of `loaded_precompiles[key]`
with that build id, and nothing when there is none. It always returns, and leaves the state (the
`require_lock` count included) as it found it. -/
def MaybeLoadedPrecompileSpec : Prop :=
  ∀ (X Y E D CI CF V Mod : Type) (o : LOps X Y E D CI CF V) (ops : ModuleRegistryOps o Mod)
    (w : Mod → JInt .u64 × JInt .u64), (∀ m, ops.moduleBuildIdWords m = pure (w m)) →
    ∀ key mods buildid, ops.loadedPrecompiles key = pure mods → ∀ s,
      (ExceptT.run (maybe_loaded_precompile o ops key buildid)).run s =
        some (.ok ((mods.getD []).find? fun m =>
          JInt.wrap .u128 ((w m).1.val * (2 ^ 64 : Int) + (w m).2.val) == buildid), s)

/-- `object_build_id(obj)` is `nothing` without a top module, and that module's build id
otherwise. -/
def ObjectBuildIdSpec : Prop :=
  ∀ (X Y E D CI CF V Object Module : Type) (o : LOps X Y E D CI CF V) (ops : ObjectBuildIdOps o Object Module)
    (top : Object → Option Module) (w : Module → JInt .u64 × JInt .u64),
    (∀ x, ops.objectTopModule x = pure (top x)) → (∀ m, ops.registry.moduleBuildIdWords m = pure (w m)) →
    ∀ x, object_build_id o ops x =
      pure ((top x).map fun m => JInt.wrap .u128 ((w m).1.val * (2 ^ 64 : Int) + (w m).2.val))

/-- A content-tracked directory include whose listing hash (`join(readdir(dir))`, the directory's
"content" per the `include_dependency` docstring) is unchanged is not stale. -/
def DirectoryIncludeContentOnly : Prop :=
  ∀ (X Y E D CI CF V Stream : Type) (o : LOps X Y E D CI CF V) (ops : IncludeStalenessOps o Stream)
    st fixup isFile fileHash dirHash, PureIncludeFs o ops st fixup isFile fileHash dirHash →
    ∀ (inc : CacheHeaderIncludes) cachefile reasons,
      ¬ (lit "@depot" ++ ops.io.pathsep).isPrefixOf inc.filename = true →
      (st inc.filename).isPath = true → (st inc.filename).isDirectory = true →
      include_mtime_recorded inc.mtime = false → dirHash inc.filename = inc.hash →
      AllOk o (any_includes_stale o ops [inc] cachefile reasons) (fun r => r.1 = false)

/-! ## Proofs -/

theorem anyIncludesStaleSound_proven : AnyIncludesStaleSound := by
  intro X Y E D CI CF V Stream o ops st fixup isFile fileHash dirHash hfs Pre InStore hsw hstore includes cachefile reasons
  exact sound o ops st fixup isFile fileHash dirHash hfs Pre InStore hsw hstore includes cachefile reasons

theorem staleCachefileRejects_proven : StaleCachefileRejects := by
  intro X Y E D CI CF V Stream Mod Reason PrefValue o ops modkey wanted modspec cachefile ig rf reasons sc vc spl
  refine ⟨fun h => t_header o ops _ _ _ _ _ _ _ _ _ _ (fun st => isvalid_none o ops.io st (h st)),
    fun h => t_flags o ops _ _ _ _ _ _ _ _ _ _ h,
    fun h => t_prefs o ops _ _ _ _ _ _ _ _ _ _ h,
    fun hvc h => t_checksums o ops _ _ _ _ _ _ _ _ _ _ hvc h,
    fun hsc h1 h2 => t_includes o ops _ _ _ _ _ _ _ _ _ _ hsc h1 h2,
    fun hsc h1 h2 => t_srcpath o ops _ _ _ _ _ _ _ _ _ _ hsc h1 h2,
    fun h rf' vc' => modspec_stale o ops modspec cachefile ig rf' reasons vc' (fun flags =>
      t_header o ops _ _ _ _ _ _ _ _ _ _ (fun st => isvalid_none o ops.io st (h st))),
    fun hsc h => t_syntax o ops _ _ _ _ _ _ _ _ _ _ hsc h⟩

theorem staleCachefileBuildId_proven : StaleCachefileBuildId := by
  intro X Y E D CI CF V Stream Mod Reason PrefValue o ops modkey wanted modspec cachefile ig rf reasons sc vc spl
  exact t_buildid o ops modkey wanted modspec cachefile ig rf reasons sc vc spl

theorem cacheFlagsRoundTrip_proven : CacheFlagsRoundTrip := by
  intro X Y E D CI CF V o cov err hconv cf hd hc hp coverage
  exact cacheflag_roundtrip o cov err hconv cf hd hc hp coverage

theorem maybeLoadedPrecompileSpec_proven : MaybeLoadedPrecompileSpec := by
  intro X Y E D CI CF V Mod o ops w hw key mods buildid hl s
  unfold maybe_loaded_precompile
  simp only [hl, pure_bind]
  cases mods with
  | none => exact withLock_pure_run o _ s
  | some ms =>
    simp only [maybeLoaded_loop o ops w hw buildid ms]
    exact withLock_pure_run o _ s

theorem objectBuildIdSpec_proven : ObjectBuildIdSpec := by
  intro X Y E D CI CF V Object Module o ops top w htop hw x
  exact object_build_id_spec o ops top w htop hw x

/-- Counterexample: a directory include recorded with `st_size` 4096 (ext4) whose directory now
reports 20480 (after files were added and removed again), with an unchanged listing hash. -/
theorem directoryIncludeContentOnly_refuted : ¬ DirectoryIncludeContentOnly := by
  intro h
  have := h Unit Unit Unit Unit Unit Unit Unit Unit Concrete.ops0 (Concrete.incOps 20480 (JInt.wrap .u32 7))
    (fun _ => Concrete.dirStat 20480) id (fun _ => false) (fun _ => JInt.wrap .u32 7) (fun _ => JInt.wrap .u32 7)
    ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
    (Concrete.dirInc 4096 (JInt.wrap .u32 7)) [] none (by decide +kernel) rfl rfl (by decide) rfl
  exact absurd (this _ _ _ Concrete.dirInc_run) (by decide)

open JuliaLean.Registry

def entries : List Entry := [
  { id := "compiler-loading-any-includes-stale-sound", juliaFile := "base/loading.jl"
    juliaFns := ["any_includes_stale(includes::Vector{CacheHeaderIncludes}, cachefile::String, reasons)"]
    statement := "any_includes_stale reports a cache fresh only if every include dependency is resolved and either is a relocated stdlib file that startswith(Sys.STDLIB) accepted, or exists with an mtime within the tolerance (mtime-tracked), or has the recorded size and either the recorded content hash or is read-only and accepted by in_package_store (content-tracked)."
    source := "base/loading.jl:4802-4851 (never accept a stale cache)"
    status := .proven, prop := ``AnyIncludesStaleSound, thm := some ``anyIncludesStaleSound_proven
    notes := "File-system callees are pure functions of the path. startswith and in_package_store are left to the model; the statement carries over whatever they guarantee when they answer true (Pre, InStore). The stdlib exemption accepts a relocated stdlib file without checking its content, as the code does." },
  { id := "compiler-loading-stale-cachefile-rejects", juliaFile := "base/loading.jl"
    juliaFns := ["stale_cachefile(modkey::PkgId, build_id::UInt128, modspec::PkgLoadSpec, cachefile::String)",
      "stale_cachefile(modspec::PkgLoadSpec, cachefile::String)", "isvalid_cache_header(f::IOStream)"]
    statement := "Every check of stale_cachefile is effective: when jl_read_verify_header, jl_match_cache_flags, stale_prefs, checksums_invalid (with verify_checksums), any_includes_stale or samefile of the source path (with stalecheck and no pinned concrete dependency), or the header's syntax version (with stalecheck) reports a mismatch, the verdict is stale. The PkgLoadSpec method inherits the header check."
    source := "base/loading.jl:4033-4046, 4916-5139 (never accept a stale cache)"
    status := .proven, prop := ``StaleCachefileRejects, thm := some ``staleCachefileRejects_proven
    notes := "Each hypothesis says the callee reports a mismatch on every call. Not stated: the checks inside loops (julia_version, dep_loaded_incompatible, dep_missing, dep_buildid_mismatch, dep_identity_changed, the coverage include and loaded-dependency checks), pkgid_mismatch, pkgimages_disabled, cpu_target and ocachefile_missing (walks for three of these did not finish within 3M heartbeats and were dropped); the AllOk loop lemma does not record that a particular element forced an early return. The acceptance direction is compiler-loading-stale-cachefile-accepts." },
  { id := "compiler-loading-stale-cachefile-buildid", juliaFile := "base/loading.jl"
    juliaFns := ["stale_cachefile(modkey::PkgId, build_id::UInt128, modspec::PkgLoadSpec, cachefile::String)"]
    statement := "A fresh verdict of stale_cachefile carries the requested build id whenever a nonzero build id was requested."
    source := "base/loading.jl:5065-5073"
    status := .proven, prop := ``StaleCachefileBuildId, thm := some ``staleCachefileBuildId_proven },
  { id := "compiler-loading-cacheflags-roundtrip", juliaFile := "base/loading.jl"
    juliaFns := ["_cacheflag_to_uint8(cf::CacheFlags)", "CacheFlags(f::UInt8, coverage::Integer)"]
    statement := "CacheFlags(_cacheflag_to_uint8(cf), coverage) recovers use_pkgimages, debug_level, check_bounds, inline and opt_level for fields in 0:3, so the flags the header parser reads are the ones the writer encoded."
    source := "base/loading.jl:1971-1978, 2012-2020 (header parsing inverts the writer)"
    status := .proven, prop := ``CacheFlagsRoundTrip, thm := some ``cacheFlagsRoundTrip_proven },
  { id := "compiler-loading-maybe-loaded-precompile", juliaFile := "base/loading.jl"
    juliaFns := ["maybe_loaded_precompile(key::PkgId, buildid::UInt128)"]
    statement := "maybe_loaded_precompile always returns, without changing the state, the first module of loaded_precompiles[key] whose build id is the requested one, and nothing when there is none."
    source := "base/loading.jl:3041-3049; the @assert at base/loading.jl:5084 relies on it"
    status := .proven, prop := ``MaybeLoadedPrecompileSpec, thm := some ``maybeLoadedPrecompileSpec_proven },
  { id := "compiler-loading-object-build-id", juliaFile := "base/loading.jl"
    juliaFns := ["object_build_id(obj)"]
    statement := "object_build_id returns nothing when the object has no top module and that module's build id otherwise."
    source := "base/loading.jl:4025-4031"
    status := .proven, prop := ``ObjectBuildIdSpec, thm := some ``objectBuildIdSpec_proven },
  { id := "compiler-loading-dir-include-size", juliaFile := "base/loading.jl"
    juliaFns := ["any_includes_stale(includes::Vector{CacheHeaderIncludes}, cachefile::String, reasons)",
      "_include_dependency!(dep_list, track_dependencies, mod, _path, track_content, path_may_be_dir)"]
    statement := "A content-tracked directory include whose content (join(readdir(dir))) is unchanged is not stale."
    source := "base/loading.jl:2766-2772 (include_dependency docstring: the content of a directory equals join(readdir(path)))"
    status := .refuted, prop := ``DirectoryIncludeContentOnly, thm := some ``directoryIncludeContentOnly_refuted
    issue := "none found (queries: include_dependency directory size; include_dependency directory recompile; fsize_changed; PRs include_dependency directory)"
    notes := "The directory's st_size is recorded and compared before the listing hash. ext4 never shrinks a directory, and sizes differ between file systems, so the same listing can be rejected with :fsize_changed. Reproduced on pinned, nightly and 1.13.3 (repro/compiler-loading-dir-include-size.jl)." }
]

end JuliaLean.Proofs.base.loading.Cachefile
