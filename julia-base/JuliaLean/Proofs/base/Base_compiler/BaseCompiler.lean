import JuliaLean.base.Base_compiler
import JuliaLean.Proofs.base.runtime_internals.Common


section
namespace JuliaLean.RuntimeCov.BaseCompiler

open JuliaLean.RuntimeCov

def OrderedGetContract : Prop :=
  (∀ (M V : Type) (getglobal : M → Sym → Sym → Rt V) m f order,
    orderedModuleGet getglobal m f order = getglobal m f order) ∧
  (∀ (O V : Type) (getfield : O → Sym → Sym → Rt V) x f order,
    orderedFieldGet getfield x f order = getfield x f order) ∧
  (∀ (T V : Type) (getfield : T → Int → Sym → Rt V) tuple index order,
    orderedTupleGet getfield tuple index order = getfield tuple index order)

theorem orderedGetContract_proven : OrderedGetContract := by
  simp [OrderedGetContract, orderedModuleGet, orderedFieldGet, orderedTupleGet]

def SwapPropertyContract : Prop :=
  (∀ (V : Type) (r : OrderedSetRuntime V) swap x f value order ty,
    r.fieldType x f = .ok ty → r.isa value ty = true →
    swapFieldProperty r swap x f value order = swap x f value order) ∧
  (∀ (V : Type) (r : OrderedSetRuntime V) swap m f value order ty,
    r.bindingType m f = .ok ty → r.isa value ty = true →
    swapGlobalProperty r swap m f value order = swap m f value order) ∧
  (∀ (V : Type) (r : OrderedSetRuntime V) swap x f value order ty converted,
    r.fieldType x f = .ok ty → r.isa value ty = false → r.convert ty value = .ok converted →
    swapFieldProperty r swap x f value order = swap x f converted order) ∧
  (∀ (V : Type) (r : OrderedSetRuntime V) swap m f value order ty converted,
    r.bindingType m f = .ok ty → r.isa value ty = false → r.convert ty value = .ok converted →
    swapGlobalProperty r swap m f value order = swap m f converted order) ∧
  (∀ (V : Type) (r : OrderedSetRuntime V) swap x f value,
    swapFieldPropertyDefault r swap x f value = swapFieldProperty r swap x f value "not_atomic") ∧
  (∀ (V : Type) (r : OrderedSetRuntime V) swap m f value,
    swapGlobalPropertyDefault r swap m f value = swapGlobalProperty r swap m f value "not_atomic")

theorem swapPropertyContract_proven : SwapPropertyContract := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro V r swap x f value order ty ht hi
    simp [swapFieldProperty, orderedSetField, ht, hi, bind, Except.bind]
  · intro V r swap m f value order ty ht hi
    simp [swapGlobalProperty, orderedSetModule, ht, hi, bind, Except.bind]
  · intro V r swap x f value order ty converted ht hi hc
    simp [swapFieldProperty, orderedSetField, ht, hi, hc, bind, Except.bind]
  · intro V r swap m f value order ty converted ht hi hc
    simp [swapGlobalProperty, orderedSetModule, ht, hi, hc, bind, Except.bind]
  · intros; rfl
  · intros; rfl

def OrderedSetContract : Prop :=
  (∀ (V : Type) (r : OrderedSetRuntime V) m field value,
    orderedSetModuleDefault r m field value = orderedSetModule r m field value "monotonic") ∧
  (∀ (V : Type), @orderedSetType V =
    .error (.errorException "setfield! fields of Types should not be changed")) ∧
  (∀ (T V : Type) (setfield : T → Int → V → Sym → Rt V) t index value order,
    orderedSetTuple setfield t index value order = setfield t index value order) ∧
  (∀ (V : Type) (r : OrderedSetRuntime V) x f value order err,
    r.fieldType x f = .error err → orderedSetField r x f value order = .error err) ∧
  (∀ (V : Type) (r : OrderedSetRuntime V) m f value order err,
    r.bindingType m f = .error err → orderedSetModule r m f value order = .error err) ∧
  (∀ (V : Type) (r : OrderedSetRuntime V) x f value order ty,
    r.fieldType x f = .ok ty → r.isa value ty = true →
    orderedSetField r x f value order = r.setfield x f value order) ∧
  (∀ (V : Type) (r : OrderedSetRuntime V) m f value order ty,
    r.bindingType m f = .ok ty → r.isa value ty = true →
    orderedSetModule r m f value order = r.setglobal m f value order) ∧
  (∀ (V : Type) (r : OrderedSetRuntime V) x f value order ty converted,
    r.fieldType x f = .ok ty → r.isa value ty = false → r.convert ty value = .ok converted →
    orderedSetField r x f value order = r.setfield x f converted order) ∧
  (∀ (V : Type) (r : OrderedSetRuntime V) m f value order ty converted,
    r.bindingType m f = .ok ty → r.isa value ty = false → r.convert ty value = .ok converted →
    orderedSetModule r m f value order = r.setglobal m f converted order) ∧
  (∀ (V : Type) (r : OrderedSetRuntime V) x f value order ty err,
    r.fieldType x f = .ok ty → r.isa value ty = false → r.convert ty value = .error err →
    orderedSetField r x f value order = .error err) ∧
  (∀ (V : Type) (r : OrderedSetRuntime V) m f value order ty err,
    r.bindingType m f = .ok ty → r.isa value ty = false → r.convert ty value = .error err →
    orderedSetModule r m f value order = .error err)

theorem orderedSetContract_proven : OrderedSetContract := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intro V; rfl
  · intro T V setfield t index value order; rfl
  · intro V r x f value order err h
    simp [orderedSetField, h, bind, Except.bind]
  · intro V r m f value order err h
    simp [orderedSetModule, h, bind, Except.bind]
  · intro V r x f value order ty ht hi
    simp [orderedSetField, ht, hi, bind, Except.bind, pure, Except.pure]
  · intro V r m f value order ty ht hi
    simp [orderedSetModule, ht, hi, bind, Except.bind, pure, Except.pure]
  · intro V r x f value order ty converted ht hi hc
    simp [orderedSetField, ht, hi, hc, bind, Except.bind, pure, Except.pure]
  · intro V r m f value order ty converted ht hi hc
    simp [orderedSetModule, ht, hi, hc, bind, Except.bind, pure, Except.pure]
  · intro V r x f value order ty err ht hi hc
    simp [orderedSetField, ht, hi, hc, bind, Except.bind]
  · intro V r m f value order ty err ht hi hc
    simp [orderedSetModule, ht, hi, hc, bind, Except.bind]

def ModifyPropertyContract : Prop :=
  (∀ (O V F R : Type) (modify : O → Sym → F → V → Sym → R) object field op value order,
    modifyFieldProperty modify object field op value order = modify object field op value order) ∧
  (∀ (O V F R : Type) (modify : O → Sym → F → V → Sym → R) object field op value order,
    modifyGlobalProperty modify object field op value order = modify object field op value order) ∧
  (∀ (O V F R : Type) (modify : O → Sym → F → V → Sym → R) object field op value,
    modifyFieldPropertyDefault modify object field op value = modify object field op value "not_atomic") ∧
  (∀ (O V F R : Type) (modify : O → Sym → F → V → Sym → R) object field op value,
    modifyGlobalPropertyDefault modify object field op value = modify object field op value "not_atomic")

theorem modifyPropertyContract_proven : ModifyPropertyContract := by
  simp [ModifyPropertyContract, modifyFieldProperty, modifyGlobalProperty,
    modifyFieldPropertyDefault, modifyGlobalPropertyDefault]

/-! ## Properties -/

def BaseCompilerBodies : Prop :=
  (∀ (μ β : Type) (inc : μ → String → β) (b : μ) (p : String), includeBase inc b p = inc b p) ∧
  (∀ (μ β : Type) (inc : μ → String → β) (m : μ) (p : String),
      callIncludeInto inc (mkIncludeInto m) p = inc m p) ∧
  atInline = .metaHead "inline" ∧ atNoinline = .metaHead "noinline" ∧ atBoundscheck = .boundscheck ∧
  -- module properties are globals; other properties are fields
  (∀ (V : Type) (r : Rt' V) (m : String) (f : Sym), getproperty r (.module m) f = r.getglobal m f) ∧
  (∀ (V : Type) (r : Rt' V) (x : Obj) (f : Sym), (∀ m, x ≠ .module m) → getproperty r x f = r.getfield x f) ∧
  (∀ (V : Type) (r : Rt' V) x f, dotgetproperty r x f = getproperty r x f) ∧
  -- setting a field of a Type or an Array is an error
  (∀ (V : Type) (r : Rt' V) (n : String) (f : Sym) (v : V),
      ∃ e, setproperty r (.type n) f v = .error e) ∧
  (∀ (V : Type) (r : Rt' V) (f : Sym) (v : V), ∃ e, setproperty r .array f v = .error e) ∧
  -- a value that already has the field type is stored unconverted
  (∀ (V : Type) (r : Rt' V) (t : String) (f : Sym) (v : V) (ty : String),
      r.fieldtype (.other t) f = .ok ty → r.isa v ty = true →
      setproperty r (.other t) f v = r.setfield (.other t) f v) ∧
  (∀ (V : Type) (r : Rt' V) (t : String) (f : Sym) (v w : V) (ty : String),
      r.fieldtype (.other t) f = .ok ty → r.isa v ty = false → r.convert ty v = .ok w →
      setproperty r (.other t) f v = r.setfield (.other t) f w) ∧
  (∀ (V : Type) (r : Rt' V) (m : String) (f : Sym) (v : V), r.isa v (r.bindingType m f) = true →
      setproperty r (.module m) f v = r.setglobal m f v) ∧
  (∀ (V : Type) (r : Rt' V) (x : Obj) (f : Sym) (v : V) (ty : String),
      (∀ m, x ≠ .module m) → r.fieldtype x f = .ok ty → r.isa v ty = true → storedValue r x f v = .ok v) ∧
  (∀ (V W : Type) (op : W) (v : V), modifyArgs op v = (op, v)) ∧
  (∀ (α : Type) (x : α), convertIdentity x = x) ∧
  (∀ (μ : Type) (rt : μ → μ) m, topmod rt m = rt m) ∧
  (∀ e b o, (setupModule e b o).1 = ["include", "eval"]) ∧
  (∀ e b o, (setupModule (some e) b o).2 = some e) ∧
  (∀ o, (setupModule none false o).2 = some o) ∧
  (∀ (μ α β : Type) (ev : μ → α → β) m x, evalIn ev m x = ev m x) ∧
  -- strcat concatenates the bytes
  (∀ x y, strcat x y = x ++ y ∧ (strcat x y).length = x.length + y.length) ∧
  (∀ t, timeNs t < 2 ^ 64) ∧
  (∀ k f ps, kwcallInvokeSig k f ps = k :: f :: ps) ∧
  (∀ (α : Type) (k kw : α) args, (kwcallApplicableArgs k kw args).drop 2 = args) ∧
  (∀ f ps, (hasmethodSig f ps).length = ps.length + 1) ∧
  (∀ (α : Type) (k kw f : α) args, (kwcallLatestArgs k kw f args).drop 3 = args) ∧
  (∀ (α : Type) w (k kw f : α) args, (kwcallWorldArgs w k kw f args).1 = w) ∧
  (∀ a, versionedParsePassesEdition true a = true) ∧
  versionedParsePassesEdition false true = false ∧
  (∀ (α : Type) [DecidableEq α] (x y : α), eqFallback x y = true ↔ x = y) ∧
  -- sysimage arguments come in flag/value pairs; anything else is an error
  (∀ args as, processSysimgArgs args = .ok as → args.length = 2 * as.length) ∧
  (∀ f, (f = "--buildsettings" ∨ f = "--buildroot" ∨ f = "--dataroot") →
      processSysimgArgs [f] = .error .boundsError)

theorem strcat_eq (x y : List UInt8) : strcat x y = x ++ y := by
  simp [strcat]

theorem processSysimgArgs_len : ∀ (args : List String) (as : List SysimgArg),
    processSysimgArgs args = .ok as → args.length = 2 * as.length
  | [], as, h => by simp [processSysimgArgs] at h; subst h; rfl
  | [f], as, h => by
    simp only [processSysimgArgs] at h
    split at h <;> simp at h
  | f :: v :: rest, as, h => by
    simp only [processSysimgArgs] at h
    cases hthis : sysimgFlag f v with
    | error e => rw [hthis] at h; simp [bind, Except.bind] at h
    | ok a =>
      rw [hthis] at h
      cases hr : processSysimgArgs rest with
      | error e => rw [hr] at h; simp [bind, Except.bind] at h
      | ok as' =>
        rw [hr] at h
        simp [bind, Except.bind, pure, Except.pure] at h
        subst h
        have := processSysimgArgs_len rest as' hr
        simp; omega

theorem baseCompilerBodies_proven : BaseCompilerBodies := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ _ _; rfl
  · intro _ _ _ _ _; rfl
  · rfl
  · rfl
  · rfl
  · intro _ _ _ _; rfl
  · intro V r x f h
    cases x with
    | module m => exact absurd rfl (h m)
    | _ => rfl
  · intro _ _ _ _; rfl
  · intro V r n f v; exact ⟨_, rfl⟩
  · intro V r f v; exact ⟨_, rfl⟩
  · intro V r t f v ty h1 h2
    simp [setproperty, h1, convertTo, h2, bind, Except.bind]
  · intro V r t f v w ty h1 h2 h3
    simp [setproperty, h1, convertTo, h2, h3, bind, Except.bind]
  · intro V r m f v h
    simp [setproperty, convertTo, h, bind, Except.bind]
  · intro V r x f v ty hx h1 h2
    cases x with
    | module m => exact absurd rfl (hx m)
    | _ => simp [storedValue, h1, convertTo, h2, bind, Except.bind]
  · intro _ _ _ _; rfl
  · intro _ _; rfl
  · intro _ _ _; rfl
  · intro e b o; cases e <;> cases b <;> rfl
  · intro e b o; rfl
  · intro o; rfl
  · intro _ _ _ _ _ _; rfl
  · intro x y; exact ⟨strcat_eq x y, by simp [strcat_eq]⟩
  · intro t; exact Nat.mod_lt _ (by decide)
  · intro _ _ _; rfl
  · intro _ _ _ _; rfl
  · intro _ _; rfl
  · intro _ _ _ _ _; rfl
  · intro _ _ _ _ _ _; rfl
  · intro a; cases a <;> rfl
  · rfl
  · intro α _ x y; simp [eqFallback]
  · intro args as h; exact processSysimgArgs_len args as h
  · intro f hf
    have this : (f = "--buildsettings" || f = "--buildroot" || f = "--dataroot") = true := by
      simpa [or_assoc] using hf
    simp only [processSysimgArgs, this, ↓reduceIte]
end JuliaLean.RuntimeCov.BaseCompiler
end
