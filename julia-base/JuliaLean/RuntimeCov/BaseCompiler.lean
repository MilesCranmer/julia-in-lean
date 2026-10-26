import JuliaLean.RuntimeCov.Common

/-!
`base/Base_compiler.jl`: the methods that survive bootstrap: `include`
forwarding, the zero-argument meta macros, the property protocol fallbacks with
their field-type conversion, `convert` identities, module setup, `eval`,
`strcat`, `time_ns`, the keyword-call forwarding methods for `invoke`,
`applicable`, `invokelatest` and `invoke_in_world`, `Core._hasmethod`,
`VersionedParse`, the `==` fallback and the sysimage argument parser.
Objects are records of named fields; conversion and binding types are inputs.
-/

namespace JuliaLean.RuntimeCov.BaseCompiler

open JuliaLean.RuntimeCov

/-- `include(path::String)`, base/Base_compiler.jl:30, and
`(this::IncludeInto)(fname)`, line 36: both forward to `include(mod, path)`. -/
def includeBase {μ β : Type} (inc : μ → String → β) (base : μ) (path : String) : β := inc base path
structure IncludeInto (μ : Type) where
  m : μ
/-- `IncludeInto(m)`, base/Base_compiler.jl:34. -/
def mkIncludeInto {μ : Type} (m : μ) : IncludeInto μ := ⟨m⟩
def callIncludeInto {μ β : Type} (inc : μ → String → β) (self : IncludeInto μ) (fname : String) : β :=
  inc self.m fname

/-- The expressions produced by `@inline()`, `@noinline()`, `@_boundscheck()`,
base/Base_compiler.jl:44-47. -/
inductive MetaExpr where
  | metaHead (head : Sym)
  | boundscheck
  deriving DecidableEq, Repr
def atInline : MetaExpr := .metaHead "inline"
def atNoinline : MetaExpr := .metaHead "noinline"
def atBoundscheck : MetaExpr := .boundscheck

/-- A value as the property protocol sees it. -/
inductive Obj where
  | module (name : String)
  | type (name : String)
  | array
  | tuple
  | other (tyName : String)
  deriving DecidableEq, Repr

/-- The runtime operations used by the property fallbacks: field access, the
declared field type, `isa`, `convert`, the binding type of a global. -/
structure Rt' (V : Type) where
  getfield : Obj → Sym → Rt V
  getglobal : String → Sym → Rt V
  fieldtype : Obj → Sym → Rt String
  bindingType : String → Sym → String
  isa : V → String → Bool
  convert : String → V → Rt V
  setfield : Obj → Sym → V → Rt V
  setglobal : String → Sym → V → Rt V

/-- `getproperty(x, f)` for modules, types, tuples and the fallback,
base/Base_compiler.jl:52-59, 71-83 (the ordered forms pass `order` through). -/
def getproperty {V : Type} (r : Rt' V) (x : Obj) (f : Sym) : Rt V :=
  match x with
  | .module m => r.getglobal m f
  | _ => r.getfield x f

/-- Convert `v` to `ty` unless it already is one (`v isa ty ? v : convert(ty, v)`). -/
def convertTo {V : Type} (r : Rt' V) (ty : String) (v : V) : Rt V :=
  if r.isa v ty then .ok v else r.convert ty v

/-- `setproperty!(x, f, v[, order])`, base/Base_compiler.jl:54-64, 72-89. -/
def setproperty {V : Type} (r : Rt' V) (x : Obj) (f : Sym) (v : V) : Rt V :=
  match x with
  | .type _ => .error (.errorException "setfield! fields of Types should not be changed")
  | .array => .error (.errorException "setfield! fields of Array should not be changed")
  | .tuple => r.setfield x f v
  | .module m => do let val ← convertTo r (r.bindingType m f) v; r.setglobal m f val
  | .other _ => do let ty ← r.fieldtype x f; let val ← convertTo r ty v; r.setfield x f val

/-- `dotgetproperty(x, f)`, base/Base_compiler.jl:69. -/
def dotgetproperty {V : Type} (r : Rt' V) (x : Obj) (f : Sym) : Rt V := getproperty r x f

/-- The value stored by `swapproperty!`, `replaceproperty!` and
`setpropertyonce!`, base/Base_compiler.jl:91-135 (fields and module globals):
the new value converted to the field or binding type. `modifyproperty!`
(lines 97-100, 120-123) passes `op` and `v` through unconverted. -/
def storedValue {V : Type} (r : Rt' V) (x : Obj) (f : Sym) (v : V) : Rt V :=
  match x with
  | .module m => convertTo r (r.bindingType m f) v
  | _ => do let ty ← r.fieldtype x f; convertTo r ty v
def modifyArgs {V W : Type} (op : W) (v : V) : W × V := (op, v)

/-- `convert(::Type{Any}, x)` and `convert(::Type{T}, x::T)`, lines 137-138. -/
def convertIdentity {α : Type} (x : α) : α := x

/-- `_topmod(m)`, base/Base_compiler.jl:147: the runtime's base module for `m`. -/
def topmod {μ : Type} (rt : μ → μ) (m : μ) : μ := rt m

/-- The effects of `_setup_module!(mod, edition)`, base/Base_compiler.jl:148-163:
the constants declared and the syntax version set (none during bootstrap or
with the flisp parser). -/
def setupModule (edition : Option (Nat × Nat)) (bootstrapParser : Bool) (oldest : Nat × Nat) :
    List Sym × Option (Nat × Nat) :=
  let consts := ["include", "eval"]
  match edition with
  | some e => (consts, some e)
  | none => if bootstrapParser then (consts, none) else (consts, some oldest)

/-- `eval(x)` and `eval(m, x)`, base/Base_compiler.jl:169-170. -/
def evalIn {μ α β : Type} (coreEval : μ → α → β) (m : μ) (x : α) : β := coreEval m x

/-- `strcat(x, y)`, base/Base_compiler.jl:194-206, on the byte contents: a
fresh string of `sizeof(x) + sizeof(y)` bytes, `x`'s bytes then `y`'s. -/
def strcat (x y : List UInt8) : List UInt8 :=
  let out := List.replicate (x.length + y.length) (0 : UInt8)
  let out := x ++ out.drop x.length
  out.take x.length ++ y ++ (out.drop (x.length + y.length))

/-- `time_ns()`, base/Base_compiler.jl:219: the runtime clock. -/
def timeNs (hrtime : Nat) : Nat := hrtime % 2 ^ 64

/-- `Core.kwcall(kwargs, invoke, f, T, args...)`, base/Base_compiler.jl:235-240:
the signature passed on is `Tuple{typeof(kwargs), typeof(f), T.parameters...}`. -/
def kwcallInvokeSig (kwT fT : String) (params : List String) : List String := kwT :: fT :: params

/-- `Core.kwcall(kwargs, applicable, args...)`, lines 246-249: the argument
list given to `applicable`. -/
def kwcallApplicableArgs {α : Type} (kwcall kwargs : α) (args : List α) : List α := kwcall :: kwargs :: args

/-- `Core._hasmethod(f, t)`, lines 250-255: `Tuple{Typeof(f), t.parameters...}`. -/
def hasmethodSig (fT : String) (params : List String) : List String := fT :: params

/-- `Core.kwcall(kwargs, invokelatest, f, args...)`, lines 274-277, and the
`invoke_in_world` form, lines 308-311: the arguments forwarded. -/
def kwcallLatestArgs {α : Type} (kwcall kwargs f : α) (args : List α) : List α := kwcall :: kwargs :: f :: args
def kwcallWorldArgs {α : Type} (world : Nat) (kwcall kwargs f : α) (args : List α) : Nat × List α :=
  (world, kwcall :: kwargs :: f :: args)

/-- `(vp::VersionedParse)(code, filename, lineno, offset, options)`, lines
318-326: whether the edition is passed to the parser. -/
def versionedParsePassesEdition (hasV114Hooks hasV110Hooks : Bool) : Bool :=
  !(!hasV114Hooks && hasV110Hooks)

/-- `==(x, y) = x === y`, base/Base_compiler.jl:338. -/
def eqFallback {α : Type} [DecidableEq α] (x y : α) : Bool := decide (x = y)

/-- `process_sysimg_args!()`, base/Base_compiler.jl:395-410: options from
`Core.ARGS[2:end]` in pairs; `none` value means `ARGS[i+1]` is out of range. -/
inductive SysimgArg where
  | buildsettings (file : String)
  | buildroot (dir : String)
  | dataroot (dir : String)
  deriving DecidableEq, Repr

/-- The value of one flag, base/Base_compiler.jl:399-406. -/
def sysimgFlag (flag v : String) : Rt SysimgArg :=
  if flag = "--buildsettings" then .ok (.buildsettings v)
  else if flag = "--buildroot" then .ok (.buildroot v)
  else if flag = "--dataroot" then .ok (.dataroot v)
  else .error (.errorException ("invalid sysimage argument: " ++ flag))

def processSysimgArgs : List String → Rt (List SysimgArg)
  | [] => .ok []
  | flag :: rest =>
    match rest with
    | [] =>
      if flag = "--buildsettings" || flag = "--buildroot" || flag = "--dataroot" then .error .boundsError
      else .error (.errorException ("invalid sysimage argument: " ++ flag))
    | v :: rest' => do
      let a ← sysimgFlag flag v
      let as ← processSysimgArgs rest'
      pure (a :: as)

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
