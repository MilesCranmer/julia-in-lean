import JuliaLean.base.Base_compiler
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.Base_compiler
open JuliaLean JuliaLean.base.Base_compiler JuliaLean.Registry

def OrderedGetContract : Prop :=
  (∀ (M V : Type) (getglobal : M → String → String → Result V) m f order,
    getpropertyModuleOrder getglobal m f order = getglobal m f order) ∧
  (∀ (O V : Type) (getfield : O → String → String → Result V) x f order,
    getpropertyOrder getfield x f order = getfield x f order) ∧
  (∀ (O V : Type) (getfield : O → String → String → Result V) x f order,
    getpropertyTypeOrder getfield x f order = getfield x f order) ∧
  (∀ (T V : Type) (getfield : T → JInt .i64 → String → Result V) tuple index order,
    getpropertyTupleOrder getfield tuple index order = getfield tuple index order)

theorem orderedGetContract_proven : OrderedGetContract := by
  simp [OrderedGetContract, getpropertyModuleOrder, getpropertyOrder, getpropertyTypeOrder, getpropertyTupleOrder]


def OrderedSetContract : Prop :=
  (∀ (O M V Ty : Type) (r : PropertyOps Result O M String V Ty) m field value,
    setpropertyModule r m field value = setpropertyModuleOrder r m field value "monotonic") ∧
  (∀ (O V : Type) (x : O) (f order : String) (v : V),
    setpropertyTypeOrder (m := Result) x f v order =
    .error (.errorException "setfield! fields of Types should not be changed")) ∧
  (∀ (T V : Type) (setfield : T → JInt .i64 → V → String → Result V) t index value order,
    setpropertyTupleOrder setfield t index value order = setfield t index value order) ∧
  (∀ (O M V Ty : Type) (r : PropertyOps Result O M String V Ty) x f value order err,
    r.fieldtype (r.typeof x) f = .error err → setpropertyOrder r x f value order = .error err) ∧
  (∀ (O M V Ty : Type) (r : PropertyOps Result O M String V Ty) m f value order err,
    r.bindingType m f = .error err → setpropertyModuleOrder r m f value order = .error err) ∧
  (∀ (O M V Ty : Type) (r : PropertyOps Result O M String V Ty) x f value order ty,
    r.fieldtype (r.typeof x) f = .ok ty → r.isa value ty = true →
    setpropertyOrder r x f value order = r.setfield x f value order) ∧
  (∀ (O M V Ty : Type) (r : PropertyOps Result O M String V Ty) m f value order ty,
    r.bindingType m f = .ok ty → r.isa value ty = true →
    setpropertyModuleOrder r m f value order = r.setglobal m f value order) ∧
  (∀ (O M V Ty : Type) (r : PropertyOps Result O M String V Ty) x f value order ty converted,
    r.fieldtype (r.typeof x) f = .ok ty → r.isa value ty = false → r.convert ty value = .ok converted →
    setpropertyOrder r x f value order = r.setfield x f converted order) ∧
  (∀ (O M V Ty : Type) (r : PropertyOps Result O M String V Ty) m f value order ty converted,
    r.bindingType m f = .ok ty → r.isa value ty = false → r.convert ty value = .ok converted →
    setpropertyModuleOrder r m f value order = r.setglobal m f converted order) ∧
  (∀ (O M V Ty : Type) (r : PropertyOps Result O M String V Ty) x f value order ty err,
    r.fieldtype (r.typeof x) f = .ok ty → r.isa value ty = false → r.convert ty value = .error err →
    setpropertyOrder r x f value order = .error err) ∧
  (∀ (O M V Ty : Type) (r : PropertyOps Result O M String V Ty) m f value order ty err,
    r.bindingType m f = .ok ty → r.isa value ty = false → r.convert ty value = .error err →
    setpropertyModuleOrder r m f value order = .error err)

theorem orderedSetContract_proven : OrderedSetContract := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intro O V x f order v; rfl
  · intro T V setfield t index value order; rfl
  · intro O M V Ty r x f value order err h
    simp [setpropertyOrder, h, bind, Except.bind]
  · intro O M V Ty r m f value order err h
    simp [setpropertyModuleOrder, h, bind, Except.bind]
  · intro O M V Ty r x f value order ty ht hi
    simp [setpropertyOrder, ht, hi, bind, Except.bind, pure, Except.pure]
  · intro O M V Ty r m f value order ty ht hi
    simp [setpropertyModuleOrder, ht, hi, bind, Except.bind, pure, Except.pure]
  · intro O M V Ty r x f value order ty converted ht hi hc
    simp [setpropertyOrder, ht, hi, hc, bind, Except.bind, pure, Except.pure]
  · intro O M V Ty r m f value order ty converted ht hi hc
    simp [setpropertyModuleOrder, ht, hi, hc, bind, Except.bind, pure, Except.pure]
  · intro O M V Ty r x f value order ty err ht hi hc
    simp [setpropertyOrder, ht, hi, hc, bind, Except.bind]
  · intro O M V Ty r m f value order ty err ht hi hc
    simp [setpropertyModuleOrder, ht, hi, hc, bind, Except.bind]


def SwapPropertyContract : Prop :=
  (∀ (O M V Ty : Type) (r : PropertyOps Result O M String V Ty) swap x f value order ty,
    r.fieldtype (r.typeof x) f = .ok ty → r.isa value ty = true →
    swappropertyOrder { r with swapfield := swap } x f value order = swap x f value order) ∧
  (∀ (O M V Ty : Type) (r : PropertyOps Result O M String V Ty) swap m f value order ty,
    r.bindingType m f = .ok ty → r.isa value ty = true →
    swappropertyModuleOrder { r with swapglobal := swap } m f value order = swap m f value order) ∧
  (∀ (O M V Ty : Type) (r : PropertyOps Result O M String V Ty) swap x f value order ty converted,
    r.fieldtype (r.typeof x) f = .ok ty → r.isa value ty = false → r.convert ty value = .ok converted →
    swappropertyOrder { r with swapfield := swap } x f value order = swap x f converted order) ∧
  (∀ (O M V Ty : Type) (r : PropertyOps Result O M String V Ty) swap m f value order ty converted,
    r.bindingType m f = .ok ty → r.isa value ty = false → r.convert ty value = .ok converted →
    swappropertyModuleOrder { r with swapglobal := swap } m f value order = swap m f converted order) ∧
  (∀ (O M V Ty : Type) (r : PropertyOps Result O M String V Ty) swap x f value,
    swapproperty { r with swapfield := swap } x f value = swappropertyOrder { r with swapfield := swap } x f value "not_atomic") ∧
  (∀ (O M V Ty : Type) (r : PropertyOps Result O M String V Ty) swap m f value,
    swappropertyModule { r with swapglobal := swap } m f value = swappropertyModuleOrder { r with swapglobal := swap } m f value "not_atomic")

theorem swapPropertyContract_proven : SwapPropertyContract := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro O M V Ty r swap x f value order ty ht hi
    simp [swappropertyOrder, ht, hi, bind, Except.bind, pure, Except.pure]
  · intro O M V Ty r swap m f value order ty ht hi
    simp [swappropertyModuleOrder, ht, hi, bind, Except.bind, pure, Except.pure]
  · intro O M V Ty r swap x f value order ty converted ht hi hc
    simp [swappropertyOrder, ht, hi, hc, bind, Except.bind, pure, Except.pure]
  · intro O M V Ty r swap m f value order ty converted ht hi hc
    simp [swappropertyModuleOrder, ht, hi, hc, bind, Except.bind, pure, Except.pure]
  · intros; rfl
  · intros; rfl


def ModifyPropertyContract : Prop :=
  (∀ (O V F R : Type) (modify : O → String → F → V → String → Result R) object field op value order,
    modifypropertyOrder modify object field op value order = modify object field op value order) ∧
  (∀ (O V F R : Type) (modify : O → String → F → V → String → Result R) object field op value order,
    modifypropertyModuleOrder modify object field op value order = modify object field op value order) ∧
  (∀ (O V F R : Type) (modify : O → String → F → V → String → Result R) object field op value,
    modifyproperty modify object field op value = modify object field op value "not_atomic") ∧
  (∀ (O V F R : Type) (modify : O → String → F → V → String → Result R) object field op value,
    modifypropertyModule modify object field op value = modify object field op value "not_atomic")

theorem modifyPropertyContract_proven : ModifyPropertyContract := by
  simp [ModifyPropertyContract, modifypropertyOrder, modifypropertyModuleOrder,
    modifyproperty, modifypropertyModule]


def entries : List Entry := [
  { id := "runtimecov-base-compiler-ordered-get", juliaFile := "base/Base_compiler.jl"
    juliaFns := ["getproperty(::Module,::Symbol,::Symbol)", "getproperty(::Type,::Symbol,::Symbol)", "getproperty(::Tuple,::Int,::Symbol)", "getproperty(::Any,::Symbol,::Symbol)"]
    statement := "Ordered property reads forward the original object, field and memory order to the corresponding global or field operation."
    source := "base/Base_compiler.jl:71,78,80,83", status := .proven
    prop := ``OrderedGetContract, thm := some ``orderedGetContract_proven },
  { id := "runtimecov-base-compiler-ordered-set", juliaFile := "base/Base_compiler.jl"
    juliaFns := ["setproperty!(::Module,::Symbol,::Any,::Symbol)", "setproperty!(::Type,::Symbol,::Any,::Symbol)", "setproperty!(::Tuple,::Int,::Any,::Symbol)", "setproperty!(::Any,::Symbol,::Any,::Symbol)"]
    statement := "Ordered property writes preserve their memory order, convert values when required, and propagate type-lookup failures; type-object writes raise an error."
    source := "base/Base_compiler.jl:72-77,79,81,84-89", status := .proven
    prop := ``OrderedSetContract, thm := some ``orderedSetContract_proven },
  { id := "runtimecov-base-compiler-modify-property", juliaFile := "base/Base_compiler.jl"
    juliaFns := ["modifyproperty!(::Any,::Symbol,::Any,::Any,::Symbol)", "modifyproperty!(::Module,::Symbol,::Any,::Any,::Symbol)"]
    statement := "Field and global modification forward the operator, operand, memory order and runtime result unchanged."
    source := "base/Base_compiler.jl:97-100,120-123", status := .proven
    prop := ``ModifyPropertyContract, thm := some ``modifyPropertyContract_proven },
  { id := "runtimecov-base-compiler-swap-property", juliaFile := "base/Base_compiler.jl"
    juliaFns := ["swapproperty!(::Any,::Symbol,::Any,::Symbol)", "swapproperty!(::Module,::Symbol,::Any,::Symbol)"]
    statement := "Field and global swaps convert to the declared type when required, forward the order and return the primitive's old value."
    source := "base/Base_compiler.jl:91-96,114-119", status := .proven
    prop := ``SwapPropertyContract, thm := some ``swapPropertyContract_proven }
]

end JuliaLean.Proofs.base.Base_compiler
