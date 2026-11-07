import JuliaLean.base.Enums
import JuliaLean.Proofs.base.Enums.Coverage

namespace JuliaLean.ExprReflect

open JuliaLean

def EnumRow17Property : Prop := ∀ base, enumRow17 base = base

theorem enumRow17_proven : EnumRow17Property := by intro; rfl

/-- `(::Type{T})(x::Enum{T2})`; `base/Enums.jl:19`. -/

def EnumRow19Property : Prop := ∀ target x value,
  enumRow19 target x = .ok value → target.min ≤ value ∧ value ≤ target.max

theorem enumRow19_proven : EnumRow19Property := by
  unfold EnumRow19Property
  intro target x value h
  cases hconvert : JInt.convert (target.name) target x.value with
  | error error => simp [enumRow19, hconvert] at h
  | ok converted =>
    simp [enumRow19, hconvert] at h
    rw [← h]
    exact converted.property

/-- `Base.cconvert(::Type{T}, x::Enum{T2})`; `base/Enums.jl:20`. -/

def EnumRow20Property : Prop := ∀ target x, enumRow20 target x = enumRow19 target x

theorem enumRow20_proven : EnumRow20Property := by unfold EnumRow20Property; intros; rfl

/-- `Base.write(io, x::Enum{T})`; `base/Enums.jl:21`. -/

def EnumRow21Property : Prop := ∀ writer x written,
  enumBoxInRange x = true → enumRow21 writer x = .ok written → written = writer x.value

theorem enumRow21_proven : EnumRow21Property := by
  unfold EnumRow21Property
  intro writer x written hrange h
  rcases x with ⟨base, stored⟩
  simp [enumBoxInRange] at hrange
  simp [enumRow21, enumRow19, JInt.convert, hrange] at h
  simpa using h.symm

def EnumRow22Property : Prop := ∀ reader base values box,
  enumRow22 reader base values = .ok box → box.base = base ∧ box.value ∈ values

theorem enumRow22_proven : EnumRow22Property := by
  unfold EnumRow22Property
  intro reader base values box h
  by_cases hmember : reader base ∈ values
  · cases hconvert : JInt.convert (base.name) base (reader base) with
    | error error => simp [enumRow22, enumConstruct, hmember, hconvert] at h
    | ok converted =>
      simp [enumRow22, enumConstruct, hmember, hconvert] at h
      cases h
      have heq : converted.val = reader base := by
        simp [JInt.convert] at hconvert
        split at hconvert <;> simp_all
        rw [← hconvert]
      exact ⟨rfl, by simpa [heq] using hmember⟩
  · simp [enumRow22, enumConstruct, hmember] at h

/-- `_enum_hash(x::Enum, h)` delegates to `hash(::Any, h)`; `base/Enums.jl:30`. -/

def EnumRow30Property : Prop := ∀ genericHash x seed,
  enumRow30 genericHash x seed = genericHash x seed

theorem enumRow30_proven : EnumRow30Property := by unfold EnumRow30Property; intros; rfl

/-- `Base.hash(x::Enum, h)` delegates to `_enum_hash`; `base/Enums.jl:31`. -/

def EnumRow31Property : Prop := ∀ specializedHash x seed,
  enumRow31 specializedHash x seed = specializedHash x seed

theorem enumRow31_proven : EnumRow31Property := by unfold EnumRow31Property; intros; rfl

/-- `Base.isless(x::T, y::T)`; `base/Enums.jl:32`. -/

def EnumRow32Property : Prop := ∀ x y, enumRow32 x y = true ↔ x.value < y.value

theorem enumRow32_proven : EnumRow32Property := by
  unfold EnumRow32Property
  intros
  simp [enumRow32]

def EnumRow34Property : Prop := ∀ names x,
  enumRow34 names x = match enumNameLookup names x.value with
    | some name => .ok name
    | none => .keyError x.value

theorem enumRow34_proven : EnumRow34Property := by
  unfold EnumRow34Property
  intros
  rfl

/-- `_symbol(x::Enum)`; `base/Enums.jl:36-40`. -/

def EnumRow36Property : Prop := ∀ names x,
  enumNameLookup names x.value = none → enumRow36 names x = "<invalid #" ++ toString x.value ++ ">"

theorem enumRow36_proven : EnumRow36Property := by
  unfold EnumRow36Property
  intro names x h
  simp [enumRow36, h]

/-- `Base.print(io, x::Enum)`; `base/Enums.jl:42`. -/

def EnumRow42Property : Prop := ∀ names x, enumRow42 names x = enumRow36 names x

theorem enumRow42_proven : EnumRow42Property := by unfold EnumRow42Property; intros; rfl

/-- Compact/module-aware `Base.show(io, x::Enum)`; `base/Enums.jl:44-55`. -/

def EnumRow44Property : Prop := ∀ names moduleName compact visible x,
  enumRow44 names moduleName compact visible x =
    (if compact then "" else if visible then "" else moduleName ++ ".") ++ enumRow36 names x

theorem enumRow44_proven : EnumRow44Property := by unfold EnumRow44Property; intros; rfl

/-- Plain-text `show` for an enum value; `base/Enums.jl:57-62`. -/

def EnumRow57Property : Prop := ∀ names typeName x,
  enumRow57 names typeName x = enumRow42 names x ++ "::" ++ typeName ++ " = " ++ toString x.value

theorem enumRow57_proven : EnumRow57Property := by unfold EnumRow57Property; intros; rfl

/-- Plain-text `show` for an enum type; `base/Enums.jl:64-76`. -/

def EnumRow64Property : Prop := ∀ typeName names,
  (enumRow64 true typeName names).length = names.length + 1 ∧
  enumRow64 false typeName names = ["invoke(show, Type)"]

theorem enumRow64_proven : EnumRow64Property := by
  unfold EnumRow64Property
  intros
  simp [enumRow64]

def EnumRow79Property : Prop := ∀ base value, enumRow79 base [value] = .ok (.interval value value)

theorem enumRow79_proven : EnumRow79Property := by
  unfold EnumRow79Property
  intro base value
  rfl

/-- `Base.broadcastable(x::Enum) = Ref(x)`; `base/Enums.jl:91`. -/

def EnumRow91Property : Prop := ∀ x, enumRow91 x = [x]

theorem enumRow91_proven : EnumRow91Property := by unfold EnumRow91Property; intro; rfl

/-- `enum_argument_error`; `base/Enums.jl:93`. -/

def EnumRow93Property : Prop := ∀ typeName value,
  enumRow93 typeName value = .error (.argumentError ("invalid value for Enum " ++ typeName ++ ": " ++ toString value))

theorem enumRow93_proven : EnumRow93Property := by unfold EnumRow93Property; intros; rfl

def EnumRow144Property : Prop := ∀ bounds request,
  (request.rawMembers = [] → enumRow144 bounds request = .error (.argumentError "no arguments given for Enum")) ∧
  (request.rawMembers ≠ [] → request.typeExpressionValid = false →
    enumRow144 bounds request = .error (.argumentError "invalid type expression for enum")) ∧
  (request.rawMembers ≠ [] → request.typeExpressionValid = true → request.baseTypeValid = false →
    enumRow144 bounds request = .error (.argumentError "invalid base type for Enum")) ∧
  (request.rawMembers ≠ [] → request.typeExpressionValid = true → request.baseTypeValid = true →
    enumRow144 bounds request = match prepareEnumMembers request.rawMembers with
      | .error error => .error error
      | .ok members => enumBuild bounds members)

theorem enumRow144_proven : EnumRow144Property := by
  unfold EnumRow144Property
  intro bounds request
  constructor
  · intro hempty; simp [enumRow144, hempty]
  constructor
  · intro hnonempty htype; simp [enumRow144, hnonempty, htype]
  constructor
  · intro hnonempty htype hbase; simp [enumRow144, hnonempty, htype, hbase]
  · intro hnonempty htype hbase
    cases prepared : prepareEnumMembers request.rawMembers <;>
      simp [enumRow144, hnonempty, htype, hbase, prepared]

/-- Generated enum constructor; `base/Enums.jl:221-224`. -/

def EnumRow221Property : Prop := ∀ base values input box,
  enumRow221 base values input = .ok box → box.value ∈ values

theorem enumRow221_proven : EnumRow221Property := by
  unfold EnumRow221Property
  intro base values input box h
  exact (enumRow22_proven (fun _ => input) base values box h).2

/-- Generated `Enums.namemap`; `base/Enums.jl:225`. -/

def EnumRow225Property : Prop := ∀ names, enumRow225 names = names

theorem enumRow225_proven : EnumRow225Property := by unfold EnumRow225Property; intro; rfl

/-- Generated `Base.typemin`; `base/Enums.jl:226`. -/

def EnumRow226Property : Prop := ∀ result, enumRow226 result = result.typeminValue

theorem enumRow226_proven : EnumRow226Property := by unfold EnumRow226Property; intro; rfl

/-- Generated `Base.typemax`; `base/Enums.jl:227`. -/

def EnumRow227Property : Prop := ∀ result, enumRow227 result = result.typemaxValue

theorem enumRow227_proven : EnumRow227Property := by unfold EnumRow227Property; intro; rfl

/-- Generated specialized `_enum_hash`; `base/Enums.jl:228-233`. -/

def EnumRow233Property : Prop := ∀ hashType hashValue typeHash x seed,
  enumRow233 hashType hashValue typeHash x seed = hashType typeHash (hashValue x.value seed)

theorem enumRow233_proven : EnumRow233Property := by unfold EnumRow233Property; intros; rfl

/-- Generated `Base.instances`; `base/Enums.jl:235-236`. -/

def EnumRow236Property : Prop := ∀ result, enumRow236 result = result.instances

theorem enumRow236_proven : EnumRow236Property := by unfold EnumRow236Property; intro; rfl

end JuliaLean.ExprReflect
