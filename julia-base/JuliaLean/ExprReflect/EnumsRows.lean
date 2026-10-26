import JuliaLean.ExprReflect.Coverage

namespace JuliaLean.ExprReflect

open JuliaLean

/-! Exact row models for `base/Enums.jl` at `bbfa0ce4150`. -/

structure EnumBox where
  base : IntTy
  value : Int
  deriving Repr, DecidableEq, Inhabited

def enumBoxInRange (box : EnumBox) : Bool :=
  box.base.min ≤ box.value && box.value ≤ box.base.max

/-- `basetype(::Type{<:Enum{T}})`; `base/Enums.jl:17`. -/
def enumRow17 (base : IntTy) : IntTy := base

def EnumRow17Property : Prop := ∀ base, enumRow17 base = base
theorem enumRow17_proven : EnumRow17Property := by intro; rfl

/-- `(::Type{T})(x::Enum{T2})`; `base/Enums.jl:19`. -/
def enumRow19 (target : IntTy) (x : EnumBox) : Jl Int := do
  match JInt.convert target x.value with
  | .error error => .error error
  | .ok value => .ok value.val

def EnumRow19Property : Prop := ∀ target x value,
  enumRow19 target x = .ok value → target.min ≤ value ∧ value ≤ target.max

theorem enumRow19_proven : EnumRow19Property := by
  unfold EnumRow19Property
  intro target x value h
  cases hconvert : JInt.convert target x.value with
  | error error => simp [enumRow19, hconvert] at h
  | ok converted =>
    simp [enumRow19, hconvert] at h
    rw [← h]
    exact converted.property

/-- `Base.cconvert(::Type{T}, x::Enum{T2})`; `base/Enums.jl:20`. -/
def enumRow20 (target : IntTy) (x : EnumBox) : Jl Int := enumRow19 target x

def EnumRow20Property : Prop := ∀ target x, enumRow20 target x = enumRow19 target x
theorem enumRow20_proven : EnumRow20Property := by unfold EnumRow20Property; intros; rfl

/-- `Base.write(io, x::Enum{T})`; `base/Enums.jl:21`. -/
def enumRow21 (writer : Int → Nat) (x : EnumBox) : Jl Nat := do
  match enumRow19 x.base x with
  | .error error => .error error
  | .ok value => .ok (writer value)

def EnumRow21Property : Prop := ∀ writer x written,
  enumBoxInRange x = true → enumRow21 writer x = .ok written → written = writer x.value

theorem enumRow21_proven : EnumRow21Property := by
  unfold EnumRow21Property
  intro writer x written hrange h
  rcases x with ⟨base, stored⟩
  simp [enumBoxInRange] at hrange
  simp [enumRow21, enumRow19, JInt.convert, hrange] at h
  simpa using h.symm

def enumConstruct (base : IntTy) (validValues : List Int) (value : Int) : Jl EnumBox := do
  if !validValues.contains value then .error (.argumentError "invalid value for Enum")
  else match JInt.convert base value with
    | .error error => .error error
    | .ok converted => .ok ⟨base, converted.val⟩

/-- `Base.read(io, ::Type{T}) where T<:Enum`; `base/Enums.jl:22`. -/
def enumRow22 (reader : IntTy → Int) (base : IntTy) (validValues : List Int) : Jl EnumBox :=
  enumConstruct base validValues (reader base)

def EnumRow22Property : Prop := ∀ reader base values box,
  enumRow22 reader base values = .ok box → box.base = base ∧ box.value ∈ values

theorem enumRow22_proven : EnumRow22Property := by
  unfold EnumRow22Property
  intro reader base values box h
  by_cases hmember : reader base ∈ values
  · cases hconvert : JInt.convert base (reader base) with
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
def enumRow30 (genericHash : EnumBox → Nat → Nat) (x : EnumBox) (seed : Nat) : Nat :=
  genericHash x seed

def EnumRow30Property : Prop := ∀ genericHash x seed,
  enumRow30 genericHash x seed = genericHash x seed
theorem enumRow30_proven : EnumRow30Property := by unfold EnumRow30Property; intros; rfl

/-- `Base.hash(x::Enum, h)` delegates to `_enum_hash`; `base/Enums.jl:31`. -/
def enumRow31 (specializedHash : EnumBox → Nat → Nat) (x : EnumBox) (seed : Nat) : Nat :=
  specializedHash x seed

def EnumRow31Property : Prop := ∀ specializedHash x seed,
  enumRow31 specializedHash x seed = specializedHash x seed
theorem enumRow31_proven : EnumRow31Property := by unfold EnumRow31Property; intros; rfl

/-- `Base.isless(x::T, y::T)`; `base/Enums.jl:32`. -/
def enumRow32 (x y : EnumBox) : Bool := x.value < y.value

def EnumRow32Property : Prop := ∀ x y, enumRow32 x y = true ↔ x.value < y.value
theorem enumRow32_proven : EnumRow32Property := by
  unfold EnumRow32Property
  intros
  simp [enumRow32]

def enumNameLookup (names : List (Int × String)) (value : Int) : Option String :=
  (names.find? (·.1 == value)).map (·.2)

/-- `Base.Symbol(x::Enum)`; `base/Enums.jl:34`. -/
inductive EnumNameResult where
  | ok (name : String)
  | keyError (value : Int)
  deriving Repr, DecidableEq, Inhabited

def enumRow34 (names : List (Int × String)) (x : EnumBox) : EnumNameResult :=
  match enumNameLookup names x.value with
  | some name => .ok name
  | none => .keyError x.value

def EnumRow34Property : Prop := ∀ names x,
  enumRow34 names x = match enumNameLookup names x.value with
    | some name => .ok name
    | none => .keyError x.value

theorem enumRow34_proven : EnumRow34Property := by
  unfold EnumRow34Property
  intros
  rfl

/-- `_symbol(x::Enum)`; `base/Enums.jl:36-40`. -/
def enumRow36 (names : List (Int × String)) (x : EnumBox) : String :=
  (enumNameLookup names x.value).getD ("<invalid #" ++ toString x.value ++ ">")

def EnumRow36Property : Prop := ∀ names x,
  enumNameLookup names x.value = none → enumRow36 names x = "<invalid #" ++ toString x.value ++ ">"

theorem enumRow36_proven : EnumRow36Property := by
  unfold EnumRow36Property
  intro names x h
  simp [enumRow36, h]

/-- `Base.print(io, x::Enum)`; `base/Enums.jl:42`. -/
def enumRow42 (names : List (Int × String)) (x : EnumBox) : String := enumRow36 names x

def EnumRow42Property : Prop := ∀ names x, enumRow42 names x = enumRow36 names x
theorem enumRow42_proven : EnumRow42Property := by unfold EnumRow42Property; intros; rfl

/-- Compact/module-aware `Base.show(io, x::Enum)`; `base/Enums.jl:44-55`. -/
def enumRow44 (names : List (Int × String)) (definitionModule : String)
    (compact visible : Bool) (x : EnumBox) : String :=
  let renderedPrefix := if compact then "" else if visible then "" else definitionModule ++ "."
  renderedPrefix ++ enumRow36 names x

def EnumRow44Property : Prop := ∀ names moduleName compact visible x,
  enumRow44 names moduleName compact visible x =
    (if compact then "" else if visible then "" else moduleName ++ ".") ++ enumRow36 names x

theorem enumRow44_proven : EnumRow44Property := by unfold EnumRow44Property; intros; rfl

/-- Plain-text `show` for an enum value; `base/Enums.jl:57-62`. -/
def enumRow57 (names : List (Int × String)) (typeName : String) (x : EnumBox) : String :=
  enumRow42 names x ++ "::" ++ typeName ++ " = " ++ toString x.value

def EnumRow57Property : Prop := ∀ names typeName x,
  enumRow57 names typeName x = enumRow42 names x ++ "::" ++ typeName ++ " = " ++ toString x.value
theorem enumRow57_proven : EnumRow57Property := by unfold EnumRow57Property; intros; rfl

/-- Plain-text `show` for an enum type; `base/Enums.jl:64-76`. -/
def enumRow64 (concrete : Bool) (typeName : String) (names : List (Int × String)) : List String :=
  if concrete then ("Enum " ++ typeName ++ ":") :: names.map (fun pair => pair.2 ++ " = " ++ toString pair.1)
  else ["invoke(show, Type)"]

def EnumRow64Property : Prop := ∀ typeName names,
  (enumRow64 true typeName names).length = names.length + 1 ∧
  enumRow64 false typeName names = ["invoke(show, Type)"]

theorem enumRow64_proven : EnumRow64Property := by
  unfold EnumRow64Property
  intros
  simp [enumRow64]

inductive EnumMembershipExpr where
  | interval (lo hi : Int)
  | disjunction (values : List Int)
  | setMembership (values : List Int)
  deriving Repr, DecidableEq, Inhabited

/-- `membershiptest(expr, values)`; `base/Enums.jl:79-88`. -/
def enumRow79 (base : IntTy) (values : List Int) : Jl EnumMembershipExpr :=
  match values with
  | [] => .error (.argumentError "extrema of empty enum values")
  | [value] => .ok (.interval value value)
  | first :: rest =>
    let lo := rest.foldl min first
    let hi := rest.foldl max first
    let span := wrapInt base (hi - lo + 1)
    if (values.length : Int) = span then .ok (.interval lo hi)
    else if values.length < 20 then .ok (.disjunction values) else .ok (.setMembership values)

def EnumRow79Property : Prop := ∀ base value, enumRow79 base [value] = .ok (.interval value value)

theorem enumRow79_proven : EnumRow79Property := by
  unfold EnumRow79Property
  intro base value
  rfl

/-- `Base.broadcastable(x::Enum) = Ref(x)`; `base/Enums.jl:91`. -/
def enumRow91 (x : EnumBox) : List EnumBox := [x]

def EnumRow91Property : Prop := ∀ x, enumRow91 x = [x]
theorem enumRow91_proven : EnumRow91Property := by unfold EnumRow91Property; intro; rfl

/-- `enum_argument_error`; `base/Enums.jl:93`. -/
def enumRow93 (typeName : String) (value : Int) : Jl Unit :=
  .error (.argumentError ("invalid value for Enum " ++ typeName ++ ": " ++ toString value))

def EnumRow93Property : Prop := ∀ typeName value,
  enumRow93 typeName value = .error (.argumentError ("invalid value for Enum " ++ typeName ++ ": " ++ toString value))
theorem enumRow93_proven : EnumRow93Property := by unfold EnumRow93Property; intros; rfl

inductive RawEnumMember where
  | line
  | implicit (name : String) (validIdentifier : Bool)
  | explicit (name : String) (validIdentifier : Bool) (value : Int)
  | documented (member : RawEnumMember)
  | invalid
  deriving Repr, DecidableEq, Inhabited

def prepareEnumMembers : List RawEnumMember → Jl (List EnumMember)
  | [] => .ok []
  | .line :: rest => prepareEnumMembers rest
  | .documented member :: rest => prepareEnumMembers (member :: rest)
  | .implicit name valid :: rest =>
    if !valid then .error (.argumentError "invalid enum identifier")
    else return ⟨name, none⟩ :: (← prepareEnumMembers rest)
  | .explicit name valid value :: rest =>
    if !valid then .error (.argumentError "invalid enum identifier")
    else return ⟨name, some value⟩ :: (← prepareEnumMembers rest)
  | .invalid :: _ => .error (.argumentError "invalid enum argument")

structure EnumMacroRequest where
  typeExpressionValid : Bool
  baseTypeValid : Bool
  rawMembers : List RawEnumMember
  deriving Repr, DecidableEq, Inhabited

/-- `@enum`; `base/Enums.jl:144-252`. -/
def enumRow144 (bounds : EnumBounds) (request : EnumMacroRequest) : Jl EnumResult :=
  if request.rawMembers.isEmpty then .error (.argumentError "no arguments given for Enum")
  else if !request.typeExpressionValid then .error (.argumentError "invalid type expression for enum")
  else if !request.baseTypeValid then .error (.argumentError "invalid base type for Enum")
  else match prepareEnumMembers request.rawMembers with
    | .error error => .error error
    | .ok members => enumBuild bounds members

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
    simp [enumRow144, hnonempty, htype, hbase]

/-- Generated enum constructor; `base/Enums.jl:221-224`. -/
def enumRow221 (base : IntTy) (values : List Int) (input : Int) : Jl EnumBox :=
  enumConstruct base values input

def EnumRow221Property : Prop := ∀ base values input box,
  enumRow221 base values input = .ok box → box.value ∈ values
theorem enumRow221_proven : EnumRow221Property := by
  unfold EnumRow221Property
  intro base values input box h
  exact (enumRow22_proven (fun _ => input) base values box h).2

/-- Generated `Enums.namemap`; `base/Enums.jl:225`. -/
def enumRow225 (names : List (Int × String)) : List (Int × String) := names

def EnumRow225Property : Prop := ∀ names, enumRow225 names = names
theorem enumRow225_proven : EnumRow225Property := by unfold EnumRow225Property; intro; rfl

/-- Generated `Base.typemin`; `base/Enums.jl:226`. -/
def enumRow226 (result : EnumResult) : Int := result.typeminValue

def EnumRow226Property : Prop := ∀ result, enumRow226 result = result.typeminValue
theorem enumRow226_proven : EnumRow226Property := by unfold EnumRow226Property; intro; rfl

/-- Generated `Base.typemax`; `base/Enums.jl:227`. -/
def enumRow227 (result : EnumResult) : Int := result.typemaxValue

def EnumRow227Property : Prop := ∀ result, enumRow227 result = result.typemaxValue
theorem enumRow227_proven : EnumRow227Property := by unfold EnumRow227Property; intro; rfl

/-- Generated specialized `_enum_hash`; `base/Enums.jl:228-233`. -/
def enumRow233 (hashType : Nat → Nat → Nat) (hashValue : Int → Nat → Nat)
    (typeHash : Nat) (x : EnumBox) (seed : Nat) : Nat :=
  hashType typeHash (hashValue x.value seed)

def EnumRow233Property : Prop := ∀ hashType hashValue typeHash x seed,
  enumRow233 hashType hashValue typeHash x seed = hashType typeHash (hashValue x.value seed)
theorem enumRow233_proven : EnumRow233Property := by unfold EnumRow233Property; intros; rfl

/-- Generated `Base.instances`; `base/Enums.jl:235-236`. -/
def enumRow236 (result : EnumResult) : List Int := result.instances

def EnumRow236Property : Prop := ∀ result, enumRow236 result = result.instances
theorem enumRow236_proven : EnumRow236Property := by unfold EnumRow236Property; intro; rfl

end JuliaLean.ExprReflect
