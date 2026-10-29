import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ReducedimRepairGenerated

open JuliaLean.Registry

inductive Error where | source (id : Nat) deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

def publicUnary (underlying : A → D → K → Result R)
    (array : A) (dims : D) (keywords : K) := underlying array dims keywords

def publicMapped (underlying : F → A → D → K → Result R)
    (function : F) (array : A) (dims : D) (keywords : K) :=
  underlying function array dims keywords

def colonUnary (underlying : (X → X) → A → C → K → Result R)
    (array : A) (colon : C) (keywords : K) := underlying id array colon keywords

def colonMapped (mapFunction : F → Result MF)
    (mapreduce : MF → Op → A → K → Result R) (fixedOperator : Op)
    (function : F) (array : A) (keywords : K) : Result R :=
  match mapFunction function with
  | .error error => .error error
  | .ok mapped => mapreduce mapped fixedOperator array keywords

def reshapedColon (parent : A → Result P) (publicFn : P → Result R) (array : A) : Result R :=
  match parent array with | .error error => .error error | .ok source => publicFn source

def anyAllUnary (underlying : (X → X) → A → K → Result R)
    (array : A) (keywords : K) := underlying id array keywords

def anyAllMapped (underlying : F → A → D → Result R)
    (function : F) (array : A) (dims : D) := underlying function array dims

def generatedBang (mapFunction : F → Result MF)
    (initarray : R → MF → Op → Bool → A → Result R)
    (mapreducedim : MF → Op → R → A → Result R) (fixedOperator : Op)
    (function : F) (result : R) (array : A) (initFlag : Bool) : Result R :=
  match mapFunction function with
  | .error error => .error error
  | .ok mapped => match initarray result mapped fixedOperator initFlag array with
    | .error error => .error error
    | .ok initialized => match mapreducedim mapped fixedOperator initialized array with
      | .error error => .error error
      | .ok _ => .ok result

def generatedBangUnary (underlying : (X → X) → R → A → Bool → Result R)
    (result : R) (array : A) (initFlag : Bool) := underlying id result array initFlag

def generatedDimsUnary (underlying : (X → X) → A → D → K → Result R)
    (array : A) (dims : D) (keywords : K) := underlying id array dims keywords

def generatedDimsMapped (mapFunction : F → Result MF)
    (mapreduce : MF → Op → A → D → K → Result R) (fixedOperator : Op)
    (function : F) (array : A) (dims : D) (keywords : K) : Result R :=
  match mapFunction function with
  | .error error => .error error
  | .ok mapped => mapreduce mapped fixedOperator array dims keywords

def Contract : Prop :=
  (∀ {A D K R : Type} underlying array dims keywords,
    publicUnary (A := A) (D := D) (K := K) (R := R) underlying array dims keywords =
      underlying array dims keywords) ∧
  (∀ {F A D K R : Type} underlying function array dims keywords,
    publicMapped (F := F) (A := A) (D := D) (K := K) (R := R)
      underlying function array dims keywords = underlying function array dims keywords) ∧
  (∀ {X A C K R : Type} underlying array colon keywords,
    colonUnary (X := X) (A := A) (C := C) (K := K) (R := R)
      underlying array colon keywords = underlying id array colon keywords) ∧
  (∀ {F MF Op A K R : Type} mapFunction mapreduce fixed function array keywords output,
    colonMapped (F := F) (MF := MF) (Op := Op) (A := A) (K := K) (R := R)
      mapFunction mapreduce fixed function array keywords = .ok output →
      ∃ mapped, mapFunction function = .ok mapped ∧ mapreduce mapped fixed array keywords = .ok output) ∧
  (∀ {A P R : Type} parent publicFn array output,
    reshapedColon (A := A) (P := P) (R := R) parent publicFn array = .ok output →
      ∃ source, parent array = .ok source ∧ publicFn source = .ok output) ∧
  (∀ {X A K R : Type} underlying array keywords,
    anyAllUnary (X := X) (A := A) (K := K) (R := R) underlying array keywords =
      underlying id array keywords) ∧
  (∀ {F A D R : Type} underlying function array dims,
    anyAllMapped (F := F) (A := A) (D := D) (R := R) underlying function array dims =
      underlying function array dims) ∧
  (∀ {F MF R Op A : Type} mapFunction initarray mapreducedim fixed function result array initFlag output,
    generatedBang (F := F) (MF := MF) (R := R) (Op := Op) (A := A)
      mapFunction initarray mapreducedim fixed function result array initFlag = .ok output →
      output = result ∧ ∃ mapped initialized changed,
        mapFunction function = .ok mapped ∧ initarray result mapped fixed initFlag array = .ok initialized ∧
        mapreducedim mapped fixed initialized array = .ok changed) ∧
  (∀ {X R A : Type} underlying result array initFlag,
    generatedBangUnary (X := X) (R := R) (A := A) underlying result array initFlag =
      underlying id result array initFlag) ∧
  (∀ {X A D K R : Type} underlying array dims keywords,
    generatedDimsUnary (X := X) (A := A) (D := D) (K := K) (R := R)
      underlying array dims keywords = underlying id array dims keywords) ∧
  (∀ {F MF Op A D K R : Type} mapFunction mapreduce fixed function array dims keywords output,
    generatedDimsMapped (F := F) (MF := MF) (Op := Op) (A := A) (D := D) (K := K) (R := R)
      mapFunction mapreduce fixed function array dims keywords = .ok output →
      ∃ mapped, mapFunction function = .ok mapped ∧
        mapreduce mapped fixed array dims keywords = .ok output)

theorem contract : Contract := by
  unfold Contract
  refine ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl,
    ?_, ?_, fun _ _ _ => rfl, fun _ _ _ _ => rfl, ?_, fun _ _ _ _ => rfl,
    fun _ _ _ _ => rfl, ?_⟩
  · intro F MF Op A K R mapFunction mapreduce fixed function array keywords output h
    cases hm : mapFunction function with
    | error error => simp [colonMapped, hm] at h
    | ok mapped => exact ⟨mapped, rfl, by simpa [colonMapped, hm] using h⟩
  · intro A P R parent publicFn array output h
    cases hp : parent array with
    | error error => simp [reshapedColon, hp] at h
    | ok source => exact ⟨source, rfl, by simpa [reshapedColon, hp] using h⟩
  · intro F MF R Op A mapFunction initarray mapreducedim fixed function result array initFlag output h
    cases hm : mapFunction function with
    | error error => simp [generatedBang, hm] at h
    | ok mapped =>
      cases hi : initarray result mapped fixed initFlag array with
      | error error => simp [generatedBang, hm, hi] at h
      | ok initialized =>
        cases hr : mapreducedim mapped fixed initialized array with
        | error error => simp [generatedBang, hm, hi, hr] at h
        | ok changed =>
            simp [generatedBang, hm, hi, hr] at h
            subst output
            exact ⟨rfl, mapped, initialized, changed, rfl, hi, hr⟩
  · intro F MF Op A D K R mapFunction mapreduce fixed function array dims keywords output h
    cases hm : mapFunction function with
    | error error => simp [generatedDimsMapped, hm] at h
    | ok mapped => exact ⟨mapped, rfl, by simpa [generatedDimsMapped, hm] using h⟩

def entries : List Entry := []

end JuliaLean.MultidimCov.ReducedimRepairGenerated
