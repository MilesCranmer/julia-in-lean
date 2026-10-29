import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ReducedimRepairCount

open JuliaLean.Registry

inductive Error where | source (id : Nat) deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

def countDefault (count : (X → X) → A → D → N → Result R)
    (array : A) (dims : D) (initial : N) := count id array dims initial

def countPredicate (count : F → A → D → N → Result R)
    (function : F) (array : A) (dims : D) (initial : N) :=
  count function array dims initial

def countColon (simpleCount : F → A → N → Result R)
    (function : F) (array : A) (initial : N) := simpleCount function array initial

def countDims (boolMap : F → Result B)
    (mapreduce : B → Op → A → D → N → Result R) (addSum : Op)
    (function : F) (array : A) (dims : D) (initial : N) : Result R :=
  match boolMap function with
  | .error error => .error error
  | .ok mapped => mapreduce mapped addSum array dims initial

def countBangDefault (countBang : (X → X) → R → A → Bool → Result R)
    (result : R) (array : A) (initFlag : Bool) := countBang id result array initFlag

def countBang (boolMap : F → Result B)
    (initarray : R → F → Op → Bool → A → Result R)
    (mapreduce : B → Op → R → A → Result R) (addSum : Op)
    (function : F) (result : R) (array : A) (initFlag : Bool) : Result R :=
  match boolMap function with
  | .error error => .error error
  | .ok mapped => match initarray result function addSum initFlag array with
    | .error error => .error error
    | .ok initialized => match mapreduce mapped addSum initialized array with
      | .error error => .error error
      | .ok _ => .ok result

def Contract : Prop :=
  (∀ {X A D N R : Type} count array dims initial,
    countDefault (X := X) (A := A) (D := D) (N := N) (R := R)
      count array dims initial = count id array dims initial) ∧
  (∀ {F A D N R : Type} count function array dims initial,
    countPredicate (F := F) (A := A) (D := D) (N := N) (R := R)
      count function array dims initial = count function array dims initial) ∧
  (∀ {F A N R : Type} simple function array initial,
    countColon (F := F) (A := A) (N := N) (R := R)
      simple function array initial = simple function array initial) ∧
  (∀ {F B Op A D N R : Type} boolMap mapreduce addSum function array dims initial output,
    countDims (F := F) (B := B) (Op := Op) (A := A) (D := D) (N := N) (R := R)
      boolMap mapreduce addSum function array dims initial = .ok output →
      ∃ mapped, boolMap function = .ok mapped ∧
        mapreduce mapped addSum array dims initial = .ok output) ∧
  (∀ {X R A : Type} countBang result array initFlag,
    countBangDefault (X := X) (R := R) (A := A) countBang result array initFlag =
      countBang id result array initFlag) ∧
  (∀ {F B R Op A : Type} boolMap initarray mapreduce addSum function result array initFlag output,
    countBang (F := F) (B := B) (R := R) (Op := Op) (A := A)
      boolMap initarray mapreduce addSum function result array initFlag = .ok output →
      output = result ∧ ∃ mapped initialized changed,
        boolMap function = .ok mapped ∧ initarray result function addSum initFlag array = .ok initialized ∧
        mapreduce mapped addSum initialized array = .ok changed)

theorem contract : Contract := by
  unfold Contract
  refine ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, ?_,
    fun _ _ _ _ => rfl, ?_⟩
  · intro F B Op A D N R boolMap mapreduce addSum function array dims initial output h
    cases hb : boolMap function with
    | error error => simp [countDims, hb] at h
    | ok mapped => exact ⟨mapped, rfl, by simpa [countDims, hb] using h⟩
  · intro F B R Op A boolMap initarray mapreduce addSum function result array initFlag output h
    cases hb : boolMap function with
    | error error => simp [countBang, hb] at h
    | ok mapped =>
        cases hi : initarray result function addSum initFlag array with
        | error error => simp [countBang, hb, hi] at h
        | ok initialized =>
            cases hm : mapreduce mapped addSum initialized array with
            | error error => simp [countBang, hb, hi, hm] at h
            | ok changed =>
                simp [countBang, hb, hi, hm] at h
                subst output
                exact ⟨rfl, mapped, initialized, changed, rfl, rfl, hm⟩

def entries : List Entry := []

end JuliaLean.MultidimCov.ReducedimRepairCount
