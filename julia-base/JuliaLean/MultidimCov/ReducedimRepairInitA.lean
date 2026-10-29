import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ReducedimRepairInitA

open JuliaLean.Registry

inductive Error where | source (id : Nat) deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

inductive IdentityKind where | zero | one deriving Repr, DecidableEq

def initIdentityArray (identity : IdentityKind → T → Result V)
    (fill : A → V → Result A) (array : A) (elementType : T)
    (kind : IdentityKind) (initFlag : Bool) : Result A :=
  if !initFlag then .ok array else
  match identity kind elementType with
  | .error error => .error error
  | .ok value => match fill array value with
    | .error error => .error error
    | .ok _ => .ok array

def initExtremaArray (mapfirst : F → A → S → Result A)
    (array : A) (function : F) (source : S) (initFlag : Bool) : Result A :=
  if !initFlag then .ok array else match mapfirst function array source with
  | .error error => .error error
  | .ok _ => .ok array

def initBooleanArray (fill : A → Bool → Result A) (array : A)
    (identity : Bool) (initFlag : Bool) : Result A :=
  if !initFlag then .ok array else match fill array identity with
  | .error error => .error error
  | .ok _ => .ok array

def initarray (reducedIndices : A → D → Result AX)
    (similar : A → T → AX → Result R) (fill : R → V → Result R)
    (array : A) (region : D) (initial : V) (targetType : T) : Result R :=
  match reducedIndices array region with
  | .error error => .error error
  | .ok axes => match similar array targetType axes with
    | .error error => .error error
    | .ok result => fill result initial

inductive TypeTree where
  | atom (name : String)
  | union (left right : TypeTree)
  deriving Repr, DecidableEq

def promoteUnion (promote : TypeTree → TypeTree → TypeTree) : TypeTree → TypeTree
  | .atom name => .atom name
  | .union left right => promote (promoteUnion promote left) (promoteUnion promote right)

inductive RealType where
  | abstractComplex
  | complex (parameter : String)
  | ordinary (name : String)
  deriving Repr, DecidableEq

def realtype : RealType → RealType
  | .abstractComplex => .ordinary "Real"
  | .complex parameter => .ordinary parameter
  | ordinary => ordinary

def mappedRealtype (isAbs : Bool) (type : RealType) : RealType :=
  if isAbs then realtype type else type

def reducedimInit (initializer : F → Op → IdentityKind → A → D → Result R)
    (function : F) (operator : Op) (kind : IdentityKind) (array : A) (region : D) :=
  initializer function operator kind array region

inductive TargetType where | any | concrete (name : String) deriving Repr, DecidableEq

def reducedimInitGeneric (realtypeFn : F → TypeTree → Result TargetType)
    (promoteUnionFn : T → Result TypeTree) (elementType : A → Result T)
    (applicableZero : TargetType → Result Bool) (zero : TargetType → Result X)
    (function : F → X → Result Y) (identity : Y → Result Z)
    (operator : Z → Z → Result Z) (fallbackReduce : F → A → Result X)
    (typeOf : Z → TargetType) (allocate : A → D → Z → TargetType → Result R)
    (f : F) (array : A) (region : D) : Result R :=
  match elementType array with
  | .error error => .error error
  | .ok element => match promoteUnionFn element with
    | .error error => .error error
    | .ok promoted => match realtypeFn f promoted with
      | .error error => .error error
      | .ok target =>
          if target = .any then fallback else
          match applicableZero target with
          | .error error => .error error
          | .ok false => fallback
          | .ok true => match zero target with
            | .error error => .error error
            | .ok zeroValue => match function f zeroValue with
              | .error error => .error error
              | .ok mapped => match identity mapped with
                | .error error => .error error
                | .ok identityValue => match operator identityValue identityValue with
                  | .error error => .error error
                  | .ok initial => allocate array region initial
                      (if typeOf initial = target then target else typeOf initial)
where
  fallback : Result R := match fallbackReduce f array with
    | .error error => .error error
    | .ok reduced => match function f reduced with
      | .error error => .error error
      | .ok mapped => match identity mapped with
        | .error error => .error error
        | .ok initial => allocate array region initial (typeOf initial)

def Contract : Prop :=
  (∀ {T V A : Type} identity fill array elementType kind initFlag output,
    initIdentityArray (T := T) (V := V) (A := A) identity fill array elementType kind initFlag = .ok output →
      output = array) ∧
  (∀ {F A S : Type} mapfirst array function source initFlag output,
    initExtremaArray (F := F) (A := A) (S := S) mapfirst array function source initFlag = .ok output →
      output = array) ∧
  (∀ {A : Type} fill array identity initFlag output,
    initBooleanArray (A := A) fill array identity initFlag = .ok output → output = array) ∧
  (∀ {A D AX T R V : Type} reducedIndices similar fill array region initial target output,
    initarray (A := A) (D := D) (AX := AX) (T := T) (R := R) (V := V)
      reducedIndices similar fill array region initial target = .ok output →
      ∃ axes result, reducedIndices array region = .ok axes ∧
        similar array target axes = .ok result ∧ fill result initial = .ok output) ∧
  (∀ promote tree, promoteUnion promote tree = match tree with
    | .atom name => .atom name
    | .union left right => promote (promoteUnion promote left) (promoteUnion promote right)) ∧
  realtype .abstractComplex = .ordinary "Real" ∧
  (∀ parameter, realtype (.complex parameter) = .ordinary parameter) ∧
  (∀ name, realtype (.ordinary name) = .ordinary name) ∧
  (∀ isAbs type, mappedRealtype isAbs type = if isAbs then realtype type else type) ∧
  (∀ {F Op A D R : Type} initializer f op kind array region,
    reducedimInit (F := F) (Op := Op) (A := A) (D := D) (R := R)
      initializer f op kind array region = initializer f op kind array region) ∧
  (∀ {F T A D X Y Z R : Type} realtypeFn promoteFn elementType applicable zero function identity operator fallback typeOf allocate f array region output,
    reducedimInitGeneric (F := F) (T := T) (A := A) (D := D) (X := X) (Y := Y)
      (Z := Z) (R := R) realtypeFn promoteFn elementType applicable zero function identity operator
      fallback typeOf allocate f array region = .ok output →
      ∃ element promoted target, elementType array = .ok element ∧ promoteFn element = .ok promoted ∧
        realtypeFn f promoted = .ok target ∧
        (target = .any → ∃ reduced mapped initial,
          fallback f array = .ok reduced ∧ function f reduced = .ok mapped ∧
          identity mapped = .ok initial ∧ allocate array region initial (typeOf initial) = .ok output))

theorem promoteUnion_equation (promote : TypeTree → TypeTree → TypeTree) (tree : TypeTree) :
    promoteUnion promote tree = match tree with
      | .atom name => .atom name
      | .union left right => promote (promoteUnion promote left) (promoteUnion promote right) := by
  cases tree <;> rfl

theorem contract : Contract := by
  unfold Contract
  refine ⟨?_, ?_, ?_, ?_, promoteUnion_equation, rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ => rfl, fun _ _ _ _ _ _ => rfl, ?_⟩
  · intro T V A identity fill array elementType kind initFlag output h
    cases initFlag <;> simp [initIdentityArray] at h
    · exact h.symm
    · cases hi : identity kind elementType with
      | error error => simp [hi] at h
      | ok identityValue =>
          cases hf : fill array identityValue with
          | error error => simp [hi, hf] at h
          | ok filled =>
              simp [hi, hf] at h
              exact h.symm
  · intro F A S mapfirst array function source initFlag output h
    cases initFlag <;> simp [initExtremaArray] at h
    · exact h.symm
    · split at h <;> simp_all
  · intro A fill array identity initFlag output h
    cases initFlag <;> simp [initBooleanArray] at h
    · exact h.symm
    · split at h <;> simp_all
  · intro A D AX T R V reducedIndices similar fill array region initial target output h
    cases hr : reducedIndices array region with
    | error error => simp [initarray, hr] at h
    | ok axes =>
        cases hs : similar array target axes with
        | error error => simp [initarray, hr, hs] at h
        | ok result => exact ⟨axes, result, rfl, hs, by simpa [initarray, hr, hs] using h⟩
  · intro F T A D X Y Z R realtypeFn promoteFn elementType applicable zero function identity operator fallback typeOf allocate f array region output h
    cases he : elementType array with
    | error error => simp [reducedimInitGeneric, he] at h
    | ok element =>
        cases hp : promoteFn element with
        | error error => simp [reducedimInitGeneric, he, hp] at h
        | ok promoted =>
            cases ht : realtypeFn f promoted with
            | error error => simp [reducedimInitGeneric, he, hp, ht] at h
            | ok target =>
                refine ⟨element, promoted, target, rfl, hp, ht, ?_⟩
                intro hany
                subst target
                simp [reducedimInitGeneric, he, hp, ht] at h
                cases hr : fallback f array with
                | error error => simp [reducedimInitGeneric.fallback, hr] at h
                | ok reduced =>
                    cases hm : function f reduced with
                    | error error => simp [reducedimInitGeneric.fallback, hr, hm] at h
                    | ok mapped =>
                        cases hi : identity mapped with
                        | error error => simp [reducedimInitGeneric.fallback, hr, hm, hi] at h
                        | ok initial => exact ⟨reduced, mapped, initial, rfl, hm, hi,
                            by simpa [reducedimInitGeneric.fallback, hr, hm, hi] using h⟩

def entries : List Entry := []

end JuliaLean.MultidimCov.ReducedimRepairInitA
