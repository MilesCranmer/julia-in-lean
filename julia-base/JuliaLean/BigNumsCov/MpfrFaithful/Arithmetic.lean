import JuliaLean.BigNumsCov.MpfrFaithful.Prelude

namespace JuliaLean.BigNumsCov.MpfrFaithful

/-! Hollow arithmetic overloads in `base/mpfr.jl:589-740`. -/

def reverse589 (operation : BFRep → Int → BFRep) (scalar : Int) (x : BFRep) : BFRep :=
  operation x scalar
def Reverse589 : Prop := ∀ operation scalar x, reverse589 operation scalar x = operation x scalar
theorem reverse589_proven : Reverse589 := by unfold Reverse589; intros; rfl

def reverse597 (operation : BFRep → Int → BFRep) (scalar : Int) (x : BFRep) : BFRep :=
  operation x scalar
def Reverse597 : Prop := ∀ operation scalar x, reverse597 operation scalar x = operation x scalar
theorem reverse597_proven : Reverse597 := by unfold Reverse597; intros; rfl

def reverse605 (operation : BFRep → Int → BFRep) (scalar : Int) (x : BFRep) : BFRep :=
  operation x scalar
def Reverse605 : Prop := ∀ operation scalar x, reverse605 operation scalar x = operation x scalar
theorem reverse605_proven : Reverse605 := by unfold Reverse605; intros; rfl

def reverse613 (operation : BFRep → Int → BFRep) (scalar : Int) (x : BFRep) : BFRep :=
  operation x scalar
def Reverse613 : Prop := ∀ operation scalar x, reverse613 operation scalar x = operation x scalar
theorem reverse613_proven : Reverse613 := by unfold Reverse613; intros; rfl

def inv678 (oneClong : Unit → Int) (divide : Int → BFRep → BFRep) (x : BFRep) : Run BFRep :=
  let one := oneClong ()
  ⟨["one(Clong)", "/(Clong,BigFloat)"], divide one x⟩
def Inv678 : Prop :=
  ∀ oneClong divide x, (inv678 oneClong divide x).value = divide (oneClong ()) x
theorem inv678_proven : Inv678 := by unfold Inv678; intros; rfl

def muladd686 (fma : BFRep → BFRep → BFRep → BFRep) (x y z : BFRep) : BFRep :=
  fma x y z
def Muladd686 : Prop := ∀ fma x y z, muladd686 fma x y z = fma x y z
theorem muladd686_proven : Muladd686 := by unfold Muladd686; intros; rfl

def div690 (allocate : Unit → BFRep) (divide : BFRep → BFRep → BFRep → BFRep)
    (truncate : BFRep → BFRep → BFRep)
    (x y : BFRep) : Run BFRep :=
  let output := allocate ()
  let quotient := divide output x y
  ⟨["BigFloat()", "mpfr_div(RoundToZero)", "mpfr_trunc"], truncate quotient quotient⟩
def Div690 : Prop :=
  ∀ allocate divide truncate x y,
    (div690 allocate divide truncate x y).value =
      let quotient := divide (allocate ()) x y
      truncate quotient quotient
theorem div690_proven : Div690 := by unfold Div690; intros; rfl

def div698 (allocate : Unit → BFRep) (divide : BFRep → BFRep → Int → BFRep)
    (truncate : BFRep → BFRep → BFRep) (x : BFRep) (scalar : Int) : Run BFRep :=
  let output := allocate ()
  let quotient := divide output x scalar
  ⟨["BigFloat()", "mpfr_div_ui(RoundToZero)", "mpfr_trunc"], truncate quotient quotient⟩
def Div698 : Prop :=
  ∀ allocate divide truncate x scalar,
    (div698 allocate divide truncate x scalar).value =
      let quotient := divide (allocate ()) x scalar
      truncate quotient quotient
theorem div698_proven : Div698 := by unfold Div698; intros; rfl

def div704 (allocate : Unit → BFRep) (divide : BFRep → Int → BFRep → BFRep)
    (truncate : BFRep → BFRep → BFRep) (scalar : Int) (x : BFRep) : Run BFRep :=
  let output := allocate ()
  let quotient := divide output scalar x
  ⟨["BigFloat()", "mpfr_ui_div(RoundToZero)", "mpfr_trunc"], truncate quotient quotient⟩
def Div704 : Prop :=
  ∀ allocate divide truncate scalar x,
    (div704 allocate divide truncate scalar x).value =
      let quotient := divide (allocate ()) scalar x
      truncate quotient quotient
theorem div704_proven : Div704 := by unfold Div704; intros; rfl

def div712 (allocate : Unit → BFRep) (divide : BFRep → BFRep → Int → BFRep)
    (truncate : BFRep → BFRep → BFRep) (x : BFRep) (scalar : Int) : Run BFRep :=
  let output := allocate ()
  let quotient := divide output x scalar
  ⟨["BigFloat()", "mpfr_div_si(RoundToZero)", "mpfr_trunc"], truncate quotient quotient⟩
def Div712 : Prop :=
  ∀ allocate divide truncate x scalar,
    (div712 allocate divide truncate x scalar).value =
      let quotient := divide (allocate ()) x scalar
      truncate quotient quotient
theorem div712_proven : Div712 := by unfold Div712; intros; rfl

def div718 (allocate : Unit → BFRep) (divide : BFRep → Int → BFRep → BFRep)
    (truncate : BFRep → BFRep → BFRep) (scalar : Int) (x : BFRep) : Run BFRep :=
  let output := allocate ()
  let quotient := divide output scalar x
  ⟨["BigFloat()", "mpfr_si_div(RoundToZero)", "mpfr_trunc"], truncate quotient quotient⟩
def Div718 : Prop :=
  ∀ allocate divide truncate scalar x,
    (div718 allocate divide truncate scalar x).value =
      let quotient := divide (allocate ()) scalar x
      truncate quotient quotient
theorem div718_proven : Div718 := by unfold Div718; intros; rfl

def div726 (allocate : Unit → BFRep) (divide : BFRep → BFRep → Int → BFRep)
    (truncate : BFRep → BFRep → BFRep) (x : BFRep) (scalar : Int) : Run BFRep :=
  let output := allocate ()
  let quotient := divide output x scalar
  ⟨["BigFloat()", "mpfr_div_d(RoundToZero)", "mpfr_trunc"], truncate quotient quotient⟩
def Div726 : Prop :=
  ∀ allocate divide truncate x scalar,
    (div726 allocate divide truncate x scalar).value =
      let quotient := divide (allocate ()) x scalar
      truncate quotient quotient
theorem div726_proven : Div726 := by unfold Div726; intros; rfl

def div732 (allocate : Unit → BFRep) (divide : BFRep → Int → BFRep → BFRep)
    (truncate : BFRep → BFRep → BFRep) (scalar : Int) (x : BFRep) : Run BFRep :=
  let output := allocate ()
  let quotient := divide output scalar x
  ⟨["BigFloat()", "mpfr_d_div(RoundToZero)", "mpfr_trunc"], truncate quotient quotient⟩
def Div732 : Prop :=
  ∀ allocate divide truncate scalar x,
    (div732 allocate divide truncate scalar x).value =
      let quotient := divide (allocate ()) scalar x
      truncate quotient quotient
theorem div732_proven : Div732 := by unfold Div732; intros; rfl

def div740 (allocate : Unit → BFRep) (divide : BFRep → BFRep → Int → BFRep)
    (truncate : BFRep → BFRep → BFRep) (x : BFRep) (scalar : Int) : Run BFRep :=
  let output := allocate ()
  let quotient := divide output x scalar
  ⟨["BigFloat()", "mpfr_div_z(RoundToZero)", "mpfr_trunc"], truncate quotient quotient⟩
def Div740 : Prop :=
  ∀ allocate divide truncate x scalar,
    (div740 allocate divide truncate x scalar).value =
      let quotient := divide (allocate ()) x scalar
      truncate quotient quotient
theorem div740_proven : Div740 := by unfold Div740; intros; rfl

end JuliaLean.BigNumsCov.MpfrFaithful
