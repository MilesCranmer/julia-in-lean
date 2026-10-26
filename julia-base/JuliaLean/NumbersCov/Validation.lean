import JuliaLean.NumbersCov.Model

namespace JuliaLean.NumbersCov.Validation

open JuliaLean JuliaLean.NumbersCov
open JuliaLean.IntArith.Rational

private def intOps : GenericOps Int where
  eq x y := decide (x = y)
  lt x y := decide (x < y)
  le x y := decide (x ≤ y)
  zero _ := 0
  one _ := 1
  oneunit _ := 1
  castOneType x := x
  convertZero _ := 0
  convertOne _ := 2
  neg x := -x
  pos x := x
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div x y := x.tdiv y
  rem x y := x.tmod y
  mod x y := x % y
  pow x y := if y = 2 then x * x else x
  powInt x y := if y = 2 then x * x else x
  widen x := x
  atan2 _ _ := 0
  isfinite _ := true
  isnan _ := false
  isinf _ := false

private def outJl (x : Jl Int) : String := match x with
  | .ok value => s!"ok:{value}"
  | .error .boundsError => "bounds"
  | .error e => s!"error:{repr e}"

private def pNumber : PromotionModel.PType := .data "Number" "Number" [] (some .any)
private def pReal : PromotionModel.PType := .data "Real" "Real" [] (some pNumber)
private def pInteger : PromotionModel.PType := .data "Integer" "Integer" [] (some pReal)
private def pSigned : PromotionModel.PType := .data "Signed" "Signed" [] (some pInteger)
private def pInt : PromotionModel.PType := .data "Int64" "Int64" [] (some pSigned)
private def pAbstractFloat : PromotionModel.PType :=
  .data "AbstractFloat" "AbstractFloat" [] (some pReal)
private def pFloat : PromotionModel.PType := .data "Float64" "Float64" [] (some pAbstractFloat)

private def pName : PromotionModel.PType → Option String
  | .data n _ _ _ => some n
  | _ => none

private def pEgal (a b : PromotionModel.PType) : Bool := pName a == pName b
private def pSubtype (a b : PromotionModel.PType) : Bool :=
  match b with
  | .any => true
  | .data n _ _ _ => PromotionModel.pHasAncestorName a n
  | _ => pEgal a b

private def pOps : PromotionModel.PTypeOps :=
  { egal := pEgal, subtype := pSubtype, typeofParameter := id }

private def outType : PromotionModel.PType → String
  | .data n _ _ _ => n
  | .any => "Any"
  | .bottom => "Bottom"
  | _ => "other"

private def outRat {t : IntTy} : Jl (Rat t) → String
  | .ok q => s!"{q.num.val}/{q.den.val}"
  | .error e => s!"error:{repr e}"

def differential : IO Unit := do
  IO.println s!"size {NumberModel.size (42 : Int) |>.length}"
  IO.println s!"size_dim_0 {match NumberModel.sizeDim (42 : Int) 0 with | .error .boundsError => "bounds" | _ => "other"}"
  IO.println s!"size_dim_2 {match NumberModel.sizeDim (42 : Int) 2 with | .ok n => n | _ => 0}"
  IO.println s!"getindex_1 {outJl (NumberModel.getindex1 (42 : Int) 1)}"
  IO.println s!"getindex_2 {outJl (NumberModel.getindex1 (42 : Int) 2)}"
  IO.println s!"afoldl {OperatorModel.afoldl (· + ·) (1 : Int) [2, 3, 4]}"
  let composed := OperatorModel.compose2 (fun x : Int => x + 1) (fun x => x * 2)
  IO.println s!"composed {composed.call 3}"
  let q := RationalModel.rationalizeInteger .i8 128 1
  IO.println s!"rationalize {q.num}/{q.den}"
  let z : ComplexModel.Cx Int := ⟨1, 2⟩
  let w : ComplexModel.Cx Int := ⟨3, 4⟩
  let p := ComplexModel.mul intOps z w
  IO.println s!"complex_mul {p.re},{p.im}"
  IO.println s!"complex_isreal {ComplexModel.isreal intOps z}"
  IO.println s!"typejoin {outType (PromotionModel.pTypejoin pOps 64 pInt pFloat)}"
  let half : Rat .i8 := ⟨JInt.lit .i8 1, JInt.lit .i8 2⟩
  let third : Rat .i8 := ⟨JInt.lit .i8 1, JInt.lit .i8 3⟩
  IO.println s!"rational_add {outRat (add half third)}"
  let twoThird : Rat .i8 := ⟨JInt.lit .i8 2, JInt.lit .i8 3⟩
  let fourNinths : Rat .i8 := ⟨JInt.lit .i8 4, JInt.lit .i8 9⟩
  IO.println s!"rational_gcd {outRat (RationalModel.gcdRat twoThird fourNinths)}"
  IO.println s!"complex_show {ComplexModel.showParts "1" "-2" false false}"

end JuliaLean.NumbersCov.Validation
