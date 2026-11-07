import JuliaLean.base.ryu.exp

namespace JuliaLean.NumMisc.Coverage

open JuliaLean

/-! ## `base/ryu/exp.jl` and `base/ryu/fixed.jl` -/

def RyuExpBehavior : Prop :=
  ∀ x precision plus space hash expchar trim,
    JuliaLean.Printf.writeexp x precision plus space hash expchar trim =
      if precision < 0 then .error (.julia (.argumentError "precision must be non-negative"))
      else
        let sign := JuliaLean.ParsePrint.Ryu.appendSign x plus space
        if JuliaLean.Float.F64.iszero x then
          .ok (sign ++ [48] ++
            (if precision > 0 && !trim then 46 :: JuliaLean.Printf.zeros precision.toNat
             else if hash then [46] else []) ++ [expchar, 43, 48, 48])
        else if JuliaLean.Float.F64.isnan x then .ok (sign ++ [78, 97, 78])
        else if !JuliaLean.Float.F64.isfinite x then .ok (sign ++ [73, 110, 102])
        else
          let rat := JuliaLean.Float.F64.toRat x
          let me := JuliaLean.Printf.sci rat.1.natAbs rat.2 precision.toNat
          let digits := JuliaLean.Printf.digits 10 false me.1
          let mantissa := digits.take 1 ++
            (if precision > 0 then 46 :: digits.drop 1 else if hash then [46] else [])
          .ok (sign ++ (if trim then JuliaLean.Printf.trimZeros hash mantissa else mantissa) ++
            [expchar] ++ JuliaLean.Printf.expPart me.2)

theorem ryuExpBehavior : RyuExpBehavior := by
  unfold RyuExpBehavior
  intros
  rfl
end JuliaLean.NumMisc.Coverage
