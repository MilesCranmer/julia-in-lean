import JuliaLean.base.ryu.fixed

namespace JuliaLean.NumMisc.Coverage

open JuliaLean

def RyuFixedBehavior : Prop :=
  ∀ x precision plus space hash trim,
    JuliaLean.Printf.writefixed x precision plus space hash trim =
      if precision < 0 then .error (.julia (.argumentError "precision must be non-negative"))
      else
        let sign := JuliaLean.ParsePrint.Ryu.appendSign x plus space
        if JuliaLean.Float.F64.iszero x then
          .ok (sign ++ [48] ++
            (if precision > 0 && !trim then 46 :: JuliaLean.Printf.zeros precision.toNat
             else if hash then [46] else []))
        else if JuliaLean.Float.F64.isnan x then .ok (sign ++ [78, 97, 78])
        else if !JuliaLean.Float.F64.isfinite x then .ok (sign ++ [73, 110, 102])
        else
          let rat := JuliaLean.Float.F64.toRat x
          let p := precision.toNat
          let rounded := JuliaLean.Printf.rheScaled rat.1.natAbs rat.2 precision
          let fractional := precision > 0 || hash
          let body := sign ++ JuliaLean.Printf.digits 10 false (rounded / 10^p) ++
            (if fractional then 46 ::
              (if p = 0 then [] else JuliaLean.Printf.padDigits p (rounded % 10^p)) else [])
          .ok (if trim && fractional then JuliaLean.Printf.trimZeros hash body else body)

theorem ryuFixedBehavior : RyuFixedBehavior := by
  unfold RyuFixedBehavior
  intros
  rfl
end JuliaLean.NumMisc.Coverage
