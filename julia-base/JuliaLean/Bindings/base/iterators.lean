import JuliaLean.base.iterators
import JuliaLean.base.range
import JuliaLean.base.int

/-!
Concrete model bindings for Julia `UnitRange{Int}` operations used by the iterator model.
-/
namespace JuliaLean.Bindings.base.iterators

open JuliaLean
open JuliaLean.base.range

abbrev IntUnitRange := UnitRange JInt64

instance : JEltype IntUnitRange JInt64 := ⟨⟩
instance : JFieldStart IntUnitRange JInt64 := ⟨UnitRange.start⟩
instance : JFieldStop IntUnitRange JInt64 := ⟨UnitRange.stop⟩
instance : JFirst IntUnitRange JInt64 := ⟨first_OrdinalRange⟩
instance : JLast IntUnitRange JInt64 := ⟨last_OrdinalRange⟩

private def intUnitRangeIsEmpty (r : IntUnitRange) : JlX Bool := by
  letI : JLt JInt64 JInt64 := ⟨JuliaLean.base.int.ltSame⟩
  exact isempty_AbstractUnitRange r

instance : JIsempty IntUnitRange := ⟨intUnitRangeIsEmpty⟩

private def intUnitRangeStep (r : IntUnitRange) : JlX JInt64 := by
  letI : JZero JInt64 := ⟨JuliaLean.base.int.lit .i64 0⟩
  letI : HSub JInt64 JInt64 JInt64 := ⟨JuliaLean.base.int.sub_int⟩
  exact pure (step_AbstractUnitRange r)

instance : JStep IntUnitRange JInt64 := ⟨intUnitRangeStep⟩
instance : JIterate1 IntUnitRange JInt64 JInt64 := ⟨iterate_OrdinalRange⟩

private def intUnitRangeIterateState (r : IntUnitRange) (state : JInt64) :
    JlX (Option (JInt64 × JInt64)) := by
  letI : JEq JInt64 JInt64 := ⟨JuliaLean.base.int.eqSame⟩
  letI : HAdd JInt64 JInt64 JInt64 := ⟨JuliaLean.base.int.add_int⟩
  exact iterate_OrdinalRange_state r state

instance : JIterate2 IntUnitRange JInt64 JInt64 := ⟨intUnitRangeIterateState⟩

private instance : JType JInt64 where
  isBool := false
  isSigned := true
  isInteger := true
  isAbstractFloat := false
  bool_eq := by intro h; cases h

private def intUnitRangeInteger (x : JInt64) : JlX JInt64 :=
  liftJl (JuliaLean.base.int.convert .i64 x)

private def intUnitRangeLength (r : IntUnitRange) : JlX JInt64 := by
  letI : JZero JInt64 := ⟨JuliaLean.base.int.lit .i64 0⟩
  letI : HAdd JInt64 JInt64 JInt64 := ⟨JuliaLean.base.int.add_int⟩
  letI : HSub JInt64 JInt64 JInt64 := ⟨JuliaLean.base.int.sub_int⟩
  letI : JInteger JInt64 JInt64 := ⟨intUnitRangeInteger⟩
  exact length_AbstractUnitRange r

instance : JLength IntUnitRange JInt64 := ⟨intUnitRangeLength⟩

end JuliaLean.Bindings.base.iterators
