import JuliaLean.Complex.Props

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 5000

namespace JuliaLean.Complex

open JuliaLean JuliaLean.Float

/-- `49.0`. -/
def f49 : F64 := F64.ofBits 0x4048800000000000
/-- `2.0^1000`. -/
def f2p1000 : F64 := F64.ofBits 0x7e70000000000000
/-- `2.0^-40`. -/
def f2m40 : F64 := F64.ofBits 0x3d70000000000000
/-- `2.0^30`. -/
def f2p30 : F64 := F64.ofBits 0x41d0000000000000

theorem divRealDivisor_refuted : ¬ DivRealDivisor := by
  intro h
  have hh := h ⟨f49, Fl.pzero⟩ f49 (by decide) (by decide) (by decide)
  revert hh
  decide

theorem divNoSpuriousNaN_refuted : ¬ DivNoSpuriousNaN := by
  intro h
  have hh := h ⟨F64.one, f2p1000⟩ ⟨f2m40, Fl.pzero⟩ (by decide) (by decide) (by decide) (by decide)
  revert hh
  decide

theorem divComponentAccurate_refuted : ¬ DivComponentAccurate := by
  intro h
  have hh := h ⟨f2p1000, Fl.pzero⟩ ⟨F64.ofBits 3, Fl.two⟩ (by decide) (by decide) (by decide)
    (by decide) (by decide)
  revert hh
  decide

theorem intDivNoNaN_refuted : ¬ IntDivNoNaN := by
  intro h
  have hh := h ⟨JInt.lit .i64 1, JInt.lit .i64 0⟩ ⟨JInt.typemin .i64, JInt.lit .i64 0⟩ (by decide)
  revert hh
  decide

theorem powIntTotal_refuted : ¬ PowIntTotal := by
  intro h
  have hh := h ⟨Fl.two, Fl.pzero⟩ (JInt.typemin .i64)
  revert hh
  decide

theorem muladdExact_refuted : ¬ MuladdExact := by
  intro h
  have hh := h ⟨f2p30, f2p30⟩ ⟨f2p30, f2p30⟩ ⟨F64.one, Fl.pzero⟩ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  revert hh
  decide

end JuliaLean.Complex
