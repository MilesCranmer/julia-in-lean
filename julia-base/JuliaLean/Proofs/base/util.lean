import JuliaLean.Registry.Types
import JuliaLean.base.util

/-!
Public statements for pinned `base/util.jl`. The adjacent TSV contains the
complete source-method inventory, exact public model blockers, and proposed
dispositions for all historical registry IDs. Frozen files remain untouched.

The Enum methods below are generated at util.jl:323 by Enums.jl:218-237.
Only the three exported-name specializations have statements here. Generic
pre-existing Enum methods and private terminal helpers are not new util APIs.
No proposed adapter, callback-correctness hypothesis or proof is included.
-/

namespace JuliaLean.Proofs.base.util.Round1

open JuliaLean JuliaLean.base.util

/-- The generated minimum is no greater than any declared terminal-attribute enum value.
Julia source: base/util.jl:321-323; base/Enums.jl:32,226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/int.jl:826-831 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def TcsetattrTypeminBoundsEveryMember : Prop :=
  ∀ x : TCSETATTRFlags,
    (tcsetattrFlagCode tcsetattrFlagTypemin).val ≤ (tcsetattrFlagCode x).val

/-- The generated maximum is no less than any declared terminal-attribute enum value.
Julia source: base/util.jl:321-323; base/Enums.jl:32,227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/int.jl:858-863 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def TcsetattrTypemaxBoundsEveryMember : Prop :=
  ∀ x : TCSETATTRFlags,
    (tcsetattrFlagCode x).val ≤ (tcsetattrFlagCode tcsetattrFlagTypemax).val

/-- The generated instance collection contains each declared enum value exactly once.
Julia source: base/util.jl:323; base/Enums.jl:235-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/Enums.jl:130-135; base/runtime_internals.jl:1518-1522 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def TcsetattrInstancesEnumeratesExactlyOnce : Prop :=
  ∀ x : TCSETATTRFlags,
    (tcsetattrFlagInstances.filter (fun y => decide (y = x))).length = 1

end JuliaLean.Proofs.base.util.Round1

namespace JuliaLean.Proofs.base.util

open JuliaLean.Registry

end JuliaLean.Proofs.base.util

/-! Batch 4 group 20: terminal-attribute enumeration contracts. -/

namespace JuliaLean.ChatGPT.Batch4.Group20

/-- util-tcsetattr-typemin: the minimum bounds every declared member. -/
theorem UtilTcsetattrTypemin_proven : JuliaLean.Proofs.base.util.Round1.TcsetattrTypeminBoundsEveryMember := by
  intro x
  cases x <;> decide

/-- util-tcsetattr-typemax: the maximum bounds every declared member. -/
theorem UtilTcsetattrTypemax_proven : JuliaLean.Proofs.base.util.Round1.TcsetattrTypemaxBoundsEveryMember := by
  intro x
  cases x <;> decide

/-- util-tcsetattr-instances: each declared member occurs exactly once. -/
theorem UtilTcsetattrInstances_proven : JuliaLean.Proofs.base.util.Round1.TcsetattrInstancesEnumeratesExactlyOnce := by
  intro x
  cases x <;> decide

end JuliaLean.ChatGPT.Batch4.Group20

namespace JuliaLean.Proofs.base.util
open JuliaLean.Registry
def entries : List Entry := [
  { id := "util-tcsetattr-typemin", juliaFile := "base/util.jl",
    juliaFns := ["typemin(::Type{TCSETATTR_FLAGS})"],
    statement := "The minimum terminal-attribute enum value is no greater than every declared member.",
    source := "base/util.jl:321-323; base/Enums.jl:32,226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.util.Round1.TcsetattrTypeminBoundsEveryMember, thm := some ``JuliaLean.ChatGPT.Batch4.Group20.UtilTcsetattrTypemin_proven },
  { id := "util-tcsetattr-typemax", juliaFile := "base/util.jl",
    juliaFns := ["typemax(::Type{TCSETATTR_FLAGS})"],
    statement := "The maximum terminal-attribute enum value is no less than every declared member.",
    source := "base/util.jl:321-323; base/Enums.jl:32,227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.util.Round1.TcsetattrTypemaxBoundsEveryMember, thm := some ``JuliaLean.ChatGPT.Batch4.Group20.UtilTcsetattrTypemax_proven },
  { id := "util-tcsetattr-instances", juliaFile := "base/util.jl",
    juliaFns := ["instances(::Type{TCSETATTR_FLAGS})"],
    statement := "The terminal-attribute enum instance collection contains every declared member exactly once.",
    source := "base/util.jl:323; base/Enums.jl:235-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.util.Round1.TcsetattrInstancesEnumeratesExactlyOnce, thm := some ``JuliaLean.ChatGPT.Batch4.Group20.UtilTcsetattrInstances_proven }
]

end JuliaLean.Proofs.base.util
