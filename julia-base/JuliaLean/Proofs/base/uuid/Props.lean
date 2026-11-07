import JuliaLean.base.uuid

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

/-- `UUID(string(u)) == u` for every `u`. -/
def UuidStringRoundtrip : Prop :=
  ∀ u : UUID, parseUUID (uuidString u) = .ok u

end JuliaLean.Base64Uuid
