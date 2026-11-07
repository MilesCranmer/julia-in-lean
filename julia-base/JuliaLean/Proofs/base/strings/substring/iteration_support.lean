import JuliaLean.base.strings.substring

namespace JuliaLean.Strings

/-- Complete iteration traces of a SubString, including a thrown error. -/
inductive SubIterTrace (ss : JSub) : JInt64 → SJl (List (UInt32 × JInt64)) → Prop where
  | done {i} : subIterate ss i = .ok none → SubIterTrace ss i (.ok [])
  | error {i e} : subIterate ss i = .error e → SubIterTrace ss i (.error e)
  | step {i c j r} : subIterate ss i = .ok (some (c, j)) → SubIterTrace ss j r →
      SubIterTrace ss i ((fun xs => (c, i) :: xs) <$> r)

end JuliaLean.Strings
