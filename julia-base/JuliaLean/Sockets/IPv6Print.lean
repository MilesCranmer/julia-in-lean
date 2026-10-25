import JuliaLean.Sockets.Props
import JuliaLean.Sockets.Lemmas

namespace JuliaLean.Sockets

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- The printer's control flow depends only on the eight zero/nonzero flags.
These 256 cases retain arbitrary values for every nonzero group. -/
theorem ipv6Rfc5952_proven : IPv6Rfc5952 := by
  intro h
  by_cases h7 : ipv6Field h 7 = 0
  all_goals by_cases h6 : ipv6Field h 6 = 0
  all_goals by_cases h5 : ipv6Field h 5 = 0
  all_goals by_cases h4 : ipv6Field h 4 = 0
  all_goals by_cases h3 : ipv6Field h 3 = 0
  all_goals by_cases h2 : ipv6Field h 2 = 0
  all_goals by_cases h1 : ipv6Field h 1 = 0
  all_goals by_cases h0 : ipv6Field h 0 = 0
  all_goals
    simp_all [ipv6Str, iprintGo, scanGo, rfc5952, bestRun, runTops, zeroLen, bestOf,
      List.range_succ, List.intercalate, List.append_assoc]

end JuliaLean.Sockets
