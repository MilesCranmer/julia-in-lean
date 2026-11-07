down_tie = round(Float16, Rational{Int64}(2051, 1), RoundDown)
down_nontie = round(Float16, Rational{Int64}(4099, 1), RoundDown)
up_tie = round(Float16, Rational{Int64}(2049, 1), RoundUp)
println("Float16 RoundDown 2051 => ", Float64(down_tie), " (expected 2050)")
println("Float16 RoundDown 4099 => ", Float64(down_nontie), " (expected 4096)")
println("Float16 RoundUp 2049 => ", Float64(up_tie), " (expected 2050)")
@assert Float64(down_tie) == 2052.0
@assert Float64(down_nontie) == 4100.0
@assert Float64(up_tie) == 2048.0
println("REPRODUCED rational-rounding-native-noninteger-targets")
