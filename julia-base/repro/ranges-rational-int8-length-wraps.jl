function reproduces_length_native_rational_range()
    first_value = Int8(-1) // Int8(2)
    last_value = Int8(125) // Int8(2)
    interval = UnitRange(first_value, last_value)
    exact_count = div(
        BigInt(numerator(last_value)) * BigInt(denominator(first_value)) -
        BigInt(numerator(first_value)) * BigInt(denominator(last_value)),
        BigInt(denominator(first_value)) * BigInt(denominator(last_value))) + 1
    return first(interval) == first_value && last(interval) == last_value &&
        exact_count == 64 && length(interval) === Int8(-64)
end

reproduced = try
    reproduces_length_native_rational_range()
catch
    false
end
println(reproduced ? "REPRODUCED ranges-rational-int8-length-wraps" :
    "NOT_REPRODUCED ranges-rational-int8-length-wraps")
