using Dates

d = Date(-1, 1, 1)
df = Dates.ISODateFormat
s = Dates.format(d, df)
parsed = parse(Date, s, df)
println("input = ", d)
println("ISODateFormat output = ", s)
println("parsed = ", parsed)
println("minimum-width year output = ", Dates.format(d, dateformat"YYYY-mm-dd"))
parsed != d && println("REPRODUCED dates-format-year-loss")
