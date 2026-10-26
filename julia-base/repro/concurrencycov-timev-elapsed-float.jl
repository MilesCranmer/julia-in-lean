# @timev prints "elapsed time (ns)" as a Float64 (e.g. "5.1190742e7") although the count is
# documented, and was printed, as an integer number of nanoseconds ("elapsed time (ns): 546769547").
out = let p = Pipe()
    redirect_stdout(p) do
        @timev sleep(0.05)
    end
    close(p.in)
    read(p, String)
end
print(out)
line = only(filter(startswith("elapsed time (ns):"), split(out, '\n')))
value = strip(split(line, ':'; limit=2)[2])
println("printed elapsed value: ", repr(value))
println(tryparse(Int, value) === nothing ?
    "REPRODUCED concurrencycov-timev-elapsed-float" :
    "NOT REPRODUCED concurrencycov-timev-elapsed-float")
