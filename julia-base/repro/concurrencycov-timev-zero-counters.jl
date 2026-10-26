# The @timev docstring says it prints "any non-zero memory allocation counters", but
# timev_print calls padded_nonzero_print with always_print=true for most counters,
# so counters that are zero are printed as well.
out = let p = Pipe()
    redirect_stdout(p) do
        @timev 1 + 1
    end
    close(p.in)
    read(p, String)
end
print(out)
zero_lines = filter(l -> occursin(r":\s*0(\.0)?$", l), split(out, '\n'))
println("zero-valued counter lines: ", zero_lines)
println(!isempty(zero_lines) ?
    "REPRODUCED concurrencycov-timev-zero-counters" :
    "NOT REPRODUCED concurrencycov-timev-zero-counters")
