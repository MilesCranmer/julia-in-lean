const BUG_ID = "memsafety-deprecated-substring-negative-count"

function construct_invalid_substring(parent)
    SubString{typeof(parent)}(parent, 2, -1, Val(:noshift))
end

function report_construction(label, parent)
    try
        ss = construct_invalid_substring(parent)
        println(label, " constructor returned ncodeunits = ", ncodeunits(ss),
                ", sizeof = ", sizeof(ss))
        return ncodeunits(ss) == -1 && sizeof(ss) == -1
    catch err
        println(label, " constructor threw ", nameof(typeof(err)))
        return err isa BoundsError
    end
end

if ARGS == ["checked"]
    report_construction("checked String", "abc")
    report_construction("checked SubString", SubString("abc"))
    exit()
end

string_invalid = report_construction("default String", "abc")
substring_invalid = report_construction("default SubString", SubString("abc"))

cmd = `$(Base.julia_cmd()) --startup-file=no --check-bounds=yes $(@__FILE__) checked`
io = IOBuffer()
proc = run(pipeline(ignorestatus(cmd); stdout=io, stderr=io))
checked_output = String(take!(io))
print(checked_output)
println("checked child exit code = ", proc.exitcode, ", signal = ", proc.termsignal)

checked_string = occursin("checked String constructor threw BoundsError", checked_output) ||
    occursin("checked String constructor returned ncodeunits = -1, sizeof = -1", checked_output)
checked_substring = occursin("checked SubString constructor threw BoundsError", checked_output) ||
    occursin("checked SubString constructor returned ncodeunits = -1, sizeof = -1", checked_output)
if string_invalid && substring_invalid && checked_string && checked_substring
    println("REPRODUCED ", BUG_ID)
end
