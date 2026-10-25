# replace(io, s, r => s"\1") only works when io is an IOBuffer.
function attempt(io)
    try
        replace(io, "abc", r"(b)" => s"<\1>")
        "ok"
    catch e
        sprint(showerror, e; context = :limit => true)[1:min(end, 80)]
    end
end
buf = IOBuffer()
results = [
    ("IOBuffer", attempt(IOBuffer())),
    ("IOContext(IOBuffer())", attempt(IOContext(buf))),
    ("devnull", attempt(devnull)),
]
mktemp() do path, f
    push!(results, ("IOStream", attempt(f)))
end
for (name, r) in results
    println(name, ": ", r)
end
println("without capture, IOContext: ", (replace(IOContext(buf), "abc", r"b" => "<b>"); String(take!(buf))))
results[1][2] == "ok" && all(r -> startswith(r[2], "MethodError"), results[2:end]) &&
    println("REPRODUCED regexunicode-replace-capture-generic-io")
