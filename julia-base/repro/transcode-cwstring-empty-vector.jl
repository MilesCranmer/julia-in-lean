v = Cwchar_t[]
try
    Base.cconvert(Cwstring, v)
    println("no error")
catch e
    println(typeof(e), ": ", sprint(showerror, e))
    e isa BoundsError && println("REPRODUCED transcode-cwstring-empty-vector")
end
