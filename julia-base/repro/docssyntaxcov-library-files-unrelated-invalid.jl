# Exercise documented Base.Linking.library_files in a temporary copy of Julia's install.
function reproduce()
    if !isdefined(Base, :Linking) || !isdefined(Base.Linking, :library_files)
        println("Base.Linking.library_files is unavailable in ", VERSION)
        println("NOT REPRODUCED docssyntaxcov-library-files-unrelated-invalid")
        return
    end
    source_root = dirname(Sys.BINDIR)
    name = "libjulia"
    @assert any(path -> basename(path) == "libjulia.so", Base.Linking.library_files(name))
    copy_root = joinpath(mktempdir(), "julia")
    run(`cp -a $source_root $copy_root`)
    copy_dir = joinpath(copy_root, "lib")
    open(joinpath(copy_dir, "libbar.1.2.3.4.so"), "w") do io
        write(io, UInt8[])
    end
    println("copied install: libbar.1.2.3.4.so beside libjulia.so")
    child = """
    name = ARGS[1]
    result = try
        Base.Linking.library_files(name)
    catch err
        err
    end
    println("library_files(", repr(name), ") = ", result isa Exception ? sprint(showerror, result) : repr(result))
    if result isa ArgumentError && occursin("1.2.3.4", sprint(showerror, result))
        println("REPRODUCED docssyntaxcov-library-files-unrelated-invalid")
    else
        error("public library lookup did not reject the unrelated version")
    end
    """
    run(Cmd([joinpath(copy_root, "bin", "julia"), "--startup-file=no", "--history-file=no", "-e", child, name]))
end
reproduce()
