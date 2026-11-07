mktempdir() do dir
    path = joinpath(dir, "append.txt")
    write(path, "old")
    open(path; append=true) do io
        write(io, "new")
    end
    contents = read(path, String)
    println("open(path; append=true) = ", repr(contents))
    contents == "oldnew" && println("REPRODUCED iocov-open-flags-append-doc")
end
