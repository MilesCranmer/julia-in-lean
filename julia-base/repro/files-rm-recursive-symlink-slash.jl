mktempdir() do sandbox
    cd(sandbox) do
        mkpath("target")
        write("target/child", "contents")
        symlink(abspath("target"), "link")

        result = try
            rm("link/"; recursive=true)
            nothing
        catch err
            err
        end

        print("result = ")
        showerror(stdout, result)
        println()
        println("islink(link) = ", islink("link"))
        println("isdir(target) = ", isdir("target"))
        println("isfile(target/child) = ", isfile("target/child"))
        if result isa Base.IOError && islink("link") && isdir("target") && !isfile("target/child")
            println("REPRODUCED files-rm-recursive-symlink-slash")
        end
    end
end
