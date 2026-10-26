mktempdir() do dir
    src = joinpath(dir, "src")
    dst = joinpath(dir, "dst")
    target = joinpath(dir, "missing-target")
    write(src, "source contents")
    symlink(target, dst)

    cp(src, dst; force=true)

    println("islink(dst) = ", islink(dst))
    println("isfile(dst) = ", isfile(dst))
    println("isfile(target) = ", isfile(target))
    println("read(dst, String) = ", repr(read(dst, String)))
    if islink(dst) && isfile(target) && read(target, String) == "source contents"
        println("REPRODUCED files-cp-force-dangling-symlink")
    end
end
