function reset_filename_rng()
    Base.Libc.srand(0x12345678)
end

mktempdir() do dir
    reset_filename_rng()
    candidate = joinpath(dir, "jl_" * Base.Filesystem._rand_filename())
    symlink("missing-target", candidate)

    reset_filename_rng()
    generated = tempname(dir; max_tries=1, cleanup=false)

    println("generated == candidate = ", generated == candidate)
    println("islink(generated) = ", islink(generated))
    println("ispath(generated) = ", ispath(generated))
    if generated == candidate && islink(generated) && !ispath(generated)
        println("REPRODUCED files-tempname-dangling-symlink")
    end
end
