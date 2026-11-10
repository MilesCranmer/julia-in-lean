# A package that declares a directory as an include dependency (`include_dependency(dir)`, which
# tracks content by default) is recompiled after the directory's `st_size` changes, even though
# its content, which the docstring defines as `join(readdir(dir))`, is unchanged.
#
# The writer records `filesize(path)` for the directory next to the hash of `join(readdir(path))`
# (base/loading.jl:2700-2702), and any_includes_stale compares the size before the hash
# (base/loading.jl:4838-4843). A directory's `st_size` is a property of the file system, not of
# its listing: ext4 never shrinks a directory, so adding files and removing them again leaves the
# listing unchanged and the size larger. The same applies when a relocatable depot is copied to
# another file system (ext4 reports 4096 for a small directory, tmpfs and APFS report sizes
# derived from the entries).
#
# Prints REPRODUCED when the listing and its hash are unchanged, the size differs, and the cache
# is rejected with `:fsize_changed`. Needs a file system that does not shrink directories (ext4,
# XFS); on others it prints NOT REPRODUCED with the reason. The temporary tree is placed under
# the home directory, which is ext4 on the build machine.

const ID = "compiler-loading-dir-include-size"
println(VERSION, " ", Base.GIT_VERSION_INFO.commit)
root = mktempdir(homedir())
try
    depot = joinpath(root, "depot"); mkpath(depot)
    pkg = joinpath(root, "lib", "DirDep")
    mkpath(joinpath(pkg, "src"))
    data = joinpath(pkg, "data"); mkpath(data)
    touch(joinpath(data, "a"))
    write(joinpath(pkg, "src", "DirDep.jl"), """
    module DirDep
    include_dependency(joinpath(@__DIR__, "..", "data"))
    f() = 1
    end
    """)
    env = Dict("JULIA_DEPOT_PATH" => "$depot:", "JULIA_LOAD_PATH" => "$(joinpath(root, "lib")):@stdlib",
               "JULIA_PKG_PRECOMPILE_AUTO" => "0")
    julia = Base.julia_cmd()
    run(addenv(`$julia --startup-file=no -e 'using DirDep'`, env))
    listing() = readdir(data)
    before = (listing(), Base._crc32c(join(listing())), filesize(data))
    for i in 1:300
        touch(joinpath(data, "file_with_a_rather_long_name_$i"))
    end
    for i in 1:300
        rm(joinpath(data, "file_with_a_rather_long_name_$i"))
    end
    after = (listing(), Base._crc32c(join(listing())), filesize(data))
    println("listing, hash, size before: ", before)
    println("listing, hash, size after:  ", after)
    child = joinpath(root, "child.jl")
    write(child, """
    pkg = Base.identify_package("DirDep")
    reasons = VERSION < v"1.14-" ? Dict{String,Int}() : Dict{Symbol,Int}()
    spec = isdefined(Base, :locate_package_load_spec) ? Base.locate_package_load_spec(pkg) : Base.locate_package(pkg)
    fresh = any(p -> Base.stale_cachefile(pkg, UInt128(0), spec, p; reasons) !== true,
                Base.find_all_in_cache_path(pkg))
    println("reasons: ", reasons)
    changed = sum(v for (k, v) in reasons if string(k) in ("fsize_changed", "file size changed"); init = 0)
    print(changed > 0 && !fresh ? "STALE" : "FRESH")
    """)
    out = read(addenv(`$julia --startup-file=no $child`, env), String)
    println(out)
    if before[1] == after[1] && before[2] == after[2] && before[3] != after[3] && endswith(out, "STALE")
        println("REPRODUCED ", ID)
    elseif before[3] == after[3]
        println("NOT REPRODUCED ", ID, ": this file system shrinks directories, so the size did not change")
    else
        println("NOT REPRODUCED ", ID)
    end
finally
    rm(root; recursive=true, force=true)
end
