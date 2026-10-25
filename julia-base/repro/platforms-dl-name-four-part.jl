using Base.BinaryPlatforms
for (path, os) in [("libcublas.so.12.1.3.1", "linux"), ("libcufft.11.0.2.54.dylib", "macos"), ("libfoo-1.2.3.4.dll", "windows")]
    r = try
        parse_dl_name_version(path, os)
    catch e
        e
    end
    println(repr(path), " => ", r isa Exception ? sprint(showerror, r) : repr(r))
    if r isa Exception && path == "libcublas.so.12.1.3.1"
        println("REPRODUCED platforms-dl-name-four-part")
    end
end
