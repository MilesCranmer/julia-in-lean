using Base.BinaryPlatforms, Libdl
using CompilerSupportLibraries_jll
paths = filter(x -> occursin("libstdc++", x), Libdl.dllist())
println("libstdc++ loaded: ", paths)
h = Libdl.dlopen(first(paths), Libdl.RTLD_NOLOAD)
exports = [m for m in 18:30 if Libdl.dlsym(h, "GLIBCXX_3.4.$m"; throw_error=false) !== nothing]
println("GLIBCXX_3.4.m exported for m in 18:30: ", exports)
v = detect_libstdcxx_version()
println("detect_libstdcxx_version() = ", repr(v))
println("libstdcxx_version(HostPlatform()) = ", repr(libstdcxx_version(HostPlatform())))
if !isempty(exports) && v === nothing
    println("REPRODUCED platforms-detect-libstdcxx-csl")
end
