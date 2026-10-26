# `library_files!` parses every directory entry. Its first parse catches
# ArgumentError, but the fallback parse is unguarded, so an unrelated library
# with a four-part version aborts a lookup that should find `libfoo.so`.
paths = String[]
listings = ["/d" => ["libbar.1.2.3.4.so", "libfoo.so"]]
result = try
    Base.Linking.library_files!(paths, "libfoo", listings)
catch e
    e
end
println("result = ", result isa Exception ? sprint(showerror, result) : repr(result))
println("paths = ", repr(paths))
if result isa ArgumentError && isempty(paths)
    println("REPRODUCED docssyntaxcov-library-files-unrelated-invalid")
end
