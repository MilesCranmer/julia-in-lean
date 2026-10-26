f = Base.open_flags(append=true)
println("open_flags(append=true) = ", f)
# open docstring table: read defaults to !write, write to truncate | append,
# truncate to !read & write; so append=true alone documents truncate == true.
if f.write && !f.read && !f.truncate
    println("REPRODUCED iocov-open-flags-append-doc")
end
