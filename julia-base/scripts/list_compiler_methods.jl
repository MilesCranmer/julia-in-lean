# Parse pinned Compiler sources without evaluating them, and write one coverage manifest per file.
# Run: julia scripts/list_compiler_methods.jl <julia-source-root> Compiler/src/<file>.jl...
# Each manifest is coverage/methods/Compiler_src_<file>.tsv, in the same format as the Base ones.
include(joinpath(@__DIR__, "list_base_methods.jl"))

function compiler_main(args=ARGS)
    root = args[1]
    outdir = joinpath(dirname(@__DIR__), "coverage", "methods")
    for file in args[2:end]
        occursin(r"^Compiler/src/[^/]+(/[^/]+)*\.jl$", file) || error("expected Compiler/src/<path>.jl, got $file")
        rows = method_rows(read(joinpath(root, file), String), file)
        out = joinpath(outdir, replace(file[1:end-3], '/' => '_') * ".tsv")
        open(out, "w") do io
            println(io, "file\tline\tendline\tname\tsignature\tstatus\tentry\tnote")
            for row in rows
                fields = map(values(row)) do value
                    text = string(value)
                    occursin('"', text) ? "\"" * replace(text, "\"" => "\"\"") * "\"" : text
                end
                println(io, join(fields, '\t'))
            end
        end
        println(stderr, "WROTE $out: $(length(rows)) method definitions")
    end
end

compiler_main()
