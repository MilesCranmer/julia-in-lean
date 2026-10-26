# Parse pinned Base sources without evaluating or expanding them.
# Run: julia scripts/list_base_methods.jl <julia-source-root>
# Stdout is the manifest; diagnostics go to stderr.
const JS = Base.JuliaSyntax

compact(node) = replace(strip(String(JS.sourcetext(node))), r"\s+" => " ")
nodekind(node) = string(JS.kind(node))
kids(node) = JS.children(node) === nothing ? () : JS.children(node)

function call_head(node)
    kind = nodekind(node)
    if kind in ("where", "::") && !isempty(kids(node))
        return call_head(first(kids(node)))
    end
    kind == "call" ? node : nothing
end

function method_name(signature)
    call = call_head(signature)
    call === nothing && return compact(signature)
    # Infix/prefix operator calls keep children in source order.
    name = JS.is_infix_op_call(call) ? kids(call)[2] : first(kids(call))
    text = compact(name)
    nodekind(name) == "::" ? "(" * text * ")" : text
end

function method_rows(source, file)
    # Meta.parseall rejects malformed input independently of the source-range tree.
    parsed = Meta.parseall(source; filename=file)
    function reject_errors(ex)
        ex isa Expr || return
        ex.head in (:error, :incomplete) && error("parse error in $file: $ex")
        foreach(reject_errors, ex.args)
    end
    reject_errors(parsed)
    root = JS.parseall(JS.SyntaxNode, source; filename=file, ignore_warnings=true)
    rows = NamedTuple[]
    function visit(node, loops=String[], evalquote=false, macro_context="",
                   function_context="", quote_context="")
        kind = nodekind(node)
        children = kids(node)
        kind in ("string", "cmdstring", "char") && return
        if kind == "quote" && !evalquote && isempty(macro_context)
            isempty(function_context) && return
            quote_context = function_context
        end
        evalquote = false
        if kind == "macrocall" && !isempty(children)
            macro_name = compact(first(children))
            evalquote = macro_name in ("@eval", "Base.@eval", "Core.@eval")
        elseif kind == "call" && !isempty(children)
            callee = compact(first(children))
            evalquote = callee in ("eval", "Base.eval", "Core.eval") ||
                (callee == "ccall" && length(children) > 1 &&
                 compact(children[2]) == ":jl_toplevel_eval_in")
        elseif kind == "macro" && !isempty(children)
            macro_context = method_name(first(children))
        end
        if kind in ("for", "while") && !isempty(children)
            loops = [loops; compact(first(children))]
        end
        signature = nothing
        if kind in ("function", "macro") && !isempty(children)
            signature = first(children)
            # Anonymous function expressions have no source-level method name.
            nodekind(signature) in ("tuple", "parameters") && (signature = nothing)
        elseif kind == "=" && !isempty(children) && call_head(first(children)) !== nothing
            signature = first(children)
        end
        if signature !== nothing
            line = JS.source_line(node)
            endline = JS.source_line(JS.sourcefile(node), JS.last_byte(node))
            note = isempty(loops) ? "" : "generated-loop: " * join(loops, "; ")
            if !isempty(macro_context) && kind != "macro"
                note = join(filter(!isempty, [note, "generated-macro: " * macro_context]), "; ")
            end
            if !isempty(quote_context)
                note = join(filter(!isempty, [note, "generated-quote: " * quote_context]), "; ")
            end
            push!(rows, (; file, line, endline, name=method_name(signature),
                         signature=compact(signature), status="todo", entry="", note))
            kind == "function" && (function_context = method_name(signature))
        end
        for child in children
            visit(child, loops, evalquote, macro_context, function_context, quote_context)
        end
    end
    visit(root)
    rows
end

function main(args=ARGS)
    root = only(args)
    isdir(joinpath(root, "base")) || error("expected pinned base/ sources under $root")
    files = sort([joinpath(dir, file) for (dir, _, files) in walkdir(joinpath(root, "base"))
                  for file in files if endswith(file, ".jl")])
    println("file\tline\tendline\tname\tsignature\tstatus\tentry\tnote")
    count = 0
    for path in files
        file = replace(relpath(path, root), '\\' => '/')
        rows = method_rows(read(path, String), file)
        for row in rows
            # TSV escaping compatible with Python's csv module.
            fields = map(values(row)) do value
                text = string(value)
                occursin('"', text) ? "\"" * replace(text, "\"" => "\"\"") * "\"" : text
            end
            println(join(fields, '\t'))
        end
        count += length(rows)
    end
    println(stderr, "PARSED $(length(files)) files; $count method definitions")
end

abspath(PROGRAM_FILE) == (@__FILE__) && main()
