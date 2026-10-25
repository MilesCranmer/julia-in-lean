# The shell_escape_wincmd docstring says it "will fail with an ArgumentError" if the
# input contains %, but it returns the % unescaped.
r = try Base.shell_escape_wincmd("100%") catch e; e end
println("shell_escape_wincmd(\"100%\") = ", repr(r))
r isa ArgumentError || println("REPRODUCED shellcmd-wincmd-percent-doc")
