# A backslash-newline line continuation followed by indentation drops characters
# when non-ASCII text precedes it in the same command (or in stripped leading space).
x = "X"
c = `ls é $x \
 --flag`
println("cmd literal: ", repr(c.exec))
r = Base.shell_split("    é\\\n x")
println("shell_split(\"    é\\\\\\n x\") = ", repr(r))
if c.exec != ["ls", "é", "X", "--flag"] || r != ["éx"]
    println("REPRODUCED shellcmd-line-continuation-index")
end
