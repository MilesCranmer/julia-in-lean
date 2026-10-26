# shell_escape_csh is documented to also work for a POSIX shell (except for linefeeds),
# but it puts backslashes inside double quotes, where POSIX sh treats them as escapes.
args = ["'\\", "\"; echo INJECTED #"]
e = Base.shell_escape_csh(args...)
println("shell_escape_csh(", join(repr.(args), ", "), ") = ", repr(e))
out = read(`sh -c "printf '<%s>' $e"`, String)
println("sh -c \"printf '<%s>' \$e\" prints ", repr(out))
e2 = Base.shell_escape_csh("'\\\\")
out2 = read(`sh -c "printf '<%s>' $e2"`, String)
println("shell_escape_csh(\"'\\\\\\\\\") = ", repr(e2), "; sh prints ", repr(out2))
if out != "<'\\><\"; echo INJECTED #>" || out2 != "<'\\\\>"
    println("REPRODUCED shellcmd-csh-posix-backslash")
end
