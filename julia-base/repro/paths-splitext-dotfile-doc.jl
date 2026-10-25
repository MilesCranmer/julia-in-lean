# splitext does not split at the last dot of a last component that starts with a dot,
# although its docstring says it splits whenever the last component contains a dot
for p in (".bashrc", "/home/user/.bashrc", "..bashrc", "a/..", ".tar.gz")
    println("splitext(", repr(p), ") = ", repr(splitext(p)))
end
if splitext(".bashrc") == (".bashrc", "") && splitext("..bashrc") == (".", ".bashrc")
    println("REPRODUCED paths-splitext-dotfile-doc")
end
