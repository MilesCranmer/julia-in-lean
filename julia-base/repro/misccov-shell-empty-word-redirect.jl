# An empty quoted word directly followed by a redirect is dropped from the command:
# `echo ''>x` runs `echo` with no argument, while `echo '' >x` passes "".
a = Base.shell_parse("echo ''>x")[1]
b = Base.shell_parse("echo '' >x")[1]
println(a)
println(b)
if a != b
    println("REPRODUCED misccov-shell-empty-word-redirect")
end
