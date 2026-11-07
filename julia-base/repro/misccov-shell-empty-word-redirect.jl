# Public backtick command syntax preserves an empty quoted word before a redirect.
direct = `echo ''>x`
spaced = `echo '' >x`
println("direct redirect: ", direct)
println("spaced redirect: ", spaced)
if direct != spaced
    println("REPRODUCED misccov-shell-empty-word-redirect")
end
