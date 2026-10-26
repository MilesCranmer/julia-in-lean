# Base.getpass needs stdin to be a terminal, so run it in a child Julia whose
# stdin is the slave side of a pseudo-terminal, and type into the master side.
const O_RDWR = 0x0002
const O_NOCTTY = Sys.islinux() ? 0x0100 : 0x20000

function typed_secret(keys::Vector{UInt8})
    mfd = ccall(:posix_openpt, Cint, (Cint,), O_RDWR | O_NOCTTY)
    mfd < 0 && error("posix_openpt failed")
    ccall(:grantpt, Cint, (Cint,), mfd) == 0 || error("grantpt failed")
    ccall(:unlockpt, Cint, (Cint,), mfd) == 0 || error("unlockpt failed")
    slave = open(unsafe_string(ccall(:ptsname, Cstring, (Cint,), mfd)), "r+")
    code = """s = Base.getpass("PROMPT>"; with_suffix=false); println(); println("SECRET ", repr(read(s, String)))"""
    p = open(pipeline(`$(Base.julia_cmd()) --startup-file=no -e $code`, stdin=slave), "r")
    readuntil(p, "PROMPT>")          # printed after the terminal is switched to raw mode
    ccall(:write, Cssize_t, (Cint, Ptr{UInt8}, Csize_t), mfd, keys, length(keys))
    out = read(p, String)
    close(slave); ccall(:close, Cint, (Cint,), mfd)
    m = match(r"SECRET (\".*\")", out)
    return m === nothing ? out : Meta.parse(m.captures[1])
end

backspace = typed_secret(UInt8['a', 'b', '\b', 'c', '\r'])
println("typed a b BACKSPACE(0x08) c RETURN -> ", repr(backspace))
delete = typed_secret(UInt8['a', 'b', 0x7f, 'c', '\r'])
println("typed a b DEL(0x7f) c RETURN       -> ", repr(delete))
if backspace == "abc"
    println("REPRODUCED iocov-getpass-backspace")
end
