# readbytes!(::Base64DecodePipe, data, nb) with isempty(data) and nb > 0 never
# returns: resize!(data, min(length(data) * 2, nb)) keeps length(data) == 0, so
# no byte is ever stored in data while the decoded bytes pile up in pipe.rest.
# stdlib/Base64/src/decode.jl:116-129
using Base64

# Run the call in a subprocess so this reproducer itself always terminates.
code = """
using Base64
pipe = Base64DecodePipe(IOBuffer("SGVsbG8h"))
n = readbytes!(pipe, UInt8[], 3)
println("TERMINATED ", n)
"""
proc = run(pipeline(`$(Base.julia_cmd()) --startup-file=no -e $code`; stdout = devnull, stderr = devnull),
           wait = false)
t0 = time()
while process_running(proc) && time() - t0 < 60
    sleep(0.2)
end
if process_running(proc)
    kill(proc)
    wait(proc)
    println("readbytes!(Base64DecodePipe(IOBuffer(\"SGVsbG8h\")), UInt8[], 3) still running after 60 s")
    println("REPRODUCED base64uuid-readbytes-empty-hang")
else
    println("readbytes! returned: bug absent")
end
