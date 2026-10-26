for s in (-1.0, 4295.0)
    try
        Libc.systemsleep(s)
        println("systemsleep($s) returned")
    catch e
        println("systemsleep($s) threw ", typeof(e))
        s == 4295.0 && e isa InexactError && println("REPRODUCED iocov-systemsleep-large")
    end
end
