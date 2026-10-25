# isready(c) on a buffered channel is documented as "has a value stored in it",
# but it also counts a put! that was woken and has not run yet. Single thread,
# deterministic schedule.
c = Channel{Int}(1)
put!(c, 1)
p = @async put!(c, 2)
yield()                       # p blocks: the buffer is full
x = take!(c)                  # removes 1 and wakes p, which has not run yet
ready = isready(c)
shown = sprint(show, MIME"text/plain"(), c)
close(c)
yield()                       # p runs and its put! throws
after = try take!(c) catch e; e end
println("took ", x, "; isready = ", ready, "; show: ", shown,
        "; put!(c, 2) failed: ", istaskfailed(p), "; next take!: ", after)
if ready && istaskfailed(p) && after isa InvalidStateException
    println("REPRODUCED channels-isready-buffered-stored")
end
