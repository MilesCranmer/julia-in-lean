# ReentrantLock counts recursive acquisitions in a UInt32 that wraps silently:
# after 2^32 + 1 nested acquisitions one unlock releases the lock.
l = ReentrantLock()
lock(l)
for _ in 1:(UInt64(2)^32)
    trylock(l)       # recursive acquisition by the owner
end
held_before = islocked(l)
unlock(l)            # 2^32 levels should still be held
held_after = islocked(l)
other = fetch(Threads.@spawn trylock(l))   # another task acquires it
println("islocked before unlock: ", held_before, "; after one unlock: ", held_after,
        "; other task trylock: ", other)
if held_before && !held_after && other
    println("REPRODUCED channels-lock-reentrancy-wrap")
end
