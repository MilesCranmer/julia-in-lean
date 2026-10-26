# deepcopy(w::WeakRef) goes through the generic mutable-struct path of
# deepcopy_internal (base/deepcopy.jl:62-99): jl_new_struct_uninit + jl_set_nth_field.
# The copy is never registered with the GC's weak-reference list (only
# WeakRef(x) -> jl_gc_new_weakref_th registers, src/gc-stock.c:359-366), and the GC
# does not mark through objects of type WeakRef (src/gc-stock.c:2744). So the
# deep-copied referent, reachable only through the copy, is freed while the
# copy's `value` field keeps pointing at it.
rawvalue(w::WeakRef) = unsafe_load(Ptr{Ptr{Cvoid}}(pointer_from_objref(w)))

@noinline function make()
    x = [1, 2, 3]
    w2 = deepcopy(WeakRef(x))
    probe = WeakRef(w2.value)   # a properly registered weak reference to the copied array
    return x, w2, probe
end

x, w2, probe = make()
nothing_ptr = rawvalue(WeakRef())
GC.gc(); GC.gc(true)
copy_freed = probe.value === nothing
field_cleared = rawvalue(w2) == nothing_ptr
println("original referent alive: ", x == [1, 2, 3])
println("deep-copied referent collected by the GC: ", copy_freed)
println("copy's WeakRef.value cleared to nothing: ", field_cleared)
if copy_freed && !field_cleared
    println("w2.value now points at freed memory")
    println("REPRODUCED dictscov-deepcopy-weakref")
end
