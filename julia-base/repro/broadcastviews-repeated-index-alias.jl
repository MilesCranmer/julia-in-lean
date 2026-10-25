# A view with repeated indices that is both the destination and an argument of `.=`
# is not unaliased, so later writes see earlier ones.
x = [10, 20, 30]
y = [10, 20, 30]
@views x[[1, 1, 2]] .+= 1        # dest === source view: not unaliased
y[[1, 1, 2]] .+= 1               # copy semantics
println("@views x[[1, 1, 2]] .+= 1 gives ", x, "; x[[1, 1, 2]] .+= 1 gives ", y)
if x != y
    println("REPRODUCED broadcastviews-repeated-index-alias")
end
