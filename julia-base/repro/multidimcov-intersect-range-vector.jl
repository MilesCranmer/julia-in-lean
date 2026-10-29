r = 1:3
v = [3, 2, 1]
order_range = intersect(r, v)
order_collected = intersect(collect(r), v)
z_range = intersect([-0.0], 0.0:1.0:1.0)
z_collected = intersect([-0.0], collect(0.0:1.0:1.0))
println("intersect(1:3, [3, 2, 1]) = ", order_range, "; intersect(collect(1:3), [3, 2, 1]) = ", order_collected)
println("intersect([-0.0], 0.0:1.0:1.0) = ", z_range, "; with the collected range: ", z_collected)
if order_range == [3, 2, 1] && order_collected == [1, 2, 3] && isequal(z_range, [-0.0]) && isempty(z_collected)
    println("REPRODUCED multidimcov-intersect-range-vector")
else
    println("NOT REPRODUCED multidimcov-intersect-range-vector")
end
