const words = UInt64[0,1,2,0x000ffffffffffffe,0x000fffffffffffff,0x0010000000000000,0x0010000000000001,0x3fdfffffffffffff,0x3fe0000000000000,0x3fe0000000000001,0x3ff0000000000000,0x3ff0000000000001,0x3ff7ffffffffffff,0x3ff8000000000000,0x4004000000000000,0x433fffffffffffff,0x4340000000000000,0x7feffffffffffffe,0x7fefffffffffffff,0x7ff0000000000000,0x7ff0000000000001,0x7ff8000000000000,0x7fffffffffffffff]
append!(words,words .| 0x8000000000000000)
for k in [7,8,15,16,31,32,63,64,127,128]
    b = reinterpret(UInt64,2.0^k)
    for j in -2:2
        push!(words,b+UInt64(j % UInt64))
        push!(words,(b+UInt64(j % UInt64)) | 0x8000000000000000)
    end
end
let state=UInt64(0x243f6a8885a308d3)
    for _ in 1:2048
        state=state*UInt64(6364136223846793005)+UInt64(1442695040888963407)
        push!(words,state)
    end
end
out(x::Float64)=isnan(x) ? "nan" : string(reinterpret(UInt64,x))
out(x::Bool)=x ? "true" : "false"
out(x::Integer)=string(x)
out(x::Tuple)=join(out.(x),",")
function emit(i,op,f)
    try
        println(i," ",op," ",out(f()))
    catch e
        e isa Union{InexactError,DomainError,MethodError} || rethrow()
        println(i," ",op," ",e isa InexactError ? "inexact" : e isa DomainError ? "domain" : "method")
    end
end
const modes=[RoundNearest,RoundNearestTiesAway,RoundUp,RoundDown,RoundToZero]
const types=[Int8,Int16,Int32,Int64,Int128,UInt8,UInt16,UInt32,UInt64,UInt128]
const scales=[-2200,-1075,-1074,-1022,-53,-1,0,1,52,1023,1074,2200]
const steps=[-10000,-2,-1,0,1,2,10000]
println("0 floatmin ",out(floatmin(Float64)))
println("0 floatmax ",out(floatmax(Float64)))
for (i,b) in enumerate(words)
    x=reinterpret(Float64,b)
    y=reinterpret(Float64,words[mod(17*(i-1)+7,length(words))+1])
    z=reinterpret(Float64,words[mod(31*(i-1)+11,length(words))+1])
    for (name,f) in [("neg",()->-x),("abs",()->abs(x)),("sqrt",()->sqrt(x)),("signbit",()->signbit(x)),("isnan",()->isnan(x)),("isinf",()->isinf(x)),("isfinite",()->isfinite(x)),("next",()->nextfloat(x)),("prev",()->prevfloat(x)),("eps",()->eps(x)),("exponent",()->exponent(x)),("significand",()->significand(x)),("frexp",()->frexp(x)),("int",()->Int(x)),("ldexp",()->ldexp(x,scales[mod(i-1,length(scales))+1])),("nextn",()->nextfloat(x,steps[mod(i-1,length(steps))+1])),("prevn",()->prevfloat(x,steps[mod(i-1,length(steps))+1]))]
        emit(i,name,f)
    end
    for (name,f) in [("add",()->x+y),("sub",()->x-y),("mul",()->x*y),("divide",()->x/y),("fma",()->fma(x,y,z)),("muladd",()->muladd(x,y,z)),("eq",()->x==y),("lt",()->x<y),("le",()->x<=y),("isequal",()->isequal(x,y)),("isless",()->isless(x,y)),("rem",()->rem(x,y)),("mod",()->mod(x,y)),("div",()->div(x,y)),("fld",()->fld(x,y)),("cld",()->cld(x,y))]
        emit(i,name,f)
    end
    for (m,r) in enumerate(modes)
        emit(i,"round$m",()->round(x,r))
        emit(i,"remmode$m",()->rem(x,y,r))
        emit(i,"divmode$m",()->div(x,y,r))
        for (t,T) in enumerate(types)
            emit(i,"roundint$m-$t",()->round(T,x,r))
        end
    end
    n = (UInt128(b)<<64) | UInt128(words[mod(i,length(words))+1])
    for (t,T) in enumerate(types)
        emit(i,"ofint$t",()->Float64(n % T))
    end
end
println("COUNT ",length(words))
