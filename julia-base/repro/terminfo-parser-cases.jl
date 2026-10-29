using Test

le16(n) = UInt8[mod(n, 256), mod(n >> 8, 256)]

function fixture(; prefix=UInt8[])
    data = copy(prefix)
    append!(data, vcat(le16(0o432), le16(2), le16(1), le16(1), le16(1), le16(4)))
    append!(data, UInt8[0x78, 0x00, 0x01])
    isodd(length(data)) && push!(data, 0x00)
    append!(data, vcat(le16(42), le16(0), UInt8[0x61, 0x62, 0x63, 0x00]))
    data
end

function parseat(bytes, position=0)
    io = IOBuffer(bytes)
    seek(io, position)
    read(io, Base.TermInfoRaw)
end

println("Julia ", VERSION, " commit ", Base.GIT_VERSION_INFO.commit)
@testset "terminfo parser" begin
    for prefix in (UInt8[], UInt8[0x55], UInt8[0x55, 0x66])
        raw = parseat(fixture(; prefix), length(prefix))
        @test raw.names == ["x"]
        @test raw.flags == [true]
        @test raw.numbers == [42]
        @test raw.strings == ["abc"]
        @test isnothing(raw.extended)
    end
    @test_throws EOFError parseat(UInt8[])
    @test_throws EOFError parseat(UInt8[0x1a])
    @test_throws ArgumentError parseat(UInt8[0, 0])
    expected_short_table = VERSION < v"1.15.0-DEV" ? ArgumentError : EOFError
    @test_throws expected_short_table parseat(fixture()[1:end-1])
    @test_throws ArgumentError Base._terminfo_read_strings(UInt8[0x61], Int16[0])
    @test Base._terminfo_read_strings(UInt8[0x61, 0], Int16[-1, -2, 0]) == [nothing, nothing, "a"]
end
