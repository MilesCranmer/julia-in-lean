import JuliaLean.Registry.Types
import JuliaLean.Sockets.Refutations
import JuliaLean.Sockets.IPv4Proofs
import JuliaLean.Sockets.IPv6Print
import JuliaLean.Sockets.Formatting
import JuliaLean.Sockets.Interface

namespace JuliaLean.Sockets

open JuliaLean.Registry

/-- Settled properties of the pure Sockets address code. -/
def entries : List Entry := [
  { id := "sockets-ipv6-empty-string", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["parse(::Type{IPv6}, ::AbstractString)"]
    statement := "Accepted IPv6 text is nonempty."
    source := "IPv6(str) docstring, IPAddr.jl:117-127; RFC 4291 section 2.2"
    status := .refuted, prop := ``IPv6Nonempty, thm := some ``ipv6Nonempty_refuted
    issue := "none found (queries: IPv6 parse, parse IPv6); related #40255 (open)"
    notes := "parse(IPv6, \"\") returns ip\"::\" on both versions." },
  { id := "sockets-ipv6-lone-colon", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["parse(::Type{IPv6}, ::AbstractString)", "parseipv6fields"]
    statement := "A leading or trailing colon in accepted IPv6 text belongs to a :: pair."
    source := "RFC 4291 section 2.2; IPv6(str) docstring"
    status := .refuted, prop := ``IPv6ColonPaired, thm := some ``ipv6ColonPaired_refuted
    issue := "none found (queries: IPv6 colon, lone colon); related #40255 (open)"
    notes := "':1' becomes '0:1::'; '1:' becomes '1::' on both versions." },
  { id := "sockets-ipv6-double-elision", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["parse(::Type{IPv6}, ::AbstractString)", "parseipv6fields"]
    statement := "Accepted IPv6 text contains at most one :: elision."
    source := "RFC 4291 section 2.2: The :: can only appear once in an address."
    status := .refuted, prop := ``IPv6OneElision, thm := some ``ipv6OneElision_refuted
    issue := "none found (queries: IPv6 parse, IPv6 colon); related #40255 (open)"
    notes := "'1::2::3' becomes '1::2:0:0'; the final field shifts right by 48 bits and vanishes." },
  { id := "sockets-ipv6-signed-field-error", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["parse(::Type{IPv6}, ::AbstractString)"]
    statement := "Rejected IPv6 text throws ArgumentError."
    source := "exception-consistency invariant; IPAddr.jl:85-88,223,246"
    status := .refuted, prop := ``IPv6ErrorIsArgument, thm := some ``ipv6ErrorIsArgument_refuted
    issue := "none found (queries: InexactError IPv6, IPv6 parse); related #40255 (open)"
    notes := "'::-1' throws InexactError. No docstring explicitly promises a uniform exception type." },
  { id := "sockets-ipv6-field-overflow", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["parse(::Type{IPv6}, ::AbstractString)", "parseipv6fields"]
    statement := "Nonempty hexadecimal groups of accepted IPv6 text have values at most 0xFFFF; embedded IPv4 tails are excluded."
    source := "RFC 4291 section 2.2; IPv6 field constructor range check, IPAddr.jl:85-88"
    status := .refuted, prop := ``IPv6FieldRange, thm := some ``ipv6FieldRange_refuted
    issue := "none found (queries: IPv6 parse, IPv6 field out of range, IPv6 10000); related #40255 (open)"
    notes := "'::10000' becomes '::1:0'; '::12345' becomes '::1:2345' on both versions." },
  { id := "sockets-ipv6-field-grammar", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["parse(::Type{IPv6}, ::AbstractString)"]
    statement := "Nonempty non-IPv4 groups of accepted IPv6 text contain only hexadecimal digits."
    source := "RFC 4291 section 2.2; IPv6(str) docstring"
    status := .refuted, prop := ``IPv6FieldBare, thm := some ``ipv6FieldBare_refuted
    issue := "none found (queries: IPv6 whitespace, IPv6 parse); related #40255 (open)"
    notes := "'::+1' and ':: 1' both become '::1'. Whitespace tolerance may be intentional." },
  { id := "sockets-ipv4-field-grammar", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["parse(::Type{IPv4}, ::AbstractString)"]
    statement := "Accepted dotted-quad IPv4 fields contain only decimal digits, without signs or whitespace."
    source := "IPv4(str) docstring; inet_pton-style dotted-quad grammar; #40255"
    status := .refuted, prop := ``IPv4FieldBare, thm := some ``ipv4FieldBare_refuted
    issue := "none found (queries: IPv4 parse, IPv4 whitespace); related #40255 (open), #9187 (closed), PR #40257 (merged)"
    notes := "'+1.2.3.4', '1.2.3.+4', '1.2.3.-0', and padded fields succeed. Release also accepts 1/2/3-part shorthand; master deliberately requires a dotted quad." },
  { id := "sockets-ipv4-overflow-error", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["parse(::Type{IPv4}, ::AbstractString)"]
    statement := "Rejected IPv4 text throws ArgumentError."
    source := "exception-consistency invariant; IPAddr.jl:201,205,208,213"
    status := .refuted, prop := ``IPv4ErrorIsArgument, thm := some ``ipv4ErrorIsArgument_refuted
    issue := "none found (queries: IPv4 parse, OverflowError parse); related #40255 (open)"
    notes := "'1.2.3.999999999999999999999999' throws OverflowError. This may be intentional propagation of Base.parse; no explicit uniform-exception promise." },
  { id := "sockets-ipv6-embedded-8fields", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["parse(::Type{IPv6}, ::AbstractString)"]
    statement := "A leading :: followed by five hexadecimal groups and an embedded IPv4 tail parses to its RFC 4291 value."
    source := "IPv6(str) docstring; RFC 4291 section 2.2 form 3"
    status := .refuted, prop := ``IPv6AcceptsFiveGroupsV4, thm := some ``ipv6AcceptsFiveGroupsV4_refuted
    issue := "none found (queries: IPv6 embedded IPv4, IPv6 parse); related #40255 (open)"
    notes := "'::1:2:3:4:5:1.2.3.4' raises ArgumentError; libc inet_pton accepts it as 0:1:2:3:4:5:102:304." },
  { id := "sockets-ipv6-boundary-single-elision", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["parse(::Type{IPv6}, ::AbstractString)"]
    statement := "Seven explicit IPv6 groups with a leading :: parse as a single omitted zero group."
    source := "RFC 4291 section 2.2; RFC 5952 section 4 input acceptance requirement"
    status := .refuted, prop := ``IPv6BoundaryElision, thm := some ``ipv6BoundaryElision_refuted
    issue := "none found (queries: IPv6 single zero, PR IPv6 parse); related #40255 (open)"
    notes := "Both '::1:2:3:4:5:6:7' and '1:2:3:4:5:6:7::' are valid but rejected on both versions." },
  { id := "sockets-bigint-constructor", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["IPv4(::Integer)", "IPv6(::Integer)"]
    statement := "Both Integer-host constructors accept nonnegative BigInt values fitting within 32 bits."
    source := "IPv4(host::Integer) and IPv6(host::Integer) docstrings, IPAddr.jl:31-34,94-97"
    status := .refuted, prop := ``BigIntConstructors, thm := some ``bigIntConstructors_refuted
    issue := "none found (queries: IPv4 BigInt, IPv6 BigInt, PR Sockets BigInt)"
    notes := "IPv4(big(1)) and IPv6(big(1)) both fail at typemax(BigInt), although ordinary Int(1) succeeds." },
  { id := "sockets-ipv4-print-canonical", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["print(::IO, ::IPv4)", "string(::IPv4)"]
    statement := "Each printed IPv4 field is a bare decimal value 0-255 without leading zeros."
    source := "IPAddr.jl:66-69; dotted-quad invariant"
    status := .proven, prop := ``IPv4PrintBare, thm := some ``ipv4PrintBare_proven },
  { id := "sockets-ipv4-roundtrip", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["parse(::Type{IPv4}, ::AbstractString)", "string(::IPv4)"]
    statement := "parse(IPv4, string(a)) == a for every IPv4 address."
    source := "print/parse roundtrip invariant; IPAddr.jl:66-69,196-219"
    status := .proven, prop := ``IPv4Roundtrip, thm := some ``ipv4Roundtrip_proven
    notes := "All 2^32 host values, symbolically. Model is master; release's extra shorthand forms do not change printed dotted-quad roundtrips." },
  { id := "sockets-ipv6-rfc5952", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["print(::IO, ::IPv6)", "string(::IPv6)"]
    statement := "IPv6 printing equals the RFC 5952 section 4 reference form: compress the longest zero run, the leftmost on ties, and never a single zero."
    source := "IPAddr.jl:142-143; https://www.rfc-editor.org/rfc/rfc5952#section-4"
    status := .proven, prop := ``IPv6Rfc5952, thm := some ``ipv6Rfc5952_proven
    notes := "256 zero/nonzero control-flow cases, with arbitrary values for nonzero groups. Section 5's mixed IPv4 display recommendations are outside this claim." },
  { id := "sockets-ipv6-hex-format", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["print_ipv6_field"]
    statement := "Every 16-bit group prints as 1-4 lowercase hexadecimal digits without leading zeros."
    source := "IPAddr.jl:130-131; RFC 5952 sections 4.1 and 4.3"
    status := .proven, prop := ``IPv6HexFormat, thm := some ``ipv6HexFormat_proven },
  { id := "sockets-isless-order", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["isless(::T, ::T) where T<:IPAddr"]
    statement := "Host-value isless is irreflexive, asymmetric, transitive, and total modulo equality."
    source := "IPAddr.jl:10; strict total order invariant"
    status := .proven, prop := ``IslessStrictOrder, thm := some ``islessStrictOrder_proven },
  { id := "sockets-inetaddr-ipv4-show", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["show(::IO, ::InetAddr{IPv4})"]
    statement := "InetAddr{IPv4} show embeds ip\"<address>\" and the decimal port in the documented constructor form."
    source := "IPAddr.jl:301-302,324-329"
    status := .proven, prop := ``Inet4ShowText, thm := some ``inet4ShowText_proven },
  { id := "sockets-inetaddr-ipv6-show", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["show(::IO, ::InetAddr{IPv6})"]
    statement := "InetAddr{IPv6} show embeds ip\"<address>\" and the decimal port in constructor form."
    source := "IPAddr.jl:324-329"
    status := .proven, prop := ``Inet6ShowText, thm := some ``inet6ShowText_proven },
  { id := "sockets-integer-constructors-inrange", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["IPv4(::Integer)", "IPv6(::Integer)"]
    statement := "Every nonnegative in-range fixed-width integer constructor preserves the exact host value."
    source := "IPAddr.jl:42-50,105-115; Core.JInt exact conversion"
    status := .proven, prop := ``WordConstructorInRange, thm := some ``wordConstructorInRange_proven },
  { id := "sockets-integer-constructors-reject", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["IPv4(::Integer)", "IPv6(::Integer)"]
    statement := "Negative and too-large fixed-width integer hosts raise ArgumentError."
    source := "IPAddr.jl:43-46,106-111"
    status := .proven, prop := ``WordConstructorRejects, thm := some ``wordConstructorRejects_proven },
  { id := "sockets-field-constructors-range", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["IPv4(::Integer, ::Integer, ::Integer, ::Integer)", "IPv6(::Integer...)"]
    statement := "An out-of-range component makes the field constructor raise ArgumentError."
    source := "IPAddr.jl:23-28,83-91"
    status := .proven, prop := ``FieldsRejectOutOfRange, thm := some ``fieldsRejectOutOfRange_proven },
  { id := "sockets-isequal-hash", juliaFile := "stdlib/Sockets/src/IPAddr.jl"
    juliaFns := ["isequal(::IPAddr, ::IPAddr)", "hash(::IPAddr, ::UInt)"]
    statement := "Equal typed address values have equal hashes for any deterministic objectid and UInt-hash functions."
    source := "base/hashing.jl:12-15,46; immutable isbits address identity"
    status := .proven, prop := ``AddressHashCongruent, thm := some ``addressHashCongruent_proven
    notes := "The C runtime's objectid and generic UInt hashing remain explicit function parameters; no numerical hash values or collision claims are assumed." }
]

end JuliaLean.Sockets
