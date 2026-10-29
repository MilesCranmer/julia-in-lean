import JuliaLean.Streams.Methods.Support

namespace JuliaLean.Streams.Methods.Stream

open JuliaLean.Streams JuliaLean.Streams.Methods JuliaLean.Registry

structure Args where
  endpoint : EndpointM
  stream : StreamM
  pipe : PipeM
  req : ReqM
  redirect : RedirectM
  bytes : List UInt8
  queued : List UInt8
  n : Nat
  m : Nat
  i : Int
  j : Int
  byte : UInt8
  flag : Bool
  flag2 : Bool
  flag3 : Bool
  status : UvStatus
  field : EndpointField
  handleKind : HandleKind
  text : String
  text2 : String
  deriving Repr, DecidableEq

structure Obs where
  endpoint : EndpointM
  stream : StreamM
  pipe : PipeM
  req : ReqM
  redirect : RedirectM
  bytes : List UInt8
  counts : List Nat
  integer : Int
  flags : List Bool
  text : String
  error : Option StreamErr
  deriving Repr, DecidableEq

def base (a : Args) : Obs :=
  ⟨a.endpoint, a.stream, a.pipe, a.req, a.redirect, a.bytes, [], a.i, [], a.text, none⟩

def withEndpoint (a : Args) : Except StreamErr EndpointM → Obs
  | .ok endpoint => { base a with endpoint }
  | .error error => { base a with error := some error }

def withStream (a : Args) : Except StreamErr (Nat × StreamM) → Obs
  | .ok (count, stream) => { base a with stream, counts := [count] }
  | .error error => { base a with error := some error }

def withRead (a : Args) : Except StreamErr (List UInt8 × StreamM) → Obs
  | .ok (bytes, stream) => { base a with bytes, stream, counts := [bytes.length] }
  | .error error => { base a with error := some error }

def reqFinishObs (a : Args) (completed tryCancel knownOwner : Bool) : Obs :=
  { base a with req := finishReq a.req completed tryCancel knownOwner }

def m29 (a : Args) : Obs := { base a with counts := [endpointField a.endpoint a.field] }

def m58 (a : Args) : Obs := { base a with counts := [endpointField a.endpoint a.field] }

def m102 (a : Args) : Obs := { base a with counts := [a.endpoint.buffer.length] }

def m104 (a : Args) : Obs := { base a with flags := [streamEof a.stream] }

def m139 (a : Args) : Obs := { base a with text := uvStatusString a.endpoint.hasHandle a.status }

def m179 (a : Args) : Obs := { base a with endpoint := endpointCtor a.endpoint.hasHandle a.status }

def m194 (a : Args) : Obs := { base a with endpoint := endpointCtor false .uninit }

def m204 (a : Args) : Obs := { base a with endpoint := endpointCtor a.flag .init }

def m224 (a : Args) : Obs := { base a with endpoint := endpointCtor a.endpoint.hasHandle a.status }

def m244 (a : Args) : Obs := { base a with endpoint := endpointCtor a.flag .init }

def m258 (a : Args) : Obs := { base a with text := endpointShow "LibuvServer" a.i a.endpoint }

def m261 (a : Args) : Obs := { base a with text := endpointShow a.text a.i a.endpoint }

def m268 (a : Args) : Obs := { base a with flags := [endpointReadable a.endpoint] }

def m275 (a : Args) : Obs := { base a with flags := [endpointWritable a.endpoint] }

def m281 (a : Args) : Obs := { base a with counts := [lockDepth a.n true] }

def m282 (a : Args) : Obs := { base a with counts := [lockDepth a.n false] }

def m284 (a : Args) : Obs := { base a with endpoint := (setupStreamStdio a.endpoint).1, flags := [(setupStreamStdio a.endpoint).2] }

def m285 (a : Args) : Obs := { base a with flags := [rawHandleModel a.endpoint] }

def m286 (a : Args) : Obs := { base a with flags := [a.endpoint.hasHandle] }

def m288 (a : Args) : Obs := match initStdioModel a.handleKind with
      | .ok kind => { base a with stream := freshStream kind }
      | .error e => { base a with error := some e }

def m328 (a : Args) : Obs := { base a with endpoint := { a.endpoint with hasHandle := a.flag, status := if a.flag then .opened else .closed } }

def m364 (a : Args) : Obs := { base a with endpoint := { a.endpoint with hasHandle := a.flag, status := if a.flag then .opened else .closed } }

def m377 (a : Args) : Obs := match endpointIsOpen a.endpoint with
      | .ok opened => { base a with flags := [opened] }
      | .error e => { base a with error := some e }

def m384 (a : Args) : Obs := withEndpoint a (match endpointCheckOpen a.endpoint with | .ok _ => .ok a.endpoint | .error e => .error e)

def m390 (a : Args) : Obs := withEndpoint a (waitReadState a.endpoint a.n)

def m493 (a : Args) : Obs := { base a with flags := [a.req.owner == .waiter] }

def m502 (a : Args) : Obs := { base a with req := markReqCancelled a.req }

def m511 (a : Args) : Obs := { base a with flags := [a.req.cancelRequested] }

def m530 (a : Args) : Obs := { base a with req := { a.req with rooted := true, owner := .detachedReq } }

def m534 (a : Args) : Obs := { base a with req := { a.req with rooted := false } }

def m540 (a : Args) : Obs := if a.flag then { base a with error := some .ioError } else base a

def m553 (a : Args) : Obs := match beginReq a.flag a.n with
      | .ok req => { base a with req }
      | .error e => { base a with error := some e }

def m575 (a : Args) : Obs := reqFinishObs a a.flag a.flag2 a.flag3

def m615 (a : Args) : Obs := { base a with flags := [a.flag], counts := [a.n + 1] }

def m626 (a : Args) : Obs := { base a with req := if a.byte = 0 then a.req else markReqCancelled a.req }

def m650 (a : Args) : Obs := reqFinishObs a a.flag a.flag2 a.flag3

def m700 (a : Args) : Obs := { base a with flags := [a.req.owner == .waiter], req := if a.req.owner == .waiter then { a.req with owner := .callbackDone } else a.req }

def m719 (a : Args) : Obs := withEndpoint a (endpointCloseWrite a.endpoint a.i)

def m750 (a : Args) : Obs := { base a with endpoint := if a.endpoint.hasHandle then a.endpoint else endpointClose a.endpoint }

def m770 (a : Args) : Obs := { base a with endpoint := endpointClose a.endpoint }

def m786 (a : Args) : Obs := { base a with endpoint := endpointClose a.endpoint }

def m809 (a : Args) : Obs := { base a with flags := [true] }

def m810 (a : Args) : Obs := { base a with flags := [false] }

def m836 (a : Args) : Obs := { base a with counts := let size := displaySizeModel (some a.n) (some a.m); [size.1, size.2] }

def m837 (a : Args) : Obs := { base a with counts := let size := displaySizeModel none none; [size.1, size.2] }

def m845 (a : Args) : Obs := { base a with counts := let size := displaySizeModel (some a.n) (some a.m); [size.1, size.2] }

def m847 (a : Args) : Obs := { base a with counts := let size := displaySizeModel (some a.n) (some a.m); [size.1, size.2] }

def m885 (a : Args) : Obs := { base a with counts := [allocRequestSize a.n a.m a.endpoint.throttle] }

def m893 (a : Args) : Obs := { base a with endpoint := notifyFilled a.endpoint a.bytes a.i }

def m895 (a : Args) : Obs := { base a with endpoint := notifyFilled a.endpoint a.bytes a.i }

def m905 (a : Args) : Obs := { base a with counts := [allocRequestSize a.endpoint.buffer.length a.n a.endpoint.throttle] }

def m910 (a : Args) : Obs := { base a with counts := [allocRequestSize a.endpoint.buffer.length a.n a.endpoint.throttle] }

def m938 (a : Args) : Obs := { base a with endpoint := notifyFilled a.endpoint a.bytes a.i }

def m941 (a : Args) : Obs := { base a with endpoint := notifyFilled a.endpoint a.bytes a.i }

def m992 (a : Args) : Obs := { base a with endpoint := if a.endpoint.status == .eof then { a.endpoint with status := .active } else a.endpoint }

def m1001 (a : Args) : Obs := { base a with endpoint := endpointClose a.endpoint }

def m1048 (a : Args) : Obs := { base a with pipe := freshPipe }

def m1049 (a : Args) : Obs := { base a with stream := a.pipe.readEnd }

def m1050 (a : Args) : Obs := { base a with stream := a.pipe.writeEnd }

def m1061 (a : Args) : Obs := { base a with pipe := { a.pipe with readEnd := { a.pipe.readEnd with status := .active }, writeEnd := { a.pipe.writeEnd with status := .active } } }

def m1068 (a : Args) : Obs := { base a with text := "Pipe(" ++ toString a.pipe.readEnd.buffer.length ++ ", " ++ toString a.pipe.writeEnd.buffer.length ++ ")" }

def m1076 (a : Args) : Obs := { base a with pipe := closePipeWrite a.pipe }

def m1080 (a : Args) : Obs := { base a with endpoint := { a.endpoint with hasHandle := a.flag, status := .opened } }

def m1093 (a : Args) : Obs := { base a with pipe := { readEnd := { a.pipe.readEnd with status := .active }, writeEnd := { a.pipe.writeEnd with status := .active } } }

def m1111 (a : Args) : Obs := { base a with pipe := { readEnd := { a.pipe.readEnd with status := .active }, writeEnd := { a.pipe.writeEnd with status := .active } } }

def m1128 (a : Args) : Obs := { base a with flags := [a.flag] }

def m1138 (a : Args) : Obs := { base a with endpoint := startReadingState a.endpoint }

def m1168 (a : Args) : Obs := { base a with endpoint := stopReadingState a.endpoint }

def m1178 (a : Args) : Obs := { base a with endpoint := stopReadingState a.endpoint }

def m1190 (a : Args) : Obs := let read := readbytesModel a.stream.buffer a.n; { base a with counts := [read.1], bytes := read.2.1, stream := { a.stream with buffer := read.2.2 } }

def m1191 (a : Args) : Obs := let read := readbytesModel a.stream.buffer a.n; { base a with counts := [read.1], bytes := read.2.1, stream := { a.stream with buffer := read.2.2 } }

def m1198 (a : Args) : Obs := withEndpoint a (waitReadState a.endpoint a.n)

def m1232 (a : Args) : Obs := withRead a (readAvailable a.stream)

def m1240 (a : Args) : Obs := withRead a (unsafeRead a.stream a.n)

def m1247 (a : Args) : Obs := withEndpoint a (waitReadState a.endpoint a.n)

def m1277 (a : Args) : Obs := withRead a (unsafeRead a.stream 1)

def m1292 (a : Args) : Obs := withRead a (readAvailable a.stream)

def m1302 (a : Args) : Obs := withRead a (readUntil a.stream a.byte a.flag)

def m1347 (a : Args) : Obs := { base a with counts := writeChunks a.bytes.length (max 1 a.n) }

def m1360 (a : Args) : Obs := { base a with counts := writeChunks a.n (max 1 a.m), req := completeReq a.req a.i a.j.toNat }

def m1478 (a : Args) : Obs := reqFinishObs a a.flag a.flag2 a.flag3

def m1558 (a : Args) : Obs := { base a with req := completeReq a.req a.i a.n }

def m1576 (a : Args) : Obs := reqFinishObs a a.flag a.flag2 a.flag3

def m1604 (a : Args) : Obs := { base a with counts := writeChunks a.n (max 1 a.m) }

def m1611 (a : Args) : Obs := { base a with counts := writeChunks a.n (max 1 a.m) }

def m1634 (a : Args) : Obs := { base a with counts := writeChunks a.n (max 1 a.m) }

def m1669 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes a.bytes.length)

def m1679 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes (min a.n a.bytes.length))

def m1691 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes a.bytes.length)

def m1699 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes (min a.n a.bytes.length))

def m1710 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes a.bytes.length)

def m1720 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes (min a.n a.bytes.length))

def m1736 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes a.n)

def m1741 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes a.n)

def m1778 (a : Args) : Obs := { base a with bytes := requeueUnwritten a.bytes a.queued a.n }

def m1795 (a : Args) : Obs := { base a with bytes := a.endpoint.sendBuffer.getD [], endpoint := { a.endpoint with sendBuffer := none } }

def m1826 (a : Args) : Obs := { base a with endpoint := { a.endpoint with sendBuffer := some [] }, counts := [a.n] }

def m1836 (a : Args) : Obs := withStream a (unsafeWrite a.stream [a.byte] 1)

def m1856 (a : Args) : Obs := { base a with req := completeReq a.req a.i a.n }

def m1909 (a : Args) : Obs := { base a with req := completeReq a.req a.i 0 }

def m1916 (a : Args) : Obs := { base a with integer := a.i }

def m1917 (a : Args) : Obs := { base a with integer := a.i }

def m1919 (a : Args) : Obs := { base a with flags := [a.endpoint.hasHandle], integer := a.i }

def m1938 (a : Args) : Obs := { base a with integer := a.i, flags := [a.flag] }

def m1949 (a : Args) : Obs := { base a with integer := a.i, flags := [a.flag] }

def m1957 (a : Args) : Obs := { base a with integer := a.i, flags := [a.flag] }

def m1963 (a : Args) : Obs := { base a with redirect := { a.redirect with outStream := .stream } }

def m1969 (a : Args) : Obs := { base a with redirect := { a.redirect with outStream := .devnull } }

def m1978 (a : Args) : Obs := { base a with redirect := { a.redirect with outStream := .stream } }

def m1984 (a : Args) : Obs := { base a with redirect := { a.redirect with outStream := .stream } }

def m1992 (a : Args) : Obs := { base a with redirect := { a.redirect with outStream := .stream } }

def m1995 (a : Args) : Obs := { base a with counts := [1] }

def m1996 (a : Args) : Obs := { base a with counts := [a.n] }

def m1997 (a : Args) : Obs := match pipeGetindex (a.pipe.readEnd, a.pipe.writeEnd) a.i with
      | some stream => { base a with stream }
      | none => { base a with error := some .argumentError }

def m2052 (a : Args) : Obs := { base a with redirect := redirectStdio a.redirect .keep .keep .keep }

def m2110 (a : Args) : Obs := { base a with redirect := redirectStdio a.redirect (if a.flag then .stream else .keep) (if a.flag2 then .stream else .keep) (if a.flag3 then .stream else .keep) }

def m2112 (a : Args) : Obs := { base a with redirect := a.redirect }

def m2115 (a : Args) : Obs := { base a with text := a.text }

def m2118 (a : Args) : Obs := { base a with redirect := { a.redirect with outStream := .stream } }

def m2122 (a : Args) : Obs := { base a with flags := [false] }

def m2123 (a : Args) : Obs := { base a with flags := [samePath a.text a.text2] }

def m2156 (a : Args) : Obs := { base a with redirect := redirectStdio a.redirect .keep .stream .keep }

def m2194 (a : Args) : Obs := { base a with counts := [a.n] }

def m2195 (a : Args) : Obs := { base a with counts := [a.n] }

def m2196 (a : Args) : Obs := { base a with counts := [a.n] }

def m2197 (a : Args) : Obs := { base a with flags := [a.flag] }

def m2199 (a : Args) : Obs := match peekModel a.endpoint.buffer a.n with
      | .ok bytes => { base a with bytes }
      | .error e => { base a with error := some e }

def m2216 (a : Args) : Obs := { base a with stream := freshStream .bufferStream }

def m2219 (a : Args) : Obs := { base a with flags := [isOpen a.stream] }

def m2225 (a : Args) : Obs := { base a with stream := { a.stream with writable := false } }

def m2231 (a : Args) : Obs := { base a with stream := bufferClose a.stream }

def m2238 (a : Args) : Obs := { base a with stream := bufferClose a.stream }

def m2239 (a : Args) : Obs := { base a with flags := [a.flag] }

def m2241 (a : Args) : Obs := match bufferReadByte a.stream with
      | .ok (byte, stream) => { base a with stream, bytes := [byte] }
      | .error e => { base a with error := some e }

def m2249 (a : Args) : Obs := withRead a (unsafeRead a.stream a.n)

def m2257 (a : Args) : Obs := { base a with counts := [a.stream.buffer.length] }

def m2259 (a : Args) : Obs := { base a with flags := [bufferReadable a.stream] }

def m2260 (a : Args) : Obs := { base a with flags := [bufferWritable a.stream] }

def m2262 (a : Args) : Obs := { base a with flags := [a.n ≤ a.stream.buffer.length || !isOpen a.stream] }

def m2277 (a : Args) : Obs := withRead a (readAvailable a.stream)

def m2288 (a : Args) : Obs := withRead a (readAvailable a.stream)

def m2297 (a : Args) : Obs := let read := bufferReadN a.stream a.n; { base a with bytes := read.1, stream := read.2, counts := [read.1.length] }

def m2303 (a : Args) : Obs := { base a with flags := [a.n ≤ a.stream.buffer.length || !isOpen a.stream] }

def m2337 (a : Args) : Obs := { base a with text := "BufferStream(" ++ toString a.stream.buffer.length ++ " bytes waiting)" }

def m2339 (a : Args) : Obs := withRead a (readUntil a.stream a.byte a.flag)

def m2358 (a : Args) : Obs := { base a with flags := [!isOpen a.stream] }

def m2373 (a : Args) : Obs := base a

def m2374 (a : Args) : Obs := base a

def m2376 (a : Args) : Obs := withStream a (unsafeWrite a.stream [a.byte] 1)

def m2382 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes a.bytes.length)

def m2388 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes a.bytes.length)

def m2395 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes a.bytes.length)

def m2404 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes a.n)

def m2416 (a : Args) : Obs := { base a with flags := [bufferEof a.stream] }

def m2427 (a : Args) : Obs := { base a with counts := [a.n] }

def m2428 (a : Args) : Obs := { base a with stream := bufferFlush a.stream }

def m2438 (a : Args) : Obs := { base a with stream := bufferSkip a.stream a.n }

def m2440 (a : Args) : Obs := { base a with stream := bufferResetEof a.stream }

/-- Dispatch by the source line of the modelled method. -/
def run : Nat → Args → Obs
  | 29, a => m29 a
  | 58, a => m58 a
  | 102, a => m102 a
  | 104, a => m104 a
  | 139, a => m139 a
  | 179, a => m179 a
  | 194, a => m194 a
  | 204, a => m204 a
  | 224, a => m224 a
  | 244, a => m244 a
  | 258, a => m258 a
  | 261, a => m261 a
  | 268, a => m268 a
  | 275, a => m275 a
  | 281, a => m281 a
  | 282, a => m282 a
  | 284, a => m284 a
  | 285, a => m285 a
  | 286, a => m286 a
  | 288, a => m288 a
  | 328, a => m328 a
  | 364, a => m364 a
  | 377, a => m377 a
  | 384, a => m384 a
  | 390, a => m390 a
  | 493, a => m493 a
  | 502, a => m502 a
  | 511, a => m511 a
  | 530, a => m530 a
  | 534, a => m534 a
  | 540, a => m540 a
  | 553, a => m553 a
  | 575, a => m575 a
  | 615, a => m615 a
  | 626, a => m626 a
  | 650, a => m650 a
  | 700, a => m700 a
  | 719, a => m719 a
  | 750, a => m750 a
  | 770, a => m770 a
  | 786, a => m786 a
  | 809, a => m809 a
  | 810, a => m810 a
  | 836, a => m836 a
  | 837, a => m837 a
  | 845, a => m845 a
  | 847, a => m847 a
  | 885, a => m885 a
  | 893, a => m893 a
  | 895, a => m895 a
  | 905, a => m905 a
  | 910, a => m910 a
  | 938, a => m938 a
  | 941, a => m941 a
  | 992, a => m992 a
  | 1001, a => m1001 a
  | 1048, a => m1048 a
  | 1049, a => m1049 a
  | 1050, a => m1050 a
  | 1061, a => m1061 a
  | 1068, a => m1068 a
  | 1076, a => m1076 a
  | 1080, a => m1080 a
  | 1093, a => m1093 a
  | 1111, a => m1111 a
  | 1128, a => m1128 a
  | 1138, a => m1138 a
  | 1168, a => m1168 a
  | 1178, a => m1178 a
  | 1190, a => m1190 a
  | 1191, a => m1191 a
  | 1198, a => m1198 a
  | 1232, a => m1232 a
  | 1240, a => m1240 a
  | 1247, a => m1247 a
  | 1277, a => m1277 a
  | 1292, a => m1292 a
  | 1302, a => m1302 a
  | 1347, a => m1347 a
  | 1360, a => m1360 a
  | 1478, a => m1478 a
  | 1558, a => m1558 a
  | 1576, a => m1576 a
  | 1604, a => m1604 a
  | 1611, a => m1611 a
  | 1634, a => m1634 a
  | 1669, a => m1669 a
  | 1679, a => m1679 a
  | 1691, a => m1691 a
  | 1699, a => m1699 a
  | 1710, a => m1710 a
  | 1720, a => m1720 a
  | 1736, a => m1736 a
  | 1741, a => m1741 a
  | 1778, a => m1778 a
  | 1795, a => m1795 a
  | 1826, a => m1826 a
  | 1836, a => m1836 a
  | 1856, a => m1856 a
  | 1909, a => m1909 a
  | 1916, a => m1916 a
  | 1917, a => m1917 a
  | 1919, a => m1919 a
  | 1938, a => m1938 a
  | 1949, a => m1949 a
  | 1957, a => m1957 a
  | 1963, a => m1963 a
  | 1969, a => m1969 a
  | 1978, a => m1978 a
  | 1984, a => m1984 a
  | 1992, a => m1992 a
  | 1995, a => m1995 a
  | 1996, a => m1996 a
  | 1997, a => m1997 a
  | 2052, a => m2052 a
  | 2110, a => m2110 a
  | 2112, a => m2112 a
  | 2115, a => m2115 a
  | 2118, a => m2118 a
  | 2122, a => m2122 a
  | 2123, a => m2123 a
  | 2156, a => m2156 a
  | 2194, a => m2194 a
  | 2195, a => m2195 a
  | 2196, a => m2196 a
  | 2197, a => m2197 a
  | 2199, a => m2199 a
  | 2216, a => m2216 a
  | 2219, a => m2219 a
  | 2225, a => m2225 a
  | 2231, a => m2231 a
  | 2238, a => m2238 a
  | 2239, a => m2239 a
  | 2241, a => m2241 a
  | 2249, a => m2249 a
  | 2257, a => m2257 a
  | 2259, a => m2259 a
  | 2260, a => m2260 a
  | 2262, a => m2262 a
  | 2277, a => m2277 a
  | 2288, a => m2288 a
  | 2297, a => m2297 a
  | 2303, a => m2303 a
  | 2337, a => m2337 a
  | 2339, a => m2339 a
  | 2358, a => m2358 a
  | 2373, a => m2373 a
  | 2374, a => m2374 a
  | 2376, a => m2376 a
  | 2382, a => m2382 a
  | 2388, a => m2388 a
  | 2395, a => m2395 a
  | 2404, a => m2404 a
  | 2416, a => m2416 a
  | 2427, a => m2427 a
  | 2428, a => m2428 a
  | 2438, a => m2438 a
  | 2440, a => m2440 a
  | _, a => base a

-- METHOD CONTRACTS

def EndpointResultContract (observed : Obs) (args : Args)
    (result : Except StreamErr EndpointM) : Prop :=
  (observed.endpoint, observed.error) =
    match result with
    | .ok endpoint => (endpoint, none)
    | .error e => (args.endpoint, some e)

def ReadResultContract (observed : Obs) (args : Args)
    (result : Except StreamErr (List UInt8 × StreamM)) : Prop :=
  (observed.bytes, observed.stream, observed.counts, observed.error) =
    match result with
    | .ok (bytes, stream) => (bytes, stream, [bytes.length], none)
    | .error e => (args.bytes, args.stream, [], some e)

def WriteResultContract (observed : Obs) (args : Args)
    (result : Except StreamErr (Nat × StreamM)) : Prop :=
  (observed.stream, observed.counts, observed.error) =
    match result with
    | .ok (count, stream) => (stream, [count], none)
    | .error e => (args.stream, [], some e)

attribute [local simp] EndpointResultContract ReadResultContract WriteResultContract
  withEndpoint withRead withStream base setupStreamStdio displaySizeModel closePipeWrite
  readbytesModel bufferReadN reqFinishObs bufferFlush bufferSkip rawHandleModel
  initStdioModel markReqCancelled beginReq redirectStdio resolveRedirect

def P29 : Prop := ∀ a, (m29 a).counts = [endpointField a.endpoint a.field]
theorem p29 : P29 := by
  intro a
  simp [m29]

def P58 : Prop := ∀ a, (m58 a).counts = [endpointField a.endpoint a.field]
theorem p58 : P58 := by
  intro a
  simp [m58]

/-- An availability query does not consume buffered bytes, and reports zero
exactly when no buffered bytes are available. -/
def P102 : Prop := ∀ a, (m102 a).endpoint = a.endpoint ∧
  ((m102 a).counts = [0] ↔ a.endpoint.buffer = [])
theorem p102 : P102 := by
  intro a
  simp [m102, base]

def P104 : Prop := ∀ a, (m104 a).flags = [streamEof a.stream]
theorem p104 : P104 := by
  intro a
  simp [m104]

def P139 : Prop := ∀ a, (m139 a).text = uvStatusString a.endpoint.hasHandle a.status
theorem p139 : P139 := by
  intro a
  simp [m139]

def P179 : Prop := ∀ a, (m179 a).endpoint = endpointCtor a.endpoint.hasHandle a.status
theorem p179 : P179 := by
  intro a
  simp [m179]

def P194 : Prop := ∀ a, (m194 a).endpoint = endpointCtor false .uninit
theorem p194 : P194 := by
  intro a
  simp [m194]

def P204 : Prop := ∀ a, (m204 a).endpoint = endpointCtor a.flag .init
theorem p204 : P204 := by
  intro a
  simp [m204]

def P224 : Prop := ∀ a, (m224 a).endpoint = endpointCtor a.endpoint.hasHandle a.status
theorem p224 : P224 := by
  intro a
  simp [m224]

def P244 : Prop := ∀ a, (m244 a).endpoint = endpointCtor a.flag .init
theorem p244 : P244 := by
  intro a
  simp [m244]

def P258 : Prop := ∀ a, (m258 a).text = endpointShow "LibuvServer" a.i a.endpoint
theorem p258 : P258 := by
  intro a
  simp [m258]

def P261 : Prop := ∀ a, (m261 a).text = endpointShow a.text a.i a.endpoint
theorem p261 : P261 := by
  intro a
  simp [m261]

def P268 : Prop := ∀ a, (m268 a).flags = [endpointReadable a.endpoint]
theorem p268 : P268 := by
  intro a
  simp [m268]

def P275 : Prop := ∀ a, (m275 a).flags = [endpointWritable a.endpoint]
theorem p275 : P275 := by
  intro a
  simp [m275]

def P281 : Prop := ∀ a, (m281 a).counts = [lockDepth a.n true]
theorem p281 : P281 := by
  intro a
  simp [m281]

def P282 : Prop := ∀ a, (m282 a).counts = [lockDepth a.n false]
theorem p282 : P282 := by
  intro a
  simp [m282]

def P284 : Prop := ∀ a, (m284 a).endpoint = a.endpoint ∧ (m284 a).flags = [false]
theorem p284 : P284 := by
  intro a
  simp [m284]

def P285 : Prop := ∀ a, (m285 a).flags = [a.endpoint.hasHandle]
theorem p285 : P285 := by
  intro a
  simp [m285, rawHandleModel]

def P286 : Prop := ∀ a, (m286 a).flags = [a.endpoint.hasHandle]
theorem p286 : P286 := by
  intro a
  simp [m286]

def P288 : Prop := ∀ a, ((m288 a).stream, (m288 a).error) =
  match initStdioModel a.handleKind with
  | .ok kind => (freshStream kind, none)
  | .error e => (a.stream, some e)
theorem p288 : P288 := by
  intro a
  cases hk : a.handleKind <;>
    simp [m288, base, initStdioModel, reinitStdioKind, hk]

def P328 : Prop := ∀ a, (m328 a).endpoint =
  { a.endpoint with hasHandle := a.flag, status := if a.flag then .opened else .closed }
theorem p328 : P328 := by
  intro a
  simp [m328]

def P364 : Prop := ∀ a, (m364 a).endpoint =
  { a.endpoint with hasHandle := a.flag, status := if a.flag then .opened else .closed }
theorem p364 : P364 := by
  intro a
  simp [m364]

def P377 : Prop := ∀ a, ((m377 a).flags, (m377 a).error) =
  match endpointIsOpen a.endpoint with
  | .ok opened => ([opened], none)
  | .error e => ([], some e)
theorem p377 : P377 := by
  intro a
  cases h : endpointIsOpen a.endpoint <;>
    simp [m377, base, h]

def P384 : Prop := ∀ a, EndpointResultContract (m384 a) a
  (match endpointCheckOpen a.endpoint with | .ok _ => .ok a.endpoint | .error e => .error e)
theorem p384 : P384 := by
  intro a
  cases h : endpointCheckOpen a.endpoint <;>
    simp [m384, EndpointResultContract, withEndpoint, base, h]

def P390 : Prop := ∀ a, EndpointResultContract (m390 a) a (waitReadState a.endpoint a.n)
theorem p390 : P390 := by
  intro a
  cases h : waitReadState a.endpoint a.n <;>
    simp [m390, EndpointResultContract, withEndpoint, base, h]

def P493 : Prop := ∀ a, (m493 a).flags = [a.req.owner == .waiter]
theorem p493 : P493 := by
  intro a
  simp [m493]

def P502 : Prop := ∀ a, (m502 a).req.cancelRequested = true
theorem p502 : P502 := by
  intro a
  simp [m502, markReqCancelled]

def P511 : Prop := ∀ a, (m511 a).flags = [a.req.cancelRequested]
theorem p511 : P511 := by
  intro a
  simp [m511]

def P530 : Prop := ∀ a, (m530 a).req.rooted = true ∧ (m530 a).req.owner = .detachedReq
theorem p530 : P530 := by
  intro a
  simp [m530]

def P534 : Prop := ∀ a, (m534 a).req.rooted = false
theorem p534 : P534 := by
  intro a
  simp [m534]

def P540 : Prop := ∀ a, (m540 a).error = if a.flag then some .ioError else none
theorem p540 : P540 := by
  intro a
  cases hf : a.flag <;> simp [m540, base, hf]

def P553 : Prop := ∀ a, ((m553 a).req, (m553 a).error) =
  if a.flag then (a.req, some .ioError)
  else (⟨.waiter, false, false, a.n, none, 0⟩, none)
theorem p553 : P553 := by
  intro a
  cases hf : a.flag <;> simp [m553, beginReq, base, hf]

def P575 : Prop := ∀ a, (m575 a).req = finishReq a.req a.flag a.flag2 a.flag3
theorem p575 : P575 := by
  intro a
  simp [m575]

def P615 : Prop := ∀ a, (m615 a).flags = [a.flag] ∧ (m615 a).counts = [a.n + 1]
theorem p615 : P615 := by
  intro a
  simp [m615]

def P626 : Prop := ∀ a, (m626 a).req =
  if a.byte = 0 then a.req else markReqCancelled a.req
theorem p626 : P626 := by
  intro a
  simp [m626]

def P650 : Prop := ∀ a, (m650 a).req = finishReq a.req a.flag a.flag2 a.flag3
theorem p650 : P650 := by
  intro a
  simp [m650]

def P700 : Prop := ∀ a, (m700 a).flags = [a.req.owner == .waiter] ∧
  (m700 a).req = if a.req.owner == .waiter then { a.req with owner := .callbackDone } else a.req
theorem p700 : P700 := by
  intro a
  simp [m700]

def P719 : Prop := ∀ a, EndpointResultContract (m719 a) a (endpointCloseWrite a.endpoint a.i)
theorem p719 : P719 := by
  intro a
  cases h : endpointCloseWrite a.endpoint a.i <;>
    simp [m719, EndpointResultContract, withEndpoint, base, h]

def P750 : Prop := ∀ a, (m750 a).endpoint =
  if a.endpoint.hasHandle then a.endpoint else endpointClose a.endpoint
theorem p750 : P750 := by
  intro a
  simp [m750]

def P770 : Prop := ∀ a, (m770 a).endpoint = endpointClose a.endpoint
theorem p770 : P770 := by
  intro a
  simp [m770]

def P786 : Prop := ∀ a, (m786 a).endpoint = endpointClose a.endpoint
theorem p786 : P786 := by
  intro a
  simp [m786]

def P809 : Prop := ∀ a, (m809 a).flags = [true]
theorem p809 : P809 := by
  intro a
  simp [m809]

def P810 : Prop := ∀ a, (m810 a).flags = [false]
theorem p810 : P810 := by
  intro a
  simp [m810]

def P836 : Prop := ∀ a, (m836 a).counts = [a.n, a.m]
theorem p836 : P836 := by
  intro a
  simp [m836]

def P837 : Prop := ∀ a, (m837 a).counts = [24, 80]
theorem p837 : P837 := by
  intro a
  simp [m837]

def P845 : Prop := ∀ a, (m845 a).counts = [a.n, a.m]
theorem p845 : P845 := by
  intro a
  simp [m845]

def P847 : Prop := ∀ a, (m847 a).counts = [a.n, a.m]
theorem p847 : P847 := by
  intro a
  simp [m847]

def P885 : Prop := ∀ a, (m885 a).counts = [allocRequestSize a.n a.m a.endpoint.throttle]
theorem p885 : P885 := by
  intro a
  simp [m885]

def P893 : Prop := ∀ a, (m893 a).endpoint = notifyFilled a.endpoint a.bytes a.i
theorem p893 : P893 := by
  intro a
  simp [m893]

def P895 : Prop := ∀ a, (m895 a).endpoint = notifyFilled a.endpoint a.bytes a.i
theorem p895 : P895 := by
  intro a
  simp [m895]

def P905 : Prop := ∀ a, (m905 a).counts =
  [allocRequestSize a.endpoint.buffer.length a.n a.endpoint.throttle]
theorem p905 : P905 := by
  intro a
  simp [m905]

def P910 : Prop := ∀ a, (m910 a).counts =
  [allocRequestSize a.endpoint.buffer.length a.n a.endpoint.throttle]
theorem p910 : P910 := by
  intro a
  simp [m910]

def P938 : Prop := ∀ a, (m938 a).endpoint = notifyFilled a.endpoint a.bytes a.i
theorem p938 : P938 := by
  intro a
  simp [m938]

def P941 : Prop := ∀ a, (m941 a).endpoint = notifyFilled a.endpoint a.bytes a.i
theorem p941 : P941 := by
  intro a
  simp [m941]

def P992 : Prop := ∀ a, (m992 a).endpoint =
  if a.endpoint.status == .eof then { a.endpoint with status := .active } else a.endpoint
theorem p992 : P992 := by
  intro a
  simp [m992]

def P1001 : Prop := ∀ a, (m1001 a).endpoint = endpointClose a.endpoint
theorem p1001 : P1001 := by
  intro a
  simp [m1001]

def P1048 : Prop := ∀ a, (m1048 a).pipe = freshPipe
theorem p1048 : P1048 := by
  intro a
  simp [m1048]

def P1049 : Prop := ∀ a, (m1049 a).stream = a.pipe.readEnd
theorem p1049 : P1049 := by
  intro a
  simp [m1049]

def P1050 : Prop := ∀ a, (m1050 a).stream = a.pipe.writeEnd
theorem p1050 : P1050 := by
  intro a
  simp [m1050]

def P1061 : Prop := ∀ a, (m1061 a).pipe.readEnd.status = .active ∧
  (m1061 a).pipe.writeEnd.status = .active
theorem p1061 : P1061 := by
  intro a
  simp [m1061]

def P1068 : Prop := ∀ a, (m1068 a).text =
  "Pipe(" ++ toString a.pipe.readEnd.buffer.length ++ ", " ++
    toString a.pipe.writeEnd.buffer.length ++ ")"
theorem p1068 : P1068 := by
  intro a
  simp [m1068]

def P1076 : Prop := ∀ a, (m1076 a).pipe.readEnd.status = .eof ∧
  (m1076 a).pipe.writeEnd.writable = false
theorem p1076 : P1076 := by
  intro a
  simp [m1076]

def P1080 : Prop := ∀ a, (m1080 a).endpoint.hasHandle = a.flag ∧
  (m1080 a).endpoint.status = .opened
theorem p1080 : P1080 := by
  intro a
  simp [m1080]

def P1093 : Prop := ∀ a, (m1093 a).pipe.readEnd.status = .active ∧
  (m1093 a).pipe.writeEnd.status = .active
theorem p1093 : P1093 := by
  intro a
  simp [m1093]

def P1111 : Prop := ∀ a, (m1111 a).pipe.readEnd.status = .active ∧
  (m1111 a).pipe.writeEnd.status = .active
theorem p1111 : P1111 := by
  intro a
  simp [m1111]

def P1128 : Prop := ∀ a, (m1128 a).flags = [a.flag]
theorem p1128 : P1128 := by
  intro a
  simp [m1128]

def P1138 : Prop := ∀ a, (m1138 a).endpoint = startReadingState a.endpoint
theorem p1138 : P1138 := by
  intro a
  simp [m1138]

def P1168 : Prop := ∀ a, (m1168 a).endpoint = stopReadingState a.endpoint
theorem p1168 : P1168 := by
  intro a
  simp [m1168]

def P1178 : Prop := ∀ a, (m1178 a).endpoint = stopReadingState a.endpoint
theorem p1178 : P1178 := by
  intro a
  simp [m1178]

def P1190 : Prop := ∀ a, (m1190 a).counts = [min a.n a.stream.buffer.length] ∧
  (m1190 a).bytes = a.stream.buffer.take (min a.n a.stream.buffer.length) ∧
  (m1190 a).stream.buffer = a.stream.buffer.drop (min a.n a.stream.buffer.length)
theorem p1190 : P1190 := by
  intro a
  simp [m1190]

def P1191 : Prop := ∀ a, (m1191 a).counts = [min a.n a.stream.buffer.length] ∧
  (m1191 a).bytes = a.stream.buffer.take (min a.n a.stream.buffer.length) ∧
  (m1191 a).stream.buffer = a.stream.buffer.drop (min a.n a.stream.buffer.length)
theorem p1191 : P1191 := by
  intro a
  simp [m1191]

def P1198 : Prop := ∀ a, EndpointResultContract (m1198 a) a (waitReadState a.endpoint a.n)
theorem p1198 : P1198 := by
  intro a
  cases h : waitReadState a.endpoint a.n <;>
    simp [m1198, EndpointResultContract, withEndpoint, base, h]

def P1232 : Prop := ∀ a, ReadResultContract (m1232 a) a (readAvailable a.stream)
theorem p1232 : P1232 := by
  intro a
  cases h : readAvailable a.stream <;>
    simp [m1232, ReadResultContract, withRead, base, h]

def P1240 : Prop := ∀ a, ReadResultContract (m1240 a) a (unsafeRead a.stream a.n)
theorem p1240 : P1240 := by
  intro a
  cases h : unsafeRead a.stream a.n <;>
    simp [m1240, ReadResultContract, withRead, base, h]

def P1247 : Prop := ∀ a, EndpointResultContract (m1247 a) a (waitReadState a.endpoint a.n)
theorem p1247 : P1247 := by
  intro a
  cases h : waitReadState a.endpoint a.n <;>
    simp [m1247, EndpointResultContract, withEndpoint, base, h]

def P1277 : Prop := ∀ a, ReadResultContract (m1277 a) a (unsafeRead a.stream 1)
theorem p1277 : P1277 := by
  intro a
  cases h : unsafeRead a.stream 1 <;>
    simp [m1277, ReadResultContract, withRead, base, h]

def P1292 : Prop := ∀ a, ReadResultContract (m1292 a) a (readAvailable a.stream)
theorem p1292 : P1292 := by
  intro a
  cases h : readAvailable a.stream <;>
    simp [m1292, ReadResultContract, withRead, base, h]

def P1302 : Prop := ∀ a, ReadResultContract (m1302 a) a (readUntil a.stream a.byte a.flag)
theorem p1302 : P1302 := by
  intro a
  cases h : readUntil a.stream a.byte a.flag <;>
    simp [m1302, ReadResultContract, withRead, base, h]

def P1347 : Prop := ∀ a, (m1347 a).counts = writeChunks a.bytes.length (max 1 a.n)
theorem p1347 : P1347 := by
  intro a
  simp [m1347]

def P1360 : Prop := ∀ a, (m1360 a).counts = writeChunks a.n (max 1 a.m) ∧
  (m1360 a).req = completeReq a.req a.i a.j.toNat
theorem p1360 : P1360 := by
  intro a
  simp [m1360]

def P1478 : Prop := ∀ a, (m1478 a).req = finishReq a.req a.flag a.flag2 a.flag3
theorem p1478 : P1478 := by
  intro a
  simp [m1478]

def P1558 : Prop := ∀ a, (m1558 a).req = completeReq a.req a.i a.n
theorem p1558 : P1558 := by
  intro a
  simp [m1558]

def P1576 : Prop := ∀ a, (m1576 a).req = finishReq a.req a.flag a.flag2 a.flag3
theorem p1576 : P1576 := by
  intro a
  simp [m1576]

def P1604 : Prop := ∀ a, (m1604 a).counts = writeChunks a.n (max 1 a.m)
theorem p1604 : P1604 := by
  intro a
  simp [m1604]

def P1611 : Prop := ∀ a, (m1611 a).counts = writeChunks a.n (max 1 a.m)
theorem p1611 : P1611 := by
  intro a
  simp [m1611]

def P1634 : Prop := ∀ a, (m1634 a).counts = writeChunks a.n (max 1 a.m)
theorem p1634 : P1634 := by
  intro a
  simp [m1634]

def P1669 : Prop := ∀ a, WriteResultContract (m1669 a) a
  (unsafeWrite a.stream a.bytes a.bytes.length)
theorem p1669 : P1669 := by
  intro a
  cases h : unsafeWrite a.stream a.bytes a.bytes.length <;>
    simp [m1669, WriteResultContract, withStream, base, h]

def P1679 : Prop := ∀ a, WriteResultContract (m1679 a) a
  (unsafeWrite a.stream a.bytes (min a.n a.bytes.length))
theorem p1679 : P1679 := by
  intro a
  cases h : unsafeWrite a.stream a.bytes (min a.n a.bytes.length) <;>
    simp [m1679, WriteResultContract, withStream, base, h]

def P1691 : Prop := ∀ a, WriteResultContract (m1691 a) a
  (unsafeWrite a.stream a.bytes a.bytes.length)
theorem p1691 : P1691 := by
  intro a
  cases h : unsafeWrite a.stream a.bytes a.bytes.length <;>
    simp [m1691, WriteResultContract, withStream, base, h]

def P1699 : Prop := ∀ a, WriteResultContract (m1699 a) a
  (unsafeWrite a.stream a.bytes (min a.n a.bytes.length))
theorem p1699 : P1699 := by
  intro a
  cases h : unsafeWrite a.stream a.bytes (min a.n a.bytes.length) <;>
    simp [m1699, WriteResultContract, withStream, base, h]

def P1710 : Prop := ∀ a, WriteResultContract (m1710 a) a
  (unsafeWrite a.stream a.bytes a.bytes.length)
theorem p1710 : P1710 := by
  intro a
  cases h : unsafeWrite a.stream a.bytes a.bytes.length <;>
    simp [m1710, WriteResultContract, withStream, base, h]

def P1720 : Prop := ∀ a, WriteResultContract (m1720 a) a
  (unsafeWrite a.stream a.bytes (min a.n a.bytes.length))
theorem p1720 : P1720 := by
  intro a
  cases h : unsafeWrite a.stream a.bytes (min a.n a.bytes.length) <;>
    simp [m1720, WriteResultContract, withStream, base, h]

def P1736 : Prop := ∀ a, WriteResultContract (m1736 a) a
  (unsafeWrite a.stream a.bytes a.n)
theorem p1736 : P1736 := by
  intro a
  cases h : unsafeWrite a.stream a.bytes a.n <;>
    simp [m1736, WriteResultContract, withStream, base, h]

def P1741 : Prop := ∀ a, WriteResultContract (m1741 a) a
  (unsafeWrite a.stream a.bytes a.n)
theorem p1741 : P1741 := by
  intro a
  cases h : unsafeWrite a.stream a.bytes a.n <;>
    simp [m1741, WriteResultContract, withStream, base, h]

def P1778 : Prop := ∀ a, (m1778 a).bytes = a.bytes.drop a.n ++ a.queued
theorem p1778 : P1778 := by
  intro a
  simp [m1778, requeueUnwritten]

def P1795 : Prop := ∀ a, (m1795 a).bytes = a.endpoint.sendBuffer.getD [] ∧
  (m1795 a).endpoint.sendBuffer = none
theorem p1795 : P1795 := by
  intro a
  simp [m1795]

def P1826 : Prop := ∀ a, (m1826 a).endpoint.sendBuffer = some [] ∧
  (m1826 a).counts = [a.n]
theorem p1826 : P1826 := by
  intro a
  simp [m1826]

def P1836 : Prop := ∀ a, WriteResultContract (m1836 a) a (unsafeWrite a.stream [a.byte] 1)
theorem p1836 : P1836 := by
  intro a
  cases h : unsafeWrite a.stream [a.byte] 1 <;>
    simp [m1836, WriteResultContract, withStream, base, h]

def P1856 : Prop := ∀ a, (m1856 a).req = completeReq a.req a.i a.n
theorem p1856 : P1856 := by
  intro a
  simp [m1856]

def P1909 : Prop := ∀ a, (m1909 a).req = completeReq a.req a.i 0
theorem p1909 : P1909 := by
  intro a
  simp [m1909]

def P1916 : Prop := ∀ a, (m1916 a).integer = a.i
theorem p1916 : P1916 := by
  intro a
  simp [m1916]

def P1917 : Prop := ∀ a, (m1917 a).integer = a.i
theorem p1917 : P1917 := by
  intro a
  simp [m1917]

def P1919 : Prop := ∀ a, (m1919 a).integer = a.i ∧ (m1919 a).flags = [a.endpoint.hasHandle]
theorem p1919 : P1919 := by
  intro a
  simp [m1919]

def P1938 : Prop := ∀ a, (m1938 a).integer = a.i ∧ (m1938 a).flags = [a.flag]
theorem p1938 : P1938 := by
  intro a
  simp [m1938]

def P1949 : Prop := ∀ a, (m1949 a).integer = a.i ∧ (m1949 a).flags = [a.flag]
theorem p1949 : P1949 := by
  intro a
  simp [m1949]

def P1957 : Prop := ∀ a, (m1957 a).integer = a.i ∧ (m1957 a).flags = [a.flag]
theorem p1957 : P1957 := by
  intro a
  simp [m1957]

def P1963 : Prop := ∀ a, (m1963 a).redirect.outStream = .stream
theorem p1963 : P1963 := by
  intro a
  simp [m1963]

def P1969 : Prop := ∀ a, (m1969 a).redirect.outStream = .devnull
theorem p1969 : P1969 := by
  intro a
  simp [m1969]

def P1978 : Prop := ∀ a, (m1978 a).redirect.outStream = .stream
theorem p1978 : P1978 := by
  intro a
  simp [m1978]

def P1984 : Prop := ∀ a, (m1984 a).redirect.outStream = .stream
theorem p1984 : P1984 := by
  intro a
  simp [m1984]

def P1992 : Prop := ∀ a, (m1992 a).redirect.outStream = .stream
theorem p1992 : P1992 := by
  intro a
  simp [m1992]

def P1995 : Prop := ∀ a, (m1995 a).counts = [1]
theorem p1995 : P1995 := by
  intro a
  simp [m1995]

def P1996 : Prop := ∀ a, (m1996 a).counts = [a.n]
theorem p1996 : P1996 := by
  intro a
  simp [m1996]

def P1997 : Prop := ∀ a, ((m1997 a).stream, (m1997 a).error) =
  match pipeGetindex (a.pipe.readEnd, a.pipe.writeEnd) a.i with
  | some stream => (stream, none)
  | none => (a.stream, some .argumentError)
theorem p1997 : P1997 := by
  intro a
  cases h : pipeGetindex (a.pipe.readEnd, a.pipe.writeEnd) a.i <;>
    simp [m1997, base, h]

def P2052 : Prop := ∀ a, (m2052 a).redirect = a.redirect
theorem p2052 : P2052 := by
  intro a
  simp [m2052, redirectStdio, resolveRedirect, base]

def P2110 : Prop := ∀ a, (m2110 a).redirect =
  redirectStdio a.redirect (if a.flag then .stream else .keep)
    (if a.flag2 then .stream else .keep) (if a.flag3 then .stream else .keep)
theorem p2110 : P2110 := by
  intro a
  simp [m2110]

def P2112 : Prop := ∀ a, (m2112 a).redirect = a.redirect
theorem p2112 : P2112 := by
  intro a
  simp [m2112]

def P2115 : Prop := ∀ a, (m2115 a).text = a.text
theorem p2115 : P2115 := by
  intro a
  simp [m2115]

def P2118 : Prop := ∀ a, (m2118 a).redirect.outStream = .stream
theorem p2118 : P2118 := by
  intro a
  simp [m2118]

def P2122 : Prop := ∀ a, (m2122 a).flags = [false]
theorem p2122 : P2122 := by
  intro a
  simp [m2122]

def P2123 : Prop := ∀ a, (m2123 a).flags = [samePath a.text a.text2]
theorem p2123 : P2123 := by
  intro a
  simp [m2123]

def P2156 : Prop := ∀ a, (m2156 a).redirect = redirectStdio a.redirect .keep .stream .keep
theorem p2156 : P2156 := by
  intro a
  simp [m2156]

def P2194 : Prop := ∀ a, (m2194 a).counts = [a.n]
theorem p2194 : P2194 := by
  intro a
  simp [m2194]

def P2195 : Prop := ∀ a, (m2195 a).counts = [a.n]
theorem p2195 : P2195 := by
  intro a
  simp [m2195]

def P2196 : Prop := ∀ a, (m2196 a).counts = [a.n]
theorem p2196 : P2196 := by
  intro a
  simp [m2196]

def P2197 : Prop := ∀ a, (m2197 a).flags = [a.flag]
theorem p2197 : P2197 := by
  intro a
  simp [m2197]

def P2199 : Prop := ∀ a, ((m2199 a).bytes, (m2199 a).error) =
  match peekModel a.endpoint.buffer a.n with
  | .ok bytes => (bytes, none)
  | .error e => (a.bytes, some e)
theorem p2199 : P2199 := by
  intro a
  cases h : peekModel a.endpoint.buffer a.n <;>
    simp [m2199, base, h]

def P2216 : Prop := ∀ a, (m2216 a).stream = freshStream .bufferStream
theorem p2216 : P2216 := by
  intro a
  simp [m2216]

def P2219 : Prop := ∀ a, (m2219 a).flags = [isOpen a.stream]
theorem p2219 : P2219 := by
  intro a
  simp [m2219]

def P2225 : Prop := ∀ a, (m2225 a).stream.writable = false
theorem p2225 : P2225 := by
  intro a
  simp [m2225]

def P2231 : Prop := ∀ a, (m2231 a).stream = bufferClose a.stream
theorem p2231 : P2231 := by
  intro a
  simp [m2231]

def P2238 : Prop := ∀ a, (m2238 a).stream = bufferClose a.stream
theorem p2238 : P2238 := by
  intro a
  simp [m2238]

def P2239 : Prop := ∀ a, (m2239 a).flags = [a.flag]
theorem p2239 : P2239 := by
  intro a
  simp [m2239]

def P2241 : Prop := ∀ a, ((m2241 a).bytes, (m2241 a).stream, (m2241 a).error) =
  match bufferReadByte a.stream with
  | .ok (byte, stream) => ([byte], stream, none)
  | .error e => (a.bytes, a.stream, some e)
theorem p2241 : P2241 := by
  intro a
  cases h : bufferReadByte a.stream <;>
    simp [m2241, base, h]

def P2249 : Prop := ∀ a, ReadResultContract (m2249 a) a (unsafeRead a.stream a.n)
theorem p2249 : P2249 := by
  intro a
  cases h : unsafeRead a.stream a.n <;>
    simp [m2249, ReadResultContract, withRead, base, h]

def P2257 : Prop := ∀ a, (m2257 a).counts = [a.stream.buffer.length]
theorem p2257 : P2257 := by
  intro a
  simp [m2257]

def P2259 : Prop := ∀ a, (m2259 a).flags = [bufferReadable a.stream]
theorem p2259 : P2259 := by
  intro a
  simp [m2259]

def P2260 : Prop := ∀ a, (m2260 a).flags = [bufferWritable a.stream]
theorem p2260 : P2260 := by
  intro a
  simp [m2260]

def P2262 : Prop := ∀ a, (m2262 a).flags =
  [a.n ≤ a.stream.buffer.length || !isOpen a.stream]
theorem p2262 : P2262 := by
  intro a
  simp [m2262]

def P2277 : Prop := ∀ a, ReadResultContract (m2277 a) a (readAvailable a.stream)
theorem p2277 : P2277 := by
  intro a
  cases h : readAvailable a.stream <;>
    simp [m2277, ReadResultContract, withRead, base, h]

def P2288 : Prop := ∀ a, ReadResultContract (m2288 a) a (readAvailable a.stream)
theorem p2288 : P2288 := by
  intro a
  cases h : readAvailable a.stream <;>
    simp [m2288, ReadResultContract, withRead, base, h]

def P2297 : Prop := ∀ a, (m2297 a).bytes = a.stream.buffer.take a.n ∧
  (m2297 a).stream.buffer = a.stream.buffer.drop a.n ∧
  (m2297 a).counts = [(a.stream.buffer.take a.n).length]
theorem p2297 : P2297 := by
  intro a
  simp [m2297]

def P2303 : Prop := ∀ a, (m2303 a).flags =
  [a.n ≤ a.stream.buffer.length || !isOpen a.stream]
theorem p2303 : P2303 := by
  intro a
  simp [m2303]

def P2337 : Prop := ∀ a, (m2337 a).text =
  "BufferStream(" ++ toString a.stream.buffer.length ++ " bytes waiting)"
theorem p2337 : P2337 := by
  intro a
  simp [m2337]

def P2339 : Prop := ∀ a, ReadResultContract (m2339 a) a (readUntil a.stream a.byte a.flag)
theorem p2339 : P2339 := by
  intro a
  cases h : readUntil a.stream a.byte a.flag <;>
    simp [m2339, ReadResultContract, withRead, base, h]

def P2358 : Prop := ∀ a, (m2358 a).flags = [!isOpen a.stream]
theorem p2358 : P2358 := by
  intro a
  simp [m2358]

def P2373 : Prop := ∀ a, (m2373 a).stream = a.stream ∧ (m2373 a).error = none
theorem p2373 : P2373 := by
  intro a
  simp [m2373, base]

def P2374 : Prop := ∀ a, (m2374 a).stream = a.stream ∧ (m2374 a).error = none
theorem p2374 : P2374 := by
  intro a
  simp [m2374, base]

def P2376 : Prop := ∀ a, WriteResultContract (m2376 a) a (unsafeWrite a.stream [a.byte] 1)
theorem p2376 : P2376 := by
  intro a
  cases h : unsafeWrite a.stream [a.byte] 1 <;>
    simp [m2376, WriteResultContract, withStream, base, h]

def P2382 : Prop := ∀ a, WriteResultContract (m2382 a) a
  (unsafeWrite a.stream a.bytes a.bytes.length)
theorem p2382 : P2382 := by
  intro a
  cases h : unsafeWrite a.stream a.bytes a.bytes.length <;>
    simp [m2382, WriteResultContract, withStream, base, h]

def P2388 : Prop := ∀ a, WriteResultContract (m2388 a) a
  (unsafeWrite a.stream a.bytes a.bytes.length)
theorem p2388 : P2388 := by
  intro a
  cases h : unsafeWrite a.stream a.bytes a.bytes.length <;>
    simp [m2388, WriteResultContract, withStream, base, h]

def P2395 : Prop := ∀ a, WriteResultContract (m2395 a) a
  (unsafeWrite a.stream a.bytes a.bytes.length)
theorem p2395 : P2395 := by
  intro a
  cases h : unsafeWrite a.stream a.bytes a.bytes.length <;>
    simp [m2395, WriteResultContract, withStream, base, h]

def P2404 : Prop := ∀ a, WriteResultContract (m2404 a) a
  (unsafeWrite a.stream a.bytes a.n)
theorem p2404 : P2404 := by
  intro a
  cases h : unsafeWrite a.stream a.bytes a.n <;>
    simp [m2404, WriteResultContract, withStream, base, h]

def P2416 : Prop := ∀ a, (m2416 a).flags = [bufferEof a.stream]
theorem p2416 : P2416 := by
  intro a
  simp [m2416]

def P2427 : Prop := ∀ a, (m2427 a).counts = [a.n]
theorem p2427 : P2427 := by
  intro a
  simp [m2427]

def P2428 : Prop := ∀ a, (m2428 a).stream = a.stream
theorem p2428 : P2428 := by
  intro a
  simp [m2428]

def P2438 : Prop := ∀ a, (m2438 a).stream.buffer = a.stream.buffer.drop a.n
theorem p2438 : P2438 := by
  intro a
  simp [m2438]

def P2440 : Prop := ∀ a, (m2440 a).stream = bufferResetEof a.stream
theorem p2440 : P2440 := by
  intro a
  simp [m2440]

def entries : List Entry := [
  methodEntry "base/stream.jl" "stream" 29 39 "getproperty(server::LibuvServer, name::Symbol)" "`getproperty(server::LibuvServer, name::Symbol)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P29 ``p29,
  methodEntry "base/stream.jl" "stream" 58 76 "getproperty(stream::LibuvStream, name::Symbol)" "`getproperty(stream::LibuvStream, name::Symbol)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P58 ``p58,
  methodEntry "base/stream.jl" "stream" 102 102 "bytesavailable(s::LibuvStream)" "bytesavailable leaves the endpoint unchanged and returns zero exactly when its receive buffer is empty." ``P102 ``p102,
  methodEntry "base/stream.jl" "stream" 104 116 "eof(s::LibuvStream; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`eof(s::LibuvStream; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P104 ``p104,
  methodEntry "base/stream.jl" "stream" 139 168 "uv_status_string(x)" "`uv_status_string(x)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P139 ``p139,
  methodEntry "base/stream.jl" "stream" 179 191 "PipeEndpoint(handle::Ptr{Cvoid}, status)" "`PipeEndpoint(handle::Ptr{Cvoid}, status)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P179 ``p179,
  methodEntry "base/stream.jl" "stream" 194 202 "PipeEndpoint()" "`PipeEndpoint()` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P194 ``p194,
  methodEntry "base/stream.jl" "stream" 204 207 "PipeEndpoint(fd::OS_HANDLE)" "`PipeEndpoint(fd::OS_HANDLE)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P204 ``p204,
  methodEntry "base/stream.jl" "stream" 224 241 "TTY(handle::Ptr{Cvoid}, status)" "`TTY(handle::Ptr{Cvoid}, status)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P224 ``p224,
  methodEntry "base/stream.jl" "stream" 244 253 "TTY(fd::OS_HANDLE)" "`TTY(fd::OS_HANDLE)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P244 ``p244,
  methodEntry "base/stream.jl" "stream" 258 260 "show(io::IO, stream::LibuvServer)" "`show(io::IO, stream::LibuvServer)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P258 ``p258,
  methodEntry "base/stream.jl" "stream" 261 264 "show(io::IO, stream::LibuvStream)" "`show(io::IO, stream::LibuvStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P261 ``p261,
  methodEntry "base/stream.jl" "stream" 268 273 "isreadable(io::LibuvStream)" "`isreadable(io::LibuvStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P268 ``p268,
  methodEntry "base/stream.jl" "stream" 275 279 "iswritable(io::LibuvStream)" "`iswritable(io::LibuvStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P275 ``p275,
  methodEntry "base/stream.jl" "stream" 281 281 "lock(s::LibuvStream)" "`lock(s::LibuvStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P281 ``p281,
  methodEntry "base/stream.jl" "stream" 282 282 "unlock(s::LibuvStream)" "`unlock(s::LibuvStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P282 ``p282,
  methodEntry "base/stream.jl" "stream" 284 284 "setup_stdio(stream::Union{LibuvStream, LibuvServer}, ::Bool)" "`setup_stdio(stream::Union{LibuvStream, LibuvServer}, ::Bool)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P284 ``p284,
  methodEntry "base/stream.jl" "stream" 285 285 "rawhandle(stream::Union{LibuvStream, LibuvServer})" "`rawhandle(stream::Union{LibuvStream, LibuvServer})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P285 ``p285,
  methodEntry "base/stream.jl" "stream" 286 286 "unsafe_convert(::Type{Ptr{Cvoid}}, s::Union{LibuvStream, LibuvServer})" "`unsafe_convert(::Type{Ptr{Cvoid}}, s::Union{LibuvStream, LibuvServer})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P286 ``p286,
  methodEntry "base/stream.jl" "stream" 288 314 "init_stdio(handle::Ptr{Cvoid})" "`init_stdio(handle::Ptr{Cvoid})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P288 ``p288,
  methodEntry "base/stream.jl" "stream" 328 361 "open(h::OS_HANDLE)" "`open(h::OS_HANDLE)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P328 ``p328,
  methodEntry "base/stream.jl" "stream" 364 374 "open(fd::RawFD)" "`open(fd::RawFD)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P364 ``p364,
  methodEntry "base/stream.jl" "stream" 377 382 "isopen(x::Union{LibuvStream, LibuvServer})" "`isopen(x::Union{LibuvStream, LibuvServer})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P377 ``p377,
  methodEntry "base/stream.jl" "stream" 384 388 "check_open(x::Union{LibuvStream, LibuvServer})" "`check_open(x::Union{LibuvStream, LibuvServer})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P384 ``p384,
  methodEntry "base/stream.jl" "stream" 390 442 "wait_readnb(x::LibuvStream, nb::Int, tok::MaybeToken=default_cancel_token())" "`wait_readnb(x::LibuvStream, nb::Int, tok::MaybeToken=default_cancel_token())` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P390 ``p390,
  methodEntry "base/stream.jl" "stream" 493 500 "_uvreq_witness_slot(w::WaitEntry)" "`_uvreq_witness_slot(w::WaitEntry)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P493 ``p493,
  methodEntry "base/stream.jl" "stream" 502 506 "_mark_uvreq_cancel_requested!(w::WaitEntry, @nospecialize(witness))" "`_mark_uvreq_cancel_requested!(w::WaitEntry, @nospecialize(witness))` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P502 ``p502,
  methodEntry "base/stream.jl" "stream" 511 517 "_uvreq_cancel_requested(req::Ptr{Cvoid})" "`_uvreq_cancel_requested(req::Ptr{Cvoid})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P511 ``p511,
  methodEntry "base/stream.jl" "stream" 530 533 "_root_detached_uvreq!(req::Ptr{Cvoid}, @nospecialize(owner))" "`_root_detached_uvreq!(req::Ptr{Cvoid}, @nospecialize(owner))` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P530 ``p530,
  methodEntry "base/stream.jl" "stream" 534 535 "_unroot_detached_uvreq!(req::Ptr{Cvoid})" "`_unroot_detached_uvreq!(req::Ptr{Cvoid})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P534 ``p534,
  methodEntry "base/stream.jl" "stream" 540 546 "_iolocked_checkcancel(src::Union{Nothing, CancellationTokenSource})" "`_iolocked_checkcancel(src::Union{Nothing, CancellationTokenSource})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P540 ``p540,
  methodEntry "base/stream.jl" "stream" 553 563 "_begin_uvreq_wait!(src::Union{Nothing, CancellationTokenSource}, @nospecialize(witness), req::Ptr{Cvoid})" "`_begin_uvreq_wait!(src::Union{Nothing, CancellationTokenSource}, @nospecialize(witness), req::Ptr{Cvoid})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P553 ``p553,
  methodEntry "base/stream.jl" "stream" 575 597 "_end_uvreq_wait!(w::WaitEntry, @nospecialize(witness), req::Ptr{Cvoid}, trycancel::Bool, @nospecialize(owner))" "`_end_uvreq_wait!(w::WaitEntry, @nospecialize(witness), req::Ptr{Cvoid}, trycancel::Bool, @nospecialize(owner))` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P575 ``p575,
  methodEntry "base/stream.jl" "stream" 615 619 "wait_enqueue!(x::UvReqWait, w::WaitEntry, first::Bool)" "`wait_enqueue!(x::UvReqWait, w::WaitEntry, first::Bool)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P615 ``p615,
  methodEntry "base/stream.jl" "stream" 626 640 "wait_dequeue!(x::UvReqWait, w::WaitEntry, why::UInt8)" "`wait_dequeue!(x::UvReqWait, w::WaitEntry, why::UInt8)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P626 ``p626,
  methodEntry "base/stream.jl" "stream" 650 691 "_wait_uvreq(src::Union{Nothing, CancellationTokenSource}, @nospecialize(witness), req::Ptr{Cvoid}, trycancel::Bool, @nospecialize(owner))" "`_wait_uvreq(src::Union{Nothing, CancellationTokenSource}, @nospecialize(witness), req::Ptr{Cvoid}, trycancel::Bool, @nospecialize(owner))` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P650 ``p650,
  methodEntry "base/stream.jl" "stream" 700 717 "_claim_uvreq_waiter(req::Ptr{Cvoid})" "`_claim_uvreq_waiter(req::Ptr{Cvoid})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P700 ``p700,
  methodEntry "base/stream.jl" "stream" 719 748 "closewrite(s::LibuvStream; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`closewrite(s::LibuvStream; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P719 ``p719,
  methodEntry "base/stream.jl" "stream" 750 768 "wait_close(x::Union{LibuvStream, LibuvServer})" "`wait_close(x::Union{LibuvStream, LibuvServer})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P750 ``p750,
  methodEntry "base/stream.jl" "stream" 770 784 "close(stream::Union{LibuvStream, LibuvServer})" "`close(stream::Union{LibuvStream, LibuvServer})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P770 ``p770,
  methodEntry "base/stream.jl" "stream" 786 806 "uvfinalize(uv::Union{LibuvStream, LibuvServer})" "`uvfinalize(uv::Union{LibuvStream, LibuvServer})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P786 ``p786,
  methodEntry "base/stream.jl" "stream" 809 809 "ispty(s::TTY)" "`ispty(s::TTY)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P809 ``p809,
  methodEntry "base/stream.jl" "stream" 810 810 "ispty(s::IO)" "`ispty(s::IO)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P810 ``p810,
  methodEntry "base/stream.jl" "stream" 836 836 "displaysize(io::IO)" "`displaysize(io::IO)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P836 ``p836,
  methodEntry "base/stream.jl" "stream" 837 838 "displaysize()" "`displaysize()` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P837 ``p837,
  methodEntry "base/stream.jl" "stream" 845 845 "displaysize_(io::IO)" "`displaysize_(io::IO)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P845 ``p845,
  methodEntry "base/stream.jl" "stream" 847 879 "displaysize(io::TTY)" "`displaysize(io::TTY)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P847 ``p847,
  methodEntry "base/stream.jl" "stream" 885 891 "alloc_request(buffer::IOBuffer, recommended_size::UInt)" "`alloc_request(buffer::IOBuffer, recommended_size::UInt)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P885 ``p885,
  methodEntry "base/stream.jl" "stream" 893 893 "notify_filled(buffer::IOBuffer, nread::Int, base::Ptr{Cvoid}, len::UInt)" "`notify_filled(buffer::IOBuffer, nread::Int, base::Ptr{Cvoid}, len::UInt)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P893 ``p893,
  methodEntry "base/stream.jl" "stream" 895 903 "notify_filled(buffer::IOBuffer, nread::Int)" "`notify_filled(buffer::IOBuffer, nread::Int)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P895 ``p895,
  methodEntry "base/stream.jl" "stream" 905 908 "alloc_buf_hook(stream::LibuvStream, size::UInt)" "`alloc_buf_hook(stream::LibuvStream, size::UInt)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P905 ``p905,
  methodEntry "base/stream.jl" "stream" 910 936 "uv_alloc_buf(handle::Ptr{Cvoid}, size::Csize_t, buf::Ptr{Cvoid})" "`uv_alloc_buf(handle::Ptr{Cvoid}, size::Csize_t, buf::Ptr{Cvoid})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P910 ``p910,
  methodEntry "base/stream.jl" "stream" 938 990 "uv_readcb(handle::Ptr{Cvoid}, nread::Cssize_t, buf::Ptr{Cvoid})" "`uv_readcb(handle::Ptr{Cvoid}, nread::Cssize_t, buf::Ptr{Cvoid})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P938 ``p938,
  methodEntry "base/stream.jl" "stream" 941 987 "readcb_specialized(stream::LibuvStream, nread::Int, nrequested::UInt)" "`readcb_specialized(stream::LibuvStream, nread::Int, nrequested::UInt)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P941 ``p941,
  methodEntry "base/stream.jl" "stream" 992 999 "reseteof(x::TTY)" "`reseteof(x::TTY)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P992 ``p992,
  methodEntry "base/stream.jl" "stream" 1001 1011 "_uv_hook_close(uv::Union{LibuvStream, LibuvServer})" "`_uv_hook_close(uv::Union{LibuvStream, LibuvServer})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1001 ``p1001,
  methodEntry "base/stream.jl" "stream" 1048 1048 "Pipe()" "`Pipe()` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1048 ``p1048,
  methodEntry "base/stream.jl" "stream" 1049 1049 "pipe_reader(p::Pipe)" "`pipe_reader(p::Pipe)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1049 ``p1049,
  methodEntry "base/stream.jl" "stream" 1050 1050 "pipe_writer(p::Pipe)" "`pipe_writer(p::Pipe)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1050 ``p1050,
  methodEntry "base/stream.jl" "stream" 1061 1066 "link_pipe!(pipe::Pipe; reader_supports_async = false, writer_supports_async = false)" "`link_pipe!(pipe::Pipe; reader_supports_async = false, writer_supports_async = false)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1061 ``p1061,
  methodEntry "base/stream.jl" "stream" 1068 1074 "show(io::IO, stream::Pipe)" "`show(io::IO, stream::Pipe)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1068 ``p1068,
  methodEntry "base/stream.jl" "stream" 1076 1076 "closewrite(pipe::Pipe)" "`closewrite(pipe::Pipe)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1076 ``p1076,
  methodEntry "base/stream.jl" "stream" 1080 1090 "open_pipe!(p::PipeEndpoint, handle::OS_HANDLE)" "`open_pipe!(p::PipeEndpoint, handle::OS_HANDLE)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1080 ``p1080,
  methodEntry "base/stream.jl" "stream" 1093 1109 "link_pipe!(read_end::PipeEndpoint, reader_supports_async::Bool, write_end::PipeEndpoint, writer_supports_async::Bool)" "`link_pipe!(read_end::PipeEndpoint, reader_supports_async::Bool, write_end::PipeEndpoint, writer_supports_async::Bool)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1093 ``p1093,
  methodEntry "base/stream.jl" "stream" 1111 1120 "link_pipe(reader_supports_async::Bool, writer_supports_async::Bool)" "`link_pipe(reader_supports_async::Bool, writer_supports_async::Bool)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1111 ``p1111,
  methodEntry "base/stream.jl" "stream" 1128 1131 "close_pipe_sync(handle::RawFD)" "`close_pipe_sync(handle::RawFD)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1128 ``p1128,
  methodEntry "base/stream.jl" "stream" 1138 1160 "start_reading(stream::LibuvStream)" "`start_reading(stream::LibuvStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1138 ``p1138,
  methodEntry "base/stream.jl" "stream" 1168 1176 "stop_reading(stream::LibuvStream)" "`stop_reading(stream::LibuvStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1168 ``p1168,
  methodEntry "base/stream.jl" "stream" 1178 1185 "stop_reading(stream::LibuvStream)" "`stop_reading(stream::LibuvStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1178 ``p1178,
  methodEntry "base/stream.jl" "stream" 1190 1190 "readbytes!(s::LibuvStream, a::Vector{UInt8}, nb = length(a))" "`readbytes!(s::LibuvStream, a::Vector{UInt8}, nb = length(a))` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1190 ``p1190,
  methodEntry "base/stream.jl" "stream" 1191 1230 "readbytes!(s::LibuvStream, a::Vector{UInt8}, nb::Int; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`readbytes!(s::LibuvStream, a::Vector{UInt8}, nb::Int; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1191 ``p1191,
  methodEntry "base/stream.jl" "stream" 1198 1207 "wait_locked(s, buf, nb, tok)" "`wait_locked(s, buf, nb, tok)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1198 ``p1198,
  methodEntry "base/stream.jl" "stream" 1232 1238 "read(stream::LibuvStream; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`read(stream::LibuvStream; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1232 ``p1232,
  methodEntry "base/stream.jl" "stream" 1240 1275 "unsafe_read(s::LibuvStream, p::Ptr{UInt8}, nb::UInt; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`unsafe_read(s::LibuvStream, p::Ptr{UInt8}, nb::UInt; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1240 ``p1240,
  methodEntry "base/stream.jl" "stream" 1247 1256 "wait_locked(s, buf, nb, tok)" "`wait_locked(s, buf, nb, tok)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1247 ``p1247,
  methodEntry "base/stream.jl" "stream" 1277 1290 "read(this::LibuvStream, ::Type{UInt8}; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`read(this::LibuvStream, ::Type{UInt8}; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1277 ``p1277,
  methodEntry "base/stream.jl" "stream" 1292 1300 "readavailable(this::LibuvStream; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`readavailable(this::LibuvStream; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1292 ``p1292,
  methodEntry "base/stream.jl" "stream" 1302 1345 "copyuntil(out::IO, x::LibuvStream, c::UInt8; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)" "`copyuntil(out::IO, x::LibuvStream, c::UInt8; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1302 ``p1302,
  methodEntry "base/stream.jl" "stream" 1347 1349 "uv_write(s::LibuvStream, p::Vector{UInt8}, cancel::CancelTokenArg=DEFAULT_CANCEL, partial::Bool=false)" "`uv_write(s::LibuvStream, p::Vector{UInt8}, cancel::CancelTokenArg=DEFAULT_CANCEL, partial::Bool=false)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1347 ``p1347,
  methodEntry "base/stream.jl" "stream" 1360 1464 "_uv_write_wait(s::LibuvStream, p::Ptr{UInt8}, n::UInt, tok::MaybeToken, @nospecialize(owner), partial::Bool, chunk::UInt=MAX_OS_WRITE)" "`_uv_write_wait(s::LibuvStream, p::Ptr{UInt8}, n::UInt, tok::MaybeToken, @nospecialize(owner), partial::Bool, chunk::UInt=MAX_OS_WRITE)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1360 ``p1360,
  methodEntry "base/stream.jl" "stream" 1478 1555 "_uv_write_cancelled_finish(s::LibuvStream, w::WaitEntry, uvw::Ptr{Cvoid}, sev::UInt8, src::CancellationTokenSource, @nospecialize(owner), others::Union{Nothing, Vector{Ptr{Cvoid}}})" "`_uv_write_cancelled_finish(s::LibuvStream, w::WaitEntry, uvw::Ptr{Cvoid}, sev::UInt8, src::CancellationTokenSource, @nospecialize(owner), others::Union{Nothing, Vector{Ptr{Cvoid}}})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1478 ``p1478,
  methodEntry "base/stream.jl" "stream" 1558 1564 "_split_complete(uvw::Ptr{Cvoid}, others::Vector{Ptr{Cvoid}})" "`_split_complete(uvw::Ptr{Cvoid}, others::Vector{Ptr{Cvoid}})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1558 ``p1558,
  methodEntry "base/stream.jl" "stream" 1576 1602 "_end_split_uvreq_wait!(w::WaitEntry, @nospecialize(witness), uvw::Ptr{Cvoid}, others::Vector{Ptr{Cvoid}}, trycancel::Bool, @nospecialize(owner))" "`_end_split_uvreq_wait!(w::WaitEntry, @nospecialize(witness), uvw::Ptr{Cvoid}, others::Vector{Ptr{Cvoid}}, trycancel::Bool, @nospecialize(owner))` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1576 ``p1576,
  methodEntry "base/stream.jl" "stream" 1604 1607 "uv_write(s::LibuvStream, p::Ptr{UInt8}, n::UInt; cancel::CancelTokenArg=DEFAULT_CANCEL, owner=nothing)" "`uv_write(s::LibuvStream, p::Ptr{UInt8}, n::UInt; cancel::CancelTokenArg=DEFAULT_CANCEL, owner=nothing)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1604 ``p1604,
  methodEntry "base/stream.jl" "stream" 1611 1625 "_uv_write_owned(s::LibuvStream, p::Ptr{UInt8}, n::UInt, cancel::CancelTokenArg, @nospecialize(owner), partial::Bool)" "`_uv_write_owned(s::LibuvStream, p::Ptr{UInt8}, n::UInt, cancel::CancelTokenArg, @nospecialize(owner), partial::Bool)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1611 ``p1611,
  methodEntry "base/stream.jl" "stream" 1634 1662 "uv_write_async(s::LibuvStream, p::Ptr{UInt8}, n::UInt, chunk::UInt=MAX_OS_WRITE)" "`uv_write_async(s::LibuvStream, p::Ptr{UInt8}, n::UInt, chunk::UInt=MAX_OS_WRITE)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1634 ``p1634,
  methodEntry "base/stream.jl" "stream" 1669 1677 "write(s::LibuvStream, a::Vector{UInt8}; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`write(s::LibuvStream, a::Vector{UInt8}; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1669 ``p1669,
  methodEntry "base/stream.jl" "stream" 1679 1684 "writepartial(s::LibuvStream, a::Vector{UInt8}; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`writepartial(s::LibuvStream, a::Vector{UInt8}; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1679 ``p1679,
  methodEntry "base/stream.jl" "stream" 1691 1697 "write(s::LibuvStream, str::Union{String, SubString{String}}; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`write(s::LibuvStream, str::Union{String, SubString{String}}; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1691 ``p1691,
  methodEntry "base/stream.jl" "stream" 1699 1705 "writepartial(s::LibuvStream, str::Union{String, SubString{String}}; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`writepartial(s::LibuvStream, str::Union{String, SubString{String}}; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1699 ``p1699,
  methodEntry "base/stream.jl" "stream" 1710 1718 "write(s::LibuvStream, a::Array; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`write(s::LibuvStream, a::Array; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1710 ``p1710,
  methodEntry "base/stream.jl" "stream" 1720 1728 "writepartial(s::LibuvStream, a::Array; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`writepartial(s::LibuvStream, a::Array; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1720 ``p1720,
  methodEntry "base/stream.jl" "stream" 1736 1739 "unsafe_write(s::LibuvStream, p::Ptr{UInt8}, n::UInt; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`unsafe_write(s::LibuvStream, p::Ptr{UInt8}, n::UInt; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1736 ``p1736,
  methodEntry "base/stream.jl" "stream" 1741 1772 "_unsafe_write_owned(s::LibuvStream, p::Ptr{UInt8}, n::UInt, cancel::CancelTokenArg, @nospecialize(owner), partial::Bool)" "`_unsafe_write_owned(s::LibuvStream, p::Ptr{UInt8}, n::UInt, cancel::CancelTokenArg, @nospecialize(owner), partial::Bool)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1741 ``p1741,
  methodEntry "base/stream.jl" "stream" 1778 1789 "_requeue_unwritten!(s::LibuvStream, arr::Vector{UInt8}, nwritten::Int)" "`_requeue_unwritten!(s::LibuvStream, arr::Vector{UInt8}, nwritten::Int)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1778 ``p1778,
  methodEntry "base/stream.jl" "stream" 1795 1824 "flush(s::LibuvStream; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`flush(s::LibuvStream; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1795 ``p1795,
  methodEntry "base/stream.jl" "stream" 1826 1832 "buffer_writes(s::LibuvStream, bufsize)" "`buffer_writes(s::LibuvStream, bufsize)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1826 ``p1826,
  methodEntry "base/stream.jl" "stream" 1836 1854 "write(s::LibuvStream, b::UInt8)" "`write(s::LibuvStream, b::UInt8)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1836 ``p1836,
  methodEntry "base/stream.jl" "stream" 1856 1907 "uv_writecb_task(req::Ptr{Cvoid}, status::Cint)" "`uv_writecb_task(req::Ptr{Cvoid}, status::Cint)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1856 ``p1856,
  methodEntry "base/stream.jl" "stream" 1909 1913 "uv_shutdowncb_task(req::Ptr{Cvoid}, status::Cint)" "`uv_shutdowncb_task(req::Ptr{Cvoid}, status::Cint)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1909 ``p1909,
  methodEntry "base/stream.jl" "stream" 1916 1916 "_fd(x::IOStream)" "`_fd(x::IOStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1916 ``p1916,
  methodEntry "base/stream.jl" "stream" 1917 1917 "_fd(x::Union{OS_HANDLE, RawFD})" "`_fd(x::Union{OS_HANDLE, RawFD})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1917 ``p1917,
  methodEntry "base/stream.jl" "stream" 1919 1926 "_fd(x::Union{LibuvStream, LibuvServer})" "`_fd(x::Union{LibuvStream, LibuvServer})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1919 ``p1919,
  methodEntry "base/stream.jl" "stream" 1938 1948 "_redirect_io_libc(stream, unix_fd::Int)" "`_redirect_io_libc(stream, unix_fd::Int)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1938 ``p1938,
  methodEntry "base/stream.jl" "stream" 1949 1956 "_redirect_io_cglobal(handle::Union{LibuvStream, IOStream, Nothing}, unix_fd::Int)" "`_redirect_io_cglobal(handle::Union{LibuvStream, IOStream, Nothing}, unix_fd::Int)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1949 ``p1949,
  methodEntry "base/stream.jl" "stream" 1957 1962 "_redirect_io_global(io, unix_fd::Int)" "`_redirect_io_global(io, unix_fd::Int)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1957 ``p1957,
  methodEntry "base/stream.jl" "stream" 1963 1968 "(f::RedirectStdStream)(handle::Union{LibuvStream, IOStream})" "`(f::RedirectStdStream)(handle::Union{LibuvStream, IOStream})` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1963 ``p1963,
  methodEntry "base/stream.jl" "stream" 1969 1977 "(f::RedirectStdStream)(::DevNull)" "`(f::RedirectStdStream)(::DevNull)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1969 ``p1969,
  methodEntry "base/stream.jl" "stream" 1978 1983 "(f::RedirectStdStream)(io::AbstractPipe)" "`(f::RedirectStdStream)(io::AbstractPipe)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1978 ``p1978,
  methodEntry "base/stream.jl" "stream" 1984 1991 "(f::RedirectStdStream)(p::Pipe)" "`(f::RedirectStdStream)(p::Pipe)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1984 ``p1984,
  methodEntry "base/stream.jl" "stream" 1992 1992 "(f::RedirectStdStream)()" "`(f::RedirectStdStream)()` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1992 ``p1992,
  methodEntry "base/stream.jl" "stream" 1995 1995 "iterate(p::Pipe)" "`iterate(p::Pipe)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1995 ``p1995,
  methodEntry "base/stream.jl" "stream" 1996 1996 "iterate(p::Pipe, i::Int)" "`iterate(p::Pipe, i::Int)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1996 ``p1996,
  methodEntry "base/stream.jl" "stream" 1997 1997 "getindex(p::Pipe, key::Int)" "`getindex(p::Pipe, key::Int)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P1997 ``p1997,
  methodEntry "base/stream.jl" "stream" 2052 2056 "redirect_stdio(;stdin=nothing, stderr=nothing, stdout=nothing)" "`redirect_stdio(;stdin=nothing, stderr=nothing, stdout=nothing)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2052 ``p2052,
  methodEntry "base/stream.jl" "stream" 2110 2154 "redirect_stdio(f; stdin=nothing, stderr=nothing, stdout=nothing)" "`redirect_stdio(f; stdin=nothing, stderr=nothing, stdout=nothing)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2110 ``p2110,
  methodEntry "base/stream.jl" "stream" 2112 2114 "resolve(new::Nothing, oldstream, mode)" "`resolve(new::Nothing, oldstream, mode)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2112 ``p2112,
  methodEntry "base/stream.jl" "stream" 2115 2117 "resolve(path::AbstractString, oldstream,mode)" "`resolve(path::AbstractString, oldstream,mode)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2115 ``p2115,
  methodEntry "base/stream.jl" "stream" 2118 2120 "resolve(new, oldstream, mode)" "`resolve(new, oldstream, mode)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2118 ``p2118,
  methodEntry "base/stream.jl" "stream" 2122 2122 "same_path(x, y)" "`same_path(x, y)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2122 ``p2122,
  methodEntry "base/stream.jl" "stream" 2123 2126 "same_path(x::AbstractString, y::AbstractString)" "`same_path(x::AbstractString, y::AbstractString)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2123 ``p2123,
  methodEntry "base/stream.jl" "stream" 2156 2167 "(f::RedirectStdStream)(thunk::Function, stream)" "`(f::RedirectStdStream)(thunk::Function, stream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2156 ``p2156,
  methodEntry "base/stream.jl" "stream" 2194 2194 "mark(x::LibuvStream)" "`mark(x::LibuvStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2194 ``p2194,
  methodEntry "base/stream.jl" "stream" 2195 2195 "unmark(x::LibuvStream)" "`unmark(x::LibuvStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2195 ``p2195,
  methodEntry "base/stream.jl" "stream" 2196 2196 "reset(x::LibuvStream)" "`reset(x::LibuvStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2196 ``p2196,
  methodEntry "base/stream.jl" "stream" 2197 2197 "ismarked(x::LibuvStream)" "`ismarked(x::LibuvStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2197 ``p2197,
  methodEntry "base/stream.jl" "stream" 2199 2205 "peek(s::LibuvStream, ::Type{T}) where T" "`peek(s::LibuvStream, ::Type{T}) where T` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2199 ``p2199,
  methodEntry "base/stream.jl" "stream" 2216 2216 "BufferStream()" "`BufferStream()` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2216 ``p2216,
  methodEntry "base/stream.jl" "stream" 2219 2219 "isopen(s::BufferStream)" "`isopen(s::BufferStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2219 ``p2219,
  methodEntry "base/stream.jl" "stream" 2225 2229 "closewrite(s::BufferStream; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`closewrite(s::BufferStream; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2225 ``p2225,
  methodEntry "base/stream.jl" "stream" 2231 2237 "close(s::BufferStream)" "`close(s::BufferStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2231 ``p2231,
  methodEntry "base/stream.jl" "stream" 2238 2238 "uvfinalize(s::BufferStream)" "`uvfinalize(s::BufferStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2238 ``p2238,
  methodEntry "base/stream.jl" "stream" 2239 2239 "setup_stdio(stream::BufferStream, child_readable::Bool)" "`setup_stdio(stream::BufferStream, child_readable::Bool)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2239 ``p2239,
  methodEntry "base/stream.jl" "stream" 2241 2248 "read(s::BufferStream, ::Type{UInt8}; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`read(s::BufferStream, ::Type{UInt8}; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2241 ``p2241,
  methodEntry "base/stream.jl" "stream" 2249 2256 "unsafe_read(s::BufferStream, a::Ptr{UInt8}, nb::UInt; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`unsafe_read(s::BufferStream, a::Ptr{UInt8}, nb::UInt; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2249 ``p2249,
  methodEntry "base/stream.jl" "stream" 2257 2257 "bytesavailable(s::BufferStream)" "`bytesavailable(s::BufferStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2257 ``p2257,
  methodEntry "base/stream.jl" "stream" 2259 2259 "isreadable(s::BufferStream)" "`isreadable(s::BufferStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2259 ``p2259,
  methodEntry "base/stream.jl" "stream" 2260 2260 "iswritable(s::BufferStream)" "`iswritable(s::BufferStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2260 ``p2260,
  methodEntry "base/stream.jl" "stream" 2262 2275 "wait_readnb(s::BufferStream, nb::Int, tok::MaybeToken=default_cancel_token())" "`wait_readnb(s::BufferStream, nb::Int, tok::MaybeToken=default_cancel_token())` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2262 ``p2262,
  methodEntry "base/stream.jl" "stream" 2277 2286 "readavailable(this::BufferStream; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`readavailable(this::BufferStream; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2277 ``p2277,
  methodEntry "base/stream.jl" "stream" 2288 2295 "read(stream::BufferStream; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`read(stream::BufferStream; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2288 ``p2288,
  methodEntry "base/stream.jl" "stream" 2297 2335 "readbytes!(s::BufferStream, a::Vector{UInt8}, nb::Int; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`readbytes!(s::BufferStream, a::Vector{UInt8}, nb::Int; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2297 ``p2297,
  methodEntry "base/stream.jl" "stream" 2303 2310 "wait_locked(s, buf, nb, tok)" "`wait_locked(s, buf, nb, tok)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2303 ``p2303,
  methodEntry "base/stream.jl" "stream" 2337 2337 "show(io::IO, s::BufferStream)" "`show(io::IO, s::BufferStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2337 ``p2337,
  methodEntry "base/stream.jl" "stream" 2339 2356 "readuntil(s::BufferStream, c::UInt8; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)" "`readuntil(s::BufferStream, c::UInt8; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2339 ``p2339,
  methodEntry "base/stream.jl" "stream" 2358 2371 "wait_close(s::BufferStream, tok::MaybeToken=default_cancel_token())" "`wait_close(s::BufferStream, tok::MaybeToken=default_cancel_token())` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2358 ``p2358,
  methodEntry "base/stream.jl" "stream" 2373 2373 "start_reading(s::BufferStream)" "`start_reading(s::BufferStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2373 ``p2373,
  methodEntry "base/stream.jl" "stream" 2374 2374 "stop_reading(s::BufferStream)" "`stop_reading(s::BufferStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2374 ``p2374,
  methodEntry "base/stream.jl" "stream" 2376 2376 "write(s::BufferStream, b::UInt8)" "`write(s::BufferStream, b::UInt8)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2376 ``p2376,
  methodEntry "base/stream.jl" "stream" 2382 2387 "write(s::BufferStream, a::Vector{UInt8}; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`write(s::BufferStream, a::Vector{UInt8}; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2382 ``p2382,
  methodEntry "base/stream.jl" "stream" 2388 2394 "write(s::BufferStream, str::Union{String, SubString{String}}; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`write(s::BufferStream, str::Union{String, SubString{String}}; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2388 ``p2388,
  methodEntry "base/stream.jl" "stream" 2395 2403 "write(s::BufferStream, a::Array; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`write(s::BufferStream, a::Array; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2395 ``p2395,
  methodEntry "base/stream.jl" "stream" 2404 2414 "unsafe_write(s::BufferStream, p::Ptr{UInt8}, nb::UInt; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`unsafe_write(s::BufferStream, p::Ptr{UInt8}, nb::UInt; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2404 ``p2404,
  methodEntry "base/stream.jl" "stream" 2416 2424 "eof(s::BufferStream; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`eof(s::BufferStream; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2416 ``p2416,
  methodEntry "base/stream.jl" "stream" 2427 2427 "buffer_writes(s::BufferStream, bufsize=0)" "`buffer_writes(s::BufferStream, bufsize=0)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2427 ``p2427,
  methodEntry "base/stream.jl" "stream" 2428 2436 "flush(s::BufferStream; cancel::CancelTokenArg=DEFAULT_CANCEL)" "`flush(s::BufferStream; cancel::CancelTokenArg=DEFAULT_CANCEL)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2428 ``p2428,
  methodEntry "base/stream.jl" "stream" 2438 2438 "skip(s::BufferStream, n)" "`skip(s::BufferStream, n)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2438 ``p2438,
  methodEntry "base/stream.jl" "stream" 2440 2446 "reseteof(s::BufferStream)" "`reseteof(s::BufferStream)` follows its source-order branches, checks, state changes, and calls for every modelled input." ``P2440 ``p2440
]

end JuliaLean.Streams.Methods.Stream
