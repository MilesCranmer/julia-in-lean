import JuliaLean.Artifacts.Model
import JuliaLean.Platforms.Lemmas

/-! Deterministic differential corpus. -/

namespace JuliaLean.Artifacts.Validation

open JuliaLean JuliaLean.Artifacts

private def str (s : Str) : String := String.ofList s

private def showSplit (input : Str) : IO Unit := do
  let result := splitArtifactSlash input
  IO.println s!"split {str input} => {str result.1}|{str result.2}"

private def baseMeta (fields : Dict Str) (hash : Option Hash := none)
    (download := false) (lazy := false) : Meta :=
  { stringFields := fields, hash, download, lazy }

private def showUnpack (label : String) (m : Meta) : IO Unit :=
  match unpackPlatform Platforms.asciiLower m with
  | .ok (some p) => match Platforms.triplet p with
    | .ok value => IO.println s!"unpack {label} => {str value}"
    | .error _ => IO.println s!"unpack {label} => error"
  | _ => IO.println s!"unpack {label} => nothing"

private def selectedNames (xs : List (Name × Meta)) : String :=
  String.intercalate "," (xs.map fun e => str e.1)

def differential : IO Unit := do
  for input in [s% "Foo", s% "Foo/bar", s% "Foo\\bar", s% "Foo//bar",
      s% "Foo/../x", s% "/Foo/x", s% "Foo/"] do
    showSplit input

  let ordered := baseMeta [(s% "arch", s% "x86_64"), (s% "os", s% "linux"),
    (s% "libc", s% "musl")]
  let reordered := baseMeta [(s% "libc", s% "musl"), (s% "os", s% "linux"),
    (s% "arch", s% "x86_64")]
  showUnpack "ordered" ordered
  showUnpack "reordered" reordered

  let eager := baseMeta [] (some 1) true false
  let lazy := baseMeta [] (some 2) true true
  let localOnly := baseMeta [] (some 3) false false
  let resolved : List Resolved := [(s% "eager", some eager), (s% "lazy", some lazy),
    (s% "local", some localOnly), (s% "missing", none)]
  IO.println s!"lazy false => {selectedNames (selectDownloadable false resolved)}"
  IO.println s!"lazy true => {selectedNames (selectDownloadable true resolved)}"

  let high := loadHashDepots [[(7, .target (.path 2))], [(7, .target (.path 1))]]
  IO.println s!"override high => {nget high.hash 7 == some (.path 2)}"
  let state : OverrideState :=
    { uuid := [(3, [(s% "payload", .path 9)])], hash := [(7, .path 2)] }
  let processed := processNameOverrides [(s% "payload", [7])] 3 state
  IO.println s!"override uuid => {nget processed.hash 7 == some (.path 9)}"
  let malformed := applyHashEntry state 7 .invalid
  IO.println s!"malformed logged => {malformed.errors == state.errors + 1}"
  IO.println s!"malformed ignored => {malformed.hash == state.hash}"

  let direct := artifactPaths 1 [(7, .path 9)] [1, 2] 7
  let existsResult := artifactExists (· == .override 9) [.override 9]
  let pathResult := artifactPath (· == .override 9) [.override 9]
  IO.println s!"path override => {direct == some [.override 9]},{existsResult},{pathResult == some (.override 9)}"

  let noUser : Platforms.UserSem := fun _ _ _ _ _ => .ok false
  match Platforms.platform Platforms.asciiLower (s% "x86_64") (s% "linux") [] false,
      Platforms.platform Platforms.asciiLower (s% "x86_64") (s% "linux")
        [(s% "cuda", .str (s% "12"))] false with
  | .ok generic, .ok specific =>
      let result := artifactMetaPlatform noUser (fun p => Platforms.unionOrder p specific)
        [(generic, s% "generic"), (specific, s% "specific")] specific
      match result with
      | .ok (some value) => IO.println s!"select => {str value}"
      | _ => IO.println "select => none"
  | _, _ => IO.println "select => error"

end JuliaLean.Artifacts.Validation
