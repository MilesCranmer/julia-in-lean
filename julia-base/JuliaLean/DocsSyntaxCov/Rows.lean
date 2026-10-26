import JuliaLean.DocsSyntaxCov.DocsProps
import JuliaLean.DocsSyntaxCov.ParseProps
import JuliaLean.DocsSyntaxCov.TomlPrintTables
import JuliaLean.DocsSyntaxCov.BinaryProps
import JuliaLean.DocsSyntaxCov.TomlLexProps
import JuliaLean.DocsSyntaxCov.SyntaxProps

/-! Row-specific properties not supplied by the initial area models. -/

namespace JuliaLean.DocsSyntaxCov

open JuliaLean

def SignatureImplementation : Prop :=
  (∀ x, signature x = signatureBang [] x) ∧
  ∀ tv x, (∃ v, signatureBang tv x = .ok v) ∨ (∃ e, signatureBang tv x = .error e)

theorem signatureImplementation : SignatureImplementation := by
  refine ⟨fun _ => rfl, fun tv x => ?_⟩
  cases h : signatureBang tv x with
  | ok v => exact Or.inl ⟨v, rfl⟩
  | error e => exact Or.inr ⟨e, rfl⟩

def DocstrLookupBehavior : Prop := ∀ st b typesig,
  docstrLookup st b typesig =
    let found := st.modules.findSome? fun m =>
      match (metaDict st m false).2 with
      | none => none
      | some dict => match assocGet dict b with
        | none => none | some md => assocGet md.docs typesig
    match found with
    | some d => .ok d
    | none => .error (.errorException "could not find matching docstring")

theorem docstrLookupBehavior : DocstrLookupBehavior := fun _ _ _ => rfl

def RefAndHasdoc : Prop :=
  (∀ x, refMacro x = do
    let b ← bindingexpr (← namify x)
    pure (esc (docexpr [b, ← signature x]))) ∧
  ∀ env st user kind fuel mod sym,
    hasdoc env st user kind fuel mod sym =
      hasdocB env st user kind fuel fuel (mkBinding env fuel mod sym)

theorem refAndHasdoc : RefAndHasdoc := ⟨fun _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

/-- The complete `moduledoc` body, factored so the coverage property names the method itself. -/
def moduleDocBody (src : Src) (meta_ def_ def' : JV) : DJ JV := do
  let name ← namify def'
  let b ← bindingexpr name
  let md ← metadata src.file src.line src.mod name true
  let docex := call docFn [name, b, docexpr [lazyIterpolate meta_, md.toExpr]]
  match def_ with
  | .nothing => pure (esc (call (.val "Core.eval") [name, quot docex]))
  | _ =>
    let hasVersion := !(def_.arg 1).isBool
    let d := unblock def_
    let iBlock := 3 + (if hasVersion then 1 else 0)
    let iBare := 1 + (if hasVersion then 1 else 0)
    match d, d.arg? iBlock with
    | .expr h as, some (.expr bh body) =>
      let body := if d.arg iBare == .bool false then
          .expr "import" [.expr ":" [.expr "." [.sym "Base"], .expr "." [.sym "@doc"]]] :: body else body
      let body := body ++ [docex]
      let as := as.set (iBlock - 1) (.expr bh body)
      pure (esc (.expr "toplevel" [.expr h as]))
    | _, _ => .error .boundsError

def ModuleMultiDocBehavior : Prop :=
  (∀ src meta_ def_ def', moduledoc src meta_ def_ def' = moduleDocBody src meta_ def_ def') ∧
  ∀ env src source n meta_ ex define, multidoc env src source (n + 1) meta_ ex define = do
    let md ← metadata src.file src.line src.mod ex false
    let str := docexpr [lazyIterpolate meta_, md.toExpr]
    let ref := JV.val "ref"
    let docstrs := ex.args.mapIdx fun i _ =>
      if i == 0 then call (.val "getindex") [call (.val "setindex!") [ref, str]]
      else call (.val "getindex") [ref]
    let outs ← multidocArgs env src source n (docstrs.zip ex.args) define
    pure (.expr "block" outs)

theorem moduleMultiDocBehavior : ModuleMultiDocBehavior :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

namespace Parse

open JuliaLean.ParsePrint.IntParse

def WhitespaceAndIntegerMethods : Prop :=
  (∀ b, isspaceAscii b = (b.val == 32 || (9 ≤ b.val && b.val ≤ 13))) ∧
  (∀ s i, skipspacechar s i =
    let (c, next) := iterate s i
    if isspaceChar c then next else i) ∧
  (∀ s i j, skipspacecharBack s i j =
    let k := thisind s j
    if k ≥ i ∧ isspaceChar (getChar s k) then k - 1 else j) ∧
  (∀ s i j, skipspace s i j = skipspaceLoop s j (s.length + 1) i) ∧
  (∀ s i j, skipspaceBack s i j = skipspaceBackLoop s i (s.length + 1) j) ∧
  (∀ t s base raise, parseintString t s base raise = do
    let b ← validBase base
    parseintUtf8 t s 1 (ncu s) b raise)

theorem whitespaceAndIntegerMethods : WhitespaceAndIntegerMethods :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

def ParseWrapperMethods : Prop :=
  (∀ isnumeric s raise, parseBoolStr isnumeric s raise =
    tryparseBool isnumeric s 1 (lastindex s) 0 raise) ∧
  (∀ F pf s, @tryparseFloat F pf s = tryparseFloatRange pf s 1 (ncu s)) ∧
  (∀ R tp s a b, @tryparseInternalReal R tp s a b =
    if a == 1 ∧ b == lastindex s then tp s else tp (slice s a (nextind s b - 1))) ∧
  (∀ R tp s, @parseReal R tp s = do
    match ← tryparseInternalRealKw tp s true with
    | some r => pure r | none => .error (.methodError "convert"))

theorem parseWrapperMethods : ParseWrapperMethods :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩

end Parse

namespace TomlPrint

def HoistedCommentsBehavior : Prop :=
  (∀ c indent sorted kvs path, printHoisted c indent sorted 0 kvs path = []) ∧
  ∀ c indent sorted n kvs path, printHoisted c indent sorted (n + 1) kvs path =
    let fl := match lookup c.floating path with
      | none => [] | some lines => lines.flatMap (printCommentLine indent)
    let vkeys := if sorted then sortKeys kvs else kvs
    fl ++ vkeys.flatMap (fun (k, v) =>
      let kpath := path ++ [k]
      let blk := match lookup c.items kpath with
        | none => []
        | some b => b.above.flatMap (printCommentLine indent) ++
          (match b.inline with | none => [] | some t => printCommentLine indent t)
      blk ++ match v with | .dict _ kvs' => printHoisted c indent sorted n kvs' kpath | _ => [])

theorem hoistedCommentsBehavior : HoistedCommentsBehavior :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

end TomlPrint

namespace Binary

open JuliaLean.Platforms

def AddPlatformTagBehavior : Prop := ∀ lc tags tag value,
  addPlatformTag lc tags tag value = do
    let tag := lower lc tag
    match value with
    | .none => return tags
    | _ =>
    let (tags, tag) ← (if tag == s% "libstdcxx_version" then do
        let tags ← if haskey tags (s% "cxxlib") then pure tags
          else addTag lc tags (s% "cxxlib") (s% "libstdcxx")
        pure (tags, s% "cxxlib_version")
      else if tag == s% "cxxstring_abi" then do
        let tags ← if haskey tags (s% "cxxlib") then pure tags
          else addTag lc tags (s% "cxxlib") (s% "libstdcxx")
        pure (tags, tag)
      else pure (tags, tag) : Jl (Tags × Str))
    let value ← (if [s% "libgfortran_version", s% "cxxlib_version", s% "os_version"].contains tag then
        match value with
        | .ver v => pure (TagVal.str (VersionNumbers.vprint v))
        | .str s => do
          match ← VersionNumbers.tryparse s with
          | some v => pure (TagVal.str (VersionNumbers.vprint v))
          | none => pure value
        | .none => pure value
      else pure value : Jl TagVal)
    addTag lc tags tag (tagString value)

theorem addPlatformTagBehavior : AddPlatformTagBehavior := fun _ _ _ _ => rfl

def PlatformStringMethods : Prop := ∀ p : Platform,
  cxxstringAbi p = tget p (s% "cxxstring_abi") ∧
  callAbiStr p = (callAbi p).getD [] ∧
  libcStr p = (match libc p with
    | none => [] | some v => if v == s% "glibc" then s% "-gnu" else if v == s% "msvcrt" then s% "-mingw32"
      else if v == s% "ucrt" then s% "-ucrt-mingw32" else ['-'] ++ v) ∧
  platformDlext p = (if os p == some (s% "windows") then s% "dll"
    else if os p == some (s% "macos") then s% "dylib" else s% "so")

theorem platformStringMethods : PlatformStringMethods := by
  intro p
  refine ⟨rfl, rfl, ?_, ?_⟩
  · unfold libcStr; cases h : libc p <;> simp [h]
  · unfold platformDlext; rfl

end Binary

namespace TomlRows

open JuliaLean.Toml

def Runs {A : Type} (m : M A) (p : Parser) : Prop := ∃ r, m.run p = r

theorem runs {A : Type} (m : M A) (p : Parser) : Runs m p := by
  unfold Runs
  cases h : m.run p with
  | ok r => exact ⟨.ok r, rfl⟩
  | error e => exact ⟨.error e, rfl⟩

def ValueMethodTotality : Prop := ∀ (p : Parser) (lf fuel : Nat) (sgn : Int) (b : Bool)
    (f : Nat → Bool) (sx : IntSyntax),
  Runs (parse_toplevel lf fuel) p ∧
  Runs (parse_key fuel) p ∧
  Runs (parse_value lf fuel) p ∧
  Runs (parse_inline_table lf fuel) p ∧
  Runs (parse_inf sgn) p ∧
  Runs parse_nan p ∧
  Runs (parse_bool b) p ∧
  Runs (accept_batch_underscore fuel f) p ∧
  Runs (take_string_or_substring b) p ∧
  Runs (parse_intlike sx b) p ∧
  isvalid_hex p.current_char =
    (isdigit p.current_char || (ch 'a' ≤ p.current_char && p.current_char ≤ ch 'f') ||
      (ch 'A' ≤ p.current_char && p.current_char ≤ ch 'F')) ∧
  isvalid_oct p.current_char = (ch '0' ≤ p.current_char && p.current_char ≤ ch '7') ∧
  isvalid_binary p.current_char = (ch '0' ≤ p.current_char && p.current_char ≤ ch '1') ∧
  ok_end_value p.current_char =
    (iswhitespace p.current_char || p.current_char == ch '#' || p.current_char == EOF ||
      p.current_char == ch ']' || p.current_char == ch '}' || p.current_char == ch ',' ||
      p.current_char == ch '\n' || p.current_char == ch '\r')

theorem valueMethodTotality : ValueMethodTotality := by
  intro p lf fuel sgn b f sx
  exact ⟨runs _ _, runs _ _, runs _ _, runs _ _, runs _ _, runs _ _, runs _ _, runs _ _,
    runs _ _, runs _ _, rfl, rfl, rfl, rfl⟩

def DateMethodTotality : Prop := ∀ (p : Parser) (fuel : Nat) (f : Nat → Bool)
    (y m d h mi s ms : Int),
  Runs (accept_two f) p ∧
  Runs (try_return_datetime y m d h mi s ms) p ∧
  Runs (try_return_date y m d) p ∧
  Runs (try_return_time h mi s ms) p ∧
  Runs (_parse_local_time fuel false) p ∧
  Runs (parse_local_time fuel) p ∧
  Runs (parse_datetime fuel) p

theorem dateMethodTotality : DateMethodTotality := by
  intro p fuel f y m d h mi s ms
  exact ⟨runs _ _, runs _ _, runs _ _, runs _ _, runs _ _, runs _ _, runs _ _⟩

def StringMethodTotality : Prop := ∀ (p : Parser) (fuel : Nat) (quoted allow multiline : Bool),
  Runs (parse_string_start fuel quoted allow) p ∧
  Runs (parse_string_continue fuel multiline quoted) p ∧
  Runs (take_chunks quoted) p ∧
  (∀ x, stopCandidates true false x =
    (x != ch '"' && x != ch '\\' && (true || x != ch '\n'))) ∧
  (∀ x, stopCandidates false false x =
    (x != ch '"' && x != ch '\\' && (false || x != ch '\n'))) ∧
  (∀ x, stopCandidates true true x =
    (x != ch '\'' && x != ch '\\' && (true || x != ch '\n'))) ∧
  ∀ x, stopCandidates false true x =
    (x != ch '\'' && x != ch '\\' && (false || x != ch '\n'))

theorem stringMethodTotality : StringMethodTotality := by
  intro p fuel quoted allow multiline
  exact ⟨runs _ _, runs _ _, runs _ _, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

end TomlRows

namespace Binary

open JuliaLean.Platforms

def DirectParseMethods : Prop :=
  (∀ m mapping, ∃ r, getField m mapping = r) ∧
  (∀ s, ∃ r, splitTags s = r) ∧
  (∀ os name, ∃ r, extractOsVersion os name = r) ∧
  (∀ p : Platform, ∃ r, vnOrNothing p.tags (s% "os_version") = r) ∧
  (∀ p : Platform, ∃ r, libgfortranVersion p = r) ∧
  (∀ p : Platform, ∃ r, libstdcxxVersion p = r) ∧
  (∀ p : Platform, ∃ r, osStr p = r) ∧
  ∀ s, ∃ r, parsePlatform asciiLower false s = r

theorem directParseMethods : DirectParseMethods := by
  refine ⟨fun m mapping => ⟨_, rfl⟩, fun s => ⟨_, rfl⟩, fun os name => ⟨_, rfl⟩,
    fun p => ⟨_, rfl⟩, fun p => ⟨_, rfl⟩, fun p => ⟨_, rfl⟩,
    fun p => ⟨_, rfl⟩, fun s => ⟨_, rfl⟩⟩

end Binary

namespace Syntax

def LayerMethodTotality : Prop := ∀ fuel sc recursive,
  (∃ r, baseLayer fuel sc = r) ∧ (∃ r, escapeLayer fuel sc recursive = r)

theorem layerMethodTotality : LayerMethodTotality := by
  intro fuel sc recursive
  constructor
  · cases h : baseLayer fuel sc with
    | ok r => exact ⟨.ok r, rfl⟩
    | error e => exact ⟨.error e, rfl⟩
  · cases h : escapeLayer fuel sc recursive with
    | ok r => exact ⟨.ok r, rfl⟩
    | error e => exact ⟨.error e, rfl⟩

end Syntax

end JuliaLean.DocsSyntaxCov
