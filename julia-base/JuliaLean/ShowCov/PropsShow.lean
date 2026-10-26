import JuliaLean.ShowCov.Values
import JuliaLean.ShowCov.Containers
import JuliaLean.ShowCov.IOContext

/-!
Properties of the `IOContext`, scalar, wrapper, container, `dump` and
`alignment` models of `base/show.jl`.
-/

namespace JuliaLean.ShowCov

open Values Containers IOCtx

/-! ## `IOContext` -/

theorem ioContextPairs_snoc (io : JIO) (kvs : List (String × PV)) (kv : String × PV) :
    ioContextPairs io (kvs ++ [kv]) = ioContextPair (ioContextPairs io kvs) kv := by
  induction kvs generalizing io with
  | nil => rfl
  | cons a rest ih => exact ih _

theorem getCtx_pair_same (io : JIO) (k : String) (v dflt : PV) :
    getCtx k dflt (ioContextPair io (k, v)) = v := by
  cases io <;> simp [ioContextPair, ioContextDict, mkCtx, dpush, getCtx, dget]

/-- `IOContext(io, dict)` never nests: it wraps the underlying stream of `io`
and carries exactly `dict`; `IOContext(io, k => v)` makes `get(_, k, d)` return
`v` and leaves other keys as in `io`, the last of several pairs wins;
`convert(IOContext, io)` is idempotent and keeps the properties; `IOContext(io,
context)` takes the properties of `context`; `pipe_reader`, `pipe_writer` and
`lock` act on the underlying stream (`base/show.jl:336-381, 456-463`). -/
def IOContextBindings : Prop :=
  ∀ (io ctx : JIO) (d : IDict) (k k' : String) (v dflt : PV) (kvs : List (String × PV)),
    unwrapcontext (mkCtx io d) = unwrapcontext io ∧
    ioproperties (ioContextDict io d) = d ∧
    unwrapcontext (ioContextDict io d) = unwrapcontext io ∧
    getCtx k dflt (ioContextPair io (k, v)) = v ∧
    (k' ≠ k → getCtx k' dflt (ioContextPair io (k, v)) = dget (ioproperties io) k' dflt) ∧
    getCtx k dflt (ioContextPairs io (kvs ++ [(k, v)])) = v ∧
    convertCtx (convertCtx io) = convertCtx io ∧
    ioproperties (convertCtx io) = ioproperties io ∧
    ioContext1 io = convertCtx io ∧
    ioproperties (ioContextIO io ctx) = ioproperties ctx ∧
    pipeReader io = unwrapcontext io ∧ pipeWriter io = unwrapcontext io ∧
    lockTarget io = unwrapcontext io ∧
    unwrapcontext (unwrapcontext io) = unwrapcontext io ∧
    Out.text (showCtx "x") = "IOContext(x)"

theorem ioContextBindings_proven : IOContextBindings := by
  intro io ctx d k k' v dflt kvs
  refine ⟨?_, ?_, ?_, getCtx_pair_same io k v dflt, ?_, ?_, ?_, ?_, rfl, ?_, rfl, rfl, rfl, ?_, rfl⟩
  · cases io <;> rfl
  · cases io <;> rfl
  · cases io <;> rfl
  · intro hk
    have hk' : (k == k') = false := by simp [Ne.symm hk]
    cases io <;> simp [ioContextPair, ioContextDict, mkCtx, dpush, getCtx, dget, hk']
  · rw [ioContextPairs_snoc]; exact getCtx_pair_same _ k v dflt
  · cases io <;> rfl
  · cases io <;> rfl
  · cases io <;> cases ctx <;> rfl
  · cases io <;> rfl

/-- `haskey(io, k)` holds exactly for the keys `keys(io)` lists; `getindex`
agrees with `get` on present keys and throws `KeyError` otherwise, where `get`
returns the default; `in(k => v, io)` implies `haskey(io, k)`; a plain stream
has no keys (`base/show.jl:465-474`). -/
def IOContextLookup : Prop :=
  ∀ (io : JIO) (k : String) (v dflt : PV),
    (haskeyCtx k io = true ↔ k ∈ keysCtx io) ∧
    (haskeyCtx k io = true → getindexCtx k io = .ok (getCtx k dflt io)) ∧
    (haskeyCtx k io = false → getindexCtx k io = .error (.keyError k) ∧ getCtx k dflt io = dflt) ∧
    (inCtx (k, v) io = true → haskeyCtx k io = true)

theorem ioContextLookup_proven : IOContextLookup := by
  intro io k v dflt
  cases io with
  | plain b => simp [haskeyCtx, keysCtx, getindexCtx, getCtx, inCtx, inWith]
  | ctx b d =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [haskeyCtx, keysCtx, dhas, List.any_eq_true]
    · intro h
      simp only [haskeyCtx, dhas] at h
      cases hf : d.find? (·.1 == k) with
      | none =>
        rw [List.find?_eq_none] at hf
        obtain ⟨x, hx, hxk⟩ := List.any_eq_true.mp h
        exact absurd hxk (hf x hx)
      | some e => simp [getindexCtx, getCtx, dget, hf]
    · intro h
      simp only [haskeyCtx, dhas] at h
      have hf : d.find? (·.1 == k) = none := by
        rw [List.find?_eq_none]
        intro x hx hxk
        have : d.any (·.1 == k) = true := List.any_eq_true.mpr ⟨x, hx, hxk⟩
        rw [h] at this; cases this
      simp [getindexCtx, getCtx, dget, hf]
    · intro h
      simp only [inCtx, inWith, List.any_eq_true, Bool.and_eq_true] at h
      obtain ⟨x, hx, h1, _⟩ := h
      exact List.any_eq_true.mpr ⟨x, hx, h1⟩

/-- `displaysize(io::IOContext)` is the `:displaysize` property when bound, the
stream's otherwise; a plain stream gives its own (`base/show.jl:476`). -/
def DisplaysizeCtx : Prop :=
  ∀ (io : JIO) (b : BaseIO) (d : IDict) (r c : Int),
    displaysizeCtx (ioContextPair io ("displaysize", .dims r c)) = .ok (r, c) ∧
    (dhas d "displaysize" = false → displaysizeCtx (.ctx b d) = .ok b.displaysize) ∧
    displaysizeCtx (.plain b) = .ok b.displaysize

theorem displaysizeCtx_proven : DisplaysizeCtx := by
  intro io b d r c
  refine ⟨?_, ?_, rfl⟩
  · cases io <;> simp [ioContextPair, ioContextDict, mkCtx, dpush, displaysizeCtx, dhas, dget]
  · intro h; simp [displaysizeCtx, h]

theorem circularScan_isSome (x : PV) (d : IDict) (k : Nat) :
    (circularScan x k d).isSome = true ↔ ("SHOWN_SET", x) ∈ d := by
  induction d generalizing k with
  | nil => simp [circularScan]
  | cons e rest ih =>
    obtain ⟨k0, v⟩ := e
    simp only [circularScan]
    by_cases h1 : k0 = "SHOWN_SET"
    · subst h1
      by_cases h2 : v = x
      · subst h2; simp
      · have h2' : ¬ x = v := fun h => h2 h.symm
        simp [h2, h2', ih]
    · have h1' : ¬ "SHOWN_SET" = k0 := fun h => h1 h.symm
      simp [h1, h1', ih]

/-- `show_circular(io, x)` prints a marker exactly when some `:SHOWN_SET`
binding of `io` is `x`; it is `false` on a plain stream; right after
`IOContext(io, :SHOWN_SET => x)` the marker is `@-1` (`base/show.jl:478-491`). -/
def ShowCircularSpec : Prop :=
  ∀ (b : BaseIO) (d : IDict) (x : PV),
    showCircular x (.plain b) = none ∧
    ((showCircular x (.ctx b d)).isSome = true ↔ ("SHOWN_SET", x) ∈ d) ∧
    showCircular x (ioContextPair (.ctx b d) ("SHOWN_SET", x)) =
      some ["#= circular reference @-" ++ toString (1 : Nat) ++ " =#"]

theorem showCircularSpec_proven : ShowCircularSpec := by
  intro b d x
  refine ⟨rfl, circularScan_isSome x d 1, ?_⟩
  simp [showCircular, ioContextPair, ioContextDict, mkCtx, dpush, ioproperties, circularScan]

/-! ## Scalars -/

/-- `show(io, ::Bool)` prints `true`/`false`, or `1`/`0` under a `Bool`
`:typeinfo`; `nonnothing_nonmissing_typeinfo` drops exactly `Nothing` and
`Missing`; `show(io, nothing)` is `nothing`; `show(io, n::Signed)` and
`print(io, n::Unsigned)` are the decimal text (`base/show.jl:1422-1425, 1437`). -/
def ShowScalars : Prop :=
  ∀ (b : Bool) (comps : List String) (n : Int) (u : Nat),
    showBool false b = (if b then "true" else "false") ∧ showBool true b = (if b then "1" else "0") ∧
    "Nothing" ∉ nonnothingNonmissing comps ∧ "Missing" ∉ nonnothingNonmissing comps ∧
    (∀ c ∈ comps, c ≠ "Nothing" → c ≠ "Missing" → c ∈ nonnothingNonmissing comps) ∧
    showNothing = "nothing" ∧ showSigned n = toString n ∧ printUnsigned u = toString u

theorem showScalars_proven : ShowScalars := by
  intro b comps n u
  refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [nonnothingNonmissing]
  · simp [nonnothingNonmissing]
  · intro c hc h1 h2; simp [nonnothingNonmissing, hc, h1, h2]

theorem hexDigitVal_digitChar : ∀ k, k < 16 → hexDigitVal (Nat.digitChar k) = k := by decide

theorem hexValue_core (fuel n : Nat) (ds : List Char) (h : n < fuel) :
    (Nat.toDigitsCore 16 fuel n ds).foldl (fun acc c => 16 * acc + hexDigitVal c) 0 =
      ds.foldl (fun acc c => 16 * acc + hexDigitVal c) n := by
  induction fuel generalizing n ds with
  | zero => omega
  | succ fuel ih =>
    simp only [Nat.toDigitsCore]
    split
    · rename_i h0
      simp only [List.foldl_cons]
      rw [hexDigitVal_digitChar _ (Nat.mod_lt _ (by decide))]
      congr 1; omega
    · rename_i h0
      rw [ih (n / 16) _ (by omega), List.foldl_cons,
        hexDigitVal_digitChar _ (Nat.mod_lt _ (by decide))]
      congr 1; omega

theorem hexValue_toDigits (n : Nat) : hexValue (Nat.toDigits 16 n) = n := by
  simp only [hexValue, Nat.toDigits]
  rw [hexValue_core _ _ _ (Nat.lt_succ_self n)]
  rfl

theorem hexValue_zeros (k : Nat) (ds : List Char) : hexValue (List.replicate k '0' ++ ds) = hexValue ds := by
  have hz : ∀ k, (List.replicate k '0').foldl (fun acc c => 16 * acc + hexDigitVal c) 0 = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ, List.foldl_cons]; exact ih
  simp only [hexValue, List.foldl_append, hz]

theorem toDigitsCore_length (fuel n : Nat) (ds : List Char) (k : Nat) (h : n < fuel)
    (hk : n < 16 ^ k) (hk1 : 1 ≤ k) : (Nat.toDigitsCore 16 fuel n ds).length ≤ k + ds.length := by
  induction fuel generalizing n ds k with
  | zero => omega
  | succ fuel ih =>
    simp only [Nat.toDigitsCore]
    split
    · simp; omega
    · rename_i h0
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with hj | hj
        · subst hj; simp at hk; omega
        · exact hj
      have hd : n / 16 < 16 ^ j := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        rw [Nat.pow_succ] at hk; exact hk
      have := ih (n / 16) (Nat.digitChar (n % 16) :: ds) j (by omega) hd hj
      simp only [List.length_cons] at this; omega

theorem unsigned_hex_aux (bits pad n : Nat) (hp : (bits + 3) / 4 = pad) (hpos : 1 ≤ pad)
    (hpow : 2 ^ bits = 16 ^ pad) (hlit : hexLiteralBits pad = bits) (hn : n < 2 ^ bits) :
    ∃ digits : List Char, showUnsigned true false bits n = "0x" ++ String.ofList digits ∧
      hexLiteralBits digits.length = bits ∧ hexValue digits = n := by
  refine ⟨List.replicate (pad - (Nat.toDigits 16 n).length) '0' ++ Nat.toDigits 16 n, ?_, ?_, ?_⟩
  · simp [showUnsigned, hexPad, hp]
  · have hl : (Nat.toDigits 16 n).length ≤ pad := by
      have := toDigitsCore_length (n + 1) n [] pad (Nat.lt_succ_self n) (by rw [← hpow]; exact hn) hpos
      simpa [Nat.toDigits] using this
    rw [List.length_append, List.length_replicate, Nat.sub_add_cancel hl, hlit]
  · rw [hexValue_zeros, hexValue_toDigits]

/-- `show(io, n::Unsigned)` with `:hexunsigned` (the default) prints a `0x`
literal whose digit count makes Julia parse it as the same unsigned type, and
whose value is `n` (`base/show.jl:1426-1436`; hexadecimal literal typing in
the manual's Integers section). -/
def UnsignedHexLiteral : Prop :=
  ∀ (bits n : Nat), bits ∈ [8, 16, 32, 64, 128] → n < 2 ^ bits →
    ∃ digits : List Char, showUnsigned true false bits n = "0x" ++ String.ofList digits ∧
      hexLiteralBits digits.length = bits ∧ hexValue digits = n

theorem unsignedHexLiteral_proven : UnsignedHexLiteral := by
  intro bits n hb hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact unsigned_hex_aux 8 2 n rfl (by decide) rfl rfl hn
  · exact unsigned_hex_aux 16 4 n rfl (by decide) rfl rfl hn
  · exact unsigned_hex_aux 32 8 n rfl (by decide) rfl rfl hn
  · exact unsigned_hex_aux 64 16 n rfl (by decide) rfl rfl hn
  · exact unsigned_hex_aux 128 32 n rfl (by decide) rfl rfl hn

/-- Without `:hexunsigned`, `show(io, n::Unsigned)` prints the decimal value,
wrapped as `UIntN(n)` unless the `:typeinfo` is the value's type
(`base/show.jl:1426-1436`). -/
def UnsignedDecimal : Prop :=
  ∀ (bits n : Nat),
    showUnsigned false true bits n = toString n ∧
    showUnsigned false false bits n = "UInt" ++ toString bits ++ "(" ++ toString n ++ ")"

theorem unsignedDecimal_proven : UnsignedDecimal := by
  intro bits n; exact ⟨rfl, by simp [showUnsigned, uintName, String.append_assoc]⟩

/-! ## `Pair` and modules -/

/-- `show(io, p::Pair)`: a delimited pair prints as `typeof(p)` applied to the
tuple; otherwise the elements are joined by `=>` (`" => "` unless `:compact`),
each parenthesised unless delimited; a pair of tight type is never delimited;
`isdelimited` is `true` for most values and `!isoperator` for functions;
`gettypeinfos` uses the `:typeinfo` fields only when `p` is an instance of it
(`base/show.jl:1439-1472`). -/
def ShowPairSpec : Prop :=
  ∀ (p : PairInfo) (op : Bool) (ft : String × String),
    (isdelimitedPair p = true → showPair p = [p.typeText, p.tupleText]) ∧
    (isdelimitedPair p = false → p.firstDelimited = true → p.secondDelimited = true →
      Out.text (showPair p) = p.firstText ++ (if p.compact then "=>" else " => ") ++ p.secondText) ∧
    (isdelimitedPair p = false → p.firstDelimited = false → p.secondDelimited = false →
      Out.text (showPair p) =
        "(" ++ p.firstText ++ ")" ++ (if p.compact then "=>" else " => ") ++ "(" ++ p.secondText ++ ")") ∧
    (hasTightType p = true → isdelimitedPair p = false) ∧
    isdelimitedAny = true ∧ isdelimitedFunction op = !op ∧
    gettypeinfos false true ft = ("Any", "Any") ∧ gettypeinfos true false ft = ("Any", "Any") ∧
    gettypeinfos true true ft = ft

theorem showPairSpec_proven : ShowPairSpec := by
  intro p op ft
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · intro h; simp [showPair, h, showPairtyped]
  · intro h h1 h2; simp [showPair, h, h1, h2, String.append_assoc]
  · intro h h1 h2; simp [showPair, h, h1, h2, String.append_assoc]
  · intro h; simp [isdelimitedPair, h]

theorem printFullname_text (m : Mod) : Out.text (printFullname id m) = fullnameJoin m := by
  induction m with
  | top n => simp [printFullname, fullnameJoin]
  | sub n p ih => simp [printFullname, fullnameJoin, ih, String.append_assoc]

/-- `show(io, m::Module)` prints a root module's name and any other module's
full dotted path, `join(fullname(m), ".")` (`base/show.jl:1474-1493`). -/
def ShowModuleSpec : Prop :=
  ∀ (m : Mod) (n : String),
    Out.text (printFullname id m) = fullnameJoin m ∧
    Out.text (showModule id false m) = fullnameJoin m ∧
    showModule id true (.top n) = [n]

theorem showModuleSpec_proven : ShowModuleSpec := by
  intro m n
  exact ⟨printFullname_text m, by simp [showModule, printFullname_text], rfl⟩

/-! ## Small wrappers -/

/-- The `text/plain` wrappers: `UndefInitializer` adds its explanation unless
`:compact`; a `UnitRange` adds `" (empty range)"` when empty and not compact;
`LinRange`/`LogRange` print the summary, `":\n"` and the elements unless empty;
a failed `Task` adds its exception; `CancellationTokenSource` names its state
and counts parents; `print(io, ::Symbol)` writes the name; `IncludeInto`/`EvalInto`
print `M.include`/`M.eval` for the module's own binding; the `Set` summary
counts elements; `show(x)` falls back to `show_default`; `JLOptions` prints one
field per line (`base/show.jl:6-39, 75-77, 235-239, 278-322, 520-525, 615,
3228, 3450-3452, 3539-3555`). -/
def ShowWrappers : Prop :=
  ∀ (shown summ printed exc modText field dflt r f v : String) (compact empty failed : Bool)
    (n : Nat) (np : Int),
    Out.text (showUndefPlain compact) =
      "UndefInitializer()" ++ (if compact then "" else ": array initializer with undefined values") ∧
    showRangePlain shown = [shown] ∧
    Out.text (showUnitRangePlain shown compact empty) =
      shown ++ (if !compact && empty then " (empty range)" else "") ∧
    (empty = true → showLinLogPlain empty shown summ printed = [shown]) ∧
    (empty = false → showLinLogPlain empty shown summ printed = [summ, ":", "\n", printed]) ∧
    showPlainForward shown = [shown] ∧
    Out.text (showTaskPlain shown failed exc) = shown ++ (if failed then "\n" ++ exc else "") ∧
    showCTS none r 0 = ["CancellationTokenSource(", "active", ")"] ∧
    showCTS (some 1) r 0 = ["CancellationTokenSource(", "cancelled", ")"] ∧
    showCTS (some 3) r 0 = ["CancellationTokenSource(", "cancelled, abandon external", ")"] ∧
    showCTS (some 4) r 0 = ["CancellationTokenSource(", "cancelled, abandon all", ")"] ∧
    showCTS (some 2) r 0 = ["CancellationTokenSource(", "cancelled, severity " ++ r, ")"] ∧
    (np > 0 → showCTS none r np =
      ["CancellationTokenSource(", "active", ", ", toString np, if np = 1 then " parent" else " parents", ")"]) ∧
    printSymbol shown = shown ∧ showBottomPlain = "Union{}" ∧ showUndef = "UndefInitializer()" ∧
    showInto true modText field dflt = [modText, "." ++ field] ∧ showInto false modText field dflt = [dflt] ∧
    summarySet shown n = [shown, " with ", toString n, if n = 1 then " element" else " elements"] ∧
    showFallback dflt = dflt ∧
    showJLOptions [(f, v)] = ["JLOptions(", "\n", "  ", f, " = ", v, "", "\n", ")"] ∧
    showJLOptions [] = ["JLOptions(", "\n", ")"]

theorem showWrappers_proven : ShowWrappers := by
  intro shown summ printed exc modText field dflt r f v compact empty failed n np
  refine ⟨?_, rfl, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases compact <;> simp [showUndefPlain, showUndef]
  · cases compact <;> cases empty <;> simp [showUnitRangePlain]
  · intro h; simp [showLinLogPlain, h]
  · intro h; subst h; rfl
  · cases failed <;> simp [showTaskPlain]
  · simp [showCTS]
  · simp [showCTS]
  · simp [showCTS]
  · simp [showCTS]
  · simp [showCTS]
  · intro h; simp [showCTS, h]

/-- `_show_default(io, x)`: a circular object prints its marker inside the
parentheses; fields are separated by `", "` with `#undef` for undefined ones;
a field-less bits type prints its bytes as one big-endian hexadecimal number,
the top byte trimmed to the leftover bits (`base/show.jl:527-568`). -/
def ShowDefaultSpec : Prop :=
  ∀ (ty marker a b : String) (fs : List Field),
    showDefault ty (some marker) fs none = [ty, "(", marker, ")"] ∧
    showDefault ty none [] none = [ty, "(", ")"] ∧
    showDefault ty none [.val a, .undef, .val b] none = [ty, "(", a, ", ", "#undef", ", ", b, ")"] ∧
    showDefault ty none [] (some ([0x34, 0x12], 16)) = [ty, "(", "0x", "12", "34", ")"] ∧
    showDefault ty none [] (some ([0x05], 4)) = [ty, "(", "0x", "5", ")"]

theorem showDefaultSpec_proven : ShowDefaultSpec := by
  intro ty marker a b fs
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · simp [showDefault]; decide
  · simp [showDefault]; decide

/-! ## Delimited lists -/

/-- The printed pieces of elements joined by `delim` and a space. -/
def joinPieces (delim : String) : List String → Out
  | [] => []
  | [x] => [x]
  | x :: y :: rest => [x, delim, " "] ++ joinPieces delim (y :: rest)

theorem delimIterLoop_cons2 (delim : String) (d1 : Bool) (n count : Int) (first : Bool) (x y : String)
    (ys : List String) (h : count + 1 ≤ n) :
    delimIterLoop delim d1 n count first (x :: y :: ys) =
      [x, delim, " "] ++ delimIterLoop delim d1 n (count + 1) false (y :: ys) := by
  have hn : ¬ (count + 1 > n) := by omega
  conv => lhs; rw [delimIterLoop]
  simp only [List.isEmpty_cons, Bool.false_eq_true, false_or, hn, ↓reduceIte]

theorem delimIterLoop_pieces (delim : String) (d1 : Bool) (n count : Int) (x : String) (rest : List String)
    (h : count + 1 + rest.length ≤ n) :
    delimIterLoop delim d1 n count false (x :: rest) = joinPieces delim (x :: rest) := by
  induction rest generalizing count x with
  | nil => simp [delimIterLoop, joinPieces]
  | cons y ys ih =>
    have hl : ((y :: ys).length : Int) = ys.length + 1 := by simp
    rw [delimIterLoop_cons2 _ _ _ _ _ _ _ _ (by omega), ih (count + 1) y (by omega)]
    rfl

theorem joinPieces_text (delim : String) (xs : List String) :
    Out.text (joinPieces delim xs) = String.join (List.intersperse (delim ++ " ") xs) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases rest with
    | nil => simp [joinPieces]
    | cons y ys =>
      simp only [joinPieces, Out.text_append, Out.text_cons, Out.text_nil] at ih ⊢
      rw [ih]; simp [String.append_assoc]

/-- `show(io, ::Tuple)` prints a 1-tuple with a trailing comma and longer
tuples with `", "` between elements and no trailing comma; `svec`/`zip` have
no trailing comma; a circular container prints its marker; an unassigned array
slot prints `#undef` (`base/show.jl:1562-1626, 3396`). -/
def DelimSpec : Prop :=
  ∀ (a b m : String) (xs : List String),
    showTuple [a] none = ["(", a, ",", ")"] ∧
    ((xs.length : Int) + 2 ≤ 2 ^ 63 - 1 →
      showTuple (a :: b :: xs) none = ["("] ++ joinPieces "," (a :: b :: xs) ++ [")"]) ∧
    Out.text (joinPieces "," (a :: b :: xs)) = String.join (List.intersperse ("," ++ " ") (a :: b :: xs)) ∧
    showSvec [a] none = ["svec(", a, ")"] ∧
    showZip [a] none = ["zip(", a, ")"] ∧
    showTuple xs (some m) = ["(", m, ")"] ∧
    showDelimArray (fun _ => none) "[" "," "]" false none 1 2 = ["[", "#undef", ",", " ", "#undef", "]"] ∧
    showEnumerate a = ["enumerate(", a, ")"]

theorem delimSpec_proven : DelimSpec := by
  intro a b m xs
  refine ⟨?_, ?_, joinPieces_text _ _, ?_, ?_, rfl, ?_, rfl⟩
  · simp [showTuple, showDelimIter, delimIterLoop]
  · intro h
    have e1 : showTuple (a :: b :: xs) none =
        ["("] ++ delimIterLoop "," true (2 ^ 63 - 1) 0 true (a :: b :: xs) ++ [")"] := rfl
    rw [e1, delimIterLoop_cons2 _ _ _ _ _ _ _ _ (by omega),
      delimIterLoop_pieces _ _ _ _ _ _ (by omega)]
    rfl
  · simp [showSvec, showDelimArray, delimArrayLoop]
  · simp [showZip, showDelimIter, delimIterLoop]
  · simp [showDelimArray, delimArrayLoop]

/-! ## Summaries and `showarg` -/

/-- `dims2string` prints `0-dimensional`, `n-element`, or the dimensions joined
by `×`; `summary(a::AbstractArray)` adds `" with indices "` exactly when an
axis is not `OneTo`; a `MemoryRef` summary counts the elements from its offset
on; `showarg` prefixes `::` below the top level, wraps types in `Type{...}`,
and the view/reshape/reinterpret forms add the element type only at the top
level (`base/show.jl:3249-3409`). -/
def SummarySpec : Prop :=
  ∀ (n a b : Int) (rest : List Int) (inds : List Axis) (s t T P D I : String) (len off : Int)
    (top : Bool) (parent : Out) (ix : List Ind) (dims : List Int),
    dims2string [] = "0-dimensional" ∧ dims2string [n] = toString n ++ "-element" ∧
    dims2string (a :: b :: rest) = "×".intercalate ((a :: b :: rest).map toString) ∧
    (inds.all isOneTo = true → arraySummary inds s = [dims2string (inds.map Axis.len), " ", s]) ∧
    (inds.all isOneTo = false →
      arraySummary inds s = [dims2string (inds.map Axis.len), " ", s, " with indices ", inds2string inds]) ∧
    indsstring (.oneTo n) = "Base.OneTo(" ++ toString n ++ ")" ∧ indsstring (.wrapped t len) = t ∧
    summaryMemoryRef len off s = [toString (len - off + 1), "-element ", s] ∧
    summaryAny s = s ∧ summaryFunction s = s ∧
    showargAny s true = [s] ∧ showargAny s false = ["::", s] ∧
    showargType s false = ["::", "Type{", s, "}"] ∧
    showindices (.slice :: ix) = ", :" :: showindices ix ∧
    showargSubArray parent ix T true = ["view("] ++ parent ++ showindices ix ++ [")", " with eltype ", T] ∧
    showargSubArray parent ix T false = ["view("] ++ parent ++ showindices ix ++ [")"] ∧
    showargReshaped parent [] T false = ["reshape("] ++ parent ++ [")"] ∧
    showargReinterpret T parent = ["reinterpret(", T, ", "] ++ parent ++ [")"] ∧
    showargReinterpretReshape T parent P top =
      ["reinterpret(reshape, ", T, ", "] ++ parent ++ [")"] ++ (if top then [" with eltype ", P] else []) ∧
    showargPairsArray T = ["pairs(IndexLinear(), ::", T, ")"] ∧
    showargPairsNamedTuple = ["pairs(::NamedTuple)"] ∧
    showargPairsGeneric D I = ["Iterators.Pairs(::", D, ", ::", I, ")"]

theorem summarySpec_proven : SummarySpec := by
  intro n a b rest inds s t T P D I len off top parent ix dims
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · intro h; simp [arraySummary, h]
  · intro h; simp [arraySummary, h]
  · simp [showargSubArray]
  · simp [showargSubArray]
  · simp [showargReshaped]

/-! ## Bit chunks -/

theorem filter_flatMap_bits {α : Type} (l : List α) (g : α → Char) (sp : α → List Char) (p : Char → Bool)
    (hg : ∀ a, p (g a) = true) (hs : ∀ a, ∀ c ∈ sp a, p c = false) :
    (l.flatMap (fun a => [g a] ++ sp a)).filter p = l.map g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.flatMap_cons, List.filter_append, ih, List.map_cons]
    have : (sp a).filter p = [] := List.filter_eq_nil_iff.mpr (fun c hc => by simp [hs a c hc])
    simp [List.filter_append, hg a, this]

def isBitChar (c : Char) : Bool := c = '0' || c = '1'

/-- `print_bit_chunk(io, c, l)` prints bit `s` of `c` for `s = 0..l-1`, with a
space after every eighth; `bitstring(B)` of a `BitArray` with at most 64
elements prints the bits of `B` in index order (`base/show.jl:3415-3440`). -/
def BitChunkSpec : Prop :=
  ∀ (c len : Nat), len ≤ 64 →
    (printBitChunk c len).filter isBitChar = (List.range len).map (fun s => if (c / 2 ^ s) % 2 = 1 then '1' else '0') ∧
    (bitshow [c] len).filter isBitChar = bitsOf [c] len

theorem bitChunkSpec_proven : BitChunkSpec := by
  intro c len hl
  have h1 : ∀ l, (printBitChunk c l).filter isBitChar =
      (List.range l).map (fun s => if (c / 2 ^ s) % 2 = 1 then '1' else '0') := by
    intro l
    unfold printBitChunk
    apply filter_flatMap_bits
    · intro a; by_cases h : (c / 2 ^ a) % 2 = 1 <;> simp [isBitChar, h]
    · intro a ch hc; by_cases h : (a + 1) % 8 = 0 <;> simp [h] at hc; subst hc; rfl
  refine ⟨h1 len, ?_⟩
  unfold bitshow bitsOf
  by_cases h0 : len = 0
  · subst h0; rfl
  · have hlen : (len - 1) % 64 + 1 = len := by omega
    have hc : [c].getLastD 0 = c := rfl
    simp only [h0, if_false, List.dropLast_singleton, List.flatMap_nil, List.nil_append, hc, hlen, h1]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    have h1 : i / 64 = 0 := by omega
    have h2 : i % 64 = i := by omega
    simp [h1, h2]

/-! ## `dump` -/

theorem dumpLines_depth (n d : Nat) (x : DV) : ∀ l ∈ dumpLines n d x, d ≤ l.1 ∧ l.1 ≤ d + n := by
  induction n generalizing d x with
  | zero =>
    cases x <;> simp [dumpLines]
  | succ n ih =>
    cases x with
    | leaf s => simp [dumpLines]
    | func s => simp [dumpLines]
    | node hd fs =>
      intro l hl
      simp only [dumpLines, List.mem_cons, List.mem_flatMap] at hl
      rcases hl with rfl | ⟨⟨⟨name, v⟩, _⟩, _, hl⟩
      · simp
      · cases v with
        | none => simp at hl; subst hl; simp
        | some v => have := ih (d + 1) v l hl; omega

/-- `dump(x; maxdepth)` nests every line at most `maxdepth` levels deep; with
`:limit`, an array of more than 10 elements shows elements `1:5` and the last
five, and all indices otherwise; the one-line methods prefix `Module`,
`String`, `Symbol`; a `DataType` header says `mutable struct`/`struct` except
for tuples and names the supertype unless it is `Any`
(`base/show.jl:2990-3167`). -/
def DumpSpec : Prop :=
  ∀ (m lx : Nat) (x : DV) (s t : String),
    (∀ l ∈ dumpTop m x, l.1 ≤ m) ∧
    (lx > 10 → dumpArrayIndices true lx = [1, 2, 3, 4, 5] ++ (List.range 5).map (· + (lx - 4))) ∧
    (lx ≤ 10 → dumpArrayIndices true lx = (List.range lx).map (· + 1)) ∧
    dumpArrayIndices false lx = (List.range lx).map (· + 1) ∧
    dumpModule s = "Module " ++ s ∧ dumpString s = "String " ++ s ∧ dumpSymbol s = "Symbol " ++ s ∧
    dumpUnion s = s ∧ dumpPtr s = s ∧
    dumpSvecHeader true = "empty SimpleVector" ∧ dumpSvecHeader false = "SimpleVector" ∧
    dumpTypeHeader true true false false false false s t = "mutable struct " ++ s ++ " <: " ++ t ∧
    dumpTypeHeader true false true false false false s t = s ++ " <: " ++ t ∧
    dumpTypeHeader false false false false true true s t = "abstract type " ++ s

theorem dumpSpec_proven : DumpSpec := by
  intro m lx x s t
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro l hl; have := dumpLines_depth m 0 x l hl; omega
  · intro h
    have h' : ¬ lx ≤ 10 := by omega
    simp [dumpArrayIndices, h, h']; rfl
  · intro h; simp [dumpArrayIndices, h]
  · simp [dumpArrayIndices]
  · simp [dumpTypeHeader, String.append_assoc]
  · simp [dumpTypeHeader, String.append_assoc]
  · simp [dumpTypeHeader, String.append_assoc]

/-! ## `alignment` -/

def noAlignMark (c : Char) : Bool := c ∉ ['.', 'e', 'E', 'f', 'F']

/-- `alignment(io, x::Real)` puts the integer part left of the alignment point
and everything from the decimal point on to the right
(`base/show.jl:3175-3199`, docstring: "alignment feature such as a decimal
point"). -/
def AlignmentDecimal : Prop :=
  ∀ (tw : Char → Nat) (a b : List Char), (∀ c ∈ a, noAlignMark c = true) →
    alignmentReal tw (a ++ '.' :: b) = (((a.map tw).sum : Int), ((('.' :: b).map tw).sum : Int))

theorem alignmentDecimal_proven : AlignmentDecimal := by
  intro tw a b ha
  have h1 : (a ++ '.' :: b).takeWhile noAlignMark = a := by
    rw [List.takeWhile_append_of_pos ha]; simp [noAlignMark]
  have h2 : (a ++ '.' :: b).dropWhile noAlignMark = '.' :: b := by
    rw [List.dropWhile_append_of_pos ha]; simp [noAlignMark]
  simp only [alignmentReal, splitRealAt]
  have e1 : (a ++ '.' :: b).takeWhile (fun c => decide (c ∉ ['.', 'e', 'E', 'f', 'F'])) = a := h1
  have e2 : (a ++ '.' :: b).dropWhile (fun c => decide (c ∉ ['.', 'e', 'E', 'f', 'F'])) = '.' :: b := h2
  rw [e1, e2]

/-- A value printed without a decimal point or exponent, such as `Inf`, `-Inf`
or `NaN`, is aligned as a whole on the left, like an integer; the docstring
places the alignment point at "a decimal point". Refuted: `Inf` is split at its
final `f` (`base/show.jl:3196`). -/
def AlignmentInf : Prop :=
  ∀ (tw : Char → Nat), ∀ s ∈ [['I', 'n', 'f'], ['-', 'I', 'n', 'f'], ['N', 'a', 'N']],
    alignmentReal tw s = (((s.map tw).sum : Int), (0 : Int))

theorem alignmentInf_refuted : ¬ AlignmentInf := by
  intro h
  have := h (fun _ => 1) ['I', 'n', 'f'] (by simp)
  revert this; decide

theorem splitRational_spec (a b : List Char) (ha : '/' ∉ a) :
    splitRational (a ++ '/' :: '/' :: b) = some (a ++ ['/'], '/' :: b) := by
  induction a with
  | nil => simp [splitRational]
  | cons c cs ih =>
    have hc : c ≠ '/' := fun h => ha (by simp [h])
    have hcs : '/' ∉ cs := fun h => ha (by simp [h])
    cases cs with
    | nil => simp [splitRational, hc]
    | cons d ds =>
      simp only [List.cons_append] at ih ⊢
      simp only [splitRational, hc, false_and, if_false, ih hcs]
      simp

/-- `alignment(io, x::Rational)` splits `n//d` after the first `/` of `//`, so
the numerator and first slash are left of the alignment point; `Pair`
alignment adds up to the full width; `nocolor` sets `:color => false`; the
`Any`/`Number` methods put all width on one side (`base/show.jl:3169-3224`). -/
def AlignmentParts : Prop :=
  ∀ (tw : Char → Nat) (a b : List Char) (w fw : Nat) (full first : Int) (d fd c : Bool)
    (props : List (String × String)),
    '/' ∉ a →
    alignmentRational tw (a ++ '/' :: '/' :: b) =
      ((((a ++ ['/']).map tw).sum : Int), ((('/' :: b).map tw).sum : Int)) ∧
    (alignmentPair full d first fd c).1 + (alignmentPair full d first fd c).2 = full ∧
    nocolor props = ("color", "false") :: props ∧
    alignmentAny w = ((0 : Int), (w : Int)) ∧ alignmentNumber w = ((w : Int), (0 : Int))

theorem alignmentParts_proven : AlignmentParts := by
  intro tw a b w fw full first d fd c props ha
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · simp [alignmentRational, splitRational_spec a b ha]
  · cases d <;> simp [alignmentPair] <;> omega

end JuliaLean.ShowCov
