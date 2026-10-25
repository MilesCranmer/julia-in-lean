import JuliaLean.RegexUnicode.UniBasic

/-!
# `isequal_normalized`, `stdlib/Unicode/src/Unicode.jl:218-345`

Model of `_isequal_normalized!` and its local function `decompose_next_chars!`
(master `bbfa0ce4150`; identical in 1.13.2).

* String iteration: `iterate(s)` and `iterate(s, state[2])` produce the characters
  of `collect(s)` in order, so an iteration state is the list of the characters not
  yet read (`chars s`, then its tails); `nothing` is the empty list and
  `state[1]` is the head.
* A `Vector{UInt32}` is `Buf`: its length and the memory it reads. `Vector{UInt32}(undef, 4)`
  has arbitrary contents, so the memory is a parameter; `resize!` changes the length
  and exposes whatever the memory holds beyond the old end; `@inbounds d[0]` reads
  the memory at position `0` (the out-of-bounds read of `d[n]` when `n == 0`).
* Buffer positions `n`, `offset`, `j1`, `j2` are `Int` in Julia; they are bounded by
  the total decomposition length of a string held in memory, so they are `Nat` here.
* utf8proc is the primitive `Utf8proc.decomposeChar` (`utf8proc_decompose_char`) and
  `Utf8proc.combiningClass`.
-/

namespace JuliaLean.RegexUnicode.Uni

open JuliaLean JuliaLean.Strings

/-- A `Vector{UInt32}`: `len` is `length(d)`; `mem k` is what `@inbounds d[k]` reads. -/
structure Buf where
  len : Nat
  mem : Nat → UInt32

/-- `@inbounds d[k]`. -/
def Buf.get (d : Buf) (k : Nat) : UInt32 := d.mem k

/-- `d[k] = v`. -/
def Buf.set (d : Buf) (k : Nat) (v : UInt32) : Buf :=
  { d with mem := fun i => if i = k then v else d.mem i }

/-- `resize!(d, m)`: new elements are uninitialized, i.e. whatever the memory holds. -/
def Buf.resize (d : Buf) (m : Nat) : Buf := { d with len := m }

/-- `d[a], d[b] = d[b], d[a]`. -/
def Buf.swap (d : Buf) (a b : Nat) : Buf := (d.set a (d.get b)).set b (d.get a)

/-- Store the first `room` elements of a list at positions `p+1, p+2, ...`. -/
def Buf.writeList (d : Buf) (p : Nat) : List UInt32 → Nat → Buf
  | [], _ => d
  | _ :: _, 0 => d
  | v :: l, r + 1 => (d.set (p + 1) v).writeList (p + 1) l r

/-- `combining_class(uc::Integer)`, `stdlib/Unicode/src/Unicode.jl:227-228`. -/
def ccOf (P : Utf8proc) (uc : UInt32) : Nat :=
  if decide (0x301 ≤ uc) && decide (uc ≤ 0x10ffff) then (P.combiningClass uc).toNat else 0

/-- `_decompose_char!(codepoint, dest, offset, options)`,
`stdlib/Unicode/src/Unicode.jl:218-222`: `utf8proc_decompose_char` with
`bufsize = length(dest) - offset` writes from `dest[offset+1]`; a negative result is
passed to `utf8proc_error`, which throws `ErrorException`. -/
def decomposeCharBang (P : Utf8proc) (c : UInt32) (d : Buf) (offset options : Nat) :
    UJl (Nat × Buf) :=
  match P.decomposeChar c options with
  | .error _ => .error .errorException
  | .ok l => .ok (l.length, d.writeList offset l (d.len - offset))

/-- The inner `while true` loop of `decompose_next_chars!`,
`stdlib/Unicode/src/Unicode.jl:291-298`: decompose, and if the result does not fit,
`resize!(d, 2n)` and decompose again. The bound `2` suffices: the second call returns
the same `n ≤ 2n`. -/
def decomposeRetry (P : Utf8proc) (c : UInt32) (offset options : Nat) : Nat → Buf → UJl (Nat × Buf)
  | 0, _ => .error .fuel
  | f + 1, d =>
    match decomposeCharBang P c d offset options with
    | .error e => .error e
    | .ok (ret, d) =>
      let n := ret + offset
      if n > d.len then decomposeRetry P c offset options f (d.resize (2 * n))
      else .ok (n, d)

/-- The `@inbounds while true` loop of `decompose_next_chars!`,
`stdlib/Unicode/src/Unicode.jl:280-304`. `ch` is `state[1]` and `rest` the state after
`state = iterate(s, state[2])`. Returns `n`, the buffer and the state. -/
def chunkLoop (P : Utf8proc) (casefold : Bool) (options : Nat) (ct : UInt32 → UInt32) :
    List UInt32 → UInt32 → Nat → Buf → UJl (Nat × Buf × List UInt32)
  | rest, ch, offset, d =>
    match codepoint ch with
    | .error e => .error (.str e)
    | .ok u =>
      let c := ct u
      if c < 0x80 then
        let n := 1 + offset
        let d := if n > d.len then d.resize (2 * n) else d
        .ok (n, d.set n (if casefold then (if inRange 0x41 0x5a c then c + 0x20 else c) else c), rest)
      else
        match decomposeRetry P c offset options 2 d with
        | .error e => .error e
        | .ok (n, d) =>
          if ccOf P (d.get n) == 0 then .ok (n, d, rest)
          else
            match rest with
            | [] => .ok (n, d, [])
            | ch' :: rest' => chunkLoop P casefold options ct rest' ch' n d

/-- `for j2 = j1:-1:2; combining_class(d[j2-1]) ≤ cc && break; swap; end`,
`stdlib/Unicode/src/Unicode.jl:311-314`, at `j2 = k + 2`. -/
def insInner (P : Utf8proc) (cc : Nat) : Nat → Buf → Buf
  | k + 2, d =>
    if ccOf P (d.get (k + 1)) ≤ cc then d
    else insInner P cc (k + 1) (d.swap (k + 1) (k + 2))
  | _, d => d

/-- `for j1 = 2:n`, `stdlib/Unicode/src/Unicode.jl:308-315`; `k` iterations remain. -/
def insOuter (P : Utf8proc) : Nat → Nat → Buf → Buf
  | 0, _, d => d
  | k + 1, j1, d =>
    let cc := ccOf P (d.get j1)
    let d := if cc == 0 then d else insInner P cc j1 d
    insOuter P k (j1 + 1) d

/-- The insertion sort for `n < 32`, `stdlib/Unicode/src/Unicode.jl:307-316`. -/
def insertionSort (P : Utf8proc) (n : Nat) (d : Buf) : Buf := insOuter P (n - 1) 2 d

/-- `j₀ = j + something(findnext(iszero ∘ combining_class, d[j+1:n], 1), n+1-j)`
(`stdlib/Unicode/src/Unicode.jl:320`): the first position `p` in `j+1:n` with a zero
combining class, else `n + 1`. `k` bounds the positions left to scan. -/
def scanZero (P : Utf8proc) (d : Buf) (n : Nat) : Nat → Nat → Nat
  | 0, _ => n + 1
  | k + 1, p => if p > n then n + 1 else if ccOf P (d.get p) == 0 then p else scanZero P d n k (p + 1)

/-- Insert `x` before the first element whose key is not smaller. -/
def insertByKey (key : UInt32 → Nat) (x : UInt32) : List UInt32 → List UInt32
  | [] => [x]
  | y :: ys => if key x ≤ key y then x :: y :: ys else y :: insertByKey key x ys

/-- Stable sort by `key`: the unique stable ordering every algorithm `sort!` selects. -/
def stableSortBy (key : UInt32 → Nat) : List UInt32 → List UInt32
  | [] => []
  | x :: xs => insertByKey key x (stableSortBy key xs)

/-- `d[p], d[p+1], ..., d[p+len-1]`. -/
def Buf.readList (d : Buf) (p : Nat) : Nat → List UInt32
  | 0 => []
  | len + 1 => d.get p :: d.readList (p + 1) len

/-- Store a list at `p, p+1, ...`. -/
def Buf.writeAt (d : Buf) (p : Nat) : List UInt32 → Buf
  | [] => d
  | v :: l => (d.set p v).writeAt (p + 1) l

/-- `sort!(d[j:j₀-1], by=combining_class)` on the view. -/
def sortRange (P : Utf8proc) (d : Buf) (j j0 : Nat) : Buf :=
  d.writeAt j (stableSortBy (ccOf P) (d.readList j (j0 - j)))

/-- `j = 1; while j < n ... end`, `stdlib/Unicode/src/Unicode.jl:318-324`; `j₀ > j`, so
`n` iterations suffice. -/
def segLoop (P : Utf8proc) (n : Nat) : Nat → Nat → Buf → Buf
  | 0, _, d => d
  | f + 1, j, d =>
    if j < n then
      let j0 := scanZero P d n (n - j) (j + 1)
      segLoop P n f j0 (sortRange P d j j0)
    else d

/-- `decompose_next_chars!(state, d, options, s)`, `stdlib/Unicode/src/Unicode.jl:277-327`:
returns `n` and the next state; the caller sets `j = 1`. -/
def decomposeNext (P : Utf8proc) (casefold : Bool) (options : Nat) (ct : UInt32 → UInt32)
    (ch : UInt32) (rest : List UInt32) (d : Buf) : UJl (Nat × Buf × List UInt32) :=
  match chunkLoop P casefold options ct rest ch 0 d with
  | .error e => .error e
  | .ok (n, d, st) =>
    .ok (n, if n < 32 then insertionSort P n d else segLoop P n n 1 d, st)

/-- The `while true` loop of `_isequal_normalized!`,
`stdlib/Unicode/src/Unicode.jl:333-344`, with iteration bound `f`. -/
def isEqLoop (P : Utf8proc) (casefold : Bool) (options : Nat) (ct : UInt32 → UInt32) :
    Nat → Buf → Nat → Nat → List UInt32 → Buf → Nat → Nat → List UInt32 → UJl Bool
  | 0, _, _, _, _, _, _, _, _ => .error .fuel
  | f + 1, d1, n1, j1, i1, d2, n2, j2, i2 =>
    let side2 (d1 : Buf) (n1 j1 : Nat) (i1 : List UInt32) : UJl Bool :=
      let cmp (d2 : Buf) (n2 j2 : Nat) (i2 : List UInt32) : UJl Bool :=
        if d1.get j1 != d2.get j2 then .ok false
        else isEqLoop P casefold options ct f d1 n1 (j1 + 1) i1 d2 n2 (j2 + 1) i2
      if j2 > n2 then
        match i2 with
        | [] => .ok false
        | c :: r =>
          match decomposeNext P casefold options ct c r d2 with
          | .error e => .error e
          | .ok (n2, d2, i2) => cmp d2 n2 1 i2
      else cmp d2 n2 j2 i2
    if j1 > n1 then
      match i1 with
      | [] => .ok (i2.isEmpty && decide (j2 > n2))
      | c :: r =>
        match decomposeNext P casefold options ct c r d1 with
        | .error e => .error e
        | .ok (n1, d1, i1) => side2 d1 n1 1 i1
    else side2 d1 n1 j1 i1

/-- The number of code points `decompose_next_chars!` stores for one character. -/
def dlen (P : Utf8proc) (options : Nat) (ct : UInt32 → UInt32) (ch : UInt32) : Nat :=
  match codepoint ch with
  | .error _ => 0
  | .ok u =>
    if ct u < 0x80 then 1
    else match P.decomposeChar (ct u) options with
      | .ok l => l.length
      | .error _ => 0

/-- Iteration bound of the main loop: each iteration that does not return advances
`j1` within a chunk of at least one character, so `Σ (dlen + 1) + 1` suffices. -/
def loopBound (P : Utf8proc) (options : Nat) (ct : UInt32 → UInt32) : List UInt32 → Nat
  | [] => 1
  | c :: cs => dlen P options ct c + 1 + loopBound P options ct cs

/-- The options of `_isequal_normalized!`, `stdlib/Unicode/src/Unicode.jl:328-330`. -/
def eqOptions (casefold stripmark : Bool) : Nat :=
  orIf stripmark (orIf casefold DECOMPOSE CASEFOLD) STRIPMARK

/-- `isequal_normalized(s1, s2; casefold, stripmark, chartransform = ct)` =
`_isequal_normalized!(s1, s2, Vector{UInt32}(undef, 4), Vector{UInt32}(undef, 4), ct; ...)`,
`stdlib/Unicode/src/Unicode.jl:270-345`. `mem1`, `mem2` are the uninitialized memory
of the two buffers. -/
def isequalNormalized (P : Utf8proc) (mem1 mem2 : Nat → UInt32) (s1 s2 : JStr)
    (casefold stripmark : Bool) (ct : UInt32 → UInt32 := id) : UJl Bool :=
  let options := eqOptions casefold stripmark
  isEqLoop P casefold options ct (loopBound P options ct (chars s1))
    ⟨4, mem1⟩ 0 1 (chars s1) ⟨4, mem2⟩ 0 1 (chars s2)

/-! ## Specification: canonical decomposition -/

/-- Decompose every character with `utf8proc_decompose_char` and concatenate. -/
def decompAll (P : Utf8proc) (options : Nat) : List UInt32 → UJl (List UInt32)
  | [] => .ok []
  | ch :: cs =>
    match codepoint ch with
    | .error e => .error (.str e)
    | .ok u =>
      match P.decomposeChar u options with
      | .error _ => .error .errorException
      | .ok l =>
        match decompAll P options cs with
        | .error e => .error e
        | .ok rest => .ok (l ++ rest)

/-- Canonical ordering (Unicode §3.11): stable sort of every maximal run of code points
with nonzero combining class. `run` is the current run. -/
def canonAux (P : Utf8proc) (run : List UInt32) : List UInt32 → List UInt32
  | [] => stableSortBy (ccOf P) run
  | x :: xs =>
    if ccOf P x == 0 then stableSortBy (ccOf P) run ++ x :: canonAux P [] xs
    else canonAux P (run ++ [x]) xs

/-- `normalize(s; decompose=true, casefold, stripmark)` as code points: per-character
decomposition concatenated, then canonical ordering. -/
def nfdSpec (P : Utf8proc) (casefold stripmark : Bool) (s : JStr) : UJl (List UInt32) :=
  match decompAll P (eqOptions casefold stripmark) (chars s) with
  | .error e => .error e
  | .ok l => .ok (canonAux P [] l)

/-- Every character converts to a code point below `0x110000`. -/
def validCps (s : JStr) : Bool :=
  (chars s).all fun c => match codepoint c with
    | .ok u => decide (u < 0x110000)
    | .error _ => false

/-- Documented behaviour of `utf8proc_decompose_char` used here: without `REJECTNA` it
succeeds on every code point; without `STRIPMARK` the decomposition is nonempty; an
ASCII code point decomposes to itself, lowercased under `CASEFOLD`. -/
structure Utf8proc.DecompAxioms (P : Utf8proc) : Prop where
  ok : ∀ u opts, u < 0x110000 → opts.testBit 6 = false → ∃ l, P.decomposeChar u opts = .ok l
  nonempty : ∀ u opts l, opts.testBit 13 = false → P.decomposeChar u opts = .ok l → l ≠ []
  ascii : ∀ u opts, u < 0x80 →
    P.decomposeChar u opts = .ok [if opts.testBit 10 && inRange 0x41 0x5a u then u + 0x20 else u]

/-- Property (`isequal_normalized` docstring, `stdlib/Unicode/src/Unicode.jl:230-268`:
whether `s1` and `s2` are canonically equivalent, with case folding and mark stripping
as in `normalize`): for strings of code points, the result is the comparison of the
canonical decompositions. -/
def IsequalNormalizedSpec : Prop :=
  ∀ P : Utf8proc, P.DecompAxioms → ∀ (mem1 mem2 : Nat → UInt32) (s1 s2 : JStr)
    (casefold stripmark : Bool), validCps s1 = true → validCps s2 = true →
    ∃ a b, nfdSpec P casefold stripmark s1 = .ok a ∧ nfdSpec P casefold stripmark s2 = .ok b ∧
      isequalNormalized P mem1 mem2 s1 s2 casefold stripmark = .ok (decide (a = b))

/-! ## A utf8proc table for `a`, `e`, `s`, `ß`, `é` and U+0301 -/

/-- `é = U+00E9 ↦ e U+0301`; U+0301 (combining acute, class 230) is stripped by
`STRIPMARK`; `ß = U+00DF ↦ ss` under `CASEFOLD`; other code points map to themselves;
code points from `0x110000` are rejected (`UTF8PROC_ERROR_NOTASSIGNED = -4`). -/
def tblDecompose (u : UInt32) (opts : Nat) : Except Int (List UInt32) :=
  let n := u.toNat
  if n ≥ 0x110000 then .error (-4)
  else if n < 0x80 then .ok [if opts.testBit 10 && inRange 0x41 0x5a u then u + 0x20 else u]
  else if n = 0xE9 then .ok (if opts.testBit 13 then [0x65] else [0x65, 0x301])
  else if n = 0x301 then .ok (if opts.testBit 13 then [] else [0x301])
  else if n = 0xDF then .ok (if opts.testBit 10 then [0x73, 0x73] else [0xDF])
  else .ok [u]

def tbl : Utf8proc where
  toupper := id
  tolower := id
  totitle := id
  category := fun _ => 0
  gbStateful := fun _ _ _ => (true, 0)
  decomposeChar := tblDecompose
  combiningClass := fun u => if u.toNat = 0x301 then 230 else 0

theorem tbl_axioms : tbl.DecompAxioms where
  ok u opts h _ := by
    have h' : ¬ u.toNat ≥ 0x110000 := by rw [UInt32.lt_iff_toNat_lt] at h; simpa using h
    simp only [tbl, tblDecompose, h', if_false]
    repeat (first | exact ⟨_, rfl⟩ | split)
  nonempty u opts l h hl := by
    intro hnil
    subst hnil
    simp only [tbl, tblDecompose] at hl
    repeat' split at hl
    all_goals simp_all
  ascii u opts h := by
    have h' : u.toNat < 0x80 := by rw [UInt32.lt_iff_toNat_lt] at h; simpa using h
    have h'' : ¬ u.toNat ≥ 0x110000 := by omega
    simp only [tbl, tblDecompose, h', h'', if_false, if_true]

/-- `"a\u0301"` and `"aa"`. -/
def strAacute : JStr := ⟨[0x61, 0xcc, 0x81], by decide⟩
def strAA : JStr := ⟨[0x61, 0x61], by decide⟩

/-- `r` returned `b`. -/
def resIs (r : UJl Bool) (b : Bool) : Bool :=
  match r with
  | .ok x => x == b
  | .error _ => false

theorem resIs_eq {r : UJl Bool} {b : Bool} (h : resIs r b = true) : r = .ok b := by
  unfold resIs at h
  split at h
  · simp at h; subst h; rfl
  · cases h

/-- With `stripmark=true`, U+0301 decomposes to nothing: `decompose_next_chars!` returns
`n = 0`, the main loop compares the stale `d1[1] = 'a'` with the second `'a'` of `"aa"`
and returns `true`; the decompositions are `"a"` and `"aa"`. -/
theorem isequalNormalizedSpec_refuted : ¬ IsequalNormalizedSpec := by
  intro h
  obtain ⟨a, b, ha, hb, he⟩ :=
    h tbl tbl_axioms (fun _ => 0) (fun _ => 0) strAacute strAA false true (by decide) (by decide)
  have ea : nfdSpec tbl false true strAacute = .ok [0x61] := by rfl
  have eb : nfdSpec tbl false true strAA = .ok [0x61, 0x61] := by rfl
  have ee : isequalNormalized tbl (fun _ => 0) (fun _ => 0) strAacute strAA false true = .ok true :=
    resIs_eq (by decide +kernel)
  rw [ea] at ha; rw [eb] at hb; rw [ee] at he
  cases ha; cases hb
  simp at he

/-! ## The other observed cases (`regexunicode-isequal-normalized-stripmark` reproducer) -/

def strCafeAcute : JStr := ⟨[0x63, 0x61, 0x66, 0x65, 0xcc, 0x81], by decide⟩
def strCafe : JStr := ⟨[0x63, 0x61, 0x66, 0x65], by decide⟩
def strCafee : JStr := ⟨[0x63, 0x61, 0x66, 0x65, 0x65], by decide⟩
def strAcute : JStr := ⟨[0xcc, 0x81], by decide⟩
def strEmpty : JStr := ⟨[], by decide⟩

/-- `isequal_normalized("cafe\u0301", "cafe"; stripmark=true) == false`,
`isequal_normalized("cafe\u0301", "cafee"; stripmark=true) == true`,
`isequal_normalized("\u0301", ""; stripmark=true) == false`, as Julia prints. -/
theorem stripmark_observed :
    isequalNormalized tbl (fun _ => 0) (fun _ => 0) strCafeAcute strCafe false true = .ok false ∧
    isequalNormalized tbl (fun _ => 0) (fun _ => 0) strCafeAcute strCafee false true = .ok true ∧
    isequalNormalized tbl (fun _ => 0) (fun _ => 0) strAcute strEmpty false true = .ok false :=
  ⟨resIs_eq (by decide +kernel), resIs_eq (by decide +kernel), resIs_eq (by decide +kernel)⟩

/-- `isequal_normalized("\u0301", "\u0301"; stripmark=true)` compares `d1[1]` and `d2[1]`,
which no call wrote: the result depends on the uninitialized buffer contents. -/
theorem stripmark_uninit :
    isequalNormalized tbl (fun _ => 0) (fun _ => 0) strAcute strAcute false true = .ok true ∧
    isequalNormalized tbl (fun _ => 0) (fun _ => 1) strAcute strAcute false true = .ok false :=
  ⟨resIs_eq (by decide +kernel), resIs_eq (by decide +kernel)⟩

end JuliaLean.RegexUnicode.Uni
