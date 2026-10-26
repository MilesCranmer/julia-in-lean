import JuliaLean.StringsCovB.AIO

/-!
# Properties of the `AnnotatedIOBuffer` methods

`base/strings/annotated_io.jl` (master `bbfa0ce4150`).
-/

namespace JuliaLean.StringsCovB.AIO

open JuliaLean JuliaLean.Strings JuliaLean.StringsCovB.Ann
open JuliaLean.IOBuffers (IOBuf IOErr)

/-- An `IOBuffer` holding `bs` (as after writing them), positioned at `ptr`. -/
def bufOf (bs : List UInt8) (ptr : Int) : IOBuf :=
  ⟨bs, true, false, true, true, true, false, ix bs.length, ix (2 ^ 63 - 1), ix ptr, ix 0, ix (-1)⟩

/-! ## Proven -/

/-- The forwarding methods: `pipe_reader`/`pipe_writer` are `io.io`;
`position`, `seek`, `seekend`, `skip` run the `IOBuffer` method on `io.io` and keep
the annotations; `copy` copies
`io.io` and the annotations; `annotations(io)` is the vector; and
`annotate!(io, range, label, value)` appends exactly that annotation. -/
def ForwardContract : Prop :=
  (∀ a, pipeReader a = a.io ∧ pipeWriter a = a.io ∧ position a = IOBuffers.position a.io) ∧
  (∀ n, seek n = onIO (IOBuffers.seekAny n)) ∧ seekend = onIO IOBuffers.seekend ∧
  (∀ n, skip n = onIO (IOBuffers.skip n)) ∧
  (∀ c a, copyAIO c a = ⟨c a.io, a.anns⟩) ∧
  (∀ a, annotationsIO a = a.anns) ∧
  (∀ r l (n : Nat) a, (annotateIO r l (some n)).run a =
    .ok () { a with anns := a.anns ++ [⟨r.1, r.2, l, some n⟩] })

theorem forwardContract : ForwardContract :=
  ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ => rfl, rfl, fun _ => rfl, fun _ _ => rfl,
   fun _ => rfl, fun _ _ _ _ => rfl⟩

/-- `_clear_annotations_in_region!` keeps every nonempty annotation disjoint from
a nonempty `span` unchanged. -/
def ClearRegionContract : Prop :=
  ∀ (anns : List RA) (span : Region) (x : RA), x ∈ anns → x.lo.val ≤ x.hi.val →
    span.1.val ≤ span.2.val → (x.hi.val < span.1.val ∨ span.2.val < x.lo.val) →
    x ∈ clearRegion anns span

theorem clearRegionContract : ClearRegionContract := by
  intro anns span x hx hlh hs hd
  unfold clearRegion
  refine List.mem_flatMap.mpr ⟨x, List.mem_filter.mpr ⟨hx, ?_⟩, ?_⟩
  · simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  · unfold clearOne
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by simp only [RA.region]; omega))]
    exact List.mem_singleton_self _

/-! ## Refuted -/

/-- `true` when the annotations of the buffer are unchanged, or the call threw. -/
def annsSame (a : AIO) {α : Type} : EStateM.Result AErr AIO α → Bool
  | .ok _ a' => a'.anns == a.anns
  | .error _ _ => true

/-- Writing an empty `AnnotatedString` writes nothing and leaves the
annotations of the buffer unchanged. -/
def WriteEmptyKeeps : Prop :=
  ∀ a : AIO, annsSame a ((writeW (.str ⟨JStr.empty, []⟩)).run a) = true

/-- The buffer `"abcde"` with `1:5 => :s`, positioned after two code units. -/
def bufAbcde (ptr : Int) : AIO := ⟨bufOf [0x61, 0x62, 0x63, 0x64, 0x65] ptr, [⟨ix 1, ix 5, 0, some 1⟩]⟩

theorem writeEmptyKeeps_refuted : ¬ WriteEmptyKeeps := by
  intro h
  have := h (bufAbcde 3)
  revert this
  decide +kernel

/-- `true` when the annotations of `dest` ending at or before its position are
still present, or the call threw. -/
def keepsBeforeW (dest : AIO) : Except AErr (JInt64 × AIO × AIO) → Bool
  | .ok (_, d', _) => dest.anns.all fun x => !decide (x.hi.val ≤ (position dest).val) || d'.anns.contains x
  | .error _ => true

/-- `write(dest::AnnotatedIOBuffer, src::AnnotatedIOBuffer)` overwrites the code
units from `position(dest) + 1` on, like `write(dest, ::AnnotatedString)`, so
annotations of `dest` ending at or before `position(dest)` are kept. -/
def WriteAioKeepsBefore : Prop :=
  ∀ dest src : AIO, keepsBeforeW dest (writeAIO dest src) = true

/-- `"XYZW"` with `1:1 => :p`, `2:4 => :d`, after `seek(io, 1)`. -/
def bufXYZW : AIO := ⟨bufOf [0x58, 0x59, 0x5a, 0x57] 2, [⟨ix 1, ix 1, 0, some 1⟩, ⟨ix 2, ix 4, 1, some 2⟩]⟩

theorem writeAioKeepsBefore_refuted : ¬ WriteAioKeepsBefore := by
  intro h
  have := h bufXYZW (bufAbcde 1)
  revert this
  decide +kernel

/-- `true` when every annotation of `src` that covers a code unit at or after the
read position has its label and value in the result, or the call threw. -/
def carries (src : AIO) : Except AErr (JInt64 × AIO × AIO) → Bool
  | .ok (_, d', _) => src.anns.all fun x =>
      !decide ((position src).val < x.hi.val) || d'.anns.any fun y => y.label == x.label && y.value == x.value
  | .error _ => true

/-- `write(dest, src::AnnotatedIOBuffer)` copies the readable code units of `src`
"along with their annotations" (`base/strings/annotated_io.jl:50-60`). -/
def WriteAioCarries : Prop :=
  ∀ dest src : AIO, carries src (writeAIO dest src) = true

theorem writeAioCarries_refuted : ¬ WriteAioCarries := by
  intro h
  have := h ⟨bufOf [0x58, 0x59] 3, [⟨ix 1, ix 2, 1, some 2⟩]⟩ (bufAbcde 3)
  revert this
  decide +kernel

/-! ## Construction, plain writes, reading, truncation and display -/

theorem onIO_anns {α : Type} (m : IOBuffers.M α) (a : AIO) :
    annsSame a ((onIO m).run a) = true := by
  unfold onIO
  simp only [EStateM.run]
  split <;> simp [annsSame]

/-- `AnnotatedIOBuffer(io)` starts without annotations and `AnnotatedIOBuffer()` wraps
`IOBuffer()`; `show` prints the type, the byte count and the annotation count with
singular/plural words; writing a plain string or a byte (`:45-48`) leaves the
annotations unchanged; writing to an `AbstractPipe` whose writer is not an
`AnnotatedIOBuffer` writes the unannotated code units (`:64-79`); `printstyled`
without methods throws `MethodError`. -/
def BufferContract : Prop :=
  (∀ io, (ofIO io).anns = [] ∧ (ofIO io).io = io) ∧
  (empty = IOBuffers.iobuffer.map ofIO) ∧
  (∀ t a, showAIO t a = t ++ "(" ++ toString (IOBuffers.filesize a.io).val ++ " byte" ++
    (if (IOBuffers.filesize a.io).val = 1 then "" else "s") ++ ", " ++ toString a.anns.length ++
    " annotation" ++ (if a.anns.length = 1 then "" else "s") ++ ")") ∧
  (∀ bs a, annsSame a ((writePlain bs).run a) = true) ∧
  (∀ b a, annsSame a ((writeByte b).run a) = true) ∧
  (∀ out (x : WArg), writePipe (.other out) x = .ok (ix (dBytes (.w x)).length, .other (out ++ dBytes (.w x)))) ∧
  (∀ out c, writePipeC (.other out) c = .ok (ix (charBytes c.char).length, .other (out ++ charBytes c.char))) ∧
  (∀ a x, writePipe (.aio a) x = match (writeW x).run a with
    | .ok n a' => .ok (n, .aio a')
    | .error e _ => .error e) ∧
  (∃ e, printstyledDecl = .error e)

theorem bufferContract : BufferContract := by
  refine ⟨fun _ => ⟨rfl, rfl⟩, ?_, fun _ _ => rfl, fun bs a => onIO_anns _ a, fun b a => onIO_anns _ a,
    fun out x => ?_, fun _ _ => rfl, fun _ _ => rfl, ⟨_, rfl⟩⟩
  · unfold empty; cases IOBuffers.iobuffer <;> rfl
  · cases x <;> rfl

/-- `read(io, AnnotatedString)` at position 0 returns all annotations, and otherwise
only annotations ending after the position, shifted to start at 1 or later;
`read(io, AnnotatedChar)` returns the annotations whose region contains the next
code unit; the `AbstractString`/`AbstractChar` forms read `String`/`Char`;
`truncate(io, n)` keeps only annotations starting at or before `n`. -/
def ReadTruncateContract : Prop :=
  (∀ anns, readAnns anns (ix 0) = anns) ∧
  (∀ anns start, start.val ≠ 0 → ∀ x ∈ readAnns anns start,
    1 ≤ x.lo.val ∧ ∃ y ∈ anns, start.val < y.hi.val ∧ x.label = y.label ∧ x.value = y.value) ∧
  (readAS = do let a ← get; let annots := readAnns a.anns (position a); let s ← readString; pure ⟨s, annots⟩) ∧
  (∀ anns pos x, x ∈ charAnns anns pos → ∃ y ∈ anns, x = y.toAnn ∧
    y.lo.val ≤ (pos + ix 1).val ∧ (pos + ix 1).val ≤ y.hi.val) ∧
  (readAC = do let a ← get; let char ← onIO readChar; pure ⟨char, charAnns a.anns (position a)⟩) ∧
  readASAny = readAS ∧ readACAny = readAC ∧
  (∀ anns n, ∀ x ∈ truncAnns anns n, x.lo.val ≤ n.val ∧ ∃ y ∈ anns, x.lo = y.lo ∧ x.label = y.label) ∧
  (∀ n, truncateAIO n = do onIO (IOBuffers.truncate n); let a ← get; setAnns (truncAnns a.anns n))

theorem imax_ge (x y : JInt64) : x.val ≤ (imax x y).val := by
  unfold imax; split <;> omega

theorem readTruncateContract : ReadTruncateContract := by
  refine ⟨fun anns => ?_, fun anns start h0 x hx => ?_, rfl, fun anns pos x hx => ?_, rfl, rfl, rfl,
    fun anns n x hx => ?_, fun _ => rfl⟩
  · simp [readAnns]
  · unfold readAnns at hx
    rw [if_neg h0] at hx
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
    obtain ⟨y, ⟨hy, hyh⟩, rfl⟩ := hx
    exact ⟨imax_ge _ _, y, hy, hyh, rfl, rfl⟩
  · unfold charAnns at hx
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
    obtain ⟨y, ⟨hy, h1, h2⟩, rfl⟩ := hx
    exact ⟨y, hy, rfl, h1, h2⟩
  · unfold truncAnns at hx
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
    obtain ⟨y, ⟨hy, hyl⟩, rfl⟩ := hx
    exact ⟨hyl, y, hy, rfl, rfl⟩

/-- `_insert_annotations!` keeps the existing annotations' positions and labels
(extending at most their end) and adds every new annotation after the merged run,
shifted by `offset`; the `AnnotatedIOBuffer` method uses the buffer's annotations. -/
def InsertContract : Prop :=
  (∀ annots new offset, ∀ x ∈ new.drop (findRun annots new offset),
    (⟨(urange (x.lo + offset) (x.hi + offset)).1, (urange (x.lo + offset) (x.hi + offset)).2, x.label, x.value⟩ : RA) ∈
      insertAnns annots new offset) ∧
  (∀ new offset a, (insertIO new offset).run a = .ok () { a with anns := insertAnns a.anns new offset })

theorem insertContract : InsertContract := by
  refine ⟨fun annots new offset x hx => ?_, fun _ _ _ => rfl⟩
  · unfold insertAnns
    exact List.mem_append_right _ (List.mem_map.mpr ⟨x, hx, rfl⟩)

/-- Without StyledStrings: `write`/`print` of an `AnnotatedString`, SubString or
`AnnotatedChar` to a plain `IO` write the unannotated code units and return their
number (`ansi_write`); `write(io, aio)` copies the readable bytes (or, with
`:color => true`, the text read as an `AnnotatedString`); printing into an
`AnnotatedIOBuffer` is `write`, `printstyled`/`styled_print` print the message
parts in order ignoring the style keywords; `escape_string` escapes the unannotated
text; `show_annot` and the `text/html` `show` methods print nothing. -/
def DisplayContract : Prop :=
  (∀ out x, ansiWrite out x = (ix (dBytes x).length, out ++ dBytes x) ∧ ansiWrite_ out x = ansiWrite out x) ∧
  (∀ out x, writeIO out x = (ix (dBytes (.w x)).length, out ++ dBytes (.w x))) ∧
  (∀ out c, writeIOC out c = (ix (charBytes c.char).length, out ++ charBytes c.char)) ∧
  (∀ out x, printIO out x = out ++ dBytes (.w x)) ∧
  (∀ out c, printIOC out c = out ++ charBytes c.char) ∧
  (∀ out (a : AIO), a.io.readable = true → writeIOAIO false out a =
    .ok ((ix (IOBuffers.slice a.io.data a.io.ptr.val a.io.size.val).length,
      out ++ IOBuffers.slice a.io.data a.io.ptr.val a.io.size.val),
      { a with io := { a.io with ptr := a.io.size + IOBuffers.i 1 } })) ∧
  (∀ out a s a', readASAny.run a = .ok s a' → writeIOAIO true out a = .ok ((ix s.str.bytes.length, out ++ s.str.bytes), a')) ∧
  (∀ x, printAIO x = do discard (writeW x)) ∧ (∀ c, printAIOC c = do discard (writeC c)) ∧
  (∀ msg kw kw', printstyledAIO msg kw = printstyledAIO msg kw' ∧ printstyledAIO msg kw = printAll msg ∧
    styledPrint_ msg kw = styledPrint msg kw) ∧
  (∀ x rest, printAll (.w x :: rest) = do printAIO x; printAll rest) ∧
  (∀ esc out x, escapeStringA esc out x = out ++ esc (dBytes (.w x))) ∧
  (∀ out, showAnnot out = out ∧ showAnnotM out = out ∧ showAnnot_ out = out ∧ showAnnotM_ out = out) ∧
  (∀ out x c, showHtml out x = out ∧ showHtmlC out c = out)

theorem displayContract : DisplayContract := by
  refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun out a h => ?_, fun out a s a' h => ?_, fun _ => rfl, fun _ => rfl, fun _ _ _ => ⟨rfl, rfl, rfl⟩,
    fun _ _ => rfl, fun _ _ _ => rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun _ _ _ => ⟨rfl, rfl⟩⟩
  · unfold writeIOAIO; simp [h]
  · unfold writeIOAIO; rw [if_pos rfl, h]; rfl

end JuliaLean.StringsCovB.AIO
