import JuliaLean.StringsCovB.AIOR

/-!
# Properties of `replace` on `AnnotatedString`s

`base/strings/annotated_io.jl:240-338`. The docstring of `replace`
(`base/strings/util.jl:1133-1185`) promises the plain `String` result; for an
`AnnotatedString` the annotations must follow the text they were attached to,
and writing the result into an `AnnotatedIOBuffer` must behave like `write`.
-/

namespace JuliaLean.StringsCovB.AIOR

open JuliaLean JuliaLean.Strings JuliaLean.StringsCovB.Ann JuliaLean.StringsCovB.AIO

/-- The pair `t => repl` for a `String` pattern `t`, searched in `s` with
`findnext(t, s, k)` (`base/strings/search.jl:468-479`). -/
def strPair (t s : JStr) (repl : Repl) : APair :=
  ⟨fun k => (findnextStr t s k).map fun o => match o with
    | none => .nothing
    | some p => .range (ix p.1) (ix p.2), repl⟩

/-- The pair `re => repl` for a `Regex` pattern searched in `s`. -/
def rePair (re : RegexUnicode.Core.Regex) (s : JStr) (repl : Repl) : APair := ⟨regexFinder re s, repl⟩

/-! ## Proven -/

/-- `replace(out::IO, str::AnnotatedString, ...)` writes the plain `replace` of
`str.string`; `replace(str, pat_f...; count = 0)` returns `str` itself; and
`replace(out::AnnotatedIOBuffer, str; count = 0)` and the call without pairs
are `write(out, str)`. -/
def ReplaceTrivialContract : Prop :=
  (∀ out str ps count, replaceIO out str ps count =
    (StringUtil.replace str.str (ps.map APair.toPair) count).map (out ++ ·)) ∧
  (∀ str ps, ps ≠ [] → replaceAS str ps (ix 0) = .ok str) ∧
  (∀ str ps, replaceAIO str ps (ix 0) = (do discard (writeW (.str str)); pure ())) ∧
  (∀ str count, replaceAIO str [] count = (do discard (writeW (.str str)); pure ()))

theorem replaceTrivialContract : ReplaceTrivialContract := by
  refine ⟨fun _ _ _ _ => rfl, fun str ps hp => ?_, fun str ps => ?_, fun str count => ?_⟩
  · cases ps with
    | nil => exact absurd rfl hp
    | cons p ps => rfl
  · unfold replaceAIO; exact if_pos (show (ix 0).val = 0 ∨ ps.isEmpty = true from Or.inl rfl)
  · unfold replaceAIO
    exact if_pos (show count.val = 0 ∨ ([] : List APair).isEmpty = true from Or.inr rfl)

/-! ## Refuted -/

/-- `true` when the replacement run left in place every annotation of the buffer
`a` that ends at or before its position (the code units `write` would not
overwrite), or when it threw. -/
def keepsBefore (a : AIO) : EStateM.Result AErr AIO Unit → Bool
  | .ok _ a' => a.anns.all fun x => !decide (x.hi.val ≤ (position a).val) || a'.anns.contains x
  | .error _ _ => true

/-- `replace(out::AnnotatedIOBuffer, str, pat => repl)` writes the replaced
string at the position of `out` like `write(out, ::AnnotatedString)`, which only
clears the annotations of the code units it overwrites
(`base/strings/annotated_io.jl:35-41`): annotations ending at or before the
position survive. -/
def ReplaceKeepsBefore : Prop :=
  ∀ (a : AIO) (str : AS) (ps : List (JStr × Repl)),
    keepsBefore a ((replaceAIO str (ps.map fun p => strPair p.1 str.str p.2) intMax).run a) = true

/-- An `AnnotatedIOBuffer` holding `"XYZW"` with annotations `1:1 => :p` and
`2:4 => :d`, positioned after its first code unit (`seek(io, 1)`). -/
def bufXYZW : AIO :=
  ⟨⟨[0x58, 0x59, 0x5a, 0x57], true, false, true, true, true, false,
    ix 4, ix (2 ^ 63 - 1), ix 2, ix 0, ix (-1)⟩,
   [⟨ix 1, ix 1, 0, some 1⟩, ⟨ix 2, ix 4, 1, some 2⟩]⟩

/-- `"ab"`. -/
def jAb : JStr := ⟨[0x61, 0x62], by decide⟩

/-- `"a"`. -/
def jA : JStr := ⟨[0x61], by decide⟩

/-- `replace(io, AnnotatedString("ab", [(1:2, :s, 3)]), "a" => "c")` into
`bufXYZW` drops the annotation `1:1 => :p` of the code unit before the position. -/
theorem replaceKeepsBefore_refuted : ¬ ReplaceKeepsBefore := by
  intro h
  have := h bufXYZW ⟨jAb, [⟨ix 1, ix 2, 2, some 3⟩]⟩ [(jA, .plain [0x63])]
  revert this
  decide +kernel

/-- `true` when the result is the subject unchanged or carries an annotation. -/
def annotatedIfChanged (str : AS) : Except AErr AS → Bool
  | .ok t => t.str.bytes == str.str.bytes || !t.anns.isEmpty
  | .error _ => true

/-- Replacing matches of a regex in an unannotated string by an annotated string
whose annotations are nonempty yields an annotated result whenever some
replacement happened. -/
def ReplaceEndAnnotated : Prop :=
  ∀ (re : RegexUnicode.Core.Regex) (str X : AS), str.anns = [] → X.anns ≠ [] →
    annotatedIfChanged str (replaceAS str [rePair re str.str (.astr X)] intMax) = true

/-- `X = AnnotatedString("X", [(1:1, :z, 1)])`. -/
def annX : AS := ⟨⟨[0x58], by decide⟩, [⟨ix 1, ix 1, 0, some 1⟩]⟩

/-- `r"$"` on `"ab"`: one empty match at the end (zero-based offset 2). -/
def reEnd : RegexUnicode.Core.Regex := ⟨RegexUnicode.Core.emptyAt [2], RegexUnicode.Core.DEFAULT_MATCH_OPTS⟩

/-- `replace(AnnotatedString("ab"), r"$" => X)` is `"abX"` without annotations. -/
theorem replaceEndAnnotated_refuted : ¬ ReplaceEndAnnotated := by
  intro h
  have := h reEnd ⟨jAb, []⟩ annX rfl (by simp [annX])
  revert this
  decide +kernel

/-- Code units `lo:hi` of `s`. -/
def sliceR (s : JStr) (lo hi : JInt64) : List UInt8 :=
  (s.bytes.drop (lo.val - 1).toNat).take (hi.val - lo.val + 1).toNat

/-- `true` when every annotation of the result covers the same code units as some
annotation of `X`. -/
def annsFollowText (X : AS) : Except AErr AS → Bool
  | .ok t => t.anns.all fun x => X.anns.any fun y => sliceR t.str x.lo x.hi == sliceR X.str y.lo y.hi
  | .error _ => true

/-- When an unannotated string has its regex matches replaced by an annotated
string `X`, every annotation of the result comes from a copy of `X` and covers
the code units of that copy that `X`'s annotation covers. -/
def ReplaceAnnotsInside : Prop :=
  ∀ (re : RegexUnicode.Core.Regex) (str X : AS), str.anns = [] →
    annsFollowText X (replaceAS str [rePair re str.str (.astr X)] intMax) = true

/-- `"abc"`. -/
def jAbc : JStr := ⟨[0x61, 0x62, 0x63], by decide⟩

/-- `r"b*"`. -/
def reBStar : RegexUnicode.Core.Regex :=
  RegexUnicode.Core.mkRegex ⟨.star (.lit [0x62]), 0⟩

/-- `replace(AnnotatedString("abc"), r"b*" => X)` is `"XaXcX"` with an
annotation `3:4` covering `"Xc"`. -/
theorem replaceAnnotsInside_refuted : ¬ ReplaceAnnotsInside := by
  intro h
  have := h reBStar ⟨jAbc, []⟩ annX rfl
  revert this
  decide +kernel

end JuliaLean.StringsCovB.AIOR
