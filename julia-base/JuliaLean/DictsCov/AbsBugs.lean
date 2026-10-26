import JuliaLean.DictsCov.AbsModel
import JuliaLean.IdDicts.IdDict
import JuliaLean.Dicts.Immutable

/-!
# Refuted promises of the generic `AbstractDict` methods

* `show(io, t::AbstractDict)` with `:limit => true` (`base/dict.jl:3-23`)
  prints an ellipsis after the tenth pair even when nothing follows.
* `filter(f, d)` and `copy(d)` (`base/abstractdict.jl:197,479-488`) build their
  result with `empty(d)` and `setindex!`; for an `ImmutableDict`,
  `empty(d)` is an `ImmutableDict` (`base/dict.jl:866`), which has no
  `setindex!`.
* `merge(d)`/`mergewith(f, d, ...)` (`base/abstractdict.jl:361-417`) copy `d`
  into a `Dict`, which compares keys with `isequal`; for an `IdDict`, whose
  keys are compared with `===`, distinct keys collapse.
-/

namespace JuliaLean.DictsCov

open JuliaLean.Dicts
open JuliaLean.IdDicts (JVal Tab egal rLookup rSet rDel)

/-! ## `show(io, t::AbstractDict)`, `base/dict.jl:3-23` -/

/-- What `show` prints: literal text or `show(recur_io, pair)` of a pair. -/
inductive ShowTok (α : Type) where
  | text (s : String)
  | pair (x : α)
  deriving Repr, DecidableEq

/-- The loop `for pair in t ... end` of `show`, with the counter `n` and the
flag `first`. -/
def showDictLoop {α : Type} (limit : Bool) : Nat → Bool → List α → List (ShowTok α)
  | _, _, [] => []
  | n, first, pair :: rest =>
    let sep : List (ShowTok α) := if first then [] else [.text ", "]
    let n := n + 1
    if limit && n ≥ 10 then sep ++ [.pair pair, .text "…"]
    else sep ++ .pair pair :: showDictLoop limit n false rest

/-- `show(io, t::AbstractDict)`: `pfx` is `typeinfo_prefix(io, t)[1]`, `limit`
is `get(io, :limit, false)`, `circular` is `show_circular(io, t)`, and `pairs`
the iteration of `t` (`isempty(t)` is `pairs = []`). -/
def showDictAD {α : Type} (pfx : String) (limit circular : Bool) (pairs : List α) : List (ShowTok α) :=
  [.text pfx, .text "("] ++
    (if !pairs.isEmpty && !circular then showDictLoop limit 0 true pairs else []) ++ [.text ")"]

/-- The `:limit` `IOContext` docstring (`base/show.jl:397-398`): limited output
prints `…` in place of omitted elements, so an ellipsis means some pair was not
shown. -/
def ShowEllipsisOmits : Prop :=
  ∀ (α : Type) (pfx : String) (pairs : List α), pfx ≠ "…" →
    ShowTok.text "…" ∈ showDictAD pfx true false pairs → 10 < pairs.length

theorem show_ten : ShowTok.text "…" ∈ showDictAD "Dict" true false (List.range 10) := by
  decide +kernel

theorem showEllipsisOmits_refuted : ¬ ShowEllipsisOmits := by
  intro h
  have := h Nat "Dict" (List.range 10) (by decide) show_ten
  exact absurd this (by decide)

/-! ## `filter`/`copy` of an `ImmutableDict` -/

/-- An `ImmutableDict{K,V}`: its type and its chain, most recent pair first. -/
structure ImmD (K V : Type) where
  ty : DictTy String
  chain : IDict K V

/-- The interface of `ImmutableDict` (`base/dict.jl:776-866`): iteration
yields the chain (`iterate`, 860-863), `get` is the chain lookup (843-849),
`empty(::ImmutableDict, K, V) = ImmutableDict{K,V}()` (866), `length` counts
the iterated pairs (864), `sizehint!` is the `AbstractDict` fallback, and the
type defines no `setindex!`, `delete!` or `empty!`. -/
def immOps {K V : Type} (eq : K → K → Bool) : DictOps String (ImmD K V) K V where
  pairs d := d.chain
  get d k := idGet eq d.chain k
  setindex _ _ _ := throw (.methodError "setindex!")
  delete _ _ := throw (.methodError "delete!")
  emptyT _ K V := ⟨⟨"ImmutableDict", K, V⟩, []⟩
  emptyBang _ := throw (.methodError "empty!")
  length d := d.chain.length
  sizehint d _ := d
  hasLength _ := true
  typeOf d := d.ty

/-- `filter` docstring (`base/abstractdict.jl:464`: "Return a copy of `d`,
removing elements for which `f` is `false`") and `copy` (a shallow copy):
both return a dictionary for every `AbstractDict`. -/
def FilterCopyNothrow : Prop :=
  ∀ (K V : Type) (eq : K → K → Bool) (d : ImmD K V) (f : K × V → Bool),
    (∃ r, filterAD (immOps eq) f d = .ok r) ∧ (∃ r, copyAD (immOps eq) d = .ok r)

theorem filterCopyNothrow_refuted : ¬ FilterCopyNothrow := by
  intro h
  obtain ⟨⟨r, hr⟩, -⟩ := h Nat Nat (· == ·) ⟨⟨"ImmutableDict", "Symbol", "Int64"⟩, [(0, 1)]⟩
    (fun _ => true)
  have e : filterAD (immOps (K := Nat) (V := Nat) (· == ·)) (fun _ => true)
      ⟨⟨"ImmutableDict", "Symbol", "Int64"⟩, [(0, 1)]⟩ = .error (.methodError "setindex!") := rfl
  rw [e] at hr
  cases hr

/-! ## `merge` of an `IdDict` -/

/-- An `IdDict{K,V}`: its type and its live pairs. -/
structure IdD' where
  ty : DictTy String
  tab : Tab

/-- The interface of `IdDict` (`base/iddict.jl`): keys are compared with `===`. -/
def idOps : DictOps String IdD' JVal JVal where
  pairs d := d.tab
  get d k := rLookup d.tab k
  setindex d v k := pure ⟨d.ty, rSet d.tab k v⟩
  delete d k := pure ⟨d.ty, rDel d.tab k⟩
  emptyT _ K V := ⟨⟨"IdDict", K, V⟩, []⟩
  emptyBang d := pure ⟨d.ty, []⟩
  length d := d.tab.length
  sizehint d _ := d
  hasLength _ := true
  typeOf d := d.ty

/-- `isequal` on the value universe as a `Dict` key comparison. -/
def isequalKO : KeyOps JVal := ⟨fun _ => JInt.lit .u64 0, JuliaLean.IdDicts.isequal, JInt.typemax .i64⟩

/-- A `Dict{K,V}` as the reference map it holds (`dicts-ops-agree`). -/
structure DictR where
  ty : DictTy String
  m : RMap JVal JVal

/-- The interface of `Dict`, through its reference map. -/
def dictROps : DictOps String DictR JVal JVal where
  pairs d := d.m
  get d k := rlookup isequalKO d.m k
  setindex d v k := pure ⟨d.ty, rset isequalKO d.m k v⟩
  delete d k := pure ⟨d.ty, rdel isequalKO d.m k⟩
  emptyT _ K V := ⟨⟨"Dict", K, V⟩, []⟩
  emptyBang d := pure ⟨d.ty, []⟩
  length d := d.m.length
  sizehint d _ := d
  hasLength _ := true
  typeOf d := d.ty

/-- `Dict{K,V}(ps)` (`dicts-dict-construct`). -/
def dictROf (K V : String) (ps : List (JVal × JVal)) : GR DictR := pure ⟨⟨"Dict", K, V⟩, rbuild isequalKO ps⟩

/-- `merge` docstring (`base/abstractdict.jl:330-333`: "Construct a merged
collection from the given collections"): `merge(d)` of an `IdDict` keeps every
key of `d`. -/
def MergeKeepsIdKeys : Prop :=
  ∀ tab : Tab, (tab.map Prod.fst).Nodup →
    ∃ r, mergeAD idOps dictROps (fun a _ => a) dictROf ⟨⟨"IdDict", "Any", "Any"⟩, tab⟩ [] = .ok r ∧
      r.m.length = tab.length

theorem mergeKeepsIdKeys_refuted : ¬ MergeKeepsIdKeys := by
  intro h
  obtain ⟨r, hr, hlen⟩ := h [(.int 1, .sym "a"), (.flt 1, .sym "b")] (by decide)
  have : r = ⟨⟨"Dict", "Any", "Any"⟩, [(.flt 1, .sym "b")]⟩ := by
    have e : mergeAD idOps dictROps (fun a _ => a) dictROf ⟨⟨"IdDict", "Any", "Any"⟩,
        [(.int 1, .sym "a"), (.flt 1, .sym "b")]⟩ [] =
        .ok ⟨⟨"Dict", "Any", "Any"⟩, [(.flt 1, .sym "b")]⟩ := rfl
    rw [e] at hr
    cases hr
    rfl
  subst this
  cases hlen

end JuliaLean.DictsCov
