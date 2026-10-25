import JuliaLean.Platforms.Basic

/-!
# `platforms_match` and `select_platform` (`base/binaryplatforms.jl:295-355, 1128-1246`)

`union(keys(tags(a)), keys(tags(b)))` is a `Set`, whose iteration order is
hash-based; it is an explicit argument `order` (any duplicate-free list of
exactly the keys of either platform). User-defined comparison strategies
(`Strat.user n`) have semantics `usem n`.
-/

namespace JuliaLean.Platforms

open JuliaLean
open JuliaLean.VersionNumbers (VersionNumber vless veq)

/-- Semantics of user-defined comparison functions. -/
abbrev UserSem := Nat → Str → Str → Bool → Bool → Jl Bool

/-- `a <= b` for `VersionNumber`s (`(a < b) | (a == b)`). -/
def vle (a b : VersionNumber) : Bool := vless a b || veq a b

/-- Calling a comparison strategy, `base/binaryplatforms.jl:1183`. -/
def compare (usem : UserSem) : Strat → Str → Str → Bool → Bool → Jl Bool
  | .dflt, a, b, _, _ => pure (a == b)
  | .cap, a, b, ar, br => do
    let a ← VersionNumbers.parse a
    let b ← VersionNumbers.parse b
    if ar && br then return veq a b
    if ar then return vle b a else return vle a b
  | .juliaMinor, a, b, _, _ => do
    let a ← VersionNumbers.parse a
    let b ← VersionNumbers.parse b
    return a.major == b.major && a.minor == b.minor
  | .user n, a, b, ar, br => usem n a b ar br

/-- `get_compare_strategy(p, key)` for a key `p` has, `base/binaryplatforms.jl:302-307`. -/
def strategy (p : Platform) (k : Str) : Strat := (dget p.strats k).getD .dflt

/-- `strict_presence_tags`, `base/binaryplatforms.jl:312`. -/
def strictPresenceTags : List Str := [s% "sanitize"]

/-- One iteration of the loop of `platforms_match`: `some r` continues
(`r = true`) or returns `false` (`r = false`). -/
def matchKey (usem : UserSem) (a b : Platform) (k : Str) : Jl Bool :=
  match tget a k, tget b k with
  | some ak, some bk => do
    let aComp := strategy a k
    let bComp := strategy b k
    if aComp != .dflt && bComp != .dflt && aComp != bComp then
      throw (.argumentError "Cannot compare Platform objects with two different non-default comparison strategies")
    let comparator := if bComp != .dflt then bComp else aComp
    compare usem comparator ak bk (aComp == comparator) (bComp == comparator)
  | _, _ => pure !(strictPresenceTags.contains k)

/-- `platforms_match(a, b)`, `base/binaryplatforms.jl:1153-1188`, iterating the
keys in `order`. -/
def platformsMatch (usem : UserSem) (order : List Str) (a b : Platform) : Jl Bool :=
  match order with
  | [] => pure true
  | k :: rest => do
    if ← matchKey usem a b k then platformsMatch usem rest a b else return false

/-- `order` is an iteration order of `union(keys(tags(a)), keys(tags(b)))`. -/
def IsUnionOrder (order : List Str) (a b : Platform) : Prop :=
  order.Nodup ∧ ∀ k, k ∈ order ↔ (haskey a.tags k = true ∨ haskey b.tags k = true)

/-- Every comparison strategy stored in `p` is one defined in `base/binaryplatforms.jl`. -/
def BuiltinStrats (p : Platform) : Prop := ∀ e ∈ p.strats, ∀ n, e.2 ≠ .user n

/-! ## `select_platform` -/

/-- Keys of `a` not among the keys of `b`. -/
def keysNotIn (a b : List Str) : List Str := a.filter (!b.contains ·)

/-- `match_loss(a, b)`, `base/binaryplatforms.jl:1226-1230`:
`length(union) - length(intersect)` of the two key sets. -/
def matchLoss (a b : Platform) : Nat :=
  let ka := keys a.tags
  let kb := keys b.tags
  (ka.length + (keysNotIn kb ka).length) - (ka.filter (kb.contains ·)).length

/-- The sort order of `select_platform`, `base/binaryplatforms.jl:1235-1242`, on
precomputed `(loss, triplet)` keys: smaller loss first, then larger triplet. -/
def selLt (x y : Nat × Str) : Bool := if x.1 != y.1 then x.1 < y.1 else strLt y.2 x.2

/-- The first element of a stable sort by `lt`: the earliest element that no
other element is strictly less than (for a strict weak order `lt`). -/
def firstMin {α : Type} (lt : α → α → Bool) : List α → Option α
  | [] => none
  | x :: xs =>
    match firstMin lt xs with
    | none => some x
    | some y => if lt y x then some y else some x

/-- `filter(f, xs)` with a throwing predicate, in iteration order. -/
def filterJ {β : Type} (f : β → Jl Bool) : List β → Jl (List β)
  | [] => pure []
  | x :: xs => do
    let keep ← f x
    let rest ← filterJ f xs
    return if keep then x :: rest else rest

/-- `map(f, xs)` with a throwing function. -/
def mapJ {β γ : Type} (f : β → Jl γ) : List β → Jl (List γ)
  | [] => pure []
  | x :: xs => do
    let y ← f x
    let rest ← mapJ f xs
    return y :: rest

/-- `select_platform(download_info, platform)`, `base/binaryplatforms.jl:1215-1246`.
`entries` lists the `Dict` entries in the order in which the matching keys are
collected (the iteration order of `filter(..., keys(download_info))`), and
`order p` is the key order `platforms_match(p, platform)` iterates.
`sort!` is stable, so the selected key is the first candidate that is minimal
for `lt`. With two or more candidates the model computes every candidate's
triplet up front, where Julia computes it only when two losses tie (the two
differ only when `triplet` throws). -/
def selectPlatform {α : Type} (usem : UserSem) (order : Platform → List Str)
    (entries : List (Platform × α)) (host : Platform) : Jl (Option α) := do
  let ps ← filterJ (fun e => platformsMatch usem (order e.1) e.1 host) entries
  match ps with
  | [] => return none
  | [e] => return some e.2
  | _ =>
    let keyed ← mapJ (fun e => do return ((matchLoss e.1 host, ← triplet e.1), e)) ps
    return (firstMin (fun x y => selLt x.1 y.1) keyed).map (·.2.2)

end JuliaLean.Platforms
