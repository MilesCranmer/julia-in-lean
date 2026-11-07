import JuliaLean.base.iddict
import JuliaLean.Registry.Types

/-!
# Method-specific models for `base/iddict.jl`

The C equality-table calls are explicit callbacks. Their result tags preserve
the source's pointer-identity tests against a default or the private sentinel.
The table model records the 32-word initial allocation, live count, and deleted
slot count; constructor folds and mutating reads retain Julia's call order.
-/

namespace JuliaLean.DictsCov.IdDictRows

open JuliaLean.Registry





def Property31 : Prop := ∀ (K V : Type), method31 (K := K) (V := V) = emptyState
theorem property31 : Property31 := by unfold Property31; intros; rfl

def Property33 : Prop := ∀ (K V : Type) hasLength sizehint setindex pairs,
  method33 (K := K) (V := V) hasLength sizehint setindex pairs =
    let d : State K V := method31
    let d := if hasLength then sizehint d pairs.length else d
    foldSet setindex d pairs
theorem property33 : Property33 := by unfold Property33; intros; rfl

def Property42 : Prop := ∀ (K V : Type) sizehint setindex pairs,
  method42 (K := K) (V := V) sizehint setindex pairs =
    foldSet setindex (sizehint method31 pairs.length) pairs
theorem property42 : Property42 := by unfold Property42; intros; rfl

def Property49 : Prop := ∀ (K V : Type) copySlots (d : State K V),
  method49 copySlots d =
    { slots := copySlots d.slots, rawWords := d.rawWords, count := d.count, ndel := d.ndel }
theorem property49 : Property49 := by unfold Property49; intros; rfl

def Property52 : Prop := ∀ (K V : Type), method52 (K := K) (V := V) = method31
theorem property52 : Property52 := by unfold Property52; intros; rfl

def Property53 : Prop := ∀ (K V : Type), method53 (K := K) (V := V) () = method52
theorem property53 : Property53 := by unfold Property53; intros; rfl

def Property55 : Prop := ∀ (K V : Type) typed pairs,
  method55 (K := K) (V := V) typed pairs = typed pairs
theorem property55 : Property55 := by unfold Property55; intros; rfl

def Property56 : Prop := ∀ (K V : Type) typed pairs,
  method56 (K := K) (V := V) typed pairs = typed pairs
theorem property56 : Property56 := by unfold Property56; intros; rfl

def Property57 : Prop := ∀ (K V : Type) typed pairs,
  method57 (K := K) (V := V) typed pairs = typed pairs
theorem property57 : Property57 := by unfold Property57; intros; rfl

def Property58 : Prop := ∀ (K V : Type) typed pairs,
  method58 (K := K) (V := V) typed pairs = typed pairs
theorem property58 : Property58 := by unfold Property58; intros; rfl

def Property60 : Prop := ∀ (I T K V : Type) eltype dictWithEltype kv,
  method60 (K := K) (V := V) (I := I) (T := T) eltype dictWithEltype kv =
    dictWithEltype kv (eltype kv)
theorem property60 : Property60 := by unfold Property60; intros; rfl

def Property62 : Prop := ∀ (K V : Type), method62 (K := K) (V := V) = method31
theorem property62 : Property62 := by unfold Property62; intros; rfl

def Property64 : Prop := ∀ (K V : Type) rehash (d : State K V) newsz,
  method64 rehash d newsz = { d with slots := rehash d.slots newsz, rawWords := newsz }
theorem property64 : Property64 := by unfold Property64; intros; rfl


def Property94 : Prop := ∀ (K V Q : Type)
    (eqtableGet : State K V → Q → V → RawGet V) (d : State K V) (key : Q) (default : V),
  method94 eqtableGet d key default = match eqtableGet d key default with
    | .default => default
    | .value value => value
theorem property94 : Property94 := by unfold Property94; intros; rfl


def Property105 : Prop := ∀ (K V Q : Type)
    (pop : State K V → Q → V → PopResult V) (d : State K V) (key : Q) (default : V),
  method105 pop d key default =
    let result := pop d key default
    if result.found then
      (result.value, { d with count := d.count - 1, ndel := d.ndel + 1 })
    else (default, d)
theorem property105 : Property105 := by unfold Property105; intros; rfl



def Property139 : Prop := ∀ (A : Type) next reinterpretInt a i,
  method139 (A := A) next reinterpretInt a i = reinterpretInt (next a i)
theorem property139 : Property139 := by unfold Property139; intros; rfl

def Property149 : Prop := ∀ (K V : Type) constructor (d : State K V),
  method149 constructor d = constructor d
theorem property149 : Property149 := by unfold Property149; intros; rfl


def Property162 : Prop := ∀ (K V Q : Type)
    (getRaw : State K V → Q → Cell V) (default : Unit → R V)
    (d : State K V) (key : Q),
  method162 getRaw default d key = match getRaw d key with
    | .sentinel => default ()
    | .stored value => .ok value
theorem property162 : Property162 := by unfold Property162; intros; rfl


def Property189 : Prop := ∀ (K V : Type) filterOnePass f (d : State K V),
  method189 filterOnePass f d = filterOnePass f d
theorem property189 : Property189 := by unfold Property189; intros; rfl

private def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/iddict.jl", juliaFns := [fn], statement := statement,
    source := source, status := .proven, prop := prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.DictsCov.IdDictRows
