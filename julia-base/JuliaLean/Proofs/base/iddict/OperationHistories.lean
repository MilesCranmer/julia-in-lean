import JuliaLean.base.iddict
import JuliaLean.Proofs.base.iddict.ValueLaws

namespace JuliaLean.IdDicts
/-! ## Call sequences -/

/-- Calls that change an `IdDict`. -/
inductive DOp where
  | set (k v : JVal)
  | delete (k : JVal)
  | pop3 (k default : JVal)
  | pop (k : JVal)
  | empty
  | sizehint (n : JInt .i64)
  | getBang (k default : JVal)
  | getBangF (fv k : JVal)

/-- One call; a throwing call leaves whatever state it reached (as under
`try ... catch end`). -/
def DOp.run (d : IdDict) : DOp → IdDict
  | .set k v => (d.setindex v k).1
  | .delete k => (d.delete k).1
  | .pop3 k dflt => (d.pop3 k dflt).1
  | .pop k => (d.pop k).1
  | .empty => d.empty
  | .sizehint n => d.sizehint n
  | .getBang k dflt => (d.getBang k dflt).1
  | .getBangF fv k => (d.getBangF fv k).1

/-- Run a call sequence from `IdDict{K,V}()`. -/
def runD (K V : JTy) (ops : List DOp) : IdDict := ops.foldl DOp.run (IdDict.new K V)

/-- The calls whose effect on the dictionary does not go through the
sentinel (`get!` reads through it and is treated separately). -/
def DOp.mutator : DOp → Bool
  | .getBang _ _ | .getBangF _ _ => false
  | _ => true

/-! ## Reference `===` map -/

/-- Reference lookup in a `===`-keyed association list. -/
def rLookup : Tab → JVal → Option JVal
  | [], _ => none
  | (k', v') :: t, k => if egal k k' then some v' else rLookup t k

/-- Reference insertion/overwrite. -/
def rSet (m : Tab) (k v : JVal) : Tab := (k, v) :: m.filter fun p => !egal p.1 k

/-- Reference deletion. -/
def rDel (m : Tab) (k : JVal) : Tab := m.filter fun p => !egal p.1 k

/-- The documented effect of a call on the reference map of an
`IdDict{K,V}`: `setindex!` throws for keys not of type `K`
(`KeyTypeError`) and for values that do not convert to `V`; `get!` stores
`convert(V, default)` exactly when the key is absent. -/
def DOp.ref (K V : JTy) (m : Tab) : DOp → Tab
  | .set k v => if isa k K then (match convert V v with | .ok w => rSet m k w | .error _ => m) else m
  | .delete k | .pop3 k _ | .pop k => rDel m k
  | .empty => []
  | .sizehint _ => m
  | .getBang k dflt | .getBangF dflt k =>
      match rLookup m k with
      | some _ => m
      | none => if isa k K then (match convert V dflt with | .ok w => rSet m k w | .error _ => m) else m

/-- The reference map after a call sequence. -/
def refD (K V : JTy) (ops : List DOp) : Tab := ops.foldl (DOp.ref K V) []

/-- Keys pairwise not `===`. -/
def keysDistinct (t : Tab) : Prop := (t.map Prod.fst).Nodup

end JuliaLean.IdDicts
