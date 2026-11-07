import JuliaLean.base.weakdict
import JuliaLean.Proofs.base.iddict.ValueLaws

namespace JuliaLean.IdDicts
inductive WOp where
  | set (k v : JVal)
  | delete (k : JVal)
  | gc (dead : List JVal)

def WOp.run (w : WKD) : WOp → WKD
  | .set k v => (w.setindex v k).1
  | .delete k => w.delete k
  | .gc dead => w.gc dead

def runW (K : JTy) (ops : List WOp) : WKD := ops.foldl WOp.run (WKD.new K)

/-- Values and keys a call mentions. -/
def WOp.mentions : WOp → List JVal
  | .set k v => [k, v]
  | .delete k => [k]
  | .gc _ => []

/-- A call sequence a program can produce: a collection frees only mutable
objects, never a value stored in the dictionary (values are strong
references; this is approximated by: never a value of any `set`), and a freed
object is not used by a later call. -/
def Realistic : List WOp → Prop
  | [] => True
  | .gc dead :: rest =>
      (∀ x ∈ dead, finalizable x = true) ∧
      (∀ x ∈ dead, ∀ op ∈ rest, x ∉ op.mentions) ∧ Realistic rest
  | _ :: rest => Realistic rest

/-- `dead` contains no value stored by any `set` of the sequence. -/
def NoValueFreed (ops : List WOp) : Prop :=
  ∀ op ∈ ops, ∀ dead, op = .gc dead → ∀ op' ∈ ops, ∀ k v, op' = .set k v → v ∉ dead

end JuliaLean.IdDicts
