import JuliaLean.base.idset
import JuliaLean.base.abstractset
import JuliaLean.Proofs.base.iddict.ValueLaws

namespace JuliaLean.IdDicts
/-! ## Call sequences -/

inductive SOp where
  | push (x : JVal)
  | pop (x : JVal)
  | pop3 (x default : JVal)
  | delete (x : JVal)
  | empty
  | sizehint (n : JInt .i64)
  | union (xs : List JVal)
  | setdiff (xs : List JVal)

/-- One call; a throwing call leaves the state it reached. -/
def SOp.run (s : IdSet) : SOp → IdSet
  | .push x => (s.push x).1
  | .pop x => (s.pop x).1
  | .pop3 x _ => (s.pop! x).1
  | .delete x => s.delete x
  | .empty => s.empty
  | .sizehint _ => s
  | .union xs => (s.union xs).1
  | .setdiff xs => s.setdiff xs

def runS (T : JTy) (ops : List SOp) : IdSet := ops.foldl SOp.run (IdSet.new T)

/-- Number of elements a call sequence mentions (an upper bound on the size
of the set). -/
def SOp.size : SOp → Nat
  | .push _ => 1
  | .union xs => xs.length
  | _ => 0

/-! ## Reference `===` set (insertion-ordered list) -/

def rPush (xs : List JVal) (x : JVal) : List JVal := if x ∈ xs then xs else xs ++ [x]

def SOp.ref (xs : List JVal) : SOp → List JVal
  | .push x => rPush xs x
  | .pop x | .pop3 x _ | .delete x => xs.erase x
  | .empty => []
  | .sizehint _ => xs
  | .union ys => ys.foldl rPush xs
  | .setdiff ys => ys.foldl List.erase xs

def refS (ops : List SOp) : List JVal := ops.foldl SOp.ref []

end JuliaLean.IdDicts
