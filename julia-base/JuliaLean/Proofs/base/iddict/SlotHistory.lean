import JuliaLean.base.iddict

namespace JuliaLean.DictsCov.EqTable
/-- One call of a program building the dictionary. -/
inductive Op where
  | set (k v : Int)
  | del (k : Int)

def run (keyhash : Int → Nat) (ops : List Op) : IdD :=
  ops.foldl (fun d op => match op with
    | .set k v => d.setindex keyhash v k
    | .del k => d.delete keyhash k) IdD.new

/-- The pairs of a dictionary by iteration. -/
def pairsOf (d : IdD) : List (Int × Int) :=
  d.ht.filterMap fun p => match p with
    | (.key k, some v) => some (k, v)
    | _ => none

end JuliaLean.DictsCov.EqTable
