import JuliaLean.Core
import JuliaLean.Registry.Types

/-!
Shared observable values for the method-by-method model of `base/loading.jl`
at Julia commit `bbfa0ce4150`.  Calls into the filesystem, TOML parser,
runtime, compiler, locks, and task scheduler are explicit arguments.  Each
method model remains responsible for the order in which it calls them and for
all control flow and state changes performed in `loading.jl`.
-/

namespace JuliaLean.Loading.Coverage

open JuliaLean.Registry

inductive LoadError where
  | io
  | argument
  | bounds
  | type
  | system
  | other
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except LoadError α

inductive Event where
  | call (name : String)
  | read (path : String)
  | write (path : String)
  | lock
  | unlock
  | warn
  | callback
  | compile
  | load
  deriving Repr, DecidableEq

structure Observed (α : Type) where
  value : Result α
  events : List Event := []

def mapObserved (f : α → β) (x : Observed α) : Observed β :=
  { value := x.value.map f, events := x.events }

def catchIo (x : Result Bool) : Result Bool :=
  match x with
  | .ok value => .ok value
  | .error .io => .ok false
  | .error error => .error error

def firstSome : List (Option α) → Option α
  | [] => none
  | none :: rest => firstSome rest
  | some value :: _ => some value

def choose (first second : Option α) : Option α :=
  match first with | some value => some value | none => second

def allDistinct [DecidableEq α] (xs : List α) : Bool :=
  xs.eraseDups.length = xs.length

def updateAssoc [BEq κ] (key : κ) (value : ν) (xs : List (κ × ν)) : List (κ × ν) :=
  (key, value) :: xs.filter (fun pair => pair.1 != key)

def lookupAssoc [BEq κ] (key : κ) (xs : List (κ × ν)) : Option ν :=
  (xs.find? fun pair => pair.1 == key).map Prod.snd

def boolToResult (error : LoadError) (condition : Bool) : Result Unit :=
  if condition then .ok () else .error error

end JuliaLean.Loading.Coverage
