import JuliaLean.Core

/-!
Generic list model of the reductions in `base/reduce.jl` and `base/accumulate.jl`.

A one-dimensional array or iterator is a `List`. Julia's dynamically typed
`op`, `f`, `reduce_first`, `reduce_empty` are passed as Lean functions, so the
same definitions serve every element type. Exceptions are `Err`.
-/

namespace JuliaLean.Reduce

/-- Julia exception types thrown by the modelled reductions. -/
inductive Err where
  | argumentError
  | inexactError
  | typeError
  | methodError
  | dimensionMismatch
  deriving Repr, DecidableEq, Inhabited

/-- A Julia call that may throw. -/
abbrev R (α : Type) := Except Err α

section
variable {α β γ : Type}

deriving instance DecidableEq for Except

/-- `mapreduce_impl(f, op, A, ifirst, ilast, blksize)`, `base/reduce.jl:252-274`, applied to
the nonempty slice `A[ifirst:ilast] = a :: rest`. `ilast - ifirst` is `rest.length`;
`imid = ifirst + (ilast - ifirst) >> 1`, so the left half `A[ifirst:imid]` is
`a :: rest.take (rest.length / 2)` and the right half `A[imid+1:ilast]` is
`rest.drop (rest.length / 2)`. `first` is `mapreduce_first(f, op, ·)`. The sequential
portion is a `@simd` loop, which lets the compiler reassociate floating-point `op`s; the
model fixes the left-to-right order written in the source. -/
def mrImpl (f : α → β) (op : β → β → β) (first : α → β) (blk : Nat) (a : α) (rest : List α) : β :=
  match rest with
  | [] => first a
  | b :: rest' =>
    if rest'.length + 1 < blk then
      rest'.foldl (fun v x => op v (f x)) (op (f a) (f b))
    else
      match h : (b :: rest').drop ((rest'.length + 1) / 2) with
      | [] => first a
      | c :: rest2 =>
        op (mrImpl f op first blk a ((b :: rest').take ((rest'.length + 1) / 2)))
          (mrImpl f op first blk c rest2)
termination_by rest.length
decreasing_by
  · simp only [List.length_take, List.length_cons]; omega
  · have := congrArg List.length h
    simp only [List.length_drop, List.length_cons] at this
    simp only [List.length_cons]; omega

/-- `_mapreduce(f, op, ::IndexLinear, A)`, `base/reduce.jl:436-457`: `empty` is the result of
`mapreduce_empty_iter` for an empty array, `first` is `mapreduce_first`, and `blk` is
`pairwise_blocksize(f, op)` (`base/reduce.jl:311-314`). -/
def mapreduceArr (f : α → β) (op : β → β → β) (first : α → β) (empty : R β) (blk : Nat) :
    List α → R β
  | [] => empty
  | [a] => .ok (first a)
  | a :: b :: rest =>
    if rest.length + 2 < 16 then .ok (rest.foldl (fun s x => op s (f x)) (op (f a) (f b)))
    else .ok (mrImpl f op first blk a (b :: rest))

/-- `_mapreduce_dim(f, op, nt, A, ::Colon)` with an `init`, `base/reducedim.jl:333-343`:
`v = op(nt, f(y[1]))`, then `v = op(v, f(x))` for the rest. -/
def mapreduceInit (f : α → β) (op : γ → β → γ) (init : γ) (A : List α) : γ :=
  A.foldl (fun v x => op v (f x)) init

/-- `mapfoldl(f, op, itr)` without `init`, `base/reduce.jl:40-63, 83-84`: the first element
goes through `BottomRF`, i.e. `reduce_first(op, f(x))` (`first`), the rest through `op`;
an empty iterator gives `reduce_empty_iter` (`empty`). -/
def mapfoldlNoInit (f : α → β) (op : β → β → β) (first : β → β) (empty : R β) :
    List α → R β
  | [] => empty
  | a :: rest => .ok (rest.foldl (fun v x => op v (f x)) (first (f a)))

/-- `mapfoldl(f, op, itr; init)`, `base/reduce.jl:40-63`: `op(init, f(x1))`, then left fold. -/
def mapfoldlInit (f : α → β) (op : γ → β → γ) (init : γ) (A : List α) : γ :=
  A.foldl (fun v x => op v (f x)) init

/-- `mapfoldr(f, op, itr)` without `init`, `base/reduce.jl:200-213`: a left fold of
`BottomRF(FlipArgs(op))` over the reversed iterator. The first visited (last) element goes
through `reduce_first(FlipArgs(op), ·)`, given as `firstFlip`. -/
def mapfoldrNoInit (f : α → β) (op : β → β → β) (firstFlip : β → β) (empty : R β)
    (A : List α) : R β :=
  mapfoldlNoInit f (fun acc x => op x acc) firstFlip empty A.reverse

/-- `mapfoldr(f, op, itr; init)`, `base/reduce.jl:200-213`: `op(f(x), acc)` from the right. -/
def mapfoldrInit (f : α → β) (op : β → γ → γ) (init : γ) (A : List α) : γ :=
  A.reverse.foldl (fun acc x => op (f x) acc) init

/-- `_accumulate1!` loop, `base/accumulate.jl:436-452`: `cur_val = op(cur_val, A[i])`. -/
def accumulateLoop (op : β → α → β) (cur : β) : List α → List β
  | [] => []
  | x :: rest => let c := op cur x; c :: accumulateLoop op c rest

/-- `_accumulate!(op, B, A::AbstractVector, nothing, init)`, `base/accumulate.jl:362-372`:
`v1 = reduce_first(op, first(A))` (`first`) without `init`, `op(init, first(A))` with it. -/
def accumulateVec (op : β → α → β) (first : α → β) (init : Option β) : List α → List β
  | [] => []
  | x :: rest =>
    let v1 := match init with | some i => op i x | none => first x
    v1 :: accumulateLoop op v1 rest

end

end JuliaLean.Reduce
