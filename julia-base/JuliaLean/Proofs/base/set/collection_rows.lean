import JuliaLean.base.set
import JuliaLean.base.abstractset

namespace JuliaLean.BitSetsCov.Coll

open Bugs

def SetBasicSpec : Prop :=
  (∀ s, setFromDict s = s) ∧ setEmpty = [] ∧ (∀ s, setCopy s = s) ∧
  (∀ xs, setTyped unionOne xs = unionOne [] xs) ∧ setAny = [] ∧ (∀ s, setKeyset s = s) ∧
  (∀ xs, setHasEltype unionOne xs = setTyped unionOne xs) ∧
  (∀ c xs, setUnknownEltype unionOne c xs = if c then setTyped unionOne xs else unionOne [] xs) ∧
  (∀ s, setEmptyLike s = []) ∧ (∀ s, setSimilar s = [])

def SetMutableSpec : Prop :=
  (∀ ti s, setShow ti s = if s.isEmpty then if ti then "Set()" else "Set{T}()" else "Set(...)") ∧
  (∀ s, setIsEmpty s = s.isEmpty) ∧ (∀ s, setLength s = s.length) ∧
  (∀ x s, setIn x s = decide (x ∈ s)) ∧
  (∀ x s, setInBang x s = if x ∈ s then (true, s) else (false, insert s x)) ∧
  (∀ s x, setPush s x = insert s x) ∧
  (∀ s x d, setPopDefault s x d = if x ∈ s then (x, erase s x) else (d, s)) ∧
  (∀ s x, setPopKey s x = if x ∈ s then some (x, erase s x) else none) ∧
  (∀ s, setPopAny s = match s with | [] => none | x :: xs => some (x, xs)) ∧
  (∀ s x, setDelete s x = erase s x) ∧ (∀ s n sh, setSizehint s n sh = s) ∧
  (∀ s, setEmptyBang s = []) ∧ (∀ s, setRehash s = s) ∧
  (∀ s st, setIterate s st = match s.drop st with | [] => none | x :: _ => some (x, st + 1)) ∧
  (∀ s, setOnly s = match s with | [x] => some x | _ => none) ∧
  (∀ s t, setSetdiff setdiffOne s t = if 2 * s.length < t.length then s.filter (fun x => decide (x ∉ t)) else setdiffOne s t)

def SetUniqueSpec : Prop :=
  (∀ f xs, uniqueBy f xs =
    (xs.foldl (fun acc x => let k := f x; if k ∈ acc.2 then acc else (acc.1 ++ [x], acc.2 ++ [k])) ([], [])).1) ∧
  (∀ xs, unique xs = uniqueBy id xs) ∧
  (∀ xs out seen i, uniqueFrom xs out seen i = out ++ unique (xs.drop i |>.filter (fun x => decide (x ∉ seen)))) ∧
  (∀ f xs, uniqueBangBy f xs = uniqueBy f xs) ∧ (∀ xs, uniqueBang xs = unique xs) ∧
  (∀ xs, groupedUnique xs = xs.foldl (fun out x => if out.getLast? = some x then out else out ++ [x]) []) ∧
  (∀ o so xs, uniqueDispatch o so xs = if o && so then groupedUnique xs else uniqueBang xs)

def SetPredicatesSpec : Prop :=
  (∀ xs, allunique xs = decide xs.Nodup) ∧ (∀ xs, hashedAllunique xs = allunique xs) ∧
  (∀ xs, indexedAllunique xs = allunique xs) ∧
  (∀ h xs, alluniqueDispatch h xs = if h && xs.length < 2 then true else if h && xs.length < 32 then indexedAllunique xs else hashedAllunique xs) ∧
  (∀ f xs, alluniqueMap f xs = alluniqueDispatch true (xs.map f)) ∧
  (∀ s, alluniqueSet s = true) ∧
  (∀ xs, alluniqueString xs = if xs.length < 32 then indexedAllunique xs else hashedAllunique xs) ∧
  (∀ xs, alluniqueTuple xs = if xs.length < 32 then indexedAllunique xs else hashedAllunique xs) ∧
  alluniqueEmptyTuple = true ∧
  (∀ xs, allequal xs = match xs with | [] => true | x :: rest => rest.all (fun y => decide (x = y))) ∧
  (∀ s, allequalSet s = decide (s.length ≤ 1)) ∧ (∀ f xs, allequalMap f xs = allequal (xs.map f)) ∧
  (∀ f xs, allequalLoop f xs = allequalMap f xs) ∧
  (∀ f xs, allequalTuple f xs = if xs.length ≤ 1 then true else allequalLoop f xs) ∧
  allequalEmptyTuple = true

def SetHelpersSpec : Prop :=
  (∀ f s, setFilterBang abstractUnsafeFilter f s = abstractUnsafeFilter f s) ∧
  (∀ h seed s, setHash h seed s = s.foldl (fun acc x => acc ^^^ h x) seed) ∧
  (∀ s, setConvertSame s = s) ∧ (∀ s, setConvert s = ofList s) ∧
  (∀ c, checkCount c = if c < 0 then .domainError else .ok (min c 9223372036854775807).toNat) ∧
  (∀ x, copyOfType x = x) ∧ (∀ b x, similarOrCopy b x = if b then x else [])

def SetReplaceSpec : Prop :=
  (∀ ps x, replacePairs ps x = match ps.find? (fun p => p.1 = x) with | some p => p.2 | none => x) ∧
  (∀ A ps c, replacePairsBang A ps c =
    (A.foldl (fun acc x => let y := if acc.2 < c then replacePairs ps x else x
      (acc.1 ++ [y], acc.2 + if x = y then 0 else 1)) ([], 0)).1) ∧
  (∀ f A c, replaceCallableBang f A c = replacePairsBang A (A.map fun x => (x, f x)) c) ∧
  (∀ A ps c, replacePairsCopy A ps c = replacePairsBang A ps c) ∧
  (∀ ts, promoteValueType ts = ts.foldl max 0) ∧
  (∀ b t s, subtractSingleton b t s = if b && t = s then 0 else t) ∧
  (∀ f A c, replaceCallableCopy f A c = replaceCallableBang f A c) ∧ replaceAmbiguous = false ∧
  (∀ p, askeyDict p = p.1) ∧ (∀ x, askeySet x = x) ∧
  (∀ f r s, replaceCollection f r s = replaceSeparate f s r) ∧
  (∀ f r s c, replaceArray f r s c = (replaceCallableBang f s c).take r.length) ∧
  (∀ f ps, replaceDict f ps = ps.map f) ∧ (∀ f s, replaceSet f s = ofList (s.map f)) ∧
  (∀ t c ps, replaceTuplePairs t c ps = replaceTuple (replacePairs ps) t c)

theorem setBasicSpec : SetBasicSpec := by simp [SetBasicSpec, setFromDict, setEmpty, setCopy, setTyped, setAny, setKeyset, setHasEltype, setUnknownEltype, setEmptyLike, setSimilar]
theorem setMutableSpec : SetMutableSpec := by
  simp [SetMutableSpec, setShow, setIsEmpty, setLength, setIn, setInBang, setPush, setPopDefault, setPopKey, setPopAny, setDelete, setSizehint, setEmptyBang, setRehash, setIterate, setOnly, setSetdiff]
  exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
theorem setUniqueSpec : SetUniqueSpec := by simp [SetUniqueSpec, uniqueBy, unique, uniqueFrom, uniqueBangBy, uniqueBang, groupedUnique, uniqueDispatch]
theorem setPredicatesSpec : SetPredicatesSpec := by
  simp [SetPredicatesSpec, allunique, hashedAllunique, indexedAllunique, alluniqueDispatch, alluniqueMap, alluniqueSet, alluniqueString, alluniqueTuple, alluniqueEmptyTuple, allequal, allequalSet, allequalMap, allequalLoop, allequalTuple, allequalEmptyTuple]
  intro xs
  rfl
theorem setHelpersSpec : SetHelpersSpec := by simp [SetHelpersSpec, setFilterBang, setHash, setConvertSame, setConvert, checkCount, copyOfType, similarOrCopy]
theorem setReplaceSpec : SetReplaceSpec := by
  simp [SetReplaceSpec, replacePairs, replacePairsBang, replaceCallableBang, replacePairsCopy, promoteValueType, subtractSingleton, replaceCallableCopy, replaceAmbiguous, askeyDict, askeySet, replaceCollection, replaceArray, replaceDict, replaceSet, replaceTuplePairs]
  intro ps x
  rfl
end JuliaLean.BitSetsCov.Coll
