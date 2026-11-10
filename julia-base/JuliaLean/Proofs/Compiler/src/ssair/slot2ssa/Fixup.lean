import JuliaLean.Proofs.Compiler.src.ssair.slot2ssa.Spec

/-!
The check of `fixup_uses!` (Compiler/src/ssair/slot2ssa.jl:151-155): on every vector of two
lowered statements built from slot 2 (the slot being fixed), slot 3 and a literal, with the use
list `scan_slot_def_use` gives for slot 2, `fixup_uses!` replaces each read of slot 2 by the new
value and changes nothing else; for `UNDEF_TOKEN`, it puts an undef error before each use.
-/

namespace JuliaLean.Proofs.Compiler.src.ssair.slot2ssa

open JuliaLean.Compiler.ssair
open JuliaLean.Proofs.Compiler.src.ssair.domtree

mutual
/-- Structural equality of IR values (`===` on the node trees). -/
def irvEq : IRV → IRV → Bool
  | .nothing, .nothing => true
  | .undefTok, .undefTok => true
  | .slot a, .slot b => a == b
  | .ssa a, .ssa b => a == b
  | .newssa a, .newssa b => a == b
  | .arg a, .arg b => a == b
  | .glob a, .glob b => a == b
  | .sym a, .sym b => a == b
  | .lit a, .lit b => a == b
  | .quot a, .quot b => a == b
  | .expr h ⟨a⟩, .expr h' ⟨b⟩ => h == h' && irvListEq a b
  | .goto a, .goto b => a == b
  | .gotoifnot c d, .gotoifnot c' d' => irvEq c c' && d == d'
  | .ret o, .ret o' => irvOptEq o o'
  | .enter c o, .enter c' o' => c == c' && irvOptEq o o'
  | .newvar a, .newvar b => a == b
  | .phi e ⟨v⟩, .phi e' ⟨w⟩ => e == e' && irvOptListEq v w
  | .phic ⟨v⟩, .phic ⟨w⟩ => irvOptListEq v w
  | .upsilon o, .upsilon o' => irvOptEq o o'
  | .pinode v t, .pinode v' t' => irvEq v v' && t == t'
  | _, _ => false
def irvListEq : List IRV → List IRV → Bool
  | [], [] => true
  | a :: as, b :: bs => irvEq a b && irvListEq as bs
  | _, _ => false
def irvOptEq : Option IRV → Option IRV → Bool
  | none, none => true
  | some a, some b => irvEq a b
  | _, _ => false
def irvOptListEq : List (Option IRV) → List (Option IRV) → Bool
  | [], [] => true
  | a :: as, b :: bs => irvOptEq a b && irvOptListEq as bs
  | _, _ => false
end

instance : BEq IRV := ⟨irvEq⟩

/-- The operands of the generated statements. -/
def fxAtoms : List IRV := [.slot 2, .slot 3, .lit "Int64:1"]

/-- The generated statements: a bare operand, a call on two operands, an assignment to slot 2
or 3 of an operand or of a call, `@isdefined` of slot 2 or 3, a conditional jump, a return, a
phi node with one edge, a `NewvarNode` and `nothing`. -/
def fxStmts : List IRV :=
  fxAtoms ++
  (fxAtoms.flatMap fun a => fxAtoms.map fun b => IRV.expr "call" #[.glob "Main.f", a, b]) ++
  ([2, 3].flatMap fun (t : Int) =>
    (fxAtoms ++ fxAtoms.map fun a => IRV.expr "call" #[.glob "Main.f", a]).map fun r =>
      IRV.expr "=" #[.slot t, r]) ++
  [2, 3].map (fun (s : Int) => IRV.expr "isdefined" #[.slot s]) ++
  fxAtoms.map (fun a => IRV.gotoifnot a 1) ++ fxAtoms.map (fun a => IRV.ret (some a)) ++
  fxAtoms.map (fun a => IRV.phi #[1] #[some a]) ++ [IRV.newvar 2, IRV.nothing]

/-- An operand with slot `s` replaced by `r`. -/
def substAtom (s : Int) (r : IRV) : IRV → IRV
  | .slot t => if t == s then r else .slot t
  | v => v

/-- The right side of an assignment with its reads of slot `s` replaced by `r`. -/
def substRhs (s : Int) (r : IRV) : IRV → IRV
  | .expr h args => .expr h (args.map (substAtom s r))
  | v => substAtom s r v

/-- A statement with every read of slot `s` replaced by `r`, by definition: the operands, the
right side of an assignment (not the slot assigned), the phi values; and `@isdefined(s)` is
`true`, since the new value is defined. -/
def substReads (s : Int) (r : IRV) : IRV → IRV
  | .slot t => substAtom s r (.slot t)
  | .expr "=" #[l, rhs] => .expr "=" #[l, substRhs s r rhs]
  | .expr "isdefined" #[.slot t] =>
    if t == s then IRV.boolLit true else .expr "isdefined" #[.slot t]
  | .expr h args => .expr h (args.map (substAtom s r))
  | .gotoifnot c d => .gotoifnot (substAtom s r c) d
  | .ret (some v) => .ret (some (substAtom s r v))
  | .phi e vals => .phi e (vals.map (Option.map (substAtom s r)))
  | v => v

def fxCtx : FixCtx := ⟨#["#self#", "x", "y"], #[]⟩

/-- The IR the two statements sit in: one block. -/
def fxIR (code : Array IRV) (nt : Array Bool) : SIR :=
  ⟨code, nt, ⟨#[⟨1, code.size, #[0], #[]⟩], #[]⟩, #[]⟩

def slotUses (r : Array SlotInfo) (s : Nat) : List Int := ((r[s]?.map (·.uses)).getD #[]).toList
def slotDefs (r : Array SlotInfo) (s : Nat) : List Int := ((r[s]?.map (·.defs)).getD #[]).toList

/-- `fixup_uses!(ir, ci, code, uses, 2, ssa)` with `uses` the uses of slot 2 by
`scan_slot_def_use`:

* for an `ssa` other than `UNDEF_TOKEN`: it returns, inserts no node, each use statement becomes
  `substReads 2 ssa` of itself and every other statement is unchanged; and on the result
  `scan_slot_def_use` finds no use of slot 2, the same defs of slot 2, and the same defs and
  uses of slot 3;
* for `UNDEF_TOKEN`: it returns, every statement that is not a use is unchanged, every node it
  inserts is `throw_undef_if_not(:x, false)`, and each use statement other than `@isdefined(x)`
  has one before it (for a phi node, before the last statement of the block of its edge); with
  `strict`, a use `@isdefined(x)` becomes `false`, since the slot has no value. -/
def fixupOK (strict : Bool) (code : Array IRV) (nt : Array Bool) (ssa : IRV) : Bool :=
  jmIs (scanSlotDefUse 1 3 code) fun r0 =>
    let uses := slotUses r0 1
    jmIs (fixupUses! fxCtx (fxIR code nt) code uses.toArray 2 ssa) fun (ir, code') =>
      code'.size == code.size &&
      match ssa with
      | .undefTok =>
        let throwAt (p : Int) := ir.newNodes.any fun n =>
          n.pos == p && n.stmt == .expr "throw_undef_if_not" #[.sym "x", IRV.boolLit false]
        ir.newNodes.all (fun n =>
          n.stmt == .expr "throw_undef_if_not" #[.sym "x", IRV.boolLit false]) &&
        (irange 1 code.size).all fun i =>
          let c := code.getD (i - 1).toNat .nothing
          if uses.contains i then
            match c with
            | .phi _ _ => throwAt code.size
            | .expr "isdefined" _ =>
              !strict || code'.getD (i - 1).toNat .nothing == IRV.boolLit false
            | _ => throwAt i
          else code'.getD (i - 1).toNat .nothing == c
      | _ =>
        ir.newNodes.isEmpty &&
        (irange 1 code.size).all (fun i =>
          let c := code.getD (i - 1).toNat .nothing
          code'.getD (i - 1).toNat .nothing == (if uses.contains i then substReads 2 ssa c else c)) &&
        jmIs (scanSlotDefUse 1 3 code') fun r1 =>
          slotUses r1 1 == [] && slotDefs r1 1 == slotDefs r0 1 &&
          slotUses r1 2 == slotUses r0 2 && slotDefs r1 2 == slotDefs r0 2

/-- `fixupOK` for every first statement `a`, every second statement, both `IR_FLAG_NOTHROW`
flags, and the new values `SSAValue(9)`, `Argument(2)` and `UNDEF_TOKEN`. -/
def fixupOKFrom (strict : Bool) (a : IRV) : Bool :=
  fxStmts.all fun b => [false, true].all fun n1 => [false, true].all fun n2 =>
    [IRV.ssa 9, .arg 2, .undefTok].all fun ssa => fixupOK strict #[a, b] #[n1, n2] ssa

/-- `fixup_uses!` replaces every read of the slot in its use statements by the new value and
changes nothing else, and for `UNDEF_TOKEN` puts an undef error before every use other than
`@isdefined` (`fixupOK false`), on every pair of statements of `fxStmts`. -/
def FixupUsesSmall : Prop := fxStmts.all (fixupOKFrom false) = true

/-- The same, and for `UNDEF_TOKEN` a use `@isdefined(x)` becomes `false` (`fixupOK true`). -/
def FixupIsdefinedUndef : Prop := fxStmts.all (fixupOKFrom true) = true

theorem fixup_0 : fixupOKFrom false (fxStmts.getD 0 .nothing) = true := by decide +kernel
theorem fixup_1 : fixupOKFrom false (fxStmts.getD 1 .nothing) = true := by decide +kernel
theorem fixup_2 : fixupOKFrom false (fxStmts.getD 2 .nothing) = true := by decide +kernel
theorem fixup_3 : fixupOKFrom false (fxStmts.getD 3 .nothing) = true := by decide +kernel
theorem fixup_4 : fixupOKFrom false (fxStmts.getD 4 .nothing) = true := by decide +kernel
theorem fixup_5 : fixupOKFrom false (fxStmts.getD 5 .nothing) = true := by decide +kernel
theorem fixup_6 : fixupOKFrom false (fxStmts.getD 6 .nothing) = true := by decide +kernel
theorem fixup_7 : fixupOKFrom false (fxStmts.getD 7 .nothing) = true := by decide +kernel
theorem fixup_8 : fixupOKFrom false (fxStmts.getD 8 .nothing) = true := by decide +kernel
theorem fixup_9 : fixupOKFrom false (fxStmts.getD 9 .nothing) = true := by decide +kernel
theorem fixup_10 : fixupOKFrom false (fxStmts.getD 10 .nothing) = true := by decide +kernel
theorem fixup_11 : fixupOKFrom false (fxStmts.getD 11 .nothing) = true := by decide +kernel
theorem fixup_12 : fixupOKFrom false (fxStmts.getD 12 .nothing) = true := by decide +kernel
theorem fixup_13 : fixupOKFrom false (fxStmts.getD 13 .nothing) = true := by decide +kernel
theorem fixup_14 : fixupOKFrom false (fxStmts.getD 14 .nothing) = true := by decide +kernel
theorem fixup_15 : fixupOKFrom false (fxStmts.getD 15 .nothing) = true := by decide +kernel
theorem fixup_16 : fixupOKFrom false (fxStmts.getD 16 .nothing) = true := by decide +kernel
theorem fixup_17 : fixupOKFrom false (fxStmts.getD 17 .nothing) = true := by decide +kernel
theorem fixup_18 : fixupOKFrom false (fxStmts.getD 18 .nothing) = true := by decide +kernel
theorem fixup_19 : fixupOKFrom false (fxStmts.getD 19 .nothing) = true := by decide +kernel
theorem fixup_20 : fixupOKFrom false (fxStmts.getD 20 .nothing) = true := by decide +kernel
theorem fixup_21 : fixupOKFrom false (fxStmts.getD 21 .nothing) = true := by decide +kernel
theorem fixup_22 : fixupOKFrom false (fxStmts.getD 22 .nothing) = true := by decide +kernel
theorem fixup_23 : fixupOKFrom false (fxStmts.getD 23 .nothing) = true := by decide +kernel
theorem fixup_24 : fixupOKFrom false (fxStmts.getD 24 .nothing) = true := by decide +kernel
theorem fixup_25 : fixupOKFrom false (fxStmts.getD 25 .nothing) = true := by decide +kernel
theorem fixup_26 : fixupOKFrom false (fxStmts.getD 26 .nothing) = true := by decide +kernel
theorem fixup_27 : fixupOKFrom false (fxStmts.getD 27 .nothing) = true := by decide +kernel
theorem fixup_28 : fixupOKFrom false (fxStmts.getD 28 .nothing) = true := by decide +kernel
theorem fixup_29 : fixupOKFrom false (fxStmts.getD 29 .nothing) = true := by decide +kernel
theorem fixup_30 : fixupOKFrom false (fxStmts.getD 30 .nothing) = true := by decide +kernel
theorem fixup_31 : fixupOKFrom false (fxStmts.getD 31 .nothing) = true := by decide +kernel
theorem fixup_32 : fixupOKFrom false (fxStmts.getD 32 .nothing) = true := by decide +kernel
theorem fixup_33 : fixupOKFrom false (fxStmts.getD 33 .nothing) = true := by decide +kernel
theorem fixup_34 : fixupOKFrom false (fxStmts.getD 34 .nothing) = true := by decide +kernel
theorem fixup_35 : fixupOKFrom false (fxStmts.getD 35 .nothing) = true := by decide +kernel
theorem fixup_36 : fixupOKFrom false (fxStmts.getD 36 .nothing) = true := by decide +kernel

theorem fxStmts_eq : fxStmts = [fxStmts.getD 0 .nothing, fxStmts.getD 1 .nothing, fxStmts.getD 2 .nothing, fxStmts.getD 3 .nothing, fxStmts.getD 4 .nothing, fxStmts.getD 5 .nothing, fxStmts.getD 6 .nothing, fxStmts.getD 7 .nothing, fxStmts.getD 8 .nothing, fxStmts.getD 9 .nothing, fxStmts.getD 10 .nothing, fxStmts.getD 11 .nothing, fxStmts.getD 12 .nothing, fxStmts.getD 13 .nothing, fxStmts.getD 14 .nothing, fxStmts.getD 15 .nothing, fxStmts.getD 16 .nothing, fxStmts.getD 17 .nothing, fxStmts.getD 18 .nothing, fxStmts.getD 19 .nothing, fxStmts.getD 20 .nothing, fxStmts.getD 21 .nothing, fxStmts.getD 22 .nothing, fxStmts.getD 23 .nothing, fxStmts.getD 24 .nothing, fxStmts.getD 25 .nothing, fxStmts.getD 26 .nothing, fxStmts.getD 27 .nothing, fxStmts.getD 28 .nothing, fxStmts.getD 29 .nothing, fxStmts.getD 30 .nothing, fxStmts.getD 31 .nothing, fxStmts.getD 32 .nothing, fxStmts.getD 33 .nothing, fxStmts.getD 34 .nothing, fxStmts.getD 35 .nothing, fxStmts.getD 36 .nothing] := rfl

theorem fixupUsesSmall_proven : FixupUsesSmall := by
  unfold FixupUsesSmall
  rw [fxStmts_eq]
  simp only [List.all_cons, List.all_nil, fixup_0, fixup_1, fixup_2, fixup_3, fixup_4, fixup_5, fixup_6, fixup_7, fixup_8, fixup_9, fixup_10, fixup_11, fixup_12, fixup_13, fixup_14, fixup_15, fixup_16, fixup_17, fixup_18, fixup_19, fixup_20, fixup_21, fixup_22, fixup_23, fixup_24, fixup_25, fixup_26, fixup_27, fixup_28, fixup_29, fixup_30, fixup_31, fixup_32, fixup_33, fixup_34, fixup_35, fixup_36, Bool.and_self]

/-- `fixup_uses!(ir, ci, code, [2], 2, UNDEF_TOKEN)` on `code = [nothing, @isdefined(x)]` turns
`@isdefined(x)` into `true`: the renaming it passes is `UNDEF_TOKEN => true`, and the
`@isdefined` case of `fixemup!` returns the second half. -/
theorem fixupIsdefined_true :
    (match fixupUses! fxCtx (fxIR #[.nothing, .expr "isdefined" #[.slot 2]] #[false, false])
        #[.nothing, .expr "isdefined" #[.slot 2]] #[2] 2 .undefTok with
     | .ok (_, code) => code.getD 1 .nothing == IRV.boolLit true
     | .error _ => false) = true := by decide +kernel

theorem fixupIsdefinedUndef_refuted : ¬ FixupIsdefinedUndef := fun h => by
  have h2 : fxStmts.all (fixupOKFrom true) = false := by decide +kernel
  unfold FixupIsdefinedUndef at h
  rw [h2] at h
  exact Bool.false_ne_true h

end JuliaLean.Proofs.Compiler.src.ssair.slot2ssa
