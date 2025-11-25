import RBTT.Core

namespace RBTT.Examples

/-!
# Resource Context Properties - Test Suite

Tests for Items #1-2 from the action list:
- ResCtx ordering properties (reflexivity, transitivity, calc mode)
- Monotonicity of ⊕
- FeasibleNat operations (fadd, widen)
-/

section ResCtxTests

variable (R S T : ResCtx)

/-- Test: Reflexivity -/
example : R ≤ R := by simp

/-- Test: Transitivity via explicit theorem -/
example (h1 : R ≤ S) (h2 : S ≤ T) : R ≤ T :=
  le_trans h1 h2

/-- Test: Transitivity via calc mode (Trans instance!) -/
example (h1 : R ≤ S) (h2 : S ≤ T) : R ≤ T := by
  calc R ≤ S := h1
       _ ≤ T := h2

/-- Test: Left monotonicity of ⊕ -/
example (h : R ≤ S) : (R ⊕ T) ≤ (S ⊕ T) := by
  simp [h]

/-- Test: Right monotonicity of ⊕ -/
example (h : S ≤ T) : (R ⊕ S) ≤ (R ⊕ T) := by
  simp [h]

/-- Test: Combined monotonicity -/
example (h1 : R ≤ S) (h2 : R ≤ T) : (R ⊕ R) ≤ (S ⊕ T) := by
  have left := add_mono_left h1
  have right := add_mono_right h2
  calc (R ⊕ R) ≤ (S ⊕ R) := left
       _       ≤ (S ⊕ T) := right

/-- Test: Resource addition properties -/
example : (R ⊕ S).time = R.time + S.time := by simp
example : (R ⊕ S).memory = R.memory + S.memory := by simp
example : (R ⊕ S).depth = Nat.max R.depth S.depth := by simp

end ResCtxTests

section FeasibleNatTests

variable (R S : ResCtx) (h_ord : R ≤ S)

/-- Test: Creating a feasible nat -/
example : FeasibleNat R :=
  { val := 5
  , bound := 10
  , val_le_bound := by decide
  , bound_le_time := by decide : 10 ≤ 100 }
  where R : ResCtx := { time := 100, memory := 1024, depth := 5 }

/-- Test: Feasible addition -/
example (x y : FeasibleNat R) (h : x.bound + y.bound ≤ R.time) :
    (FeasibleNat.fadd x y h).val = x.val + y.val := by
  simp

example (x y : FeasibleNat R) (h : x.bound + y.bound ≤ R.time) :
    (FeasibleNat.fadd x y h).bound = x.bound + y.bound := by
  simp

/-- Test: Widening preserves value -/
example (x : FeasibleNat R) :
    (FeasibleNat.widen h_ord x).val = x.val := by
  simp

/-- Test: Widening preserves bound -/
example (x : FeasibleNat R) :
    (FeasibleNat.widen h_ord x).bound = x.bound := by
  simp

/-- Test: Full example with concrete values -/
example : True := by
  let R : ResCtx := { time := 100, memory := 2048, depth := 5 }
  let x : FeasibleNat R :=
    { val := 10, bound := 20
    , val_le_bound := by decide
    , bound_le_time := by decide }
  let y : FeasibleNat R :=
    { val := 15, bound := 25
    , val_le_bound := by decide
    , bound_le_time := by decide }
  let z := FeasibleNat.fadd x y (by decide : x.bound + y.bound ≤ R.time)

  -- Verify properties
  have : z.val = 25 := rfl
  have : z.bound = 45 := rfl
  have : z.val ≤ z.bound := z.val_le_bound
  have : z.bound ≤ R.time := z.bound_le_time

  trivial

end FeasibleNatTests

section ModalityTests

open Box

variable {A B : Type} (R S : ResCtx) (h_ord : R ≤ S)

/-- Test: Counit extracts value -/
example (b : Box R A) : counit b = b.val := rfl

/-- Test: Weakening preserves value -/
example (b : Box R A) : (weaken h_ord b).val = b.val := by simp

/-- Test: Map functoriality -/
example (f : A → B) (b : Box R A) : (map f b).val = f b.val := by simp

/-- Test: Product preservation -/
example (ba : Box R A) (bb : Box R B) :
    (box_prod (ba, bb)).val = (ba.val, bb.val) := rfl

/-- Test: Comultiplication -/
example (R₁ R₂ : ResCtx) (b : Box (R₁ ⊕ R₂) A) :
    (comult b).val.val = b.val := rfl

end ModalityTests

section STLCTests

open Ty Tm

/-- Test: Identity function is well-typed with bound 0 -/
example (R : ResCtx) :
    [] ⊢[R;0] lam (var Var.zero) : (nat ⇒ nat) :=
  HasBound.lam HasBound.var

/-- Test: Application increases bound by 1 -/
example (R : ResCtx) :
    [] ⊢[R;1] app (lam (var Var.zero)) (natLit 5) : nat :=
  HasBound.app
    (HasBound.lam HasBound.var)
    HasBound.natLit

/-- Test: Conditional has max-bound rule -/
example (R : ResCtx) :
    [] ⊢[R;1] ite true (natLit 1) (natLit 2) : nat :=
  HasBound.ite
    HasBound.true
    HasBound.natLit
    HasBound.natLit

/-- Test: Pair has additive bounds -/
example (R : ResCtx) :
    [] ⊢[R;0] pair (natLit 3) (natLit 4) : (nat × nat) :=
  HasBound.pair HasBound.natLit HasBound.natLit

end STLCTests

end RBTT.Examples
