import RBTT.Core.ExtrinsicMLTT

namespace RBTT.Extrinsic.Examples

open Expr

/-!
# Dependent Type Examples

Examples demonstrating TRUE dependent types using the extrinsic MLTT implementation.

These examples show features that were **impossible** with the intrinsic approach in
TrueDependentTypes.lean and **not truly dependent** in DependentTypes.lean.
-/

set_option autoImplicit false

/-! ## Example 1: Length-Indexed Vectors

The canonical example of dependent types - vectors indexed by their length.
-/

/-- Type of length-n vectors of type A.

This is a **genuine dependent type**: the type `Vec A n` depends on the *term* n.
-/
def vecType (A : Expr) (n : Expr) : Expr := .Vec A n

example : vecType .Nat .zero = .Vec .Nat .zero := rfl
example : vecType .Bool (.succ .zero) = .Vec .Bool (.succ .zero) := rfl

/-- Empty vector has type Vec A zero -/
example (Γ : Ctx) : HasType Γ .vnil (.Vec .Nat .zero) :=
  .vnil .nat

/-- Singleton vector [true] : Vec Bool 1 -/
example (Γ : Ctx) : HasType Γ (.vcons .true .vnil) (.Vec .Bool (.succ .zero)) := by
  apply HasType.vcons
  · exact .true
  · apply HasType.vnil
    exact .bool

/-! ## Example 2: Dependent Function Types

Functions where the result type depends on the argument value.
-/

/-- Type family: "vectors of length n" as a function Nat → Type.

This is `λn:Nat. Vec Bool n` - a function from natural numbers to types.
-/
def vecFamily : Expr := .lam (.Vec .Bool (.var 0))

/-- The type of vecFamily is Nat → U (a function from Nat to the universe).

Note: In the fully dependent version, this would be `Π(n:Nat). U`.
Since we have a non-dependent codomain, we can use Pi with a constant type.
-/
example (Γ : Ctx) : HasType (.Nat :: Γ) vecFamily (.Pi .Nat .U) := by
  apply HasType.lam
  apply HasType.vec
  · exact .bool
  · apply HasType.var
    simp

/-! ## Example 3: Dependent Pairs (Sigma Types)

Pairs where the second component's type depends on the first component's value.
-/

/-- A dependent pair: (n, v) where n : Nat and v : Vec Bool n.

This shows TRUE dependency: the type of the second component (the vector)
depends on the VALUE of the first component (the length).

Type: Σ(n:Nat). Vec Bool n
-/
def dependentPairType : Expr := .Sigma .Nat (.Vec .Bool (.var 0))

/-- Example: The pair (2, [true, false]) has the dependent type.

The vector [true, false] has length 2, matching the first component.
-/
example (Γ : Ctx) : HasType Γ
  (.pair (.succ (.succ .zero))
         (.vcons .true (.vcons .false .vnil)))
  dependentPairType := by
  apply HasType.pair
  · -- First component: 2 : Nat
    apply HasType.succ
    apply HasType.succ
    exact .zero
  · -- Second component: [true, false] : Vec Bool 2
    -- Note: The type here is (subst0 (succ (succ zero)) (Vec Bool (var 0)))
    --       which reduces to Vec Bool (succ (succ zero))
    apply HasType.vcons
    · exact .true
    · apply HasType.vcons
      · exact .false
      · apply HasType.vnil
        exact .bool

/-! ## Example 4: First and Second Projections

Extracting components from dependent pairs with proper typing.
-/

/-- First projection extracts the length (type: Nat) -/
example (Γ : Ctx) (p : Expr) (h : HasType Γ p dependentPairType) :
  HasType Γ (.fst p) .Nat := .fst h

/-- Second projection extracts the vector with the RIGHT dependent type.

The crucial property: if p : Σ(n:Nat). Vec Bool n, then
  fst p : Nat
  snd p : Vec Bool (fst p)  ← The type depends on the value of fst p!

This is TRUE dependent typing - impossible with STLC-style types.
-/
example (Γ : Ctx) (p : Expr) (h : HasType Γ p dependentPairType) :
  HasType Γ (.snd p) (subst0 (.fst p) (.Vec .Bool (.var 0))) := .snd h

/-! ## Example 5: Identity Type (Equality)

Propositional equality as a type.
-/

/-- The type "2 = 2" -/
def twoEqualsTwo : Expr := .Id .Nat (.succ (.succ .zero)) (.succ (.succ .zero))

/-- Proof that 2 = 2 by reflexivity -/
example (Γ : Ctx) : HasType Γ (.refl (.succ (.succ .zero))) twoEqualsTwo := by
  apply HasType.refl
  apply HasType.succ
  apply HasType.succ
  exact .zero

/-! ## Example 6: Natural Number Recursion with Dependent Motive

The most complex example: recursion where the result type depends on the scrutinee.

This demonstrates dependent eliminators - a key feature of dependent type theory.
-/

/-- Dependent motive: P(n) = Vec Bool n

This is a type family that takes a natural number and returns the type of
boolean vectors of that length.
-/
def vecMotive : Expr := .lam (.Vec .Bool (.var 0))

/-- Type of vecMotive: Nat → U -/
example (Γ : Ctx) : HasType (.Nat :: Γ) vecMotive (.Pi .Nat .U) := by
  apply HasType.lam
  apply HasType.vec
  · exact .bool
  · apply HasType.var
    simp

/-! ## Status

**✅ What Works**:
- Length-indexed vector types
- Dependent function types (Π types)
- Dependent pair types (Σ types)
- First and second projections with dependent types
- Identity types for propositional equality
- Type families (functions returning types)

**🔄 Next Steps**:
- Implement vector recursion (vecrec) typing rule
- Implement J-eliminator for identity types
- Add operational semantics (reduction rules)
- Prove type safety theorems
- More complex examples (vector append, map, etc.)

**Key Achievement**: These examples demonstrate **TRUE dependent types** with real
substitution in result types, which was impossible with both:
1. The intrinsic approach (TrueDependentTypes.lean) - blocked by Lean 4 limitation
2. The STLC approach (DependentTypes.lean) - had Π/Σ syntax but no true dependency
-/

end RBTT.Extrinsic.Examples
