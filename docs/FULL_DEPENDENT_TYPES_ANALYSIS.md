# Full Dependent Types: Requirements Analysis

**Date**: 2026-01-06
**Status**: Architecture Design Document
**Purpose**: Outline what's needed to upgrade from Option A (simplified) to full dependent types

---

## Executive Summary

**Current State**: We have MLTT-style syntax (`pi`, `sigma`, `natrec`, `vecrec`) but with **STLC semantics** (non-dependent).

**Target State**: True dependent types where:
- Types can depend on term values
- `pi A B` where `B : Ty (Γ, x:A)` depends on `x`
- Application `app f a` has type `B[a/x]` (substitution required)
- Indexed types like `Vec A n` where `n : Nat`

**Effort Estimate**: 40-60 hours even with axiomatized proofs, due to:
1. Complex type system refactoring (mutual recursion, universe levels)
2. Substitution infrastructure (hardest part)
3. Lean 4 technical challenges (universe polymorphism, positivity checking)

---

## Part 1: Core Type System Changes

### 1.1 Context-Indexed Types

**Current (Option A)**:
```lean
inductive DepTy : Type where
  | nat   : DepTy
  | pi    : DepTy → DepTy → DepTy      -- NOT dependent!
  | sigma : DepTy → DepTy → DepTy
  | vec   : DepTy → DepTy

abbrev DepCtx := List DepTy
```

**Required (True Dependent Types)**:
```lean
mutual
  /-- Contexts as telescopes -/
  inductive TrueCtx : Type where
    | nil  : TrueCtx
    | snoc : (Γ : TrueCtx) → TrueTy Γ → TrueCtx

  /-- Types indexed by context -/
  inductive TrueTy : TrueCtx → Type 1 where
    | nat   : ∀ {Γ}, TrueTy Γ
    | pi    : ∀ {Γ}, (A : TrueTy Γ) → TrueTy (TrueCtx.snoc Γ A) → TrueTy Γ
    | sigma : ∀ {Γ}, (A : TrueTy Γ) → TrueTy (TrueCtx.snoc Γ A) → TrueTy Γ
    | vec   : ∀ {Γ}, TrueTy Γ → TrueTm Γ nat → TrueTy Γ  -- length-indexed!
    | idty  : ∀ {Γ}, (A : TrueTy Γ) → TrueTm Γ A → TrueTm Γ A → TrueTy Γ

  /-- Terms indexed by context and type -/
  inductive TrueTm : (Γ : TrueCtx) → TrueTy Γ → Type where
    | var  : ∀ {Γ A}, TrueVar Γ A → TrueTm Γ A
    | lam  : ∀ {Γ A B}, TrueTm (TrueCtx.snoc Γ A) B → TrueTm Γ (TrueTy.pi A B)
    | app  : ∀ {Γ A B}, TrueTm Γ (TrueTy.pi A B) → (a : TrueTm Γ A) → TrueTm Γ (B[a])  -- SUBSTITUTION!
    -- ... more constructors

  /-- Variables with weakening -/
  inductive TrueVar : (Γ : TrueCtx) → TrueTy Γ → Type where
    | zero : ∀ {Γ A}, TrueVar (TrueCtx.snoc Γ A) (weaken A)
    | succ : ∀ {Γ A B}, TrueVar Γ A → TrueVar (TrueCtx.snoc Γ B) (weaken A)
end
```

**Key Changes**:
1. `mutual ... end` block for mutually recursive definitions
2. `TrueTy : TrueCtx → Type 1` (indexed by context, universe level 1)
3. `pi A B` where `B : TrueTy (Γ.snoc A)` - the codomain lives in extended context
4. `vec A n` where `n : TrueTm Γ nat` - length as term dependency
5. `idty A a b` for equality types with two endpoints

---

## Part 2: Substitution Infrastructure

### 2.1 Type Substitution (Most Critical)

**What We Need**:
```lean
/-- Substitute term `a : A` for variable 0 in type `B : Ty (Γ, x:A)` -/
def substTy {Γ : TrueCtx} {A : TrueTy Γ} :
    (B : TrueTy (TrueCtx.snoc Γ A)) → TrueTm Γ A → TrueTy Γ :=
  sorry  -- This is the HARD part

notation:max B "[" a "]" => substTy B a
```

**Why It's Hard**:
- Must traverse type structure recursively
- Must handle De Bruijn index shifting
- Must preserve well-formedness
- Interacts with weakening in complex ways

**Lean 4 Challenges**:
- **Termination**: Lean must prove substitution terminates
- **Universe levels**: Must carefully manage `Type 1` vs `Type 0`
- **Positivity**: Ensure inductive definitions are strictly positive

**Axiomatized Version** (for scaffold):
```lean
axiom substTy {Γ : TrueCtx} {A : TrueTy Γ} :
    TrueTy (TrueCtx.snoc Γ A) → TrueTm Γ A → TrueTy Γ

axiom substTm {Γ : TrueCtx} {A : TrueTy Γ} {B : TrueTy (TrueCtx.snoc Γ A)} :
    TrueTm (TrueCtx.snoc Γ A) B → (a : TrueTm Γ A) → TrueTm Γ (substTy B a)
```

### 2.2 Weakening Operations

**What We Need**:
```lean
/-- Weaken type from Γ to Γ, x:B -/
axiom weaken {Γ : TrueCtx} {B : TrueTy Γ} : TrueTy Γ → TrueTy (TrueCtx.snoc Γ B)

/-- Weaken term from Γ to Γ, x:B -/
axiom weakenTm {Γ : TrueCtx} {A B : TrueTy Γ} :
    TrueTm Γ A → TrueTm (TrueCtx.snoc Γ B) (weaken A)
```

**Substitution Lemmas** (even axiomatized, these are needed):
```lean
-- Substitution preserves typing
axiom subst_preserves_typing {Γ : TrueCtx} {A : TrueTy Γ} {B : TrueTy (TrueCtx.snoc Γ A)}
    {t : TrueTm (TrueCtx.snoc Γ A) B} {a : TrueTm Γ A} :
    TrueTm Γ (substTy B a)  -- t[a] has type B[a]

-- Weakening commutes with substitution
axiom weaken_subst {Γ : TrueCtx} {A B C : TrueTy Γ} {t : TrueTm Γ A} :
    substTy (weaken B) t = B  -- if B doesn't mention the variable

-- Substitution composition
axiom subst_comp {Γ : TrueCtx} {A : TrueTy Γ} {B : TrueTy (TrueCtx.snoc Γ A)}
    {C : TrueTy (TrueCtx.snoc (TrueCtx.snoc Γ A) B)}
    {a : TrueTm Γ A} {b : TrueTm (TrueCtx.snoc Γ A) B} :
    substTy (substTy C b) a = substTy (substTy C (weakenTm a)) (substTm b a)
```

---

## Part 3: Term Constructors with Dependency

### 3.1 Dependent Application

**Current (Option A)**:
```lean
| app : DepTm Γ (DepTy.pi A B) → DepTm Γ A → DepTm Γ B  -- B is just a type
```

**Required (True Dependent)**:
```lean
| app : ∀ {Γ A B},
        TrueTm Γ (TrueTy.pi A B) →
        (a : TrueTm Γ A) →
        TrueTm Γ (substTy B a)  -- Result type DEPENDS on argument a
```

**Impact**: Every use of `app` now requires substitution infrastructure.

### 3.2 Dependent Pairs

**Current (Option A)**:
```lean
| pair : DepTm Γ A → DepTm Γ B → DepTm Γ (DepTy.sigma A B)
| snd  : DepTm Γ (DepTy.sigma A B) → DepTm Γ B  -- B is just a type
```

**Required (True Dependent)**:
```lean
| pair : ∀ {Γ A B},
         (a : TrueTm Γ A) →
         TrueTm Γ (substTy B a) →  -- Second component has type B[a]
         TrueTm Γ (TrueTy.sigma A B)

| fst  : ∀ {Γ A B}, TrueTm Γ (TrueTy.sigma A B) → TrueTm Γ A

| snd  : ∀ {Γ A B},
         (p : TrueTm Γ (TrueTy.sigma A B)) →
         TrueTm Γ (substTy B (fst p))  -- Type depends on first projection!
```

### 3.3 Natural Number Recursion (Dependent Motive)

**Current (Option A)**:
```lean
| natrec : DepTm Γ A →                                  -- z-case
           DepTm Γ (DepTy.pi DepTy.nat (DepTy.pi A A)) → -- step
           DepTm Γ DepTy.nat →                          -- scrutinee
           DepTm Γ A                                    -- result (fixed type A)
```

**Required (True Dependent)**:
```lean
| natrec : ∀ {Γ},
           (P : TrueTy (TrueCtx.snoc Γ nat)) →          -- Motive: nat → Type
           TrueTm Γ (substTy P zero) →                  -- z-case: P(0)
           TrueTm Γ (∀ n, P n → P (succ n)) →           -- step: ∀n. P(n) → P(n+1)
           (n : TrueTm Γ nat) →                         -- scrutinee
           TrueTm Γ (substTy P n)                       -- result: P(n)
```

**Key Difference**: The motive `P : nat → Type` allows the result type to depend on the natural number.

### 3.4 Length-Indexed Vectors

**Current (Option A)**:
```lean
| vec : DepTy → DepTy  -- Length implicit
```

**Required (True Dependent)**:
```lean
| vec : ∀ {Γ}, TrueTy Γ → TrueTm Γ nat → TrueTy Γ  -- Vec A n

| vnil  : ∀ {Γ A}, TrueTm Γ (TrueTy.vec A zero)

| vcons : ∀ {Γ A n},
          TrueTm Γ A →
          TrueTm Γ (TrueTy.vec A n) →
          TrueTm Γ (TrueTy.vec A (succ n))  -- Length increases!

| vecrec : ∀ {Γ A},
           (P : TrueTy (TrueCtx.snoc Γ (TrueTy.vec A ???))) → -- Motive over vectors
           TrueTm Γ (substTy P vnil) →                        -- nil-case
           (∀ n x xs, P xs → P (vcons x xs)) →                -- cons-case
           (v : TrueTm Γ (TrueTy.vec A n)) →
           TrueTm Γ (substTy P v)
```

**Complexity**: Length indexing requires:
- Natural number arithmetic in types
- Proofs that lengths match in operations like `append`
- More complex substitution (substituting natural number expressions)

---

## Part 4: Universe Levels

### 4.1 The Universe Problem

**Current (Option A)**:
```lean
inductive DepTy : Type where  -- Universe 0
```

**Required (True Dependent)**:
```lean
inductive TrueTy : TrueCtx → Type 1 where  -- Must be Type 1!
  | nat   : TrueTy Γ
  | pi    : (A : TrueTy Γ) → TrueTy (Γ.snoc A) → TrueTy Γ
```

**Why Type 1?**
- `TrueTy Γ` is a type of types (must live in higher universe)
- `TrueTm Γ A` where `A : TrueTy Γ` lives in `Type 0`
- Without universe levels, Lean rejects the definition

### 4.2 Universe Polymorphism (Advanced)

For full MLTT, we'd want:
```lean
inductive TrueTy : TrueCtx → Type (u+1) where
  | univ  : TrueTy Γ  -- Type u lives in Type (u+1)
  | pi    : (A : TrueTy Γ) → TrueTy (Γ.snoc A) → TrueTy Γ
```

This allows:
- `Type 0 : Type 1 : Type 2 : ...`
- Impredicative polymorphism
- Function types over universes

**For scaffold**: Can defer with `Type 1` and single universe.

---

## Part 5: Cost Semantics Impact

### 5.1 Cost Judgment Changes

**Current (Option A)**:
```lean
inductive DepHasCost (R : ResCtx) : (Γ : DepCtx) → {A : DepTy} → DepTm Γ A → Nat → Prop where
  | app : DepHasCost R Γ f kf → DepHasCost R Γ a ka →
          DepHasCost R Γ (DepTm.app f a) (kf + ka + 1)
```

**Required (True Dependent)**:
```lean
inductive TrueHasCost (R : ResCtx) :
    (Γ : TrueCtx) → {A : TrueTy Γ} → TrueTm Γ A → Nat → Prop where
  | app : ∀ {Γ A B f a kf ka},
          TrueHasCost R Γ f kf →
          TrueHasCost R Γ a ka →
          TrueHasCost R Γ (@TrueTm.app Γ A B f a) (kf + ka + 1)
          -- Note: type annotation needed because result type is B[a]
```

**Key Challenge**: The cost judgment must track substitution in types.

### 5.2 Dependent Cost Analysis (Advanced)

True dependent types enable **cost bounds that depend on term values**:

```lean
-- Cost of natrec depends on the NATURAL NUMBER n, not just R.depth
| natrec : ∀ {Γ P z s n kz ks kn},
           TrueHasCost R Γ z kz →
           TrueHasCost R Γ s ks →
           TrueHasCost R Γ n kn →
           (n_val : Nat) →  -- RUNTIME VALUE of n
           TrueHasCost R Γ (TrueTm.natrec P z s n) (kz + ks + kn + n_val * ks)
           -- Cost = base + step + scrutinee + (value of n) * (step cost)
```

**This is Option B's dependent cost analysis**: costs depend on term semantics, not just syntax.

For scaffold: Can use fuel-based `R.depth * ks` bound (current Option A approach).

---

## Part 6: Identity Types (Equality)

### 6.1 Identity Type Constructor

```lean
| idty : ∀ {Γ}, (A : TrueTy Γ) → TrueTm Γ A → TrueTm Γ A → TrueTy Γ

| refl : ∀ {Γ A}, (a : TrueTm Γ A) → TrueTm Γ (TrueTy.idty A a a)
```

### 6.2 Path Induction (J-eliminator)

```lean
| J : ∀ {Γ A},
      (P : TrueTy (TrueCtx.snoc (TrueCtx.snoc (TrueCtx.snoc Γ A) A) (TrueTy.idty ...))) →
      (d : ∀ x, TrueTm Γ (P x x refl)) →  -- reflexivity case
      ∀ x y (p : TrueTm Γ (TrueTy.idty A x y)),
      TrueTm Γ (substTy P p)
```

**Complexity**: J-eliminator is one of the most complex constructors in MLTT.

For scaffold: Can add `refl` constructor but defer J-eliminator.

---

## Part 7: Implementation Phases (with `sorry` proofs)

### Phase 1: Mutual Definitions (15-20 hours)

**Goal**: Get basic structure compiling

**Tasks**:
1. Define `mutual TrueCtx`, `TrueTy`, `TrueVar`, `TrueTm`
2. Add universe level `Type 1` to `TrueTy`
3. Handle Lean 4 positivity checker
4. Fix mutual recursion termination issues

**Axiomatize**:
- Substitution operations (entire infrastructure)
- Weakening operations
- Helper lemmas

**Deliverable**: File compiles, basic terms can be constructed

### Phase 2: Substitution Axioms (10-15 hours)

**Goal**: Establish substitution interface

**Tasks**:
1. Define `axiom substTy`
2. Define `axiom substTm`
3. Add substitution notation `B[a]`
4. Axiomatize key lemmas (preservation, commutation)

**Deliverable**: Can write term constructors that use substitution

### Phase 3: Dependent Eliminators (10-15 hours)

**Goal**: Implement `app`, `snd`, `natrec` with dependency

**Tasks**:
1. Update `app` to use `B[a]` for result type
2. Update `snd` to use dependent `B[fst p]`
3. Add dependent motive to `natrec`
4. Optional: Length-indexed vectors

**Deliverable**: All term constructors defined, examples compile

### Phase 4: Cost Semantics (5-10 hours)

**Goal**: Extend cost judgment

**Tasks**:
1. Update `TrueHasCost` inductive
2. Handle substitution in cost rules
3. Axiomatize cost soundness
4. Add examples with cost bounds

**Deliverable**: Cost semantics for dependent types

---

## Part 8: Key Technical Challenges

### 8.1 Lean 4 Mutual Recursion

**Problem**: Lean 4 is strict about mutual inductive definitions.

**Solutions**:
- Use `mutual ... end` blocks
- Ensure each constructor is well-founded
- May need to split definitions into stages

**Alternative**: Use axioms for problematic parts:
```lean
axiom TrueTy : TrueCtx → Type 1
axiom TrueTm : (Γ : TrueCtx) → TrueTy Γ → Type
-- Define constructors separately
```

### 8.2 Universe Level Management

**Problem**: `Type 1` vs `Type 0` vs `Type u`

**Solutions**:
- Start with concrete `Type 1` (not polymorphic)
- Use `.{1}` annotations when needed
- Accept universe restrictions for MVP

### 8.3 Positivity and Termination

**Problem**: Lean must verify:
- Inductive types are strictly positive
- Recursive functions terminate

**Solutions**:
- Axiomatize problematic operations
- Use `partial` for functions that don't terminate
- Defer termination proofs with `sorry`

### 8.4 Substitution Complexity

**Problem**: Substitution is the hardest part.

**Solutions**:
- **For scaffold**: Completely axiomatize
- **For production**: Use existing Lean libraries (e.g., `mathlib` has substitution infrastructure)
- Consider using Lean's built-in substitution via `Expr` and metaprogramming

---

## Part 9: Effort Estimation Summary

### With All Proofs Axiomatized (`sorry` everywhere)

| Phase | Component | Estimated Hours | Complexity |
|-------|-----------|-----------------|------------|
| **Phase 1** | Mutual definitions | 15-20 | 🔴 High |
| **Phase 2** | Substitution axioms | 10-15 | 🔴 High |
| **Phase 3** | Dependent eliminators | 10-15 | 🟡 Medium |
| **Phase 4** | Cost semantics | 5-10 | 🟡 Medium |
| **Total** | **MVP with axioms** | **40-60 hours** | - |

### Additional Work for Proven Substitution

| Component | Estimated Hours | Complexity |
|-----------|-----------------|------------|
| Substitution implementation | 20-30 | 🔴 Very High |
| Weakening implementation | 10-15 | 🔴 High |
| Substitution lemmas | 15-25 | 🔴 Very High |
| **Total** | **45-70 hours** | - |

**Grand Total** (Full dependent types with proofs): **85-130 hours**

---

## Part 10: Recommended Approach

### Option: Incremental Upgrade Path

**Step 1**: Add context indexing (keep non-dependent pi/sigma)
```lean
inductive Ty : Ctx → Type 1 where
  | pi : Ty Γ → Ty Γ → Ty Γ  -- Still non-dependent, but indexed
```
**Effort**: 10-15 hours

**Step 2**: Add substitution infrastructure (axiomatized)
```lean
axiom substTy : Ty (Γ.snoc A) → Tm Γ A → Ty Γ
```
**Effort**: 5-10 hours

**Step 3**: Make pi/sigma dependent
```lean
| pi : (A : Ty Γ) → Ty (Γ.snoc A) → Ty Γ
```
**Effort**: 15-20 hours

**Step 4**: Add dependent eliminators
**Effort**: 10-15 hours

**Total Incremental**: 40-60 hours (matches full estimate)

---

## Part 11: Comparison to Current State

### What We Have (Option A)

```lean
-- Non-indexed types
inductive DepTy : Type where
  | pi : DepTy → DepTy → DepTy

-- Simple context
abbrev DepCtx := List DepTy

-- No substitution needed
| app : DepTm Γ (pi A B) → DepTm Γ A → DepTm Γ B
```

**Pros**:
- ✅ Simple, compiles easily
- ✅ No substitution complexity
- ✅ Establishes MLTT syntax

**Cons**:
- ❌ Not actually dependent
- ❌ Can't express `Vec A n` with length
- ❌ Can't express dependent motive in `natrec`

### What We'd Get (Full Dependent)

```lean
-- Context-indexed types
inductive Ty : Ctx → Type 1 where
  | pi : (A : Ty Γ) → Ty (Γ.snoc A) → Ty Γ

mutual
  inductive Ctx ...
  inductive Ty ...
  inductive Tm ...
end

-- Substitution everywhere
| app : Tm Γ (pi A B) → (a : Tm Γ A) → Tm Γ (B[a])
```

**Pros**:
- ✅ True dependent types
- ✅ Can express length-indexed vectors
- ✅ Dependent motives in eliminators
- ✅ Full MLTT expressiveness

**Cons**:
- ❌ 40-60 hours work (even with axioms)
- ❌ Complex substitution infrastructure
- ❌ Lean 4 technical challenges
- ❌ Harder to maintain and extend

---

## Part 12: Conclusion

### Is It Worth It?

**For RB-TT's Cost Analysis Goals**:
- **Current Option A is probably sufficient** if goal is just cost tracking
- Dependent types add complexity without clear cost analysis benefits
- Fuel-based recursion bounds work fine without dependency

**When Full Dependent Types Are Needed**:
- Proving precise complexity bounds (e.g., "cost is exactly n" not "at most R.depth")
- Length-indexed vectors for array bound checking
- Type-level computation and proofs
- Full MLTT research requiring dependent elimination

### Recommendation

**For RB-TT Project**:
1. **Keep Option A** for main development
2. **Create separate branch** for full dependent types exploration
3. **Focus effort** on completing cost soundness proofs for current system
4. **Revisit** if research goals require true dependency

**If Pursuing Full Dependent Types**:
1. Start with **incremental upgrade** (context indexing first)
2. **Axiomatize everything** initially (get structure right)
3. **Use existing libraries** for substitution (don't reinvent)
4. **Budget 40-60 hours** minimum for scaffold with axioms
5. **Budget 85-130 hours** for fully proven implementation

---

## Appendix A: Skeleton Code for Full Dependent Types

```lean
import RBTT.Res
import RBTT.Core.STLC

namespace RBTT.TrueDependent

set_option autoImplicit false

/-! ## Mutually Defined Structures -/

mutual
  /-- Contexts as telescopes -/
  inductive TrueCtx : Type where
    | nil  : TrueCtx
    | snoc : (Γ : TrueCtx) → TrueTy Γ → TrueCtx

  /-- Types indexed by context (universe level 1) -/
  inductive TrueTy : TrueCtx → Type 1 where
    | nat   : ∀ {Γ}, TrueTy Γ
    | pi    : ∀ {Γ}, (A : TrueTy Γ) → TrueTy (TrueCtx.snoc Γ A) → TrueTy Γ
    | sigma : ∀ {Γ}, (A : TrueTy Γ) → TrueTy (TrueCtx.snoc Γ A) → TrueTy Γ
    | vec   : ∀ {Γ}, TrueTy Γ → TrueTm Γ nat → TrueTy Γ
    | idty  : ∀ {Γ}, (A : TrueTy Γ) → TrueTm Γ A → TrueTm Γ A → TrueTy Γ

  /-- Variables -/
  inductive TrueVar : (Γ : TrueCtx) → TrueTy Γ → Type where
    | zero : ∀ {Γ A}, TrueVar (TrueCtx.snoc Γ A) (weaken A)
    | succ : ∀ {Γ A B}, TrueVar Γ A → TrueVar (TrueCtx.snoc Γ B) (weaken A)

  /-- Terms -/
  inductive TrueTm : (Γ : TrueCtx) → TrueTy Γ → Type where
    | var   : ∀ {Γ A}, TrueVar Γ A → TrueTm Γ A
    | lam   : ∀ {Γ A B}, TrueTm (TrueCtx.snoc Γ A) B → TrueTm Γ (TrueTy.pi A B)
    | app   : ∀ {Γ A B}, TrueTm Γ (TrueTy.pi A B) → (a : TrueTm Γ A) → TrueTm Γ (substTy B a)
    | pair  : ∀ {Γ A B}, (a : TrueTm Γ A) → TrueTm Γ (substTy B a) → TrueTm Γ (TrueTy.sigma A B)
    | fst   : ∀ {Γ A B}, TrueTm Γ (TrueTy.sigma A B) → TrueTm Γ A
    | snd   : ∀ {Γ A B}, (p : TrueTm Γ (TrueTy.sigma A B)) → TrueTm Γ (substTy B (fst p))
    | zero  : ∀ {Γ}, TrueTm Γ TrueTy.nat
    | succ  : ∀ {Γ}, TrueTm Γ TrueTy.nat → TrueTm Γ TrueTy.nat
    | natrec : sorry  -- Complex dependent eliminator
    | vnil   : sorry
    | vcons  : sorry
    | vecrec : sorry
    | refl   : ∀ {Γ A}, (a : TrueTm Γ A) → TrueTm Γ (TrueTy.idty A a a)
end

/-! ## Substitution (Axiomatized) -/

axiom substTy {Γ : TrueCtx} {A : TrueTy Γ} :
    TrueTy (TrueCtx.snoc Γ A) → TrueTm Γ A → TrueTy Γ

axiom weaken {Γ : TrueCtx} {B : TrueTy Γ} :
    TrueTy Γ → TrueTy (TrueCtx.snoc Γ B)

notation:max B "[" a "]" => substTy B a

/-! ## Cost Semantics -/

inductive TrueHasCost (R : ResCtx) :
    (Γ : TrueCtx) → {A : TrueTy Γ} → TrueTm Γ A → Nat → Prop where
  | var : ∀ {Γ A x}, TrueHasCost R Γ (TrueTm.var x) 0
  | lam : ∀ {Γ A B t k},
          TrueHasCost R (TrueCtx.snoc Γ A) t k →
          TrueHasCost R Γ (TrueTm.lam t) k
  | app : ∀ {Γ A B f a kf ka},
          TrueHasCost R Γ f kf →
          TrueHasCost R Γ a ka →
          TrueHasCost R Γ (TrueTm.app f a) (kf + ka + 1)
  -- ... more constructors

end RBTT.TrueDependent
```

**Status**: This skeleton would compile if `mutual` block accepts the definitions and substitution is axiomatized.

**Estimated Effort to Complete**: 40-60 hours with all proofs as `sorry` or `axiom`.

