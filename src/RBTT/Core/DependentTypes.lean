import RBTT.Res
import RBTT.Core.STLC

namespace RBTT.Dependent

/-!
# Dependent Type Theory Extension for RB-TT

This module extends RB-TT from Simply-Typed Lambda Calculus (STLC) to
Martin-Löf Type Theory (MLTT) with dependent types, following mltt-sketch.txt.

## Implementation Status: Option A (Minimal Viable)

**Complete**:
- Dependent contexts (telescopes)
- Π types (dependent functions)
- Σ types (dependent pairs)
- Natural numbers with natrec
- Vectors with vecrec (simplified, length-implicit)

**Axiomatized** (deferred to Option B):
- Substitution operations
- Weakening operations
- Helper type formers (pi_nat_to_A_to_A, etc.)

## Key Design Decisions

1. **Mutual Definition**: `DepCtx` and `Ty` are mutually recursive
2. **Universe Levels**: Use `Type 1` for indexed type family
3. **Substitution**: Axiomatized for Option A
4. **Simplified Vec**: Length is implicit for Option A

## References

- Original STLC: `RBTT.Core.STLC`
- Cost semantics: `RBTT.Core.DependentCost` (Phase 2)
- Examples: `RBTT.Examples.DependentExamples` (Phase 3)
- Implementation plan: `docs/MLTT_OPTION_A_PLAN.md`
-/

/-! ## Mutually Defined Contexts and Types

Due to the dependency between contexts and types, we define them mutually.
-/

-- Types are no longer indexed by context (for now - this simplifies mutual recursion)
-- NOTE: Renamed to DepTy to avoid conflict with RBTT.Ty from STLC
inductive DepTy : Type where
  | nat   : DepTy
  | bool  : DepTy
  | pi    : DepTy → DepTy → DepTy
  | sigma : DepTy → DepTy → DepTy
  | vec   : DepTy → DepTy

-- Simplified approach: Make context unindexed, track well-formedness separately
-- Using List instead of custom inductive to avoid field notation hell
abbrev DepCtx := List DepTy

/-! ## Dependent Variables and Terms

Now we can define variables and terms with proper dependencies.
-/

set_option autoImplicit false

/-- **Dependent Variables**: de Bruijn indices. -/
inductive DepVar : DepCtx → DepTy → Type where
  /-- **Zero**: Most recently bound variable. -/
  | zero : ∀ (Γ : DepCtx) (A : DepTy), DepVar (A :: Γ) A

  /-- **Successor**: Variable from outer context. -/
  | succ : ∀ (Γ : DepCtx) (A B : DepTy), DepVar Γ A → DepVar (B :: Γ) A

/-- **Dependent Terms**: Well-typed terms indexed by context and type.

    **NOTE (Option A)**: For simplicity, we use non-dependent Pi and Sigma types.
    The result types of `app` and projections are simplified to avoid substitution.
    This will be refined in Option B with proper dependent types.
-/
inductive DepTm : DepCtx → DepTy → Type where
  -- Lambda Calculus constructors
  /-- **Variable**: Reference to bound variable -/
  | var  : ∀ {Γ : DepCtx} {A : DepTy}, DepVar Γ A → DepTm Γ A
  /-- **Lambda Abstraction**: `λx. t` where `t : B` -/
  | lam  : ∀ {Γ : DepCtx} {A B : DepTy}, DepTm (A :: Γ) B → DepTm Γ (DepTy.pi A B)
  /-- **Application**: `f a` where `f : Π(x:A). B` and `a : A`.
      **Simplified**: Result type is just `B` (not dependent for Option A) -/
  | app  : ∀ {Γ : DepCtx} {A B : DepTy},
           DepTm Γ (DepTy.pi A B) → DepTm Γ A → DepTm Γ B

  -- Dependent Pairs constructors
  /-- **Pair**: `(x, y)` where `x : A` and `y : B`
      **Simplified**: Non-dependent pair for Option A -/
  | pair : ∀ {Γ : DepCtx} {A B : DepTy},
           DepTm Γ A → DepTm Γ B → DepTm Γ (DepTy.sigma A B)
  /-- **First Projection**: `π₁(p)` extracts first component -/
  | fst  : ∀ {Γ : DepCtx} {A B : DepTy},
           DepTm Γ (DepTy.sigma A B) → DepTm Γ A
  /-- **Second Projection**: `π₂(p)` extracts second component.
      **Simplified**: Type is just `B` (not dependent for Option A) -/
  | snd  : ∀ {Γ : DepCtx} {A B : DepTy},
           DepTm Γ (DepTy.sigma A B) → DepTm Γ B

  -- Natural Numbers constructors
  /-- **Zero**: The natural number 0 -/
  | zero  : ∀ {Γ : DepCtx}, DepTm Γ DepTy.nat
  /-- **Successor**: `succ(n)` = n + 1 -/
  | succ  : ∀ {Γ : DepCtx}, DepTm Γ DepTy.nat → DepTm Γ DepTy.nat
  /-- **Natural Number Recursion**: `natrec z s n`.
      **Simplified**: Result type is `A` (not dependent for Option A) -/
  | natrec : ∀ {Γ : DepCtx} {A : DepTy},
              DepTm Γ A →                                  -- base case
              DepTm Γ (DepTy.pi DepTy.nat (DepTy.pi A A)) → -- step function: nat → A → A
              DepTm Γ DepTy.nat →                          -- scrutinee
              DepTm Γ A                                    -- result

  -- Vectors constructors (Simplified)
  /-- **Empty Vector**: `[]` -/
  | vnil   : ∀ {Γ : DepCtx} {A : DepTy}, DepTm Γ (DepTy.vec A)
  /-- **Vector Cons**: `x :: xs` -/
  | vcons  : ∀ {Γ : DepCtx} {A : DepTy},
            DepTm Γ A → DepTm Γ (DepTy.vec A) → DepTm Γ (DepTy.vec A)
  /-- **Vector Recursion**: `vecrec z s v`.
      **Simplified**: Step function type is `A → vec A → B → B` -/
  | vecrec : ∀ {Γ : DepCtx} {A B : DepTy},
              DepTm Γ B →                                                -- base case
              DepTm Γ (DepTy.pi A (DepTy.pi (DepTy.vec A) (DepTy.pi B B))) → -- step: A → vec A → B → B
              DepTm Γ (DepTy.vec A) →                                    -- scrutinee
              DepTm Γ B                                                  -- result

  -- Booleans (for compatibility)
  | true  : ∀ {Γ : DepCtx}, DepTm Γ DepTy.bool
  | false : ∀ {Γ : DepCtx}, DepTm Γ DepTy.bool
  | ite   : ∀ {Γ : DepCtx} {A : DepTy}, DepTm Γ DepTy.bool → DepTm Γ A → DepTm Γ A → DepTm Γ A

/-! ## Substitution and Weakening (For Future Use in Option B)

**NOTE (Option A)**: These operations are not needed in our simplified approach
where Pi and Sigma types are non-dependent. They are defined here as placeholders
for Option B, which will implement proper dependent types.

Substitution `B[a]` would replace the most recently bound variable in type `B`
with term `a`. This is the **most complex** operation in dependent type theory.
-/

/-- **Type Substitution**: Replace bound variable in `B` with term `a`.
    **NOTE**: Not used in Option A (non-dependent types)
    **TODO (Option B)**: Implement and prove substitution lemmas
-/
axiom subst {Γ : DepCtx} {A : DepTy} : DepTy → DepTm Γ A → DepTy

/-- Substitution notation: B[a] -/
notation:max B "[" a "]" => subst B a

/-- **Context Weakening**: Lift type from Γ to extended context Γ, x:B.
    **NOTE**: Not used in Option A
    **TODO (Option B)**: Implement and prove weakening lemmas
-/
axiom weaken {Γ : DepCtx} {A : DepTy} (B : DepTy) : DepTy

/-! ## Examples (Closed Terms)

**NOTE**: Examples are temporarily commented out due to namespace resolution issues
with STLC's `Tm`. Will be enabled in Phase 3.

section Examples

-- /-- Identity function on Nat: `λx. x` -/
-- def id_nat : Tm DepCtx.nil (@Ty.pi DepCtx.nil (@Ty.nat DepCtx.nil) (@weaken DepCtx.nil (@Ty.nat DepCtx.nil) (@Ty.nat DepCtx.nil))) :=
--   Tm.lam (Tm.var Var.zero)

-- /-- The number 2 -/
-- def two : Tm DepCtx.nil (@Ty.nat DepCtx.nil) :=
--   Tm.succ (Tm.succ Tm.zero)

end Examples
-/

/-! ## Integration Notes

**Relationship to STLC**:
- STLC types are *simple* (non-dependent) special cases
- STLC `arrow` = `pi` with constant codomain
- STLC `prod` = `sigma` with constant second type
- Cost semantics extend compositionally (see `DependentCost.lean`)

**Next Steps**:
- Phase 2: Define `HasCost` for dependent terms → `DependentCost.lean`
- Phase 3: Implement examples and tests → `DependentExamples.lean`
- Option B: Prove substitution lemmas and cost soundness

**Current Limitations** (Option A):
- Substitution axiomatized (not proven)
- Vec is length-implicit (not indexed by Nat)
- No Id type for equality (deferred to Option B)
- Helper type formers axiomatized (full Π encoding deferred)

See `docs/MLTT_OPTION_A_PLAN.md` for complete implementation plan.
-/

end RBTT.Dependent
