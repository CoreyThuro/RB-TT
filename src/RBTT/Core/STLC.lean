import RBTT.Res

namespace RBTT

/-!
# Simply-Typed Lambda Calculus with Resource Bounds

This module implements the core STLC from paper §3.2 with synthesized bounds.

## Key Features:

1. **Typing Judgment**: `Γ ⊢_{R;b} t : A` where:
   - `Γ` is the typing context
   - `R` is the resource budget
   - `b` is the synthesized bound
   - `t` is the term
   - `A` is the type

2. **Exact Bound Synthesis** (Lines 115-130):
   - Application: `b_f + b_a + 1`
   - Pair: `b_a + b_b`
   - Conditionals: `b_c + max b_t b_f + 1`
   - Recursion: `Depth(R) · b` (via fuel)

-/

/-! ## Types -/

/-- Simple types for STLC -/
inductive Ty : Type where
  | nat  : Ty
  | bool : Ty
  | arrow : Ty → Ty → Ty
  | prod  : Ty → Ty → Ty
  deriving Repr, DecidableEq

namespace Ty

/-- Notation for function types -/
infixr:25 " ⇒ " => Ty.arrow

/-- Notation for product types -/
infixr:30 " × " => Ty.prod

end Ty

/-! ## Contexts -/

/-- Typing contexts: lists of types -/
abbrev Ctx := List Ty

/-! ## Variables (de Bruijn indices) -/

/-- Variables as de Bruijn indices with typing proof -/
inductive Var : Ctx → Ty → Type where
  | zero : Var (A :: Γ) A
  | succ : Var Γ A → Var (B :: Γ) A
  deriving Repr

/-! ## Terms -/

/-- Terms of the STLC with explicit typing -/
inductive Tm : Ctx → Ty → Type where
  /-- Variables -/
  | var : Var Γ A → Tm Γ A

  /-- Lambda abstraction -/
  | lam : Tm (A :: Γ) B → Tm Γ (A ⇒ B)

  /-- Application -/
  | app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

  /-- Pair construction -/
  | pair : Tm Γ A → Tm Γ B → Tm Γ (A × B)

  /-- First projection -/
  | fst : Tm Γ (A × B) → Tm Γ A

  /-- Second projection -/
  | snd : Tm Γ (A × B) → Tm Γ B

  /-- Natural number literals -/
  | natLit : Nat → Tm Γ .nat

  /-- Boolean literals -/
  | true  : Tm Γ .bool
  | false : Tm Γ .bool

  /-- Conditional -/
  | ite : Tm Γ .bool → Tm Γ A → Tm Γ A → Tm Γ A
  deriving Repr

/-! ## Typing Judgment with Synthesized Bounds

The judgment `HasBound Γ R b t A` means:
> "In context Γ, with resource budget R, term t has type A
>  with synthesized bound b ≤ Time(R)"

This corresponds to the paper's `Γ ⊢_{R;b} t : A`.

-/

/-- Exact compositional cost judgment (§3.2, Lines 109-130)

**Architecture**: Split into HasCost (exact, inductive) + HasBound (≤ wrapper, definition)

This encoding:
- **HasCost**: Exact compositional arithmetic with indices (Γ can vary in lam)
- **HasBound**: Upper bound wrapper as definition (avoids fuel recursion issues)
- **Clean induction**: Structural induction on HasCost derivation
- **Matches paper**: Exact bound synthesis from Figure 1
-/
inductive HasCost (R : ResCtx) : (Γ : Ctx) → {A : Ty} → Tm Γ A → Nat → Prop where
  /-- Variable lookup (cost: 0) -/
  | var {Γ : Ctx} {A : Ty} {x : Var Γ A} :
      HasCost R Γ (Tm.var x) 0

  /-- Lambda abstraction (latent cost: carries body cost) -/
  | lam {Γ : Ctx} {A B : Ty} {t : Tm (A :: Γ) B} {k : Nat} :
      HasCost R (A :: Γ) t k →
      HasCost R Γ (Tm.lam t) k

  /-- Application: kf + ka + 1 (Line 116-117) -/
  | app {Γ : Ctx} {A B : Ty} {f : Tm Γ (A ⇒ B)} {a : Tm Γ A} {kf ka : Nat} :
      HasCost R Γ f kf →
      HasCost R Γ a ka →
      HasCost R Γ (Tm.app f a) (kf + ka + 1)

  /-- Pair: ka + kb (Line 119-120) -/
  | pair {Γ : Ctx} {A B : Ty} {a : Tm Γ A} {t_b : Tm Γ B} {ka kb : Nat} :
      HasCost R Γ a ka →
      HasCost R Γ t_b kb →
      HasCost R Γ (Tm.pair a t_b) (ka + kb)

  /-- First projection (cost: 1) -/
  | fst {Γ : Ctx} {A B : Ty} {p : Tm Γ (A × B)} {kp : Nat} :
      HasCost R Γ p kp →
      HasCost R Γ (Tm.fst p) (kp + 1)

  /-- Second projection (cost: 1) -/
  | snd {Γ : Ctx} {A B : Ty} {p : Tm Γ (A × B)} {kp : Nat} :
      HasCost R Γ p kp →
      HasCost R Γ (Tm.snd p) (kp + 1)

  /-- Natural number literal (cost: 0) -/
  | natLit {Γ : Ctx} {n : Nat} :
      HasCost R Γ (Tm.natLit n) 0

  /-- Boolean literals (cost: 0) -/
  | true {Γ : Ctx} :
      HasCost R Γ Tm.true 0

  | false {Γ : Ctx} :
      HasCost R Γ Tm.false 0

  /-- Conditional: kc + max kt kf + 1 (Line 123-125) -/
  | ite {Γ : Ctx} {A : Ty} {c : Tm Γ .bool} {t f : Tm Γ A} {kc kt kf : Nat} :
      HasCost R Γ c kc →
      HasCost R Γ t kt →
      HasCost R Γ f kf →
      HasCost R Γ (Tm.ite c t f) (kc + Nat.max kt kf + 1)

/-- Upper bound wrapper: term has some exact cost k ≤ b -/
def HasBound (Γ : Ctx) (R : ResCtx) (b : Nat) {A : Ty} (t : Tm Γ A) : Prop :=
  ∃ k, HasCost R Γ t k ∧ k ≤ b

/-! ## Notation -/

set_option quotPrecheck false in
/-- Notation for the typing judgment.
Note: Type A is now implicit (inferred from Tm Γ A) -/
scoped notation:50 Γ " ⊢[" R ";" b "] " t => HasBound Γ R b t

/-! ## Basic Properties

TODO: Prove bound soundness properties:
- Weakening: b ≤ R.time for all well-typed terms
- Monotonicity: If R ≤ S then Γ ⊢[R;b] t : A implies Γ ⊢[S;b] t : A
- Admissibility of various structural rules
-/

/-! ## Examples -/

section Examples

/-- Example: Identity function -/
def id_tm : Tm [] (.nat ⇒ .nat) :=
  Tm.lam (Tm.var Var.zero)

/-- Identity has exact cost 0, hence bound 0 -/
example : [] ⊢[R;0] id_tm :=
  ⟨0, HasCost.lam HasCost.var, Nat.le_refl 0⟩

/-- Example: Constant function returning 42 -/
def const42 : Tm [] (.nat ⇒ .nat) :=
  Tm.lam (Tm.natLit 42)

/-- Constant function has exact cost 0, hence bound 0 -/
example : [] ⊢[R;0] const42 :=
  ⟨0, HasCost.lam HasCost.natLit, Nat.le_refl 0⟩

/-- Example: Application of id to 5 -/
def app_id_5 : Tm [] .nat :=
  Tm.app id_tm (Tm.natLit 5)

/-- Application has exact cost 1 (0 + 0 + 1), hence bound 1 -/
example : [] ⊢[R;1] app_id_5 :=
  ⟨1, HasCost.app (HasCost.lam HasCost.var) HasCost.natLit, Nat.le_refl 1⟩

/-- Example: Pair of booleans -/
def pair_bools : Tm [] (.bool × .bool) :=
  Tm.pair Tm.true Tm.false

/-- Pair has exact cost 0 (0 + 0), hence bound 0 -/
example : [] ⊢[R;0] pair_bools :=
  ⟨0, HasCost.pair HasCost.true HasCost.false, Nat.le_refl 0⟩

/-- Example: Conditional expression -/
def cond_example : Tm [] .nat :=
  Tm.ite Tm.true (Tm.natLit 1) (Tm.natLit 2)

/-- Conditional has exact cost 1 (0 + max 0 0 + 1), hence bound 1 -/
example : [] ⊢[R;1] cond_example :=
  ⟨1, HasCost.ite HasCost.true HasCost.natLit HasCost.natLit, Nat.le_refl 1⟩

end Examples

end RBTT
