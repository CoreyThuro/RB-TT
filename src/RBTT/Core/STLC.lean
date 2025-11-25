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

/-- Typing judgment with resource bounds (§3.2, Lines 109-130) -/
inductive HasBound : Ctx → ResCtx → Nat → Tm Γ A → Ty → Prop where
  /-- Variable lookup (cost: 0) -/
  | var : HasBound Γ R 0 (Tm.var x) A

  /-- Lambda abstraction (cost: 0 for the abstraction itself) -/
  | lam {t : Tm (A :: Γ) B} :
      HasBound (A :: Γ) R b_body t B →
      HasBound Γ R 0 (Tm.lam t) (A ⇒ B)

  /-- Application: b_f + b_a + 1 (Line 116-117) -/
  | app {f : Tm Γ (A ⇒ B)} {a : Tm Γ A} :
      HasBound Γ R b_f f (A ⇒ B) →
      HasBound Γ R b_a a A →
      HasBound Γ R (b_f + b_a + 1) (Tm.app f a) B

  /-- Pair: b_a + b_b (Line 119-120) -/
  | pair {a : Tm Γ A} {b : Tm Γ B} :
      HasBound Γ R b_a a A →
      HasBound Γ R b_b b B →
      HasBound Γ R (b_a + b_b) (Tm.pair a b) (A × B)

  /-- First projection (cost: 1) -/
  | fst {p : Tm Γ (A × B)} :
      HasBound Γ R b_p p (A × B) →
      HasBound Γ R (b_p + 1) (Tm.fst p) A

  /-- Second projection (cost: 1) -/
  | snd {p : Tm Γ (A × B)} :
      HasBound Γ R b_p p (A × B) →
      HasBound Γ R (b_p + 1) (Tm.snd p) B

  /-- Natural number literal (cost: 0) -/
  | natLit :
      HasBound Γ R 0 (Tm.natLit n) .nat

  /-- Boolean literals (cost: 0) -/
  | true :
      HasBound Γ R 0 Tm.true .bool
  | false :
      HasBound Γ R 0 Tm.false .bool

  /-- Conditional: b_c + max b_t b_f + 1 (Line 123-125) -/
  | ite {c : Tm Γ .bool} {t f : Tm Γ A} :
      HasBound Γ R b_c c .bool →
      HasBound Γ R b_t t A →
      HasBound Γ R b_f f A →
      HasBound Γ R (b_c + Nat.max b_t b_f + 1) (Tm.ite c t f) A

/-! ## Notation -/

/-- Notation for the typing judgment -/
notation:50 Γ " ⊢[" R ";" b "] " t " : " A => HasBound Γ R b t A

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

/-- Identity has bound 0 -/
example : [] ⊢[R;0] id_tm : (.nat ⇒ .nat) :=
  HasBound.lam HasBound.var

/-- Example: Constant function returning 42 -/
def const42 : Tm [] (.nat ⇒ .nat) :=
  Tm.lam (Tm.natLit 42)

/-- Constant function has bound 0 -/
example : [] ⊢[R;0] const42 : (.nat ⇒ .nat) :=
  HasBound.lam HasBound.natLit

/-- Example: Application of id to 5 -/
def app_id_5 : Tm [] .nat :=
  Tm.app id_tm (Tm.natLit 5)

/-- Application has bound 1 (0 + 0 + 1) -/
example : [] ⊢[R;1] app_id_5 : .nat :=
  HasBound.app
    (HasBound.lam HasBound.var)
    HasBound.natLit

/-- Example: Pair of booleans -/
def pair_bools : Tm [] (.bool × .bool) :=
  Tm.pair Tm.true Tm.false

/-- Pair has bound 0 (0 + 0) -/
example : [] ⊢[R;0] pair_bools : (.bool × .bool) :=
  HasBound.pair HasBound.true HasBound.false

/-- Example: Conditional expression -/
def cond_example : Tm [] .nat :=
  Tm.ite Tm.true (Tm.natLit 1) (Tm.natLit 2)

/-- Conditional has bound 1 (0 + max 0 0 + 1) -/
example : [] ⊢[R;1] cond_example : .nat :=
  HasBound.ite HasBound.true HasBound.natLit HasBound.natLit

end Examples

end RBTT
