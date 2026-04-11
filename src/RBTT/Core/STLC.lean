-- STATUS: mechanized core
import RBTT.Res
import RBTT.Core.CostModel

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

2. **Exact Bound Synthesis** (Paper v2 §3, aligned with machine δ constants):
   - Variable: `δ_var` (environment lookup)
   - Lambda: `k + δ_lam` (body bound + closure creation overhead)
   - Application: `b_f + b_a + b_f + δ_app` (double b_f: eval cost + latent body cost)
   - Pair: `b_a + b_b + δ_pair`
   - Conditionals: `b_c + max b_t b_f + δ_ite`
   - Projections: `b_p + δ_fst` / `b_p + δ_snd`
   - Literals: `δ_lit`

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

/-! ## Renaming and Substitution -/

/-- Renamings map variables in Γ to variables in Δ, preserving types. -/
abbrev Ren (Γ Δ : Ctx) : Type := ∀ {A : Ty}, Var Γ A → Var Δ A

/-- Substitutions map variables in Γ to terms in Δ, preserving types. -/
abbrev Sub (Γ Δ : Ctx) : Type := ∀ {A : Ty}, Var Γ A → Tm Δ A

/-- Lift a renaming under a binder. -/
def Ren.lift {Γ Δ : Ctx} {A : Ty} (ρ : Ren Γ Δ) : Ren (A :: Γ) (A :: Δ)
  | _, Var.zero => Var.zero
  | _, Var.succ x => Var.succ (ρ x)

mutual

/-- Apply a renaming to a term. -/
def ren {Γ Δ : Ctx} (ρ : Ren Γ Δ) : Tm Γ A → Tm Δ A
  | .var x => .var (ρ x)
  | .lam t => .lam (ren (Ren.lift ρ) t)
  | .app f a => .app (ren ρ f) (ren ρ a)
  | .pair a b => .pair (ren ρ a) (ren ρ b)
  | .fst p => .fst (ren ρ p)
  | .snd p => .snd (ren ρ p)
  | .natLit n => .natLit n
  | .true => .true
  | .false => .false
  | .ite c t f => .ite (ren ρ c) (ren ρ t) (ren ρ f)

/-- Lift a substitution under a binder. -/
def Sub.lift {Γ Δ : Ctx} {A : Ty} (σ : Sub Γ Δ) : Sub (A :: Γ) (A :: Δ)
  | _, Var.zero => .var Var.zero
  | _, Var.succ x => ren Var.succ (σ x)

/-- Apply a substitution to a term. -/
def sub {Γ Δ : Ctx} (σ : Sub Γ Δ) : Tm Γ A → Tm Δ A
  | .var x => σ x
  | .lam t => .lam (sub (Sub.lift σ) t)
  | .app f a => .app (sub σ f) (sub σ a)
  | .pair a b => .pair (sub σ a) (sub σ b)
  | .fst p => .fst (sub σ p)
  | .snd p => .snd (sub σ p)
  | .natLit n => .natLit n
  | .true => .true
  | .false => .false
  | .ite c t f => .ite (sub σ c) (sub σ t) (sub σ f)

end

/-- Empty-context renaming into any target context. -/
def renEmpty (Γ : Ctx) : Ren [] Γ := fun x => nomatch x

/-- Substitute a closed term for variable 0 in a term over `(A :: Γ)`. -/
def subst {A B : Ty} {Γ : Ctx} (s : Tm [] A) (t : Tm (A :: Γ) B) : Tm Γ B :=
  let sΓ : Tm Γ A := ren (renEmpty Γ) s
  let σ : Sub (A :: Γ) Γ := fun {C} x =>
    match x with
    | Var.zero => sΓ
    | Var.succ x => .var x
  sub σ t

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
  /-- Variable lookup (cost: δ_var) -/
  | var {Γ : Ctx} {A : Ty} {x : Var Γ A} :
      HasCost R Γ (Tm.var x) δ_var

  /-- Lambda abstraction: body bound k + closure overhead δ_lam.
      The total cost k + δ_lam serves as both the evaluation cost of the lambda
      (machine charges δ_lam ≤ k + δ_lam) and the latent body bound
      (machine body cost ≤ k ≤ k + δ_lam). -/
  | lam {Γ : Ctx} {A B : Ty} {t : Tm (A :: Γ) B} {k : Nat} :
      HasCost R (A :: Γ) t k →
      HasCost R Γ (Tm.lam t) (k + δ_lam)

  /-- Application: kf + ka + kf + δ_app (double b_f: eval cost + latent body cost) -/
  | app {Γ : Ctx} {A B : Ty} {f : Tm Γ (A ⇒ B)} {a : Tm Γ A} {kf ka : Nat} :
      HasCost R Γ f kf →
      HasCost R Γ a ka →
      HasCost R Γ (Tm.app f a) (kf + ka + kf + δ_app)

  /-- Pair: ka + kb + δ_pair -/
  | pair {Γ : Ctx} {A B : Ty} {a : Tm Γ A} {t_b : Tm Γ B} {ka kb : Nat} :
      HasCost R Γ a ka →
      HasCost R Γ t_b kb →
      HasCost R Γ (Tm.pair a t_b) (ka + kb + δ_pair)

  /-- First projection: kp + δ_fst -/
  | fst {Γ : Ctx} {A B : Ty} {p : Tm Γ (A × B)} {kp : Nat} :
      HasCost R Γ p kp →
      HasCost R Γ (Tm.fst p) (kp + δ_fst)

  /-- Second projection: kp + δ_snd -/
  | snd {Γ : Ctx} {A B : Ty} {p : Tm Γ (A × B)} {kp : Nat} :
      HasCost R Γ p kp →
      HasCost R Γ (Tm.snd p) (kp + δ_snd)

  /-- Natural number literal: δ_lit -/
  | natLit {Γ : Ctx} {n : Nat} :
      HasCost R Γ (Tm.natLit n) δ_lit

  /-- Boolean literals: δ_lit -/
  | true {Γ : Ctx} :
      HasCost R Γ Tm.true δ_lit

  | false {Γ : Ctx} :
      HasCost R Γ Tm.false δ_lit

  /-- Conditional: kc + max kt kf + δ_ite -/
  | ite {Γ : Ctx} {A : Ty} {c : Tm Γ .bool} {t f : Tm Γ A} {kc kt kf : Nat} :
      HasCost R Γ c kc →
      HasCost R Γ t kt →
      HasCost R Γ f kf →
      HasCost R Γ (Tm.ite c t f) (kc + Nat.max kt kf + δ_ite)

/-- Upper bound wrapper: term has some exact cost k ≤ b -/
def HasBound (Γ : Ctx) (R : ResCtx) (b : Nat) {A : Ty} (t : Tm Γ A) : Prop :=
  ∃ k, HasCost R Γ t k ∧ k ≤ b

/-- Computable compositional cost bound matching `HasCost` arithmetic. -/
def costOf : {Γ : Ctx} → {A : Ty} → Tm Γ A → Nat
  | _, _, Tm.var _      => δ_var
  | _, _, Tm.lam t      => costOf t + δ_lam
  | _, _, Tm.app f a    => costOf f + costOf a + costOf f + δ_app
  | _, _, Tm.pair a b   => costOf a + costOf b + δ_pair
  | _, _, Tm.fst p      => costOf p + δ_fst
  | _, _, Tm.snd p      => costOf p + δ_snd
  | _, _, Tm.natLit _   => δ_lit
  | _, _, Tm.true       => δ_lit
  | _, _, Tm.false      => δ_lit
  | _, _, Tm.ite c t f  => costOf c + Nat.max (costOf t) (costOf f) + δ_ite

/-- `HasCost` holds at the computed cost. -/
theorem hasCost_costOf (R : ResCtx) :
  {Γ : Ctx} → {A : Ty} → (t : Tm Γ A) → HasCost R Γ t (costOf t)
  | _, _, Tm.var x => by
      simpa [costOf] using (HasCost.var (R := R) (x := x))
  | _, _, Tm.lam t => by
      simpa [costOf] using
        (HasCost.lam (R := R) (t := t) (k := costOf t) (hasCost_costOf R t))
  | _, _, Tm.app f a => by
      have h := HasCost.app (R := R) (f := f) (a := a)
          (kf := costOf f) (ka := costOf a)
          (hasCost_costOf R f) (hasCost_costOf R a)
      simp only [costOf] at h ⊢
      exact h
  | _, _, Tm.pair a b => by
      simpa [costOf, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (HasCost.pair (R := R) (a := a) (t_b := b)
          (ka := costOf a) (kb := costOf b)
          (hasCost_costOf R a) (hasCost_costOf R b))
  | _, _, Tm.fst p => by
      simpa [costOf] using
        (HasCost.fst (R := R) (p := p) (kp := costOf p) (hasCost_costOf R p))
  | _, _, Tm.snd p => by
      simpa [costOf] using
        (HasCost.snd (R := R) (p := p) (kp := costOf p) (hasCost_costOf R p))
  | _, _, Tm.natLit n => by
      simpa [costOf] using (HasCost.natLit (R := R) (n := n))
  | _, _, Tm.true => by
      simpa [costOf] using (HasCost.true (R := R))
  | _, _, Tm.false => by
      simpa [costOf] using (HasCost.false (R := R))
  | _, _, Tm.ite c t f => by
      simpa [costOf, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (HasCost.ite (R := R) (c := c) (t := t) (f := f)
          (kc := costOf c) (kt := costOf t) (kf := costOf f)
          (hasCost_costOf R c) (hasCost_costOf R t) (hasCost_costOf R f))

/-- The computed cost is an immediate valid bound. -/
theorem hasBound_costOf {Γ : Ctx} {A : Ty} (R : ResCtx) (t : Tm Γ A) :
  HasBound Γ R (costOf t) t := by
  refine ⟨costOf t, hasCost_costOf R t, Nat.le_refl _⟩

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

/-- Identity has cost δ_var + δ_lam = 2 -/
example : [] ⊢[R;2] id_tm :=
  ⟨δ_var + δ_lam, HasCost.lam HasCost.var, Nat.le_refl _⟩

/-- Example: Constant function returning 42 -/
def const42 : Tm [] (.nat ⇒ .nat) :=
  Tm.lam (Tm.natLit 42)

/-- Constant function has cost δ_lit + δ_lam = 2 -/
example : [] ⊢[R;2] const42 :=
  ⟨δ_lit + δ_lam, HasCost.lam HasCost.natLit, Nat.le_refl _⟩

/-- Example: Application of id to 5 -/
def app_id_5 : Tm [] .nat :=
  Tm.app id_tm (Tm.natLit 5)

/-- Application has cost (δ_var+δ_lam) + δ_lit + (δ_var+δ_lam) + δ_app = 6 -/
example : [] ⊢[R;6] app_id_5 :=
  ⟨(δ_var + δ_lam) + δ_lit + (δ_var + δ_lam) + δ_app,
   HasCost.app (HasCost.lam HasCost.var) HasCost.natLit, Nat.le_refl _⟩

/-- Example: Pair of booleans -/
def pair_bools : Tm [] (.bool × .bool) :=
  Tm.pair Tm.true Tm.false

/-- Pair has cost δ_lit + δ_lit + δ_pair = 3 -/
example : [] ⊢[R;3] pair_bools :=
  ⟨δ_lit + δ_lit + δ_pair, HasCost.pair HasCost.true HasCost.false, Nat.le_refl _⟩

/-- Example: Conditional expression -/
def cond_example : Tm [] .nat :=
  Tm.ite Tm.true (Tm.natLit 1) (Tm.natLit 2)

/-- Conditional has cost δ_lit + max δ_lit δ_lit + δ_ite = 3 -/
example : [] ⊢[R;3] cond_example :=
  ⟨δ_lit + Nat.max δ_lit δ_lit + δ_ite,
   HasCost.ite HasCost.true HasCost.natLit HasCost.natLit, Nat.le_refl _⟩

end Examples

end RBTT
