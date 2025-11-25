import RBTT.Core.STLC

namespace RBTT

/-!
# Operational Semantics and Cost Model

This module implements the operational semantics from paper §3.3 with
unit-cost reduction steps and the cost soundness theorem.

## Key Components (Lines 136-146):

1. **Values**: Canonical forms that don't reduce further
2. **Small-step reduction** (`→`): Single reduction steps with unit cost
3. **Multi-step reduction** (`⇒*`): Transitive closure with cost tracking
4. **Cost Soundness** (Theorem 3.1): If `Γ ⊢_{R;b} t : A` and `t` closed,
   then `∃v,k. t ⇒* v` with `k ≤ b ≤ Time(R)`

-/

open Tm

/-! ## Values -/

/-- Values: terms in canonical form that don't reduce -/
inductive Value : Tm [] A → Prop where
  | lam : Value (lam t)
  | pair : Value a → Value b → Value (pair a b)
  | natLit : Value (natLit n)
  | true : Value true
  | false : Value false

/-! ## Substitution -/

/-- Substitution: replace variable with a term.
    TODO: Proper implementation with weakening and shifting -/
axiom subst {A B : Ty} {Γ : Ctx} : Tm [] A → Tm (A :: Γ) B → Tm Γ B

/-! ## Small-Step Operational Semantics -/

/-- Single reduction step with unit cost (§3.3, Lines 138-143) -/
inductive Step : {A : Ty} → Tm [] A → Tm [] A → Prop where
  /-- Beta reduction: (λx.t) v → t[v/x] [cost: 1] -/
  | beta {A B : Ty} {t : Tm [A] B} {v : Tm [] A} :
      Value v →
      Step (app (lam t) v) (subst v t)

  /-- Conditional true: if true then t else f → t [cost: 1] -/
  | ite_true {t f : Tm [] A} :
      Step (ite Tm.true t f) t

  /-- Conditional false: if false then t else f → f [cost: 1] -/
  | ite_false {t f : Tm [] A} :
      Step (ite Tm.false t f) f

  /-- First projection: π₁(v₁,v₂) → v₁ [cost: 1] -/
  | fst_pair {v₁ : Tm [] A} {v₂ : Tm [] B} :
      Value v₁ → Value v₂ →
      Step (fst (pair v₁ v₂)) v₁

  /-- Second projection: π₂(v₁,v₂) → v₂ [cost: 1] -/
  | snd_pair {v₁ : Tm [] A} {v₂ : Tm [] B} :
      Value v₁ → Value v₂ →
      Step (snd (pair v₁ v₂)) v₂

  /-- Congruence rules (evaluation contexts) -/
  | app_left {f f' : Tm [] (A ⇒ B)} {a : Tm [] A} :
      Step f f' →
      Step (app f a) (app f' a)

  | app_right {f : Tm [] (A ⇒ B)} {a a' : Tm [] A} :
      Value f →
      Step a a' →
      Step (app f a) (app f a')

  | pair_left {a a' : Tm [] A} {b : Tm [] B} :
      Step a a' →
      Step (pair a b) (pair a' b)

  | pair_right {a : Tm [] A} {b b' : Tm [] B} :
      Value a →
      Step b b' →
      Step (pair a b) (pair a b')

  | fst_cong {p p' : Tm [] (A × B)} :
      Step p p' →
      Step (fst p) (fst p')

  | snd_cong {p p' : Tm [] (A × B)} :
      Step p p' →
      Step (snd p) (snd p')

  | ite_cond {c c' : Tm [] .bool} {t f : Tm [] A} :
      Step c c' →
      Step (ite c t f) (ite c' t f)

/-! ## Multi-Step Reduction with Cost Tracking -/

/-- Multi-step reduction: `t ⇒*[k] v` means "t reduces to v in exactly k steps" -/
inductive MultiStep : Tm [] A → Tm [] A → Nat → Prop where
  | refl : Value v → MultiStep v v 0
  | step : Step t t' → MultiStep t' v k → MultiStep t v (k + 1)

/-! ## Notation -/

notation:50 t " →₁ " t' => Step t t'
notation:50 t " ⇒*[" k "] " v => MultiStep t v k

/-! ## Basic Properties -/

/-- Determinism: reduction is deterministic -/
axiom step_deterministic {A : Ty} {t t' t'' : Tm [] A} :
    Step t t' → Step t t'' → t' = t''

/-- Progress: closed well-typed terms are either values or can step -/
axiom progress {A : Ty} {R : ResCtx} {b : Nat} {t : Tm [] A} :
    ([] ⊢[R;b] t : A) → Value t ∨ ∃ t', Step t t'

/-- Preservation: reduction preserves types and doesn't increase bounds -/
axiom preservation {A : Ty} {R : ResCtx} {b b' : Nat} {t t' : Tm [] A} :
    ([] ⊢[R;b] t : A) → Step t t' → ([] ⊢[R;b'] t' : A) ∧ b' ≤ b

/-! ## Cost Soundness Theorem -/

/-- **Theorem 3.1 (Cost Soundness)** - Paper §3.3, Lines 144-146

If a closed term has synthesized bound `b` in resource context `R`,
then it reduces to a value in at most `b` steps, and `b ≤ Time(R)`.

This is the **central theorem** of RB-TT's STLC fragment.

TODO: Prove this by induction on typing derivation using progress + preservation.
For now we admit it with `sorry` to establish the infrastructure.
-/
theorem cost_soundness {t : Tm [] A} {Γ : Ctx} {R : ResCtx} {b : Nat} :
    Γ = [] →                              -- t is closed
    (Γ ⊢[R;b] t : A) →                    -- t has synthesized bound b
    b ≤ R.time →                           -- b fits in budget
    ∃ (v : Tm [] A) (k : Nat),
      MultiStep t v k ∧                    -- t reduces to v in k steps
      k ≤ b ∧                               -- actual cost ≤ bound
      Value v := by
  sorry

/-! ## Examples with Cost Tracking -/

section Examples

variable (R : ResCtx) (h : 10 ≤ R.time)

/-- Example: (λx.x) 5 reduces to 5 in 1 step -/
example :
    let t := app (lam (var Var.zero)) (natLit 5)
    ∃ v k, (t ⇒*[k] v) ∧ k ≤ 1 := by
  sorry  -- Would prove: beta reduction takes 1 step

/-- Example: if true then 1 else 2 reduces to 1 in 1 step -/
example :
    let t := Tm.ite Tm.true (natLit 1) (natLit 2)
    ∃ v k, (t ⇒*[k] v) ∧ k ≤ 1 := by
  sorry  -- Would prove: ite_true takes 1 step

/-- Example: fst (3, 4) reduces to 3 in 1 step -/
example :
    let t := fst (pair (natLit 3) (natLit 4))
    ∃ v k, (t ⇒*[k] v) ∧ k ≤ 1 := by
  sorry  -- Would prove: fst_pair takes 1 step

end Examples

end RBTT
