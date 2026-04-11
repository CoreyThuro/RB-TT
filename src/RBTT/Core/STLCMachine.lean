-- STATUS: mechanized core
import RBTT.Core.STLC
import RBTT.Core.CostModel

namespace RBTT

open Ty Tm

mutual
  /-- Runtime values for intrinsic STLC. -/
  inductive Val : Ty → Type where
    | clo  {Γ A B} : (body : Tm (A :: Γ) B) → (ρ : Env Γ) → (bodyBound : Nat) → Val (A ⇒ B)
    | pair {A B} : Val A → Val B → Val (A × B)
    | nat  : Nat → Val .nat
    | btrue  : Val .bool
    | bfalse : Val .bool

  /-- Environments aligned with the context. -/
  inductive Env : Ctx → Type where
    | nil  : Env []
    | cons : Val A → Env Γ → Env (A :: Γ)
end

/-- Lookup a de Bruijn variable in an environment. -/
def Env.lookup : Env Γ → Var Γ A → Val A
  | Env.cons v _, Var.zero => v
  | Env.cons _ ρ, Var.succ x => Env.lookup ρ x

/-- Big-step machine evaluation with 1-step overheads. -/
inductive Eval : {Γ : Ctx} → {A : Ty} → Tm Γ A → Env Γ → Val A → Nat → Prop where
  | var {Γ A} (x : Var Γ A) (ρ : Env Γ) :
      Eval (Tm.var x) ρ (ρ.lookup x) δ_var

  | lam {Γ A B} (t : Tm (A :: Γ) B) (ρ : Env Γ) (bodyBound : Nat) :
      Eval (Tm.lam t) ρ (Val.clo t ρ bodyBound) δ_lam

  | natLit {Γ} (n : Nat) (ρ : Env Γ) :
      Eval (Tm.natLit n) ρ (Val.nat n) δ_lit

  | true {Γ} (ρ : Env Γ) :
      Eval (Tm.true) ρ Val.btrue δ_lit

  | false {Γ} (ρ : Env Γ) :
      Eval (Tm.false) ρ Val.bfalse δ_lit

  | pair {Γ A B} (t : Tm Γ A) (u : Tm Γ B) (ρ : Env Γ)
      (v : Val A) (w : Val B) (kt ku : Nat) :
      Eval t ρ v kt →
      Eval u ρ w ku →
      Eval (Tm.pair t u) ρ (Val.pair v w) (kt + ku + δ_pair)

  | fst {Γ A B} (p : Tm Γ (A × B)) (ρ : Env Γ)
      (v : Val A) (w : Val B) (kp : Nat) :
      Eval p ρ (Val.pair v w) kp →
      Eval (Tm.fst p) ρ v (kp + δ_fst)

  | snd {Γ A B} (p : Tm Γ (A × B)) (ρ : Env Γ)
      (v : Val A) (w : Val B) (kp : Nat) :
      Eval p ρ (Val.pair v w) kp →
      Eval (Tm.snd p) ρ w (kp + δ_snd)

  | ite_true {Γ A} (c : Tm Γ .bool) (t f : Tm Γ A) (ρ : Env Γ)
      (kc kt : Nat) (v : Val A) :
      Eval c ρ Val.btrue kc →
      Eval t ρ v kt →
      Eval (Tm.ite c t f) ρ v (kc + kt + δ_ite)

  | ite_false {Γ A} (c : Tm Γ .bool) (t f : Tm Γ A) (ρ : Env Γ)
      (kc kf : Nat) (v : Val A) :
      Eval c ρ Val.bfalse kc →
      Eval f ρ v kf →
      Eval (Tm.ite c t f) ρ v (kc + kf + δ_ite)

  | app {Γ A B} (f : Tm Γ (A ⇒ B)) (a : Tm Γ A) (ρ : Env Γ)
      (body : Tm (A :: Γ') B) (ρf : Env Γ') (bodyBound : Nat)
      (va : Val A) (v : Val B) (kf ka kb : Nat) :
      Eval f ρ (Val.clo body ρf bodyBound) kf →
      Eval a ρ va ka →
      Eval body (Env.cons va ρf) v kb →
      Eval (Tm.app f a) ρ v (kf + ka + kb + δ_app)

end RBTT
