import RBTT.Res
import RBTT.Core.Modality
import RBTT.Core.STLC
import RBTT.Core.OpCost
import RBTT.Core.Recursion
import RBTT.Infra.Cost

namespace RBTT

structure FeasibleNat (R : ResCtx) where
  val   : Nat
  bound : Nat
  val_le_bound  : val ≤ bound
  bound_le_time : bound ≤ R.time
deriving Repr, DecidableEq

namespace FeasibleNat

variable {R : ResCtx}

/-- Addition on feasible naturals, with additive bounds.
    Requires that the sum of bounds fits in R.time. -/
def fadd (x y : FeasibleNat R) (h_sum : x.bound + y.bound ≤ R.time) : FeasibleNat R :=
  { val := x.val + y.val
  , bound := x.bound + y.bound
  , val_le_bound := Nat.add_le_add x.val_le_bound y.val_le_bound
  , bound_le_time := h_sum }

@[simp] theorem val_fadd (x y : FeasibleNat R) (h : x.bound + y.bound ≤ R.time) :
  (fadd x y h).val = x.val + y.val := rfl

@[simp] theorem bound_fadd (x y : FeasibleNat R) (h : x.bound + y.bound ≤ R.time) :
  (fadd x y h).bound = x.bound + y.bound := rfl

theorem fadd_comm (x y : FeasibleNat R) (hxy : x.bound + y.bound ≤ R.time)
    (hyx : y.bound + x.bound ≤ R.time) :
  (fadd x y hxy).val = (fadd y x hyx).val := by
  simp [fadd, Nat.add_comm]

/-- Transport a feasible value along an order-preserving resource extension.
    If R ≤ S and x is feasible in R, then x is feasible in S (more resources). -/
def widen {R S : ResCtx} (h : R ≤ S) (x : FeasibleNat R) : FeasibleNat S :=
  { val := x.val
  , bound := x.bound
  , val_le_bound := x.val_le_bound
  , bound_le_time := Nat.le_trans x.bound_le_time h.1 }

end FeasibleNat

end RBTT
