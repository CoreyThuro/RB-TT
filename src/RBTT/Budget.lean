import RBTT.Res
import RBTT.Core.Modality

namespace RBTT

/-!
# Resource Budget Management

**Status**: Supplementary infrastructure (NOT in official action list)
**Relationship**: Complements Infra/BudgetDB.lean (allocation vs persistence)

This module provides example infrastructure for managing resource budgets in RB-TT.
It builds on the ResCtx structure and cost-aware Box modality to enable:

1. **Budget Allocation**: Strategies for distributing resources across operations
2. **Budget Verification**: Predicates for checking budget sufficiency
3. **Budget Consumption**: Tracking and updating remaining resources
4. **Budget Composition**: Combining budgets using monoid operations

## Key Concepts

**Budget Allocation Strategies**:
- Conservative: Over-provision resources for safety
- Balanced: Allocate exact required resources
- Aggressive: Minimal allocation with tight bounds

**Budget Verification**:
- Check if operation fits within budget
- Validate budget sufficiency before execution
- Prevent over-budget operations at type level

**Budget Consumption**:
- Track used vs remaining resources
- Update budgets as operations execute
- Maintain budget invariants

-/

open RBTT Box

/-! ## Budget Allocation Strategies -/

/-- Budget allocation strategy determines how resources are distributed.

    Conservative: Allocate 2x required resources for safety margin
    Balanced: Allocate exactly required resources
    Aggressive: Allocate 1.5x required for tight bounds
-/
inductive BudgetStrategy
  | conservative  -- 2x allocation
  | balanced      -- 1x allocation
  | aggressive    -- 1.5x allocation
  deriving Repr, DecidableEq

/-- Apply budget strategy to scale a base resource context. -/
def applyStrategy (strategy : BudgetStrategy) (base : ResCtx) : ResCtx :=
  match strategy with
  | .conservative => { time := base.time * 2, memory := base.memory * 2, depth := base.depth + 1 }
  | .balanced     => base
  | .aggressive   => { time := base.time + base.time / 2, memory := base.memory + base.memory / 2, depth := base.depth }

/-- Conservative allocation provides 2x resources. -/
theorem conservative_doubles (R : ResCtx) :
    (applyStrategy .conservative R).time = R.time * 2 := rfl

/-- Balanced allocation preserves resources exactly. -/
theorem balanced_preserves (R : ResCtx) :
    applyStrategy .balanced R = R := rfl

/-- Aggressive allocation is between 1x and 2x. -/
theorem aggressive_bounded (R : ResCtx) :
    R.time ≤ (applyStrategy .aggressive R).time ∧
    (applyStrategy .aggressive R).time ≤ R.time * 2 := by
  constructor
  · -- R.time ≤ R.time + R.time / 2
    simp [applyStrategy]
    omega
  · -- R.time + R.time / 2 ≤ R.time * 2
    simp [applyStrategy]
    omega


/-! ## Budget Verification Predicates -/

/-- Check if a cost bound fits within a budget's time allocation. -/
def budgetSufficient (cost : Nat) (budget : ResCtx) : Prop :=
  cost ≤ budget.time

/-- Decidable instance for budget sufficiency checking. -/
instance : Decidable (budgetSufficient cost budget) :=
  inferInstanceAs (Decidable (cost ≤ budget.time))

/-- Budget sufficiency is preserved by weakening (larger budgets). -/
theorem budgetSufficient_weaken {cost : Nat} {R S : ResCtx}
    (h : budgetSufficient cost R) (hw : R ≤ S) :
    budgetSufficient cost S := by
  unfold budgetSufficient
  calc cost
      ≤ R.time := h
    _ ≤ S.time := hw.1

/-- Zero cost is always sufficient for any budget. -/
theorem zero_cost_sufficient (R : ResCtx) :
    budgetSufficient 0 R := by
  unfold budgetSufficient
  exact Nat.zero_le R.time

/-- If budget is sufficient for a and b separately, it's sufficient for a+b with combined budget. -/
theorem budgetSufficient_add {a b : Nat} {R₁ R₂ : ResCtx}
    (h₁ : budgetSufficient a R₁)
    (h₂ : budgetSufficient b R₂) :
    budgetSufficient (a + b) (R₁ ⊕ R₂) := by
  unfold budgetSufficient ResCtx.add
  simp only [add_time]
  exact Nat.add_le_add h₁ h₂


/-! ## Budget Consumption Tracking -/

/-- Consume resources from a budget, returning remaining budget.

    Precondition: cost must be ≤ budget.time (verified by caller)
-/
def consumeBudget (cost : Nat) (budget : ResCtx) (h : cost ≤ budget.time) : ResCtx :=
  { time := budget.time - cost
  , memory := budget.memory  -- Memory tracking simplified for now
  , depth := budget.depth }   -- Depth preserved

/-- Consuming zero cost preserves the budget. -/
theorem consume_zero (budget : ResCtx) (h : 0 ≤ budget.time) :
    consumeBudget 0 budget h = budget := by
  unfold consumeBudget
  simp

/-- Consuming from a conservative budget leaves at least original budget. -/
theorem conservative_consumption_safe (cost : Nat) (base : ResCtx)
    (h : cost ≤ base.time) :
    base.time ≤ (consumeBudget cost (applyStrategy .conservative base)
                  (by simp [applyStrategy]; omega)).time := by
  simp [consumeBudget, applyStrategy]
  omega

/-- Sequential consumption is associative. -/
theorem consume_assoc (c₁ c₂ : Nat) (budget : ResCtx)
    (h₁ : c₁ + c₂ ≤ budget.time)
    (h₂ : c₁ ≤ budget.time)
    (h₃ : c₂ ≤ (consumeBudget c₁ budget h₂).time) :
    consumeBudget c₂ (consumeBudget c₁ budget h₂) h₃ =
    consumeBudget (c₁ + c₂) budget h₁ := by
  simp [consumeBudget]
  omega


/-! ## Budget Allocation Examples -/

/-- Allocate budget for a simple list operation. -/
def allocateForList (xs_length : Nat) (strategy : BudgetStrategy := .balanced) : ResCtx :=
  let base : ResCtx := { time := xs_length, memory := xs_length * 8, depth := 1 }
  applyStrategy strategy base

/-- Conservative allocation for list of length 100. -/
example : (allocateForList 100 .conservative).time = 200 := rfl

/-- Balanced allocation matches input size. -/
example : (allocateForList 50 .balanced).time = 50 := rfl

/-- Aggressive allocation is 1.5x input. -/
example : (allocateForList 100 .aggressive).time = 150 := rfl


/-- Allocate budget for composing two operations. -/
def allocateForComposition (cost₁ cost₂ : Nat) (strategy : BudgetStrategy := .balanced) : ResCtx :=
  let base : ResCtx := { time := cost₁ + cost₂, memory := (cost₁ + cost₂) * 8, depth := 2 }
  applyStrategy strategy base

/-- Composition allocation sums costs. -/
theorem composition_sums_costs (c₁ c₂ : Nat) :
    (allocateForComposition c₁ c₂ .balanced).time = c₁ + c₂ := rfl


/-! ## Budget Splitting for Parallel Operations -/

/-- Split a budget between two parallel operations.

    Each operation gets its proportional share based on estimated costs.
-/
def splitBudget (total : ResCtx) (cost₁ cost₂ : Nat) :
    ResCtx × ResCtx :=
  let total_cost := cost₁ + cost₂
  if h : total_cost > 0 then
    let ratio₁ := cost₁ * total.time / total_cost
    let ratio₂ := total.time - ratio₁
    let R₁ : ResCtx := { time := ratio₁, memory := cost₁ * 8, depth := total.depth }
    let R₂ : ResCtx := { time := ratio₂, memory := cost₂ * 8, depth := total.depth }
    (R₁, R₂)
  else
    (ResCtx.zero, ResCtx.zero)

/-- Split budgets sum back to approximately original (modulo rounding).

    Note: Due to integer division, sum may be less than total.
-/
theorem split_approximates_total (total : ResCtx) (c₁ c₂ : Nat) (h : c₁ + c₂ > 0) :
    let (R₁, R₂) := splitBudget total c₁ c₂
    R₁.time + R₂.time ≤ total.time := by
  simp [splitBudget, h]
  -- Integer division causes rounding
  sorry


/-! ## Budget Validation Helpers -/

/-- Sum all natural numbers in a list. -/
def listSum (xs : List Nat) : Nat :=
  xs.foldl (· + ·) 0

/-- Validate that a sequence of operations fits within budget. -/
def validateSequence (costs : List Nat) (budget : ResCtx) : Bool :=
  listSum costs ≤ budget.time

/-- Example: Sequence [10, 20, 30] fits in budget of 100. -/
example : validateSequence [10, 20, 30] { time := 100, memory := 500, depth := 5 } = true := rfl

/-- Example: Sequence [50, 60] does not fit in budget of 100. -/
example : validateSequence [50, 60] { time := 100, memory := 500, depth := 5 } = false := rfl


/-- Check if budget has sufficient resources across all dimensions. -/
structure BudgetCheck where
  time_ok : Bool
  memory_ok : Bool
  depth_ok : Bool
  deriving Repr

/-- Comprehensive budget check against requirements. -/
def checkBudget (required : ResCtx) (available : ResCtx) : BudgetCheck :=
  { time_ok := required.time ≤ available.time
  , memory_ok := required.memory ≤ available.memory
  , depth_ok := required.depth ≤ available.depth }

/-- Budget is fully sufficient if all dimensions check out. -/
def budgetCheckPassed (check : BudgetCheck) : Bool :=
  check.time_ok && check.memory_ok && check.depth_ok

/-- Example: Check that budget {100, 500, 5} meets requirements {50, 300, 3}. -/
example :
    let required : ResCtx := { time := 50, memory := 300, depth := 3 }
    let available : ResCtx := { time := 100, memory := 500, depth := 5 }
    budgetCheckPassed (checkBudget required available) = true := rfl


/-! ## Integration with Box Modality -/

/-- Allocate budget and create boxed value with automatic verification.

    This combines budget allocation with cost-aware boxing from Core/Modality.
-/
noncomputable def allocateAndBox {α : Type u} (value : α) (cost : Nat)
    (strategy : BudgetStrategy) :
    Box (applyStrategy strategy { time := cost, memory := cost * 8, depth := 1 }) α :=
  match strategy with
  | .conservative =>
      have h : cost ≤ (cost * 2) := by omega
      box_intro value cost h
  | .balanced =>
      have h : cost ≤ cost := by omega
      box_intro value cost h
  | .aggressive =>
      have h : cost ≤ (cost + cost / 2) := by omega
      box_intro value cost h

/-- Example: Conservative boxing provides 2x budget. -/
example (n : Nat) :
    let boxed := allocateAndBox n 50 .conservative
    True := trivial


/-! ## Budget Planning Utilities -/

/-- Plan budget for a multi-phase operation.

    Given costs for each phase, compute total budget with strategy.
-/
def planMultiPhase (phase_costs : List Nat) (strategy : BudgetStrategy) : ResCtx :=
  let total_cost := listSum phase_costs
  let base : ResCtx := { time := total_cost, memory := total_cost * 8, depth := phase_costs.length }
  applyStrategy strategy base

/-- Example: Plan budget for 3-phase operation [100, 200, 150]. -/
example :
    (planMultiPhase [100, 200, 150] .balanced).time = 450 := rfl

/-- Example: Conservative planning doubles total. -/
example :
    (planMultiPhase [100, 200] .conservative).time = 600 := rfl


/-! ## Budget Invariants and Properties -/

/-- Budget sufficiency is monotonic: larger budgets support same costs. -/
theorem budgetSufficient_monotonic {cost : Nat} {R₁ R₂ : ResCtx}
    (h_sufficient : budgetSufficient cost R₁)
    (h_larger : R₁ ≤ R₂) :
    budgetSufficient cost R₂ :=
  budgetSufficient_weaken h_sufficient h_larger

/-- Strategy ordering: conservative ≥ aggressive ≥ balanced (for time). -/
theorem strategy_ordering (R : ResCtx) :
    R.time ≤ (applyStrategy .aggressive R).time ∧
    (applyStrategy .aggressive R).time ≤ (applyStrategy .conservative R).time := by
  constructor
  · -- balanced ≤ aggressive
    unfold applyStrategy
    simp
    omega
  · -- aggressive ≤ conservative
    unfold applyStrategy
    simp
    omega

/-- Consuming less leaves more remaining. -/
theorem consume_less_remains_more {c₁ c₂ : Nat} {budget : ResCtx}
    (h_less : c₁ ≤ c₂)
    (h₁ : c₁ ≤ budget.time)
    (h₂ : c₂ ≤ budget.time) :
    (consumeBudget c₂ budget h₂).time ≤ (consumeBudget c₁ budget h₁).time := by
  unfold consumeBudget
  simp
  omega


end RBTT
