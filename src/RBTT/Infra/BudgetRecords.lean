import Lean
import RBTT.Res
import RBTT.Infra.BudgetDB

namespace RBTT.Infra

open Lean

/-!
# Budget Baseline Records

**Purpose**: Persistent budget baselines for tracked proofs in RB-TT.

This module provides the baseline budgets established from `#rb_cost` measurements
in `Examples/Lists.lean`. These baselines serve as the source of truth for CI
budget regression detection via `scripts/CheckBudgets.lean`.

## Baseline Source

All baselines derived from `#rb_cost` output in Examples/Lists.lean:
- `list_length`: size=7, apps=2, lambdas=2, maxDepth=4
- `list_append`: size=30, apps=13, lambdas=3, maxDepth=10
- `list_map`: size=13, apps=4, lambdas=4, maxDepth=8
- `list_filter`: size=10, apps=3, lambdas=3, maxDepth=6
- `list_reverse`: size=7, apps=2, lambdas=2, maxDepth=4

## Budget Formula

From BudgetDB.lean's `recordBudgetFromCost`:
- `time := cost.size * timeMultiplier` (default multiplier = 1)
- `memory := cost.size * 8 * memoryMultiplier` (default multiplier = 1)
- `depth := cost.maxDepth`

## Usage Pattern

```lean
-- In CheckBudgets.lean or CI scripts:
import RBTT.Infra.BudgetRecords

def validateListLength : BudgetCheckResult :=
  checkBudget env `RBTT.Examples.list_length
    { time := 7, memory := 56, depth := 4 }

-- Compare measured cost against list_length_baseline
```

## Maintenance

When proof implementations change and costs shift:
1. Run `#rb_cost` on the proof to get new measurements
2. Update the corresponding baseline in this file
3. Commit the baseline change with justification
4. CI will enforce the new baseline going forward

This creates an auditable history of budget changes over time.
-/

/-! ## List Operation Baselines -/

/-- Budget baseline for list_length operation.
    Source: Examples/Lists.lean #rb_cost output
    Measurement: size=7, apps=2, lambdas=2, maxDepth=4
-/
def list_length_baseline : ResCtx :=
  { time := 7
  , memory := 56  -- size * 8
  , depth := 4 }

/-- Budget baseline for list_append operation.
    Source: Examples/Lists.lean #rb_cost output
    Measurement: size=30, apps=13, lambdas=3, maxDepth=10
-/
def list_append_baseline : ResCtx :=
  { time := 30
  , memory := 240  -- size * 8
  , depth := 10 }

/-- Budget baseline for list_map operation.
    Source: Examples/Lists.lean #rb_cost output
    Measurement: size=13, apps=4, lambdas=4, maxDepth=8
-/
def list_map_baseline : ResCtx :=
  { time := 13
  , memory := 104  -- size * 8
  , depth := 8 }

/-- Budget baseline for list_filter operation.
    Source: Examples/Lists.lean #rb_cost output
    Measurement: size=10, apps=3, lambdas=3, maxDepth=6
-/
def list_filter_baseline : ResCtx :=
  { time := 10
  , memory := 80  -- size * 8
  , depth := 6 }

/-- Budget baseline for list_reverse operation.
    Source: Examples/Lists.lean #rb_cost output
    Measurement: size=7, apps=2, lambdas=2, maxDepth=4
-/
def list_reverse_baseline : ResCtx :=
  { time := 7
  , memory := 56  -- size * 8
  , depth := 4 }

/-! ## Baseline Registry -/

/-- Complete mapping of tracked proofs to their baseline budgets.

    This registry serves as the single source of truth for CheckBudgets.lean.
    Each entry maps a fully qualified proof name to its baseline budget.
-/
def baselineRegistry : List (Name × ResCtx) := [
  (`RBTT.Examples.list_length, list_length_baseline),
  (`RBTT.Examples.list_append, list_append_baseline),
  (`RBTT.Examples.list_map, list_map_baseline),
  (`RBTT.Examples.list_filter, list_filter_baseline),
  (`RBTT.Examples.list_reverse, list_reverse_baseline)
]

/-- Lookup a baseline budget by proof name.
    Returns `none` if proof is not in the baseline registry.
-/
def getBaseline (name : Name) : Option ResCtx :=
  baselineRegistry.lookup name

/-- Check if a proof has a registered baseline. -/
def hasBaseline (name : Name) : Bool :=
  (getBaseline name).isSome

/-- Get all tracked proof names from the baseline registry. -/
def trackedProofs : List Name :=
  baselineRegistry.map (·.1)

/-! ## Validation Helpers -/

/-- Validate that a measured cost is within its baseline budget.

    This is the core validation function used by CheckBudgets.lean.
    Returns a BudgetCheckResult indicating pass/fail/missing-baseline.
-/
def validateAgainstBaseline (name : Name) (measured : ResCtx) : BudgetCheckResult :=
  match getBaseline name with
  | none => .noBudgetStored name
  | some baseline =>
      if measured.time ≤ baseline.time ∧
         measured.memory ≤ baseline.memory ∧
         measured.depth ≤ baseline.depth then
        .withinBudget name measured baseline
      else
        .overBudget name measured baseline

/-- Batch validate multiple proofs against their baselines. -/
def batchValidate (measurements : List (Name × ResCtx)) : List BudgetCheckResult :=
  measurements.map fun (name, measured) => validateAgainstBaseline name measured

/-! ## Example Usage -/

/-- Example: Validate list_length against its baseline. -/
example : BudgetCheckResult :=
  let measured : ResCtx := { time := 7, memory := 56, depth := 4 }
  validateAgainstBaseline `RBTT.Examples.list_length measured
  -- Result: .withinBudget (exact match)

/-- Example: Detect regression in list_append. -/
example : BudgetCheckResult :=
  let measured : ResCtx := { time := 35, memory := 280, depth := 11 }
  validateAgainstBaseline `RBTT.Examples.list_append measured
  -- Result: .overBudget (exceeds baseline)

/-- Example: Handle missing baseline. -/
example : BudgetCheckResult :=
  let measured : ResCtx := { time := 10, memory := 80, depth := 5 }
  validateAgainstBaseline `RBTT.Examples.unknown_proof measured
  -- Result: .noBudgetStored

/-! ## Integration Notes

**For CheckBudgets.lean**:
```lean
import RBTT.Infra.BudgetRecords

def main (args : List String) : IO UInt32 := do
  -- Measure current costs (requires environment access)
  let measurements : List (Name × ResCtx) := [...]

  -- Validate against baselines
  let results := batchValidate measurements

  -- Report and determine exit code
  if countRegressions results > 0 then
    return 1  -- Fail CI
  else
    return 0  -- Pass CI
```

**For Manual Verification**:
```lean
#eval trackedProofs
-- Output: List of all tracked proof names

#eval getBaseline `RBTT.Examples.list_length
-- Output: some { time := 7, memory := 56, depth := 4 }
```

This provides a clean, maintainable, and auditable budget baseline system.
-/

end RBTT.Infra
