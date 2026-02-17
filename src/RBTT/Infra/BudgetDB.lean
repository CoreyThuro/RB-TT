import Lean
import RBTT.Res
import RBTT.Infra.Cost

namespace RBTT.Infra

open Lean

/-!
# Budget Database Infrastructure

This module provides persistent storage and comparison for proof budgets,
enabling CI-based regression detection and resource tracking.

## Key Components

1. **Budget Storage**: Environment extension mapping proof names to resource budgets
2. **Budget Recording**: API to store budget measurements from ProofCost analysis
3. **Budget Comparison**: Detect regressions by comparing current vs stored budgets
4. **CI Integration**: Support for scripts/CheckBudgets.lean workflow

## Design

The BudgetDB stores `Name → ResCtx` mappings in Lean's environment as persistent
attributes. This allows:
- Cross-session budget persistence
- Git-trackable budget baselines
- Automated regression detection in CI

## Usage Pattern

```lean
-- Record a budget for a proof
#rb_cost my_proof  -- Measures ProofCost (lines 20-50 of Cost.lean)
#record_budget my_proof { time := 150, memory := 800, depth := 5 }

-- Check for regressions
#check_budget my_proof  -- Compares current cost vs stored budget
```

-/

/-! ## Budget Record Structure -/

/-- A budget record associating a proof name with its resource bounds.

    This structure is stored persistently in the environment to enable
    cross-session budget tracking and regression detection.
-/
structure BudgetRecord where
  /-- The fully qualified name of the proof/definition. -/
  defName : Name
  /-- The resource budget for this proof. -/
  budget : ResCtx
  /-- Optional description or metadata. -/
  description : String := ""
  deriving Repr

instance : Inhabited BudgetRecord where
  default := { defName := .anonymous, budget := { time := 0, memory := 0, depth := 0 }, description := "" }

/-! ## Environment Extension for Budget Storage -/

/-- Initialize budget database as environment extension.

    This stores a persistent map from proof names to their budgets,
    allowing budget information to survive across compilation units
    and be tracked in version control.
-/
initialize budgetDBExtension : SimplePersistentEnvExtension BudgetRecord (Lean.RBMap Name ResCtx Name.quickCmp) ←
  registerSimplePersistentEnvExtension {
    name := `budgetDB
    addImportedFn := fun as =>
      -- Merge imported budget records
      let merged := as.foldl (init := ∅) fun acc records =>
        records.foldl (init := acc) fun map record =>
          map.insert record.defName record.budget
      merged
    addEntryFn := fun map record => map.insert record.defName record.budget
  }

/-! ## Core Budget Database Operations -/

/-- Store a budget record in the environment.

    This adds a budget record to the persistent database, making it
    available for future comparisons and regression detection.
-/
def storeBudget (env : Environment) (name : Name) (budget : ResCtx)
    (description : String := "") : Environment :=
  let record : BudgetRecord := { defName := name, budget := budget, description := description }
  budgetDBExtension.addEntry env record

/-- Retrieve a stored budget for a given proof name.

    Returns `some budget` if a budget exists for the name, `none` otherwise.
-/
def getBudget (env : Environment) (name : Name) : Option ResCtx :=
  let db := budgetDBExtension.getState env
  db.find? name

/-- Check if a budget exists for a given proof name. -/
def hasBudget (env : Environment) (name : Name) : Bool :=
  (getBudget env name).isSome

/-- Get all stored budget records from the environment. -/
def getAllBudgets (env : Environment) : Lean.RBMap Name ResCtx Name.quickCmp :=
  budgetDBExtension.getState env

/-! ## Budget Comparison and Regression Detection -/

/-- Comparison result for budget vs actual cost. -/
inductive BudgetCheckResult
  | withinBudget (name : Name) (actual : ResCtx) (budget : ResCtx)
  | overBudget (name : Name) (actual : ResCtx) (budget : ResCtx)
  | noBudgetStored (name : Name)
  deriving Repr

/-- Compare actual resource usage against stored budget.

    Returns:
    - `withinBudget` if actual ≤ budget
    - `overBudget` if actual exceeds budget (regression)
    - `noBudgetStored` if no budget exists for this proof
-/
def checkBudget (env : Environment) (name : Name) (actual : ResCtx) : BudgetCheckResult :=
  match getBudget env name with
  | none => .noBudgetStored name
  | some budget =>
      -- Use direct component comparison since we have ResCtx.le
      if actual.time ≤ budget.time ∧ actual.memory ≤ budget.memory ∧ actual.depth ≤ budget.depth then
        .withinBudget name actual budget
      else
        .overBudget name actual budget

/-- Format a budget check result as human-readable string. -/
def formatCheckResult (result : BudgetCheckResult) : String :=
  match result with
  | .withinBudget name actual budget =>
      s!"✅ {name}: Within budget\n" ++
      s!"   Actual: (time={actual.time}, mem={actual.memory}, depth={actual.depth})\n" ++
      s!"   Budget: (time={budget.time}, mem={budget.memory}, depth={budget.depth})"
  | .overBudget name actual budget =>
      let timeOver := actual.time - budget.time
      let memOver := actual.memory - budget.memory
      let depthOver := if actual.depth > budget.depth then actual.depth - budget.depth else 0
      s!"❌ {name}: BUDGET EXCEEDED (Regression!)\n" ++
      s!"   Actual: (time={actual.time}, mem={actual.memory}, depth={actual.depth})\n" ++
      s!"   Budget: (time={budget.time}, mem={budget.memory}, depth={budget.depth})\n" ++
      s!"   Over by: (time=+{timeOver}, mem=+{memOver}, depth=+{depthOver})"
  | .noBudgetStored name =>
      s!"⚠️  {name}: No budget stored (run #record_budget first)"

/-! ## Batch Operations for CI/CD -/

/-- Check multiple proofs against their stored budgets.

    Returns a list of check results, useful for CI workflows that need
    to validate multiple proofs at once.
-/
def checkMultipleBudgets (env : Environment) (checks : List (Name × ResCtx)) :
    List BudgetCheckResult :=
  checks.map fun (name, actual) => checkBudget env name actual

/-- Count how many proofs are over budget in a batch check. -/
def countRegressions (results : List BudgetCheckResult) : Nat :=
  results.foldl (init := 0) fun count result =>
    match result with
    | .overBudget .. => count + 1
    | _ => count

/-- Generate a summary report for batch budget checks. -/
def generateBatchReport (results : List BudgetCheckResult) : String :=
  let total := results.length
  let regressions := countRegressions results
  let passed := results.foldl (init := 0) fun count result =>
    match result with
    | .withinBudget .. => count + 1
    | _ => count
  let noBaseline := results.foldl (init := 0) fun count result =>
    match result with
    | .noBudgetStored .. => count + 1
    | _ => count

  let header := s!"Budget Check Report: {passed}/{total} passed, {regressions} regressions, {noBaseline} missing baselines\n" ++
                (String.mk (List.replicate 80 '=')) ++ "\n\n"

  let details := results.foldl (init := "") fun acc result =>
    acc ++ formatCheckResult result ++ "\n\n"

  header ++ details

/-! ## Helper Functions for Budget Management -/

/-- Calculate percentage increase of actual over budget. -/
def budgetOveragePercent (actual budget : Nat) : Float :=
  if budget == 0 then 100.0
  else
    -- Simple percentage calculation
    let diff := if actual > budget then actual - budget else 0
    let diffFloat : Float := diff.toFloat
    let budgetFloat : Float := budget.toFloat
    (diffFloat / budgetFloat) * 100.0

/-- Check if a budget check result represents a regression. -/
def isRegression (result : BudgetCheckResult) : Bool :=
  match result with
  | .overBudget .. => true
  | _ => false

/-- Extract all regression results from a batch check. -/
def getRegressions (results : List BudgetCheckResult) : List BudgetCheckResult :=
  results.filter isRegression

/-- Update a stored budget with new values.

    This is useful when intentionally increasing budgets after
    optimizing other aspects or accepting necessary cost increases.
-/
def updateBudget (env : Environment) (name : Name) (newBudget : ResCtx)
    (description : String := "Updated budget") : Environment :=
  storeBudget env name newBudget description

/-! ## Integration with Cost Infrastructure -/

/-- Record budget from a ProofCost measurement.

    Converts ProofCost (from Infra/Cost.lean) to ResCtx and stores it.
    Uses ProofCost.size as the time metric (total expression nodes).
    This is the primary way to establish budget baselines.
-/
def recordBudgetFromCost (env : Environment) (name : Name) (cost : ProofCost)
    (timeMultiplier : Nat := 1) (memoryMultiplier : Nat := 1)
    (description : String := "Auto-recorded from #rb_cost") : Environment :=
  let budget : ResCtx := {
    time := cost.size * timeMultiplier,
    memory := cost.size * 8 * memoryMultiplier,
    depth := cost.maxDepth
  }
  storeBudget env name budget description

/-- Compare a ProofCost measurement against stored budget.

    Uses ProofCost.size as the time metric (total expression nodes).
-/
def checkCostAgainstBudget (env : Environment) (name : Name) (cost : ProofCost)
    (timeMultiplier : Nat := 1) (memoryMultiplier : Nat := 1) : BudgetCheckResult :=
  let actual : ResCtx := {
    time := cost.size * timeMultiplier,
    memory := cost.size * 8 * memoryMultiplier,
    depth := cost.maxDepth
  }
  checkBudget env name actual

/-! ## Example Usage Patterns -/

/-- Example: Store a budget baseline for a proof. -/
example (env : Environment) : Environment :=
  storeBudget env `MyModule.myTheorem
    { time := 150, memory := 800, depth := 5 }
    "Initial baseline from manual measurement"

/-- Example: Check if proof stays within budget. -/
example (env : Environment) : BudgetCheckResult :=
  let actual : ResCtx := { time := 140, memory := 750, depth := 4 }
  checkBudget env `MyModule.myTheorem actual

/-- Example: Batch check multiple proofs. -/
example (env : Environment) : List BudgetCheckResult :=
  let checks := [
    (`Proof1, { time := 100, memory := 500, depth := 3 }),
    (`Proof2, { time := 200, memory := 1000, depth := 5 }),
    (`Proof3, { time := 150, memory := 800, depth := 4 })
  ]
  checkMultipleBudgets env checks

/-! ## CI/CD Integration Notes

For CI workflows (scripts/CheckBudgets.lean):

1. **Baseline Recording**: Run once to establish budgets
   ```lean
   #rb_cost my_proof
   #record_budget my_proof <measured_budget>
   ```

2. **Regression Detection**: Run in CI on each commit
   ```lean
   #rb_cost my_proof  -- Measure current cost
   #check_budget my_proof  -- Compare vs stored
   ```

3. **Batch Validation**: Check all tracked proofs
   ```lean
   let results := checkMultipleBudgets env all_proofs
   let report := generateBatchReport results
   IO.println report
   if countRegressions results > 0 then
     IO.Process.exit 1  -- Fail CI on regression
   ```

This enables automated detection of performance regressions in proofs,
maintaining resource bounds over time.
-/

end RBTT.Infra
