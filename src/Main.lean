import RBTT.Core
open RBTT

/-- Simple demonstration of RB-TT resource-bounded computation -/
def main : IO Unit := do
  IO.println "RB-TT: Resource-Bounded Homotopy Type Theory"
  IO.println "==============================================="
  IO.println ""

  -- Define a resource context
  let R : ResCtx := { time := 100, memory := 2048, depth := 5 }
  IO.println s!"Resource Context: {repr R}"
  IO.println ""

  -- Create feasible natural numbers
  let x : FeasibleNat R :=
    { val := 15
    , bound := 20
    , val_le_bound := by decide
    , bound_le_time := by decide }

  let y : FeasibleNat R :=
    { val := 25
    , bound := 30
    , val_le_bound := by decide
    , bound_le_time := by decide }

  IO.println s!"x = {x.val} (bound: {x.bound})"
  IO.println s!"y = {y.val} (bound: {y.bound})"
  IO.println ""

  -- Demonstrate feasible addition
  let z := FeasibleNat.fadd x y (by decide : x.bound + y.bound ≤ R.time)
  IO.println s!"x + y = {z.val} (bound: {z.bound})"
  IO.println s!"Bound check: {z.bound} ≤ {R.time} ✓"
  IO.println ""

  -- Demonstrate widening to larger context
  let S : ResCtx := { time := 200, memory := 4096, depth := 10 }
  let x_wider := FeasibleNat.widen (by decide : R ≤ S) x
  IO.println s!"Widened to larger context S: {repr S}"
  IO.println s!"x in S still has val={x_wider.val}, bound={x_wider.bound}"
  IO.println ""

  IO.println "✓ All operations type-checked with resource proofs!"
