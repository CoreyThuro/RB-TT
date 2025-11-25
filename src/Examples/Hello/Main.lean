import RBTT.Core
open RBTT

def main : IO Unit := do
  let R : ResCtx := { time := 10, memory := 2048, depth := 3 }
  let x : FeasibleNat R :=
    { val := 2
    , bound := 5
    , val_le_bound := by decide
    , bound_le_time := by decide }
  let y : FeasibleNat R :=
    { val := 3
    , bound := 4
    , val_le_bound := by decide
    , bound_le_time := by decide }
  let z := FeasibleNat.fadd x y (by decide : x.bound + y.bound ≤ R.time)
  IO.println s!"R = {repr R}"
  IO.println s!"x = {repr x}, y = {repr y}"
  IO.println s!"z = {repr z}"
  IO.println s!"z.val = {z.val}, z.bound = {z.bound}"
