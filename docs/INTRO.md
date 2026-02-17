# RB-TT: Resource-Bounded Ultrafinitist TT (workable skeleton)

This repository is a *compiling-ready* skeleton for a graded/resource-aware foundation.
It contains:
- Lean 4 library `RBTT` with minimal `ResCtx` and `FeasibleNat`.
- Executable `rbtt` printing a tiny demo.
- `archive/` holds your original drafts one level deep, untouched.

## Build (Lean 4)
1. Install elan: https://leanprover-community.github.io/get_started.html
2. In this folder:
   ```
   lake build
   lake exe rbtt
   ```
## Python mock demo
   ```
   python demo/feasible_demo.py
   ```

## Next steps
- Add costed small-step semantics.
- Add proofs: substitution, weakening along `R ≤ S`, and type safety.
- Introduce graded modalities for feasibility.
