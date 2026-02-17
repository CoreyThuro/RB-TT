# Archived Documentation

This directory contains **historical** documentation that is no longer current but preserved for reference.

## Contents

### MLTT Implementation History

- **MLTT_IMPLEMENTATION_ROADMAP.md** - Original roadmap exploring multiple approaches
  - **Status**: Superseded by ExtrinsicMLTT.lean implementation
  - **Date**: Pre-2026-01-10
  - **Historical Value**: Documents the exploration process and failed approaches

- **MLTT_OPTION_A_PLAN.md** - Plan for STLC-style dependent types
  - **Status**: Abandoned in favor of extrinsic typing approach
  - **Date**: Pre-2026-01-10
  - **Historical Value**: Shows why STLC-style approach was insufficient

## Why Archived?

These documents reference files that no longer exist:
- `DependentTypes.lean` (deleted - was STLC-style, not truly dependent)
- `TrueDependentTypes.lean` (deleted - intrinsic approach failed in Lean 4)
- `DependentCost.lean` (deleted - cost semantics for old approach)

## Current Documentation

For up-to-date MLTT implementation documentation, see:
- [MLTT_STATUS.md](../MLTT_STATUS.md) - Current implementation status
- [DEPENDENT_TYPES_GUIDE.md](../DEPENDENT_TYPES_GUIDE.md) - User guide
- [MLTT_IMPLEMENTATION_COMPLETE.md](../MLTT_IMPLEMENTATION_COMPLETE.md) - Technical details
- [src/RBTT/Core/ExtrinsicMLTT.lean](../../src/RBTT/Core/ExtrinsicMLTT.lean) - Source code

## Lessons Learned

1. **Intrinsic typing doesn't work in Lean 4** for dependent types due to mutual recursion limitations
2. **STLC-style Π/Σ types** aren't truly dependent - need real substitution
3. **Extrinsic typing is the correct approach** - standard from type theory literature

---

**Note**: These documents are kept for historical reference only. Do not use them for current development.
