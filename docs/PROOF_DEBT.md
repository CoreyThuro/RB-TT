# Proof Debt Tracking

**Last Updated**: 2026-01-14
**Total Sorry Count**: 30
**Total Axiom Count**: 33

This document tracks all incomplete proofs (`sorry`) and assumed axioms in the RB-TT codebase.

---

## Summary by File

| File | Sorry | Axiom | Status | Priority |
|------|-------|-------|--------|----------|
| [SubstitutionLemmas.lean](#substitutionlemmaslean) | 10 | 0 | Scaffolding | P1 - High |
| [OpCost.lean](#opcostlean) | 8 | 18 | Partial | P1 - High |
| [PresheafSet.lean](#presheafsetlean) | 6 | 5 | Experimental | P2 - Medium |
| [Recursion.lean](#recursionlean) | 3 | 4 | Experimental | P3 - Low |
| [BinarySearch.lean](#binarysearchlean) | 2 | 0 | Example | P3 - Low |
| [Universe.lean](#universelean) | 0 | 8 | Core | P1 - High |
| [Budget.lean](#budgetlean) | 1 | 0 | Infrastructure | P2 - Medium |
| [Modality.lean](#modalitylean) | 0 | 1 | Core | P1 - High |
| [Cost.lean](#costlean) | 0 | 1 | Infrastructure | P2 - Medium |

---

## Core Files (Priority 1)

### SubstitutionLemmas.lean
**Location**: `src/RBTT/Core/SubstitutionLemmas.lean`
**Status**: 🔄 Phase 2 scaffolding - all proofs stubbed with `sorry`
**Priority**: P1 - Required for type safety proofs

#### Incomplete Proofs (10 sorry)

1. **shift_zero** (line ~43)
   - **Claim**: `shift c 0 e = e` - shifting by 0 is identity
   - **Plan**: Induction on `Expr` structure
   - **Difficulty**: Easy (~10 lines)
   - **Blocks**: None

2. **shift_above_free** (line ~50)
   - **Claim**: Shifting above all free variables does nothing
   - **Plan**: Define free variable predicate, induction on `Expr`
   - **Difficulty**: Medium (~20 lines)
   - **Blocks**: None

3. **shift_shift** (line ~64)
   - **Claim**: Composing two shifts works correctly
   - **Plan**: Induction on `Expr`, case analysis on cutoff relationships
   - **Difficulty**: Medium (~30 lines)
   - **Blocks**: None

4. **subst_shift** (line ~73)
   - **Claim**: Substitution commutes with shift (when n >= c)
   - **Plan**: Induction on `Expr`, careful index arithmetic
   - **Difficulty**: Hard (~40 lines)
   - **Blocks**: None

5. **shift_subst** (line ~82)
   - **Claim**: Shift commutes with substitution (when c <= n)
   - **Plan**: Induction on `Expr`, index arithmetic
   - **Difficulty**: Hard (~40 lines)
   - **Blocks**: None

6. **subst_subst** (line ~91)
   - **Claim**: Composing two substitutions works correctly
   - **Plan**: Induction on `Expr`, complex case analysis
   - **Difficulty**: Hard (~50 lines)
   - **Blocks**: None

7. **typing_substitution** (line ~205) ⭐ **CRITICAL**
   - **Claim**: Substitution preserves typing (main theorem)
   - **Plan**: Induction on `HasType` derivation
   - **Difficulty**: Very Hard (~200 lines)
   - **Blocks**: Requires lemmas 1-6 above
   - **Impact**: Justifies all dependent type operations

8. **typing_substitution_simple** (line ~217)
   - **Claim**: Simplified case for empty context extension
   - **Plan**: Specialize `typing_substitution`
   - **Difficulty**: Easy (~10 lines)
   - **Blocks**: Requires `typing_substitution`

9. **typing_weakening** (line ~229)
   - **Claim**: Adding unused variables preserves typing
   - **Plan**: Induction on `HasType` derivation
   - **Difficulty**: Medium (~30 lines)
   - **Blocks**: None

**Estimated Total Effort**: 1-2 weeks for complete proofs

---

### OpCost.lean
**Location**: `src/RBTT/Core/OpCost.lean`
**Status**: ⚠️ Partial - core operational semantics with proof gaps
**Priority**: P1 - Required for cost soundness

#### Axioms (18)

1. **Δ, Δ₀, Δₐ, Δₚ** (δ cost constants)
   - Unit costs for operations
   - **Justification**: Meta-level parameters, externally specified
   - **Status**: Acceptable as axioms

2-18. **Various cost axioms** (need detailed audit)
   - Cost algebra properties
   - Lattice operations
   - **Action Required**: Review which should be theorems vs axioms

#### Incomplete Proofs (8 sorry)

1. **step_deterministic** (line ~434)
   - **Claim**: Single-step reduction is deterministic
   - **Plan**: Case analysis on `Step` derivation
   - **Difficulty**: Medium (~50 lines)
   - **Blocks**: None
   - **Status**: Partially proved, needs completion

2-8. **Cost soundness theorems** (lines 685, 691, 697, etc.)
   - Various cost bound correctness properties
   - **Plan**: Requires completed step semantics
   - **Difficulty**: Hard
   - **Blocks**: `step_deterministic` and axiom cleanup

**Action Required**:
- Audit axioms: which are legitimate assumptions vs should be proved?
- Complete `step_deterministic` proof
- Prove cost soundness properties

---

### Universe.lean
**Location**: `src/RBTT/Core/Universe.lean`
**Status**: ⚠️ Type-in-Type axiomatization
**Priority**: P1 - Foundational (but acceptable for RB-TT)

#### Axioms (8)

All axioms relate to the Type-in-Type universe structure:
- `U : U` (Type-in-Type)
- Universe lifting and coherence

**Note**: Type-in-Type is **inconsistent as a logic** (Girard's paradox) but **acceptable for RB-TT** as a programming language with cost bounds. This is documented in the paper.

**Status**: ✅ Acceptable - these are intentional design decisions, not proof debt

---

### Modality.lean
**Location**: `src/RBTT/Core/Modality.lean`
**Status**: Core modality definition
**Priority**: P1

#### Axioms (1)

1. **Modality operations axiom**
   - **Action Required**: Review if this should be proved from more primitive axioms

---

## Experimental Files (Priority 2-3)

### PresheafSet.lean
**Location**: `src/RBTT/Semantics/PresheafSet.lean`
**Status**: 🧪 Experimental presheaf semantics
**Priority**: P2 - Research scaffold, not production

#### Axioms (5) + Sorry (6)

This file is entirely experimental scaffolding for category-theoretic semantics.

**Status**: ✅ Acceptable as research exploration
**Action**: Consider moving to `src/RBTT/Experimental/` or `src/RBTT/Research/`

---

### Recursion.lean
**Location**: `src/RBTT/Core/Recursion.lean`
**Status**: 🧪 Experimental recursion via fuel
**Priority**: P3 - **SHOULD BE MOVED**

#### Axioms (4) + Sorry (3)

This file introduces recursion via fuel and various axioms:
- `fix_has_bound`
- `sorry : Tm ...`

**Issue**: File is in `Core/` but is experimental and not referenced in paper.

**Action Required**:
- **PRIORITY**: Move to `src/RBTT/Experimental/RecursionFuel.lean`
- Update imports
- Document as exploratory work

---

### BinarySearch.lean
**Location**: `src/RBTT/Examples/BinarySearch.lean`
**Status**: Example implementation
**Priority**: P3 - Example only

#### Incomplete Proofs (2 sorry)

Example-level proofs, acceptable for demonstration code.

**Status**: ✅ Acceptable for examples

---

## Infrastructure (Priority 2)

### Budget.lean
**Location**: `src/RBTT/Budget.lean`
**Status**: Budget management infrastructure
**Priority**: P2

#### Incomplete Proofs (1 sorry)

**Action Required**: Review and complete or document justification

---

### Cost.lean
**Location**: `src/RBTT/Infra/Cost.lean`
**Status**: Cost infrastructure
**Priority**: P2

#### Axioms (1)

**Action Required**: Review if axiom is justified or should be proved

---

## Action Plan

### Immediate (This Week)

1. ✅ **DONE**: Create this PROOF_DEBT.md file
2. **Move Recursion.lean** to Experimental directory
3. **Audit OpCost.lean axioms**: Determine which are legitimate vs need proofs

### Short Term (Next 2 Weeks)

4. **Complete SubstitutionLemmas.lean** identity lemmas (shift_zero, shift_above_free)
5. **Complete step_deterministic** in OpCost.lean
6. **Review infrastructure axioms** in Budget.lean, Cost.lean, Modality.lean

### Medium Term (1-2 Months)

7. **Complete SubstitutionLemmas.lean** composition lemmas
8. **Prove typing_substitution** theorem (the big one)
9. **Cost soundness proofs** in OpCost.lean

### Long Term (Research Goals)

10. **PresheafSet.lean**: Either complete or explicitly mark as research exploration
11. **Advanced features**: Vector recursion, J-eliminator proofs

---

## Tracking Updates

When completing proofs or adding axioms:
1. Update the counts at the top of this file
2. Move the item from "Incomplete" to "✅ Complete" section
3. Document the proof strategy used
4. Add git commit reference

### Completed Proofs

*None yet - this is the initial tracking document*

---

## References

- **Type Theory**: Benjamin Pierce, "Types and Programming Languages" (TAPL)
- **Dependent Types**: Robert Harper, "Practical Foundations for Programming Languages" (PFPL)
- **Substitution**: Standard lemmas from Agda and Coq standard libraries

---

**Maintained by**: Corey Thuro
**Review Frequency**: Update after each proof completion or axiom addition
