# RB-TT — Resource-Bounded Type Theory

![RB-TT logo](docs/rbtt-logo.png)

**Resource-Bounded Type Theory** (RB-TT) is a type-theoretic framework for **compositional cost analysis**, where terms are typed with synthesized bounds drawn from an abstract **resource lattice** $(L, \preceq, \oplus, \sqcup, \bot)$, and a graded **feasibility modality** $\Box_r$ tracks which computations are admissible under a given resource budget.

This is the **first paper** in the RB-TT series:

| Paper | Topic | Status |
|-------|-------|--------|
| **RB-TT** (this repo) | Simply-typed λ-calculus with resource bounds | ✅ Complete |
| **RB-MLTT** | Dependent types, size-indexed bounds | 📝 Draft |
| **RB-MLTT-G** | Groupoid-valued costs | 📅 Planned |
| **RB-HoTT** | Homotopy type theory with resources | 📅 Planned |

---

## 📄 Paper

The mathematical development is in [`RB_TT.pdf`](RB_TT.pdf):

> **Resource-Bounded Type Theory: Compositional Cost Analysis via Graded Modalities**  
> Mirco A. Mannucci and Corey Thuro, 2025

**Key results:**
- Type soundness (preservation + progress)
- Cost soundness (synthesized bound ≥ operational cost)
- Presheaf semantics in $\mathbf{Set}^L$ with internal lattice $\mathbb{L}$
- Initiality of the syntactic model

---

## 🎯 What's in This Repository

### ✅ Implemented

- **Core calculus** (`src/RBTT/Core/`)
  - Resource contexts (`Res.lean`) with lattice operations $\oplus$, $\sqcup$, $\preceq$
  - Types and terms (`STLC.lean`) with de Bruijn indices
  - Typing judgment `Γ ⊢[R;b] t : A` with synthesized bounds
  - Graded modality $\Box_R$ as comonad (`Modality.lean`)

- **Operational semantics** (`src/RBTT/Core/OpCost.lean`)
  - Small-step reduction with cost accumulation
  - Multi-step evaluation

- **Presheaf semantics** (`src/RBTT/Semantics/PresheafSet.lean`)
  - Presheaves over $(L, \preceq)$
  - Shift functor interpretation of $\Box_R$
  - Natural transformations (counit, comultiplication)

- **Examples** (`src/RBTT/Examples/`)
  - Binary search with $O(\log n)$ bound (`BinarySearch.lean`)
  - List operations (`Lists.lean`)
  - Cost integration tests

- **CI infrastructure** (`.github/workflows/`)
  - Budget checking workflow
  - Lean build validation

### 🟡 Work in Progress

- Full proofs of metatheorems (currently `sorry` stubs)
- Comonad laws for presheaf semantics
- Mechanized cost soundness

---

## 🚀 Getting Started

### Prerequisites

- [Lean 4](https://leanprover.github.io/) (v4.8.0 — see `lean-toolchain`)
- [Lake](https://github.com/leanprover/lake) (included with Lean 4)
- Git

**Recommended:** VS Code with the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)

### Build

```bash
git clone https://github.com/CoreyThuro/RB-TT.git
cd RB-TT
lake build
```

### Run the demo

```bash
lake exe rbtt
```

### Run budget checks

```bash
lake exe check-budgets --verbose
```

---

## 📁 Repository Structure

```
RB-TT/
├── RB_TT.pdf                    # Main paper
├── README.md                    # This file
├── LICENSE                      # MIT License
├── lakefile.lean                # Lake build configuration
├── lean-toolchain               # Lean version (4.8.0)
│
├── src/
│   ├── Main.lean                # Entry point for rbtt executable
│   ├── RBTT.lean                # Main library import
│   └── RBTT/
│       ├── Res.lean             # Resource contexts (L, ⊕, ⊔, ⊥)
│       ├── Init.lean            # Basic imports
│       ├── Budget.lean          # Budget management
│       ├── Core/
│       │   ├── STLC.lean        # Types, terms, typing judgment
│       │   ├── OpCost.lean      # Operational semantics + cost
│       │   ├── Modality.lean    # Graded modality □_R
│       │   ├── Recursion.lean   # Recursion patterns
│       │   └── Universe.lean    # Universe hierarchy
│       ├── Semantics/
│       │   └── PresheafSet.lean # Presheaf model in Set^L
│       ├── Examples/
│       │   ├── BinarySearch.lean
│       │   ├── Lists.lean
│       │   └── CostIntegrationTest.lean
│       └── Infra/
│           ├── Cost.lean        # Cost measurement
│           ├── BudgetDB.lean    # Budget database
│           └── BudgetRecords.lean
│
├── scripts/
│   ├── bootstrap_lean.sh
│   └── RBTT/Scripts/
│       └── CheckBudgets.lean    # Budget checking executable
│
├── demo/
│   └── feasible_demo.py         # Python demo
│
├── docs/
│   ├── INTRO.md                 # Introduction
│   └── rbtt-logo.png            # Logo
│
├── archive/                     # Historical drafts and notes
│
└── .github/
    └── workflows/
        └── budget.yml           # CI budget checking
```

---

## 🔧 Using RB-TT as a Dependency

Add to your `lakefile.lean`:

```lean
package myproject

require RBTT from git
  "https://github.com/CoreyThuro/RB-TT.git"
```

Then:

```bash
lake update
lake build
```

Import modules:

```lean
import RBTT.Core           -- Syntax + typing
import RBTT.Core.OpCost    -- Operational semantics
import RBTT.Core.Modality  -- □_R modality
import RBTT.Semantics.PresheafSet  -- Presheaf model
```

---

## 📊 Key Concepts

### The Typing Judgment

$$\Gamma \vdash_{R;\,b} t : A$$

- $\Gamma$: typing context
- $R$: resource budget (element of lattice $L$)
- $b$: synthesized bound ($b \preceq R$)
- $t$: term
- $A$: type

### Cost Composition Rules

| Construct | Bound |
|-----------|-------|
| Variable | $0$ |
| Lambda | $0$ (latent cost in body) |
| Application | $b_f \oplus b_a \oplus \delta_{\mathsf{app}}$ |
| Pair | $b_1 \oplus b_2$ |
| Conditional | $b_c \oplus (b_t \sqcup b_f) \oplus \delta_{\mathsf{if}}$ |
| Box | $b$ (with $b \preceq s$ for $\Box_s$) |

### The Feasibility Modality

$\Box_r A$ represents values of type $A$ computable within budget $r$.

**Comonad structure:**
- Counit: $\Box_r A \to A$ (use the value)
- Comultiplication: $\Box_{r_1 \oplus r_2} A \to \Box_{r_1}(\Box_{r_2} A)$ (split resources)
- Monotonicity: $r \preceq s \Rightarrow \Box_r A \to \Box_s A$ (weaken budget)

### Presheaf Semantics

Types are presheaves over the resource poset:
$$\llbracket A \rrbracket : L^{\mathrm{op}} \to \mathbf{Set}$$

The shift interpretation:
$$(\Box_R A)(S) := A(S \oplus R)$$

---

## 🧪 Examples

### Identity function (cost 0)

```lean
def id_tm : Tm [] (.nat ⇒ .nat) :=
  Tm.lam (Tm.var Var.zero)

example : [] ⊢[R;0] id_tm : (.nat ⇒ .nat) :=
  HasBound.lam HasBound.var
```

### Application (cost 1)

```lean
def app_id_5 : Tm [] .nat :=
  Tm.app id_tm (Tm.natLit 5)

example : [] ⊢[R;1] app_id_5 : .nat :=
  HasBound.app (HasBound.lam HasBound.var) HasBound.natLit
```

### Binary search (cost $O(\log n)$)

See [`src/RBTT/Examples/BinarySearch.lean`](src/RBTT/Examples/BinarySearch.lean) for a complete implementation with fuel-based termination and logarithmic complexity bound.

---

## 📜 License

This project is licensed under the **MIT License**. See [`LICENSE`](LICENSE) for details.

---

## 📚 Citation

```bibtex
@article{mannucci2025rbtt,
  title={Resource-Bounded Type Theory: Compositional Cost Analysis via Graded Modalities},
  author={Mannucci, Mirco A. and Thuro, Corey},
  year={2025},
  note={arXiv preprint}
}
```

---

## 🔗 Related Work

- [Granule](https://granule-project.github.io/) — Graded modal type system
- [RAML](https://www.raml.co/) — Resource-aware ML
- [Quantitative Type Theory](https://bentnib.org/quantitative-type-theory.html) — Atkey's QTT

---

## 🤝 Contributing

Contributions welcome! Areas of interest:

- Completing `sorry` proofs in metatheory
- Additional examples and case studies
- Performance benchmarks
- Documentation improvements

Please open an issue to discuss before submitting large changes.

---

## 📧 Contact

- **Mirco A. Mannucci** — mirco@holomathics.com
- **Corey Thuro** — cthuro1@umbc.edu
