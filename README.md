# RB-TT --- Resource-Bounded Type Theory

![RB-TT logo](docs/rbtt-logo.png)

Resource-Bounded Type Theory (RB-TT) is a typed lambda-calculus for **compositional cost analysis**.

Terms carry synthesized cost bounds drawn from an abstract **resource lattice**
\((L, \preceq, \oplus, \bot)\), and a graded **feasibility modality** \(\Box_r\) tracks which
programs are admissible under a given resource budget.

Two companion papers describe the mathematical development:
- **RB-TT** (STLC fragment): syntax, cost rules, machine semantics, cost soundness.
- **RB-MLTT**: extension to Martin-Lof dependent types, presheaf semantics, universe structure.

This repository contains the **Lean 4 mechanization** of the STLC core and scaffolds
for the dependent/semantic extensions.

> **Scope warning.** This repo is **not** a full mechanization of RB-MLTT.
> It contains a proved STLC machine core (9/10 cost soundness cases; App
> higher-order case has one `sorry`), extrinsic MLTT typing rules (scaffold),
> presheaf semantics (scaffold with axioms), and engineering examples.
> No MLTT-level metatheory (preservation, cost soundness for dependent fragment)
> is mechanized here — those exist only as paper-level proofs.

---

## Proof status

| Component | Lean status | File(s) | Detail |
| --- | --- | --- | --- |
| Resource algebra | **Lean proved** | `Res.lean` | Lattice, ordering, composition |
| Delta constants | **Lean proved** | `Core/CostModel.lean` | Single source of truth |
| STLC syntax + cost typing | **Lean proved** | `Core/STLC.lean` | `HasCost`, `HasBound`, `costOf` |
| Closure machine semantics | **Lean proved** | `Core/STLCMachine.lean` | `Val`, `Env`, `Eval` |
| Cost soundness: non-App cases | **Lean proved** | `Meta/STLCMachineSoundness.lean` | 9/10 cases |
| Cost soundness: App (direct-lambda) | **Lean proved** (no separate closed theorem) | `Meta/STLCMachineSoundness.lean` | Informally documented |
| Cost soundness: App (general higher-order) | **Open** | `Meta/STLCMachineSoundness.lean` | 1 sorry — needs `kbody <= kf` |
| Extrinsic MLTT typing rules | Scaffold / axiomatized | `Core/ExtrinsicMLTT.lean` | Syntax + rules, no metatheory |
| Presheaf semantics | Scaffold / axiomatized | `Semantics/PresheafSet.lean` | 4 sorry, 5 axioms |
| Resource-indexed universes | Scaffold / axiomatized | `Core/Universe.lean` | 3 axioms |
| Feasibility modality | Scaffold / axiomatized | `Core/Modality.lean` | 1 axiom (cost-aware box intro) |
| Budget infrastructure | Experimental | `Budget.lean`, `Infra/` | CI budget tracking (1 sorry in Budget.lean) |
| Examples | Experimental | `Examples/` | Some contain sorry |
| Experimental recursion | Experimental | `Experimental/RecursionFuel.lean` | 3 sorry, 1 axiom |

### The higher-order cost gap

The single `sorry` in the mechanized core is the **App cost bound**. The App
rule uses the "double b_f" pattern: `kf + ka + kf + delta_app`. The second `kf`
is intended to upper-bound the closure body cost `kbody`.

- **When `f = Tm.lam body`**: `kf = kbody + delta_lam`, so `kbody < kf`. Sound.
- **When `f = Tm.var x`**: `kf = delta_var = 1`, but `kbody` can be arbitrary. Gap.

**Resolution**: cost-annotated arrow types `A -{k}-> B`, where the body cost
bound `k` is carried in the type. This is standard (Crary--Weirich 2000,
RAML/Hoffmann et al. 2012) and is adopted in the companion RB-MLTT paper for
annotated dependent function types. The STLC paper diagnoses the obstruction;
the RB-MLTT paper proposes the annotated-arrow resolution at the paper level (the Lean repo does not yet mechanize that resolution).

### What the STLC mechanization proves

The STLC core is **not** the final architecture. It is:
- A minimal compositional resource calculus
- The place where the closure-cost problem becomes visible
- A useful proved fragment (all first-order / direct-lambda programs)
- Not the final higher-order theory

This is a deliberately staged research program: STLC exposes the latent-cost
obstruction; the MLTT paper proposes annotated dependent arrows as the resolution (paper-level; not yet mechanized in this repo).

---

## Repository structure

Every Lean file carries a `-- STATUS:` header on its first line.

### Layer 1: Mechanized core (proved)

| File | Content |
| --- | --- |
| `src/RBTT/Res.lean` | Resource contexts and lattice |
| `src/RBTT/Core/CostModel.lean` | Delta overhead constants |
| `src/RBTT/Core/STLC.lean` | Types, terms, `HasCost`, `costOf` |
| `src/RBTT/Core/STLCMachine.lean` | `Val`, `Env`, `Eval` (closure machine) |
| `src/RBTT/Meta/STLCMachineSoundness.lean` | Cost soundness (9/10 cases; App open) |

### Layer 2: Forward theory scaffolds

| File | Content | Status |
| --- | --- | --- |
| `src/RBTT/Core/ExtrinsicMLTT.lean` | Pi, Sigma, Nat, Vec, Bool, Id | Typing rules only |
| `src/RBTT/Semantics/PresheafSet.lean` | Presheaves over `(ResCtx, <=)` | Axioms + sorry |
| `src/RBTT/Core/Universe.lean` | Resource-indexed universes | Axioms |
| `src/RBTT/Core/Modality.lean` | Feasibility modality | 1 axiom |
| `src/RBTT/Experimental/RecursionFuel.lean` | Fuel-based recursion | Experimental |

### Infrastructure and examples

| File | Content |
| --- | --- |
| `src/RBTT/Budget.lean` | Budget allocation strategies |
| `src/RBTT/Infra/` | Proof cost measurement, budget DB, baselines |
| `src/RBTT/Examples/` | Binary search, lists, cost integration, dependent types |
| `src/Main.lean` | Demo executable |

### Paper-to-code map

| Paper section | Lean file(s) | Mechanization level |
| --- | --- | --- |
| Resource lattice + contexts | `src/RBTT/Res.lean` | **proved** |
| Syntax + typing | `src/RBTT/Core/STLC.lean` | **proved** |
| Delta overhead constants | `src/RBTT/Core/CostModel.lean` | **proved** |
| Machine semantics (closures) | `src/RBTT/Core/STLCMachine.lean` | **proved** |
| Cost soundness (Thm 6.X) | `src/RBTT/Meta/STLCMachineSoundness.lean` | **9/10 cases; App has sorry** |
| MLTT typing rules | `src/RBTT/Core/ExtrinsicMLTT.lean` | scaffold (syntax + rules only) |
| Feasibility modality | `src/RBTT/Core/Modality.lean` | scaffold (1 axiom) |
| Presheaf model | `src/RBTT/Semantics/PresheafSet.lean` | scaffold (4 sorry, 5 axioms) |

---

## Getting started

### Prerequisites

- [Lean 4](https://leanprover.github.io/) (version in `lean-toolchain`: 4.8.0)
- Lake (included with Lean 4)

### Build

```bash
git clone https://github.com/CoreyThuro/RB-TT.git
cd RB-TT
lake build
```

### Run demo

```bash
lake exe rbtt
```

---

## License

MIT License. See `LICENSE`.

## Citing

> Mirco A. Mannucci, Corey Thuro. *Resource-Bounded Type Theory:
> Compositional Cost Analysis via Graded Modalities*, 2025.
