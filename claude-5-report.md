# Status Handoff for Codex GPT-5

Repository: `/mnt/c/Users/mirco/Desktop/RB-TT/RB-TT-main` (git initialized locally)
Snapshot tag: `snapshot-subst-20260215` (current baseline)

## Mission Focus (next 1–2 weeks)
1. **Phase-2 substitution** (absolute priority)
   - File: `src/RBTT/Core/SubstitutionLemmas.lean`
   - CtxWF locked in (head/tail/extend proved), `WfHasType` inductive used for typing proofs.
   - Remaining work:
     * Finalize `subst_subst` with the minimal freshness hypothesis (`noVar`/`fv_lt`).
     * Finish `typing_substitution_simple_core`/`typing_substitution_simple` using `WfHasType`.
     * Prove `typing_weakening` in the same framework.
   - Status: 4 `sorry`s still present (see lines ~875, 971, 999, 1022). Composition lemmas `shift_shift_le/gt_safe` and `shift_subst` are proved; `subst_shift` now follows from `shift_subst`.

2. **OpCost cleanup** (after Phase-2 is green)
   - File: `src/RBTT/Core/OpCost.lean`
   - Currently contains 18 axioms (`subst`, progress/preservation, multistep congruence, lambda body cost, cost substitution, etc.) and multiple `sorry`s (examples + the final `cost_soundness_goal`).
   - Do **not** tackle until substitution lemmas are solved; OpCost needs the real substitution framework for preservation.

3. **Presheaf semantics variance (CP-1)**
   - File: `src/RBTT/Semantics/PresheafSet.lean`
   - Still written as contravariant presheaves with `sorry`s. Decision is to switch to **covariant** functors, but this is deferred until core proofs are stable.

## Ground Truth Reminders
- `docs/MECHANIZATION_STATUS.md` explicitly states that no metatheorems (substitution, progress, preservation, cost soundness) are proved yet. Keep it updated as proofs land.
- `docs/PROOF_DEBT.md` tracks full sorry/axiom inventory; do not remove entries unless proofs are finished.
- Recovery instructions live in `docs/RECOVERY.md` (how to diff/restore from the snapshot tag).

## Build/Testing Status
- `lake build` has **not been run in this session** (CLI environment currently lacks `lake`). Run it once Lean toolchain is available to ensure new proofs compile.

## Recommended Next Steps for GPT-5
1. Implement `subst_subst` driven by the needs of `typing_substitution_simple_core` (add the weakest freshness premise that makes the binder cases go through).
2. Complete `typing_substitution_simple_core`/`typing_substitution_simple` under `WfHasType`, then prove `typing_weakening`.
3. Once substitution is solid and CI/lake build succeeds, start methodically removing OpCost axioms (begin with `subst` axiom by importing the real lemma, then tackle progress/preservation).
4. Leave `PresheafSet.lean` variance refactor for after CP-4 progress, unless Corey explicitly reprioritizes.

## Known Blockers / Risks
- Without `typing_substitution`, OpCost preservation cannot be proved. Do not attempt cost soundness until substitution + weakening are finished.
- Semantics still contradict the covariant SetL decision; document this in PRs to avoid regressions.
- No automated tests or CI runs yet; once `lake` is available, wire CI to fail on `sorry`/`axiom` reintroduction per action list CP‑0.

Keep handoffs honest: every change affecting mechanization status should update `docs/MECHANIZATION_STATUS.md` and `docs/PROOF_DEBT.md`.
