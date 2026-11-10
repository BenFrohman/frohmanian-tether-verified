# Jacobi companion papers I and II (version 1.1)

Author: Benjamin Stanley Frohman (metadata form: Frohman, Benjamin Stanley)
Affiliation: Independent Researcher, Texas, United States
ORCID 0009-0006-7068-3718 · frohmanbenjamin@gmail.com · Apache-2.0 · preprint, not peer reviewed

- `paper-I-restricted.tex` / `.pdf`: restricted Jacobi identity on the divergence-free
  e_x-directed shear class, for every axis with `pr u u ≠ 0`.
- `paper-II-counterexample.tex` / `.pdf`: antisymmetry and cyclic Jacobi fail for the specified
  finite-Fourier operation (and for the R³ cross-product witness).

Both papers are about the operation `brT κ w u` in `FTVerified/May/FieldJacobi.lean` (frozen
axis, free complex `κ, w`, complex-bilinear pairing, Lean division). They are not about the
geometric bracket, a Poisson bracket, Navier–Stokes, or any Clay problem.

## Source, versions, rebuild, CI

- Lean source: `FTVerified/May/FieldJacobi.lean`, `FTVerified/May/JacobiWitness.lean` (unchanged
  since `26f16da`), `FTVerified/Companion/JacobiCompanion.lean` (new). Code commit
  `cf04afd5cd9b314703a5c8b196d83ec6b7979e6d` (PR #2).
- Lean `leanprover/lean4:v4.30.0-rc1`; Mathlib `v4.30.0-rc1` = `0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`.
- Rebuild: `lake exe cache get && lake build && python3 scripts/check_jacobi_axioms.py`
- CI: https://github.com/BenFrohman/frohmanian-tether-verified/actions/runs/42923330722 (pass:
  full library build, comment-aware sorry/admit/native_decide/axiom scan over 31 modules,
  `PASS: 49 declarations, standard axioms only`).

## Lean hypotheses versus the papers' assumptions

| Paper statement | Lean declaration | Lean hypotheses | Paper assumption | Match |
|---|---|---|---|---|
| I, Lemma (Jacobiator reduction) | `FieldJacobi.jacT_eq_mixedSum` | `pr u u ≠ 0` | `⟨u,u⟩ ≠ 0` | exact |
| I, Lemma (brackets in the class vanish) | `FieldJacobi.br_eq_zero_of_xOnly_divFree` | `XOnly`, `DivergenceFree` for `a`, `b` | both e_x-directed, divergence-free | exact |
| I, Lemma (mixed sum vanishes) | `FieldJacobi.mixedSumF_eq_zero_of_shear` | `XOnly`, `DivergenceFree` for `u, a, b, c` | same | exact |
| I, Theorem (u = u_Y) | `FieldJacobi.shearY_jacobi_holds` | `XOnly`, `DivergenceFree` for `a, b, c` | same | exact |
| I, Theorem (general axis) | `JacobiCompanion.shear_jacobi_holds_of_pr_ne_zero` | `XOnly u`, `DivergenceFree u`, `pr u u ≠ 0`, class hypotheses on `a, b, c` | same | exact |
| I, Prop. (non-vacuity) | `JacobiCompanion.paperI_nonvacuous`, `brT_uY_eX_eX_ne_zero` | `κ * w ≠ 0` for the nonzero claim | same | exact |
| I, Prop. (isotropic guard) | `JacobiCompanion.shear_jacobi_fails_isotropic` | `κ * w ≠ 0` | same; relies on Lean's `x / 0 = 0` (stated in the paper) | exact |
| II, Theorem (coefficient) | `FieldJacobi.shearY_transverse_coeff` | none | none | exact |
| II, Theorem (Jacobi fails) | `FieldJacobi.shearY_jacobi_fails_transverse` | `κ * w ≠ 0` | `κw ≠ 0` (divergence-freeness is a separate proved fact, not a hypothesis) | exact |
| II, Remark (antisymmetry fails) | `JacobiCompanion.brT_uY_aZ_aZ`, `brT_not_antisymm` | `κ * w ≠ 0` for the second | same | exact |
| II, Theorem (R³ witness) | `JacobiWitness.mixed_sum_eq`, `tethered_jacobiator_ne_zero` | real `κ w`, `κ * w ≠ 0` | same | exact |
| II, non-vacuity | `JacobiCompanion.paperII_nonvacuous` | none (κ = w = 1) | — | exact |

No hypothesis restates a conclusion, and each hypothesis set is shown to be inhabited. No
mismatch was found. Recorded limitations (in the papers): both counterexample witnesses repeat
arguments; nothing transports to the state-dependent geometric bracket; a kernel check does not
show that the definitions model any geometry.
