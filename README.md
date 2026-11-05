# Frohmanian Tether: verified architecture and obstructions

Lean 4 (v4.30.0-rc1, Mathlib v4.30.0-rc1) formalization that maps the claims of the technical
compilation *The Frohmanian Symplectic Tether: Architecture, Reduced Jacobi Identity, and the
Frohmanian Curve* (Zenodo record 23942466) to machine-checked theorems. Each claim ends up as
proved, conditional, refuted or not formalized. **This repository makes no Clay
Millennium claim.**

## Build

    lake build                                # 2684 jobs, no `sorry`
    lake env lean scripts/AxiomAudit.lean     # 37 key theorems; only propext / Classical.choice / Quot.sound

## Status table (see `FTVerified/Paper.lean`)

| PDF claim (page) | Status | Lean |
|---|---|---|
| C1/C3 locality, self-pairing ≤ 0 (p6) | PROVED | `frohmanianTether_self_nonpos`, `tetherKernel_self_nonpos` |
| C2 degeneracy on kinetic energy (p6–7) | PROVED | `frohmanianTether_degenerate`, `tetherKernel_degenerates_on_kinetic_energy` |
| C3 negative feedback, coefficient fixed (p6) | CONDITIONAL (finite-dim, Route A) | `frohmanianTether_feedback`, `feedback_fixes_coefficient`, `routeA_determines_kappa` |
| C4/C5 uniqueness (p6) | CONDITIONAL (admissible class) | `uniqueness_of_minimal_metric_tether` |
| Tether damps the energy budget (p3, p10) | REFUTED | `ObstructionAudit.flow_contribution_zero_of_C2`, `bilin_kernel_of_nonpos_of_self_zero`, `energy_conservation_not_C2` |
| Chevalley–Eilenberg d²B = 0 (p6) | CONDITIONAL (coboundary); symmetric part not a cochain | `CE.d2_d1`, `CE.cocycle_of_coboundary`, `CE.symPart_not_cochain` |
| 9-term Jacobi expansion (p8) | PROVED | `jacobiator_nine_terms`, `jacobi_iff_mixed_cancel`, `FieldJacobi.jacT_eq_mixedSum`, `FieldJacobi.jacF_eq_zero` |
| Jacobi vanishes on the reduced orbit (p3, p8, p11) | REFUTED | `JacobiWitness.tethered_jacobiator_ne_zero`, `FieldJacobi.shearY_jacobi_fails_transverse` (+ `divFree_aZ`); bracket is metriplectic, `FieldMetriplectic.dissF_nonpos` |
| Jacobi in special cases | CONDITIONAL | `jacobiator_eq_zero_of_central`, `FieldJacobi.shearY_jacobi_holds`, `tethered_jacobi_identity` (vanishing assumed) |
| Shear counterexample ⇒ reduced orbit necessary (p7–8) | PARTLY REFUTED | `shearX_jacobi_fails`, `not_divFree_uX`, `Shear.shear_divFree` |
| Independent majorant, quartic absorption (p9) | CONDITIONAL (ODE inequality assumed) | `comparison_bound`, `layer2_bound`, `Riccati.tethered_ceiling`, `Riccati.riccati_blowup` |
| Negative feedback at maxima (p9–10) | CONDITIONAL (pointwise) | `viscous_nonpos_at_max`, `periodic_exists_max` |
| Clay-standard global regularity (p1, p3, §7) | CONDITIONAL only | `frohmanian_symplectic_tether_theorem(_global)` (open hypotheses) |
| Alain's Curve (§2); Frohmanian Curve J_red = 0 (§4); §5 representations; explicit majorant ODE | NOT FORMALIZED | none; the PDF gives no explicit J_red |

## Provenance

Files are copied unchanged except for `import` paths:

* `FTVerified/May/*` from `BenFrohman/frohmanian-symplectic-tether-may-form` @ `878b311`
  (`TetherMayForm/*`); includes the transitive dependencies of `Final`.
* `FTVerified/Sdiff/*` from `BenFrohman/frohmanian-tether-geometric` (formerly sdiff), branch
  `gateaux-pairing` @ `9e40ae7`: `ObstructionAudit` and its imports `SymplecticTether`,
  `ArnoldGeometric`, `NS_Equations`, `ForMathlib/Projection`.
  Note: `SymplecticTether.reduced_pairing_of_unmodified_and_tether` carries a `hweight`
  hypothesis that is unsatisfiable as discussed in the source repo's `HWEIGHT_OBSTRUCTION.md`.
* New: `FTVerified/Paper.lean`, `scripts/AxiomAudit.lean`.

Author: Benjamin Stanley Frohman (ORCID 0009-0006-7068-3718). License: Apache-2.0.

## Paper

`paper/frohmanian-tether-verified.pdf` (source `paper/frohmanian-tether-verified.tex`) reports only the
proved/conditional results above and states the refuted and unformalized claims as such.

## Copyright and license

Copyright 2026 Benjamin Stanley Frohman. Licensed under Apache-2.0; see `LICENSE`, `NOTICE`, `AUTHORS`, `CITATION.cff`.
