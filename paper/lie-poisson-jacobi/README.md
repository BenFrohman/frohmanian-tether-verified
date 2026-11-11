# Lie–Poisson Jacobi identity on the regular dual of sdiff(T³), every cancellation displayed (v1.1)

Author: Benjamin Stanley Frohman (Frohman, Benjamin Stanley) · Independent Researcher, Texas,
United States · ORCID 0009-0006-7068-3718 · frohmanbenjamin@gmail.com

An expository re-derivation of a classical theorem (Arnold 1966; Marsden–Weinstein 1983). It
claims no new result and makes no PDE or Clay claim.

## What Lean checks, and what it does not

| Note step | Lean | Status |
|---|---|---|
| Steps 4–5: the six Hessian terms cancel by symmetry, and the remainder vanishes by the Jacobi identity of the Lie algebra | `LiePoissonCore.six_terms_cancel`, `LiePoissonCore.lie_poisson_jacobi_core` in `FTVerified/Companion/LiePoissonJacobiCore.lean` | kernel-checked; axioms `[propext, Quot.sound]` |
| Lemma (symmetry of the second derivative), the product lemma, the formula for δ{G,H}/δm, the torus, Leray projection and admissible class | none | pen and paper only (written out in the note), plus symbolic/numeric checks in `scripts/` |

Hypothesis mapping for the Lean core: `m : L →ₗ[R] R` is the pairing with the state, linear (as in
the note). `QF QG QH` symmetric is Lemma (symmetry of the second derivative). `[LieRing L]
[LieAlgebra R L]` is the vector-field Lie algebra, whose Jacobi identity the note uses as a
classical fact. These are satisfiable (`Q = 0`), and the result is false without symmetry. No
mismatch was found.

Rebuild (repo root): `lake exe cache get && lake build && python3 scripts/check_jacobi_axioms.py`
(CI run https://github.com/BenFrohman/frohmanian-tether-verified/actions/runs/42923330722, pass).
PDF: `tectonic lie_poisson_jacobi.tex`. The Python checks in `scripts/` are evidence, not proofs.
They were not re-run for v1.1.
