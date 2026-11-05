-- SPDX-FileCopyrightText: 2026 Benjamin Stanley Frohman
-- SPDX-License-Identifier: Apache-2.0
import FTVerified.May.Main
import FTVerified.May.Final
import FTVerified.May.JacobiWitness
import FTVerified.May.FieldMetriplectic
import FTVerified.May.ChevalleyEilenberg
import FTVerified.May.RiccatiComparison
import FTVerified.Sdiff.ObstructionAudit
import FTVerified.May.GlobalRegularity

/-!
# Paper map: "The Frohmanian Symplectic Tether ... and the Frohmanian Curve" (Zenodo 23942466)

Each PDF claim, its status, and the Lean theorems that settle it.
NOT FORMALIZED (no Lean counterpart): s2 Alain's Curve; s4 the Frohmanian Curve J_red(x,y)=0
(the PDF gives no explicit J_red); s5 symplectic/Melnikov/spectral/holographic forms;
the explicit majorant ODE y' = C y^2 sqrt(y^3) + (pi/4) C_abs.
-/

-- p6 C1/C3 tether locality, self-pairing nonpositive
-- STATUS: PROVED
#check @Frohman.Tether.frohmanianTether_self_nonpos
#check @FrohmanianTether.tetherKernel_self_nonpos

-- p6-7 C2 exact degeneracy on kinetic energy H
-- STATUS: PROVED
#check @Frohman.Tether.frohmanianTether_degenerate
#check @FrohmanianTether.tetherKernel_degenerates_on_kinetic_energy

-- p6 C3 negative quadratic feedback / coefficient fixed
-- STATUS: CONDITIONAL (finite-dim, Route-A hypothesis)
#check @Frohman.Tether.frohmanianTether_feedback
#check @Frohman.Tether.feedback_fixes_coefficient
#check @Frohman.Tether.routeA_determines_kappa

-- p6 C4/C5 uniqueness of tether kernel
-- STATUS: CONDITIONAL (minimal/admissible class only)
#check @Frohman.Tether.uniqueness_of_minimal_metric_tether

-- p3/p10 tether supplies damping in the energy budget
-- STATUS: REFUTED (C2 kills B(M,H))
#check @FrohmanianTether.ObstructionAudit.flow_contribution_zero_of_C2
#check @FrohmanianTether.ObstructionAudit.bilin_kernel_of_nonpos_of_self_zero
#check @FrohmanianTether.ObstructionAudit.energy_conservation_not_C2

-- p6 Chevalley-Eilenberg closure d^2 B = 0
-- STATUS: CONDITIONAL (B a coboundary); symmetric tether is not a CE cochain
#check @Frohman.Tether.CE.d2_d1
#check @Frohman.Tether.CE.cocycle_of_coboundary
#check @Frohman.Tether.CE.symPart_not_cochain

-- p8 9-term Jacobi expansion
-- STATUS: PROVED
#check @Frohman.Tether.jacobiator_nine_terms
#check @Frohman.Tether.jacobi_iff_mixed_cancel
#check @Frohman.Tether.FieldJacobi.jacT_eq_mixedSum
#check @Frohman.Tether.FieldJacobi.jacF_eq_zero

-- p3/p8/p11 Jacobi vanishes on reduced (div-free) orbit
-- STATUS: REFUTED (fails for div-free u=(sin y,0,0))
#check @Frohman.Tether.JacobiWitness.tethered_jacobiator_ne_zero
#check @Frohman.Tether.FieldJacobi.shearY_jacobi_fails_transverse
#check @Frohman.Tether.FieldJacobi.divFree_aZ
#check @Frohman.Tether.FieldMetriplectic.dissF_nonpos

-- Jacobi in special cases
-- STATUS: CONDITIONAL (central u; x-only div-free shear class)
#check @Frohman.Tether.jacobiator_eq_zero_of_central
#check @Frohman.Tether.FieldJacobi.shearY_jacobi_holds
#check @FrohmanianTether.tethered_jacobi_identity

-- p7-8 T^3 shear shows reduced orbit necessary
-- STATUS: PARTLY REFUTED (non-div-free failure true; div-free sin y also fails)
#check @Frohman.Tether.FieldJacobi.shearX_jacobi_fails
#check @Frohman.Tether.FieldJacobi.not_divFree_uX
#check @Frohman.Tether.Shear.shear_divFree
#check @Frohman.Tether.Shear.shearBad_not_divFree

-- p9 independent majorant, quartic absorption ceiling
-- STATUS: CONDITIONAL (ODE inequality assumed)
#check @Frohman.Tether.comparison_bound
#check @Frohman.Tether.layer2_bound
#check @Frohman.Tether.Riccati.tethered_ceiling
#check @Frohman.Tether.Riccati.riccati_blowup

-- p9-10 negative feedback at maxima
-- STATUS: CONDITIONAL (pointwise max-principle lemmas)
#check @Frohman.Tether.viscous_nonpos_at_max
#check @Frohman.Tether.periodic_exists_max

-- p1/p3/s7 Clay-standard global regularity
-- STATUS: CONDITIONAL only (open hypotheses); no Clay claim
#check @Frohman.Tether.frohmanian_symplectic_tether_theorem
#check @Frohman.Tether.frohmanian_symplectic_tether_theorem_global

