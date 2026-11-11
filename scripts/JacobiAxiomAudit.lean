-- SPDX-FileCopyrightText: 2026 Benjamin Stanley Frohman
-- SPDX-License-Identifier: Apache-2.0
-- Author: Benjamin Stanley Frohman
-- Axiom audit for the Jacobi companion papers I, II and the Lie–Poisson core.
-- Checked by scripts/check_jacobi_axioms.py: only propext, Classical.choice, Quot.sound.
import FTVerified.May.FieldJacobi
import FTVerified.May.JacobiWitness
import FTVerified.Companion.JacobiCompanion
import FTVerified.Companion.LiePoissonJacobiCore

#print axioms Frohman.Tether.FieldJacobi.jacF_eq_zero
#print axioms Frohman.Tether.FieldJacobi.br_self
#print axioms Frohman.Tether.FieldJacobi.jacT_eq_mixedSum
#print axioms Frohman.Tether.FieldJacobi.pr_uY_uY
#print axioms Frohman.Tether.FieldJacobi.br_eq_zero_of_xOnly_divFree
#print axioms Frohman.Tether.FieldJacobi.mixedF_eq_zero_of_shear
#print axioms Frohman.Tether.FieldJacobi.mixedSumF_eq_zero_of_shear
#print axioms Frohman.Tether.FieldJacobi.shearY_mixed_cancel
#print axioms Frohman.Tether.FieldJacobi.shearY_jacobi_holds
#print axioms Frohman.Tether.FieldJacobi.mixedSumF_diag
#print axioms Frohman.Tether.FieldJacobi.pr_uY_aZ
#print axioms Frohman.Tether.FieldJacobi.pr_aZ_aZ
#print axioms Frohman.Tether.FieldJacobi.br_uY_aZ_coeff
#print axioms Frohman.Tether.FieldJacobi.divFree_aZ
#print axioms Frohman.Tether.FieldJacobi.divFree_uY
#print axioms Frohman.Tether.FieldJacobi.xOnly_uY
#print axioms Frohman.Tether.FieldJacobi.xOnly_eX
#print axioms Frohman.Tether.FieldJacobi.divFree_eX
#print axioms Frohman.Tether.FieldJacobi.shearY_transverse_coeff
#print axioms Frohman.Tether.FieldJacobi.shearY_transverse_ne_zero
#print axioms Frohman.Tether.FieldJacobi.shearY_jacobi_fails_transverse
#print axioms Frohman.Tether.JacobiWitness.crossBr_isClassical
#print axioms Frohman.Tether.JacobiWitness.mixed_sum_eq
#print axioms Frohman.Tether.JacobiWitness.mixed_sum_ne_zero
#print axioms Frohman.Tether.JacobiWitness.tethered_jacobiator_ne_zero
#print axioms Frohman.Tether.JacobiCompanion.shear_jacobi_holds_of_pr_ne_zero
#print axioms Frohman.Tether.JacobiCompanion.shearY_jacobi_holds_eq_special_case
#print axioms Frohman.Tether.JacobiCompanion.pr_uY_eX
#print axioms Frohman.Tether.JacobiCompanion.uY_ne_zero
#print axioms Frohman.Tether.JacobiCompanion.brT_uY_eX_eX
#print axioms Frohman.Tether.JacobiCompanion.brT_uY_eX_eX_ne_zero
#print axioms Frohman.Tether.JacobiCompanion.paperI_nonvacuous
#print axioms Frohman.Tether.JacobiCompanion.xOnly_uIso
#print axioms Frohman.Tether.JacobiCompanion.divFree_uIso
#print axioms Frohman.Tether.JacobiCompanion.xOnly_cY
#print axioms Frohman.Tether.JacobiCompanion.divFree_cY
#print axioms Frohman.Tether.JacobiCompanion.uIso_ne_zero
#print axioms Frohman.Tether.JacobiCompanion.pr_uIso_uIso
#print axioms Frohman.Tether.JacobiCompanion.pr_uIso_cY
#print axioms Frohman.Tether.JacobiCompanion.pr_cY_cY
#print axioms Frohman.Tether.JacobiCompanion.pr_smul_left
#print axioms Frohman.Tether.JacobiCompanion.piF_uIso
#print axioms Frohman.Tether.JacobiCompanion.jacT_uIso_cY
#print axioms Frohman.Tether.JacobiCompanion.shear_jacobi_fails_isotropic
#print axioms Frohman.Tether.JacobiCompanion.brT_uY_aZ_aZ
#print axioms Frohman.Tether.JacobiCompanion.brT_not_antisymm
#print axioms Frohman.Tether.JacobiCompanion.paperII_nonvacuous
#print axioms LiePoissonCore.six_terms_cancel
#print axioms LiePoissonCore.lie_poisson_jacobi_core
