-- SPDX-FileCopyrightText: 2026 Benjamin Stanley Frohman
-- SPDX-License-Identifier: Apache-2.0
/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman

# Jacobi companion papers I and II: generalization, non-vacuity, exact limits

Everything here is about the finite-Fourier operation `brT κ w u` of
`FTVerified/May/FieldJacobi.lean` (complex-bilinear pairing `pr`, Lean division,
free complex parameters `κ, w`). Nothing here is about the geometric
state-dependent bracket, a reduced coadjoint orbit, or the Navier–Stokes equations.

* `shear_jacobi_holds_of_pr_ne_zero`: the restricted Jacobi identity for EVERY
  `e_x`-directed divergence-free axis `u` with `pr u u ≠ 0` (paper I, generalizing
  `shearY_jacobi_holds`, which is the case `u = uY`).
* Non-vacuity for paper I: the hypothesis class is inhabited, and inside it the
  tether term (hence the whole bracket) is nonzero: `brT κ w uY eX eX = -(κw) • uY`.
  So the identity is not the trivial statement "every bracket in the class is 0".
* `shear_jacobi_fails_isotropic`: the guard `pr u u ≠ 0` cannot be dropped. For the
  `e_x`-directed divergence-free complex axis `uIso = e^{iy} e_x` one has
  `pr uIso uIso = 0`; with Lean's convention `x / 0 = 0` the projection is the
  identity and the Jacobiator on the real shear field `cY = (2 cos y, 0, 0)` equals
  `6 (κw)^2 • uIso ≠ 0`. This is a statement about the operation exactly as defined
  (including the division convention), not about any geometric bracket.
* Paper II: antisymmetry fails as a stated theorem (`brT_uY_aZ_aZ`,
  `brT_not_antisymm`), and the counterexample hypotheses are inhabited (`κ = w = 1`).
-/
import FTVerified.May.FieldJacobi
import FTVerified.May.JacobiWitness

set_option linter.unusedSimpArgs false

namespace Frohman.Tether.JacobiCompanion
open Frohman.Tether.FieldJacobi Frohman.Tether.BiotSavart
open scoped Matrix

noncomputable section

/-! ## Paper I: restricted Jacobi for every non-isotropic shear axis -/

/-- Restricted Jacobi identity for every `e_x`-directed divergence-free axis `u` with
`pr u u ≠ 0`, on the `e_x`-directed divergence-free class. -/
theorem shear_jacobi_holds_of_pr_ne_zero {κ w : ℂ} {u a b c : Fld}
    (hu : XOnly u) (hdu : DivergenceFree u) (huu : pr u u ≠ 0)
    (ha : XOnly a) (hda : DivergenceFree a) (hb : XOnly b) (hdb : DivergenceFree b)
    (hc : XOnly c) (hdc : DivergenceFree c) :
    jacT κ w u a b c = 0 := by
  rw [jacT_eq_mixedSum huu]
  exact mixedSumF_eq_zero_of_shear κ w hu hdu ha hda hb hdb hc hdc

/-- The earlier theorem is the special case `u = uY`. -/
theorem shearY_jacobi_holds_eq_special_case {κ w : ℂ} {a b c : Fld}
    (ha : XOnly a) (hda : DivergenceFree a) (hb : XOnly b) (hdb : DivergenceFree b)
    (hc : XOnly c) (hdc : DivergenceFree c) :
    jacT κ w uY a b c = 0 :=
  shear_jacobi_holds_of_pr_ne_zero xOnly_uY divFree_uY (by rw [pr_uY_uY]; norm_num)
    ha hda hb hdb hc hdc

/-! ## Paper I: non-vacuity -/

theorem pr_uY_eX : pr uY eX = 0 := by
  simp [uY, eX, pr_add_left, pr_single, Finsupp.single_apply, dotProduct,
    Fin.sum_univ_three, ky, funext_iff, Fin.forall_fin_succ]

theorem uY_ne_zero : uY ≠ 0 := by
  intro h
  have := congrArg (fun f : Fld => f ky 0) h
  simp [uY, Finsupp.single_apply, ne_ky] at this

/-- Inside the class the Lie part vanishes but the tether part does not. -/
theorem brT_uY_eX_eX (κ w : ℂ) : brT κ w uY eX eX = (-(κ * w)) • uY := by
  simp only [brT, br_self, zero_add, tetF, piF_of_pr_zero pr_uY_eX, pr_eX_eX, mul_one]

theorem brT_uY_eX_eX_ne_zero {κ w : ℂ} (h : κ * w ≠ 0) : brT κ w uY eX eX ≠ 0 := by
  rw [brT_uY_eX_eX]
  exact smul_ne_zero (neg_ne_zero.mpr h) uY_ne_zero

/-- All hypotheses of `shear_jacobi_holds_of_pr_ne_zero` are satisfied by
`u = uY`, `a = b = c = eX`, and there the bracket is nonzero when `κ w ≠ 0`. -/
theorem paperI_nonvacuous :
    XOnly uY ∧ DivergenceFree uY ∧ pr uY uY ≠ 0 ∧ XOnly eX ∧ DivergenceFree eX ∧
      brT 1 1 uY eX eX ≠ 0 ∧ jacT 1 1 uY eX eX eX = 0 :=
  ⟨xOnly_uY, divFree_uY, by rw [pr_uY_uY]; norm_num, xOnly_eX, divFree_eX,
    brT_uY_eX_eX_ne_zero (by norm_num),
    shear_jacobi_holds_of_pr_ne_zero xOnly_uY divFree_uY (by rw [pr_uY_uY]; norm_num)
      xOnly_eX divFree_eX xOnly_eX divFree_eX xOnly_eX divFree_eX⟩

/-! ## Paper I: the guard `pr u u ≠ 0` is needed -/

/-- The complex single mode `e^{iy} e_x`: `e_x`-directed, divergence-free, isotropic. -/
def uIso : Fld := Finsupp.single ky ![1, 0, 0]

/-- The real shear field `(2 cos y, 0, 0) = e^{iy} e_x + e^{-iy} e_x`. -/
def cY : Fld := Finsupp.single ky ![1, 0, 0] + Finsupp.single (-ky) ![1, 0, 0]

theorem xOnly_uIso : XOnly uIso := by
  intro k; simp [uIso, Finsupp.single_apply]; split_ifs <;> simp

theorem divFree_uIso : DivergenceFree uIso := by
  intro k; simp [uIso, Finsupp.single_apply, kC, dotProduct, Fin.sum_univ_three, ky]
  split_ifs with h <;> subst_vars <;> simp

theorem xOnly_cY : XOnly cY := by
  intro k; simp [cY, Finsupp.single_apply]; split_ifs <;> simp

theorem divFree_cY : DivergenceFree cY := by
  intro k; simp [cY, Finsupp.single_apply, kC, dotProduct, Fin.sum_univ_three, ky]
  split_ifs with h1 h2 <;> subst_vars <;> simp

theorem uIso_ne_zero : uIso ≠ 0 := by
  intro h
  have := congrArg (fun f : Fld => f ky 0) h
  simp [uIso] at this

theorem pr_uIso_uIso : pr uIso uIso = 0 := by
  simp [uIso, pr_single, Finsupp.single_apply, ne_ky.symm]

theorem pr_uIso_cY : pr uIso cY = 1 := by
  simp [uIso, cY, pr_single, Finsupp.single_apply, dotProduct, Fin.sum_univ_three,
    ne_ky.symm, ne_ky]

theorem pr_cY_cY : pr cY cY = 2 := by
  simp [cY, pr_add_left, pr_add_right, pr_single, Finsupp.single_apply, dotProduct,
    Fin.sum_univ_three, ne_ky.symm, ne_ky]
  norm_num

theorem pr_smul_left (a b : Fld) (r : ℂ) : pr (r • a) b = r * pr a b := by
  unfold pr
  rw [Finsupp.sum_smul_index' (fun p => by simp), Finsupp.mul_sum]
  simp [smul_dotProduct]

theorem piF_uIso (x : Fld) : piF uIso x = x := by
  simp [piF, pr_uIso_uIso]

/-- For the isotropic axis, the Jacobiator on the real shear field is nonzero. -/
theorem jacT_uIso_cY (κ w : ℂ) :
    jacT κ w uIso cY cY cY = (6 * (κ * w) ^ 2) • uIso := by
  have hb : br cY cY = 0 := br_self cY
  have h1 : brT κ w uIso cY cY = (-(κ * w) * 2) • uIso := by
    simp only [brT, hb, zero_add, tetF, piF_uIso, pr_cY_cY]
  have h2 : br ((-(κ * w) * 2) • uIso) cY = 0 :=
    br_eq_zero_of_xOnly_divFree (xOnly_smul xOnly_uIso _) (divFree_smul divFree_uIso _)
      xOnly_cY divFree_cY
  have h3 : brT κ w uIso ((-(κ * w) * 2) • uIso) cY = (6 * (κ * w) ^ 2 / 3) • uIso := by
    simp only [brT, h2, zero_add, tetF, piF_uIso, pr_smul_left, pr_uIso_cY]
    congr 1; ring
  simp only [jacT, h1, h3, ← add_smul]
  congr 1; ring

theorem shear_jacobi_fails_isotropic {κ w : ℂ} (h : κ * w ≠ 0) :
    XOnly uIso ∧ DivergenceFree uIso ∧ pr uIso uIso = 0 ∧ XOnly cY ∧ DivergenceFree cY ∧
      jacT κ w uIso cY cY cY ≠ 0 := by
  refine ⟨xOnly_uIso, divFree_uIso, pr_uIso_uIso, xOnly_cY, divFree_cY, ?_⟩
  rw [jacT_uIso_cY]
  exact smul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 h)) uIso_ne_zero

/-! ## Paper II: antisymmetry fails; hypotheses inhabited -/

theorem brT_uY_aZ_aZ (κ w : ℂ) : brT κ w uY aZ aZ = (-(κ * w) / 2) • uY := by
  simp only [brT, br_self, zero_add, tetF, piF_of_pr_zero pr_uY_aZ, pr_aZ_aZ]
  congr 1; ring

theorem brT_not_antisymm {κ w : ℂ} (h : κ * w ≠ 0) :
    brT κ w uY aZ aZ ≠ -brT κ w uY aZ aZ := by
  rw [brT_uY_aZ_aZ]
  intro h0
  have h2 : (2 : ℂ) • ((-(κ * w) / 2) • uY) = 0 := by
    rw [two_smul]; nth_rewrite 1 [h0]; simp
  rw [smul_smul] at h2
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact h (by linear_combination -h3)
  · exact uY_ne_zero h3

theorem paperII_nonvacuous :
    DivergenceFree uY ∧ DivergenceFree aZ ∧ jacT 1 1 uY aZ aZ aZ ≠ 0 ∧
      brT 1 1 uY aZ aZ ≠ -brT 1 1 uY aZ aZ :=
  ⟨divFree_uY, divFree_aZ, shearY_jacobi_fails_transverse (by norm_num),
    brT_not_antisymm (by norm_num)⟩

end
end Frohman.Tether.JacobiCompanion
