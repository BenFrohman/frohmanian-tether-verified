-- SPDX-FileCopyrightText: 2026 Benjamin Stanley Frohman
-- SPDX-License-Identifier: Apache-2.0
/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman (prepared with assistance from Grok; not a co-author).

# Field-level tethered bracket on trigonometric-polynomial vector fields on 𝕋³

Fields are finite Fourier sums `a(x) = Σ_k â_k e^{ik·x}` (`Fld`), reusing `kC` from
`BiotSavart.lean`. On them:

* `br` — the vector-field Lie bracket `[a,b] = (a·∇)b − (b·∇)a`, mode-wise
  `[v e^{ip·x}, w e^{iq·x}] = i((v·q)w − (w·p)v) e^{i(p+q)·x}`; it satisfies Jacobi
  (`jacF_eq_zero`), so the Arnold / Lie–Poisson bracket on linear functionals is classical.
* `pr` — the `L²` pairing `(2π)⁻³∫ a·b`, extended complex-bilinearly (`Σ_k â_k·b̂_{−k}`).
* `piF u` — field-level `Π_u x = x − (⟨u,x⟩/⟨u,u⟩) u`; `tetF` — `T(a,b) = −(κw)⟨Π_u a,Π_u b⟩ u`.
* `DivergenceFree a` — `k·â_k = 0` for all `k`. This is where divergence-freeness enters.

Results:
1. `jacT_eq_mixedSum`: for `⟨u,u⟩ ≠ 0`, the tethered Jacobiator equals the mixed cyclic sum.
2. `br_eq_zero_of_xOnly_divFree`: divergence-free `e_x`-directed fields (parallel shears
   `f(y,z) e_x`) commute; hence `shearY_jacobi_holds` / `shearY_mixed_cancel`: at
   `u = (sin y,0,0)` the mixed terms cancel and Jacobi holds on that class.
3. `shearX_mixed_coeff`, `shearX_jacobi_fails`: at `u = (sin x,0,0)` (`not_divFree_uX`) with the
   divergence-free triple `a = b = c = (1,0,0)`, the mixed sum has `e^{ix}` coefficient
   `(3/2)κw ≠ 0`.
4. `shearY_transverse_coeff`, `shearY_jacobi_fails_transverse`: at `u = (sin y,0,0)` with the
   divergence-free triple `a = b = c = (0,0,sin x)`, the mixed sum has `e^{i(x+y)}`,
   `z`-coefficient `(3i/8)κw ≠ 0`. So divergence-freeness alone does not give cancellation.

Caveats: the witnesses use `a = b = c`, where the Jacobiator is `3·{{a,a},a}`. That is
non-trivial only because `T` is symmetric (metriplectic). The link from Fourier coefficients to
the `fderiv`-based fields of `Torus.lean` is not formalized for `br` here. Scalars are complex
(the real fields used are conjugate-symmetric).
-/
import FTVerified.May.BiotSavart

set_option linter.unusedSimpArgs false

namespace Frohman.Tether.FieldJacobi
open Frohman.Tether.BiotSavart
open scoped Matrix

noncomputable section

/-- Trigonometric-polynomial vector fields on `𝕋³`, by Fourier coefficients. -/
abbrev Fld := (Fin 3 → ℤ) →₀ (Fin 3 → ℂ)

/-- Mode-pair bracket coefficient. -/
def bvec (p q : Fin 3 → ℤ) (v w : Fin 3 → ℂ) : Fin 3 → ℂ :=
  Complex.I • ((v ⬝ᵥ kC q) • w - (w ⬝ᵥ kC p) • v)

/-- Vector-field Lie bracket `[a,b] = (a·∇)b − (b·∇)a`. -/
def br (a b : Fld) : Fld :=
  a.sum fun p v => b.sum fun q w => Finsupp.single (p + q) (bvec p q v w)

/-- `L²` pairing `(2π)⁻³ ∫ a·b`, complex-bilinearly extended. -/
def pr (a b : Fld) : ℂ := a.sum fun p v => v ⬝ᵥ b (-p)

theorem bvec_zero_left (p q w) : bvec p q 0 w = 0 := by simp [bvec]
theorem bvec_zero_right (p q v) : bvec p q v 0 = 0 := by simp [bvec]

theorem br_single (p q v w) :
    br (Finsupp.single p v) (Finsupp.single q w) = Finsupp.single (p + q) (bvec p q v w) := by
  unfold br
  rw [Finsupp.sum_single_index, Finsupp.sum_single_index] <;> simp [bvec_zero_left, bvec_zero_right]

theorem br_add_left (a b c : Fld) : br (a + b) c = br a c + br b c := by
  unfold br
  apply Finsupp.sum_add_index'
  · intro p; simp [bvec_zero_left]
  · intro p v v'
    rw [← Finsupp.sum_add]
    congr 1; funext q w
    rw [← Finsupp.single_add]; congr 1
    ext i; simp [bvec, add_dotProduct]; ring

theorem br_add_right (a b c : Fld) : br a (b + c) = br a b + br a c := by
  unfold br
  rw [← Finsupp.sum_add]
  congr 1; funext p v
  apply Finsupp.sum_add_index'
  · intro q; simp [bvec_zero_right]
  · intro q w w'
    rw [← Finsupp.single_add]; congr 1
    ext i; simp [bvec, add_dotProduct]; ring

theorem br_zero_left (c : Fld) : br 0 c = 0 := by simp [br]
theorem br_zero_right (c : Fld) : br c 0 = 0 := by simp [br]

theorem pr_single (p v) (b : Fld) : pr (Finsupp.single p v) b = v ⬝ᵥ b (-p) := by
  unfold pr; rw [Finsupp.sum_single_index]; simp

theorem pr_add_left (a b c : Fld) : pr (a + b) c = pr a c + pr b c := by
  unfold pr; apply Finsupp.sum_add_index' <;> intros <;> simp [add_dotProduct]

theorem pr_add_right (a b c : Fld) : pr a (b + c) = pr a b + pr a c := by
  unfold pr; rw [← Finsupp.sum_add]; congr 1; funext p v; simp [dotProduct_add]

theorem pr_smul_right (a b : Fld) (r : ℂ) : pr a (r • b) = r * pr a b := by
  unfold pr; rw [Finsupp.mul_sum]; congr 1; funext p v; simp [dotProduct_smul]

theorem pr_zero_left (b : Fld) : pr 0 b = 0 := by simp [pr]
theorem pr_zero_right (b : Fld) : pr b 0 = 0 := by simp [pr]

/-- Field-level `Π_u x = x − (⟨u,x⟩/⟨u,u⟩) u`. -/
def piF (u x : Fld) : Fld := x - (pr u x / pr u u) • u

/-- Field-level tether, vector-valued: `T(a,b) = −(κw)⟨Π_u a, Π_u b⟩ u`. -/
def tetF (κ w : ℂ) (u a b : Fld) : Fld := (-(κ * w) * pr (piF u a) (piF u b)) • u

/-- Mixed term `[T(a,b),c] + T([a,b],c)`. -/
def mixedF (κ w : ℂ) (u a b c : Fld) : Fld := br (tetF κ w u a b) c + tetF κ w u (br a b) c

def mixedSumF (κ w : ℂ) (u a b c : Fld) : Fld :=
  mixedF κ w u a b c + mixedF κ w u b c a + mixedF κ w u c a b

/-- `DivergenceFree` (the May 28, 2026 skeleton's predicate, `Skeleton/PaperOverview.lean`):
`k · û_k = 0` for every mode. -/
def DivergenceFree (a : Fld) : Prop := ∀ k, kC k ⬝ᵥ a k = 0

theorem piF_zero (u : Fld) : piF u 0 = 0 := by simp [piF, pr_zero_right]
theorem tetF_zero_left (κ w : ℂ) (u c : Fld) : tetF κ w u 0 c = 0 := by
  simp [tetF, piF_zero, pr_zero_left]

theorem br_smul_left (r : ℂ) (a c : Fld) : br (r • a) c = r • br a c := by
  induction a using Finsupp.induction_linear with
  | zero => simp [br_zero_left]
  | add a b ha hb => rw [smul_add, br_add_left, br_add_left, ha, hb, smul_add]
  | single p v =>
    rw [Finsupp.smul_single]
    induction c using Finsupp.induction_linear with
    | zero => simp [br_zero_right]
    | add c d hc hd => rw [br_add_right, br_add_right, hc, hd, smul_add]
    | single q w =>
      rw [br_single, br_single, Finsupp.smul_single]; congr 1
      ext i; simp [bvec, smul_dotProduct]; ring


/-! ## The classical (Arnold) bracket satisfies Jacobi -/

/-- Jacobiator of the field bracket. -/
def jacF (a b c : Fld) : Fld := br (br a b) c + br (br b c) a + br (br c a) b

theorem jacF_cycle (a b c : Fld) : jacF a b c = jacF b c a := by unfold jacF; abel

theorem jacF_add_left (a a' b c : Fld) : jacF (a + a') b c = jacF a b c + jacF a' b c := by
  simp only [jacF, br_add_left, br_add_right]; abel

theorem jacF_zero_left (b c : Fld) : jacF 0 b c = 0 := by
  simp [jacF, br_zero_left, br_zero_right]

theorem jacF_single (p q r : Fin 3 → ℤ) (v w z : Fin 3 → ℂ) :
    jacF (Finsupp.single p v) (Finsupp.single q w) (Finsupp.single r z) = 0 := by
  simp only [jacF, br_single]
  rw [show q + r + p = p + q + r by abel, show r + p + q = p + q + r by abel,
    ← Finsupp.single_add, ← Finsupp.single_add, Finsupp.single_eq_zero]
  ext i
  fin_cases i <;> simp [bvec, dotProduct, Fin.sum_univ_three, kC] <;> ring

/-- **Jacobi for the vector-field Lie bracket on trigonometric polynomials** (so the classical
Arnold / Lie–Poisson bracket on linear functionals `F(m)=⟨m,a⟩` satisfies Jacobi). -/
theorem jacF_eq_zero (a b c : Fld) : jacF a b c = 0 := by
  induction a using Finsupp.induction_linear with
  | zero => exact jacF_zero_left b c
  | add a a' ha ha' => rw [jacF_add_left, ha, ha', add_zero]
  | single p v =>
    rw [jacF_cycle]
    induction b using Finsupp.induction_linear with
    | zero => exact jacF_zero_left _ _
    | add b b' hb hb' => rw [jacF_add_left, hb, hb', add_zero]
    | single q w =>
      rw [jacF_cycle]
      induction c using Finsupp.induction_linear with
      | zero => exact jacF_zero_left _ _
      | add c c' hc hc' => rw [jacF_add_left, hc, hc', add_zero]
      | single r z => rw [← jacF_cycle, ← jacF_cycle]; exact jacF_single p q r v w z

/-! ## Parallel shear flows: divergence-free ⇒ abelian ⇒ mixed terms cancel -/

/-- Fields pointing along `e_x`. -/
def XOnly (a : Fld) : Prop := ∀ k, a k 1 = 0 ∧ a k 2 = 0

theorem br_eq_zero_of_xOnly_divFree {a b : Fld} (ha : XOnly a) (hda : DivergenceFree a)
    (hb : XOnly b) (hdb : DivergenceFree b) : br a b = 0 := by
  unfold br Finsupp.sum
  apply Finset.sum_eq_zero; intro p _
  apply Finset.sum_eq_zero; intro q _
  have h1 := hda p; have h2 := hdb q
  obtain ⟨a1, a2⟩ := ha p; obtain ⟨b1, b2⟩ := hb q
  simp only [kC, dotProduct, Fin.sum_univ_three, a1, a2, b1, b2] at h1 h2
  rw [Finsupp.single_eq_zero]
  ext i
  fin_cases i <;> simp [bvec, dotProduct, Fin.sum_univ_three, kC, a1, a2, b1, b2] <;>
    linear_combination (a p 0) * h2 - (b q 0) * h1

theorem xOnly_smul {a : Fld} (h : XOnly a) (r : ℂ) : XOnly (r • a) := by
  intro k; simp [(h k).1, (h k).2]

theorem divFree_smul {a : Fld} (h : DivergenceFree a) (r : ℂ) : DivergenceFree (r • a) := by
  intro k; simp [dotProduct_smul, h k]

/-- **Cancellation on the divergence-free parallel shear class.** If `u`, `a`, `b`, `c` are all
divergence-free and point along `e_x` (i.e. are shear flows `f(y,z) e_x`, such as
`(sin y,0,0)`), every mixed term vanishes. -/
theorem mixedF_eq_zero_of_shear {u a b c : Fld} (κ w : ℂ) (hu : XOnly u) (hdu : DivergenceFree u)
    (ha : XOnly a) (hda : DivergenceFree a) (hb : XOnly b) (hdb : DivergenceFree b)
    (hc : XOnly c) (hdc : DivergenceFree c) : mixedF κ w u a b c = 0 := by
  unfold mixedF
  rw [br_eq_zero_of_xOnly_divFree ha hda hb hdb, tetF_zero_left, add_zero]
  exact br_eq_zero_of_xOnly_divFree (xOnly_smul hu _) (divFree_smul hdu _) hc hdc

theorem mixedSumF_eq_zero_of_shear {u a b c : Fld} (κ w : ℂ) (hu : XOnly u) (hdu : DivergenceFree u)
    (ha : XOnly a) (hda : DivergenceFree a) (hb : XOnly b) (hdb : DivergenceFree b)
    (hc : XOnly c) (hdc : DivergenceFree c) : mixedSumF κ w u a b c = 0 := by
  unfold mixedSumF
  rw [mixedF_eq_zero_of_shear κ w hu hdu ha hda hb hdb hc hdc,
    mixedF_eq_zero_of_shear κ w hu hdu hb hdb hc hdc ha hda,
    mixedF_eq_zero_of_shear κ w hu hdu hc hdc ha hda hb hdb]; simp

/-! ## Explicit fields -/

def kx : Fin 3 → ℤ := ![1, 0, 0]
def ky : Fin 3 → ℤ := ![0, 1, 0]

/-- `(sin y, 0, 0)`. -/
def uY : Fld := Finsupp.single ky ![-Complex.I / 2, 0, 0] + Finsupp.single (-ky) ![Complex.I / 2, 0, 0]
/-- `(sin x, 0, 0)`. -/
def uX : Fld := Finsupp.single kx ![-Complex.I / 2, 0, 0] + Finsupp.single (-kx) ![Complex.I / 2, 0, 0]
/-- `(0, 0, sin x)`. -/
def aZ : Fld := Finsupp.single kx ![0, 0, -Complex.I / 2] + Finsupp.single (-kx) ![0, 0, Complex.I / 2]
/-- The constant field `(1, 0, 0)`. -/
def eX : Fld := Finsupp.single 0 ![1, 0, 0]

theorem ne_kx : kx ≠ -kx := by intro h; have := congrFun h 0; simp [kx] at this
theorem ne_ky : ky ≠ -ky := by intro h; have := congrFun h 1; simp [ky] at this

theorem br_antisymm (a b : Fld) : br a b = -br b a := by
  induction a using Finsupp.induction_linear with
  | zero => simp [br_zero_left, br_zero_right]
  | add a a' ha ha' => rw [br_add_left, br_add_right, ha, ha', neg_add]
  | single p v =>
    induction b using Finsupp.induction_linear with
    | zero => simp [br_zero_left, br_zero_right]
    | add b b' hb hb' => rw [br_add_right, br_add_left, hb, hb', neg_add]
    | single q w =>
      rw [br_single, br_single, ← Finsupp.single_neg, add_comm q p]; congr 1
      ext i; simp [bvec]; ring

theorem br_self (a : Fld) : br a a = 0 := by
  have h := br_antisymm a a
  have h2 : (2 : ℂ) • br a a = 0 := by rw [two_smul]; nth_rewrite 1 [h]; simp
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/-- With `a = b = c`, the mixed sum is `3 s [u,a]`, `s = −(κw)⟨Π_u a, Π_u a⟩`. -/
theorem mixedSumF_diag (κ w : ℂ) (u a : Fld) :
    mixedSumF κ w u a a a = (3 * (-(κ * w) * pr (piF u a) (piF u a))) • br u a := by
  simp only [mixedSumF, mixedF, br_self, tetF_zero_left, add_zero]
  simp only [tetF, br_smul_left]
  module

theorem kx_ne : ∀ {k : Fin 3 → ℤ}, k = kx → k ≠ -kx := by rintro _ rfl; exact ne_kx

theorem pr_uY_aZ : pr uY aZ = 0 := by
  simp [uY, aZ, pr_add_left, pr_single, Finsupp.single_apply, dotProduct, Fin.sum_univ_three,
    kx, ky, funext_iff, Fin.forall_fin_succ]

theorem pr_aZ_aZ : pr aZ aZ = 1 / 2 := by
  simp [aZ, pr_add_left, pr_single, Finsupp.single_apply, dotProduct, Fin.sum_univ_three,
    kx, funext_iff, Fin.forall_fin_succ]; ring_nf; simp; norm_num

theorem br_uY_aZ_coeff : br uY aZ (ky + kx) 2 = -Complex.I / 4 := by
  simp [uY, aZ, br_add_left, br_add_right, br_single, Finsupp.single_apply, bvec, dotProduct,
    Fin.sum_univ_three, kx, ky, kC, funext_iff, Fin.forall_fin_succ]; ring_nf
  have h3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  rw [h3]; ring

theorem pr_uX_eX : pr uX eX = 0 := by
  simp [uX, eX, pr_add_left, pr_single, Finsupp.single_apply, dotProduct, Fin.sum_univ_three,
    kx, funext_iff, Fin.forall_fin_succ]

theorem pr_eX_eX : pr eX eX = 1 := by
  simp [eX, pr_single, dotProduct, Fin.sum_univ_three]

theorem br_uX_eX_coeff : br uX eX kx 0 = -1 / 2 := by
  simp [uX, eX, br_add_left, br_single, Finsupp.single_apply, bvec, dotProduct,
    Fin.sum_univ_three, kx, kC, funext_iff, Fin.forall_fin_succ]
  ring_nf; simp; norm_num

theorem piF_of_pr_zero {u x : Fld} (h : pr u x = 0) : piF u x = x := by simp [piF, h]

/-! ## Divergence facts -/

theorem divFree_uY : DivergenceFree uY := by
  intro k; simp [uY, Finsupp.single_apply, kC, dotProduct, Fin.sum_univ_three, ky]
  split_ifs with h1 h2 <;> subst_vars <;> simp

theorem divFree_aZ : DivergenceFree aZ := by
  intro k; simp [aZ, Finsupp.single_apply, kC, dotProduct, Fin.sum_univ_three, kx]
  split_ifs with h1 h2 <;> subst_vars <;> simp

theorem divFree_eX : DivergenceFree eX := by
  intro k; simp [eX, Finsupp.single_apply, kC, dotProduct, Fin.sum_univ_three]
  split_ifs with h <;> subst_vars <;> simp

theorem xOnly_uY : XOnly uY := by
  intro k; simp [uY, Finsupp.single_apply]; split_ifs <;> simp

theorem xOnly_uX : XOnly uX := by
  intro k; simp [uX, Finsupp.single_apply]; split_ifs <;> simp

theorem xOnly_eX : XOnly eX := by
  intro k; simp [eX, Finsupp.single_apply]; split_ifs <;> simp

/-- `(sin x,0,0)` is **not** divergence-free (`div = cos x`). -/
theorem not_divFree_uX : ¬ DivergenceFree uX := by
  intro h; have := h kx
  simp [uX, Finsupp.single_apply, kC, dotProduct, Fin.sum_univ_three, kx, ne_kx] at this

/-! ## Main results -/

/-- **(1) Divergence-free shear, own class: mixed terms cancel.** For `u = (sin y,0,0)` and
any divergence-free `e_x`-directed `a, b, c` (shear flows `f(y,z) e_x`). -/
theorem shearY_mixed_cancel (κ w : ℂ) {a b c : Fld} (ha : XOnly a) (hda : DivergenceFree a)
    (hb : XOnly b) (hdb : DivergenceFree b) (hc : XOnly c) (hdc : DivergenceFree c) :
    mixedSumF κ w uY a b c = 0 :=
  mixedSumF_eq_zero_of_shear κ w xOnly_uY divFree_uY ha hda hb hdb hc hdc

/-- **(2) Compressible shear: explicit failure, even with a divergence-free triple.**
For `u = (sin x,0,0)` and `a = b = c = (1,0,0)` (div-free, `e_x`-directed), the `e^{ix}`,
`x`-component coefficient of the mixed sum is `(3/2) κ w`. -/
theorem shearX_mixed_coeff (κ w : ℂ) : mixedSumF κ w uX eX eX eX kx 0 = 3 / 2 * (κ * w) := by
  rw [mixedSumF_diag, piF_of_pr_zero pr_uX_eX, pr_eX_eX, Finsupp.smul_apply, Pi.smul_apply,
    br_uX_eX_coeff, smul_eq_mul]; ring

theorem shearX_mixed_ne_zero {κ w : ℂ} (h : κ * w ≠ 0) : mixedSumF κ w uX eX eX eX ≠ 0 := by
  intro h0
  have := shearX_mixed_coeff κ w
  rw [h0] at this; simp at this
  exact h (mul_eq_zero.2 this)

/-- **(3) Divergence-free shear, general div-free triple: explicit failure.** For
`u = (sin y,0,0)` and `a = b = c = (0,0,sin x)` (both div-free), the `e^{i(x+y)}`,
`z`-component coefficient of the mixed sum is `(3i/8) κ w`. So divergence-freeness alone does
not make the mixed terms cancel; (1) needs the triple to stay in the shear class. -/
theorem shearY_transverse_coeff (κ w : ℂ) :
    mixedSumF κ w uY aZ aZ aZ (ky + kx) 2 = 3 * Complex.I / 8 * (κ * w) := by
  rw [mixedSumF_diag, piF_of_pr_zero pr_uY_aZ, pr_aZ_aZ, Finsupp.smul_apply, Pi.smul_apply,
    br_uY_aZ_coeff, smul_eq_mul]; ring

theorem shearY_transverse_ne_zero {κ w : ℂ} (h : κ * w ≠ 0) :
    mixedSumF κ w uY aZ aZ aZ ≠ 0 := by
  intro h0
  have := shearY_transverse_coeff κ w
  rw [h0] at this; simp at this
  exact h (mul_eq_zero.2 this)

/-! ## Full tethered bracket: Jacobiator = mixed sum -/

/-- Field-level tethered bracket `{a,b} = [a,b] + T(a,b)`. -/
def brT (κ w : ℂ) (u a b : Fld) : Fld := br a b + tetF κ w u a b

def jacT (κ w : ℂ) (u a b c : Fld) : Fld :=
  brT κ w u (brT κ w u a b) c + brT κ w u (brT κ w u b c) a + brT κ w u (brT κ w u c a) b

theorem piF_add (u x y : Fld) : piF u (x + y) = piF u x + piF u y := by
  simp only [piF, pr_add_right, add_div, add_smul]; abel

theorem tetF_add_left (κ w : ℂ) (u x y c : Fld) :
    tetF κ w u (x + y) c = tetF κ w u x c + tetF κ w u y c := by
  simp only [tetF, piF_add, pr_add_left, mul_add, add_smul]

theorem piF_smul_self {u : Fld} (hu : pr u u ≠ 0) (s : ℂ) : piF u (s • u) = 0 := by
  simp only [piF, pr_smul_right, mul_div_assoc, div_self hu, mul_one, sub_self]

theorem tetF_tetF {u : Fld} (hu : pr u u ≠ 0) (κ w : ℂ) (a b c : Fld) :
    tetF κ w u (tetF κ w u a b) c = 0 := by
  rw [tetF, tetF, piF_smul_self hu, pr_zero_left]; simp

/-- **Exact Jacobi condition at field level.** With `⟨u,u⟩ ≠ 0`, the Jacobiator of the tethered
bracket equals the mixed cyclic sum (classical terms cancel by `jacF_eq_zero`; tether–tether
terms vanish because `Π_u u = 0`). -/
theorem jacT_eq_mixedSum {u : Fld} (hu : pr u u ≠ 0) (κ w : ℂ) (a b c : Fld) :
    jacT κ w u a b c = mixedSumF κ w u a b c := by
  have e : jacT κ w u a b c = jacF a b c + mixedSumF κ w u a b c := by
    simp only [jacT, brT, jacF, mixedSumF, mixedF, br_add_left, tetF_add_left, tetF_tetF hu,
      add_zero]
    abel
  rw [e, jacF_eq_zero, zero_add]

theorem pr_uX_uX : pr uX uX = 1 / 2 := by
  simp [uX, pr_add_left, pr_single, Finsupp.single_apply, dotProduct, Fin.sum_univ_three,
    kx, funext_iff, Fin.forall_fin_succ]; ring_nf; simp; norm_num

theorem pr_uY_uY : pr uY uY = 1 / 2 := by
  simp [uY, pr_add_left, pr_single, Finsupp.single_apply, dotProduct, Fin.sum_univ_three,
    ky, funext_iff, Fin.forall_fin_succ]; ring_nf; simp; norm_num

/-- The field-level tethered bracket at `u = (sin x,0,0)` **fails Jacobi**. -/
theorem shearX_jacobi_fails {κ w : ℂ} (h : κ * w ≠ 0) : jacT κ w uX eX eX eX ≠ 0 := by
  rw [jacT_eq_mixedSum (by rw [pr_uX_uX]; norm_num)]; exact shearX_mixed_ne_zero h

/-- The field-level tethered bracket at `u = (sin y,0,0)` also **fails Jacobi** on the
divergence-free triple `(0,0,sin x)`. -/
theorem shearY_jacobi_fails_transverse {κ w : ℂ} (h : κ * w ≠ 0) : jacT κ w uY aZ aZ aZ ≠ 0 := by
  rw [jacT_eq_mixedSum (by rw [pr_uY_uY]; norm_num)]; exact shearY_transverse_ne_zero h

/-- At `u = (sin y,0,0)`, Jacobi **holds** on the divergence-free shear class. -/
theorem shearY_jacobi_holds {κ w : ℂ} {a b c : Fld} (ha : XOnly a) (hda : DivergenceFree a)
    (hb : XOnly b) (hdb : DivergenceFree b) (hc : XOnly c) (hdc : DivergenceFree c) :
    jacT κ w uY a b c = 0 := by
  rw [jacT_eq_mixedSum (by rw [pr_uY_uY]; norm_num)]
  exact shearY_mixed_cancel κ w ha hda hb hdb hc hdc

end
end Frohman.Tether.FieldJacobi
