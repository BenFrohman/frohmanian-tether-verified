/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman (prepared with assistance from Grok; not a co-author).

# Biot–Savart on 𝕋³: `curl⁻¹` (LOCAL)

Two levels.

**(A) Fourier-coefficient level (exact, all modes `k ∈ ℤ³ \ {0}`).**
`curl` acts on the `k`-th coefficient as `û ↦ i k × û`, `div` as `û ↦ i k·û`. The Biot–Savart
multiplier `û = i k × ω̂ / |k|²` satisfies, whenever `k·ω̂ = 0` (div-free) and `k ≠ 0`:
`curl û = ω̂`, `div û = 0`, and it is the UNIQUE div-free preimage; and (real amplitudes)
`|k|²|û|² = |ω̂|²`, the per-mode form of `‖∇u‖₂ = ‖ω‖₂` (Parseval then sums it).

**(B) Function level on trigonometric polynomials.** For a real mode
`ω(x) = cos(K·x) a + sin(K·x) b` with `K ≠ 0`, `K·a = K·b = 0` we give an explicit
`u = cos(K·x) α + sin(K·x) β` with `curl u = ω`, `div u = 0`, using the `fderiv`-based `curl`
of `Torus.lean`; by linearity this extends to every finite sum of such modes, which discharges
`CurlRightInverse` on the class of (div-free, mean-zero) real trigonometric polynomials.

Remaining bridge (NOT done): extending `curl⁻¹` from trigonometric polynomials to all smooth
periodic fields needs uniform convergence of Fourier series of smooth periodic functions on `𝕋³`
together with their derivatives (Mathlib has Fourier series only on `AddCircle`, i.e. 1-D), and
`‖∇u‖₂ = ‖ω‖₂` as an integral identity needs Parseval on `𝕋³`.
-/
import FTVerified.May.CurlNS
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option linter.unusedSimpArgs false

namespace Frohman.Tether.BiotSavart
open Frohman.Tether.Torus Frohman.Tether.VorticityTether Frohman.Tether.CurlNS Real
open scoped Matrix

noncomputable section

/-! ## (A) Fourier-coefficient level -/

section Coeff

/-- Wavevector as a complex vector. -/
def kC (k : Fin 3 → ℤ) : Fin 3 → ℂ := fun i => (k i : ℂ)

/-- `|k|²` as a complex number. -/
def kSq (k : Fin 3 → ℤ) : ℂ := kC k ⬝ᵥ kC k

/-- `curl` on the `k`-th coefficient: `i k × û`. -/
def curlC (k : Fin 3 → ℤ) (u : Fin 3 → ℂ) : Fin 3 → ℂ := Complex.I • crossProduct (kC k) u

/-- `div` on the `k`-th coefficient: `i k · û`. -/
def divC (k : Fin 3 → ℤ) (u : Fin 3 → ℂ) : ℂ := Complex.I * (kC k ⬝ᵥ u)

/-- **Biot–Savart multiplier** `curl⁻¹ ω̂(k) = i k × ω̂ / |k|²`. -/
noncomputable def bsC (k : Fin 3 → ℤ) (w : Fin 3 → ℂ) : Fin 3 → ℂ :=
  (Complex.I / kSq k) • crossProduct (kC k) w

theorem kSq_ne_zero {k : Fin 3 → ℤ} (hk : k ≠ 0) : kSq k ≠ 0 := by
  have hpos : (0 : ℝ) < ∑ i, ((k i : ℝ)) ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
      by_contra h; push Not at h; exact hk (funext h)
    have : (0 : ℝ) < ((k i : ℝ)) ^ 2 := by positivity
    exact lt_of_lt_of_le this (Finset.single_le_sum (fun j _ => sq_nonneg ((k j : ℝ)))
      (Finset.mem_univ i))
  have h : kSq k = ((∑ i, ((k i : ℝ)) ^ 2 : ℝ) : ℂ) := by
    simp [kSq, kC, dotProduct, Fin.sum_univ_three, sq]
  rw [h]; exact_mod_cast hpos.ne'

/-- **Biot–Savart, coefficient level:** `curl (curl⁻¹ ω̂) = ω̂` for `k ≠ 0`, `k·ω̂ = 0`. -/
theorem curlC_bsC {k : Fin 3 → ℤ} (hk : k ≠ 0) {w : Fin 3 → ℂ} (hw : kC k ⬝ᵥ w = 0) :
    curlC k (bsC k w) = w := by
  have hn := kSq_ne_zero hk
  unfold curlC bsC
  rw [LinearMap.map_smul, cross_cross_eq_smul_sub_smul', hw, zero_smul, zero_sub, smul_smul,
    smul_neg, smul_smul]
  have : Complex.I * (Complex.I / kSq k) * (kC k ⬝ᵥ kC k) = -1 := by
    rw [show kC k ⬝ᵥ kC k = kSq k from rfl]; field_simp; simp
  rw [this]; simp

/-- `div (curl⁻¹ ω̂) = 0`. -/
theorem divC_bsC (k : Fin 3 → ℤ) (w : Fin 3 → ℂ) : divC k (bsC k w) = 0 := by
  unfold divC bsC
  rw [dotProduct_smul, dot_self_cross]; simp

/-- **Uniqueness:** a div-free coefficient `û` with `curl û = ω̂` IS `curl⁻¹ ω̂`. -/
theorem bsC_unique {k : Fin 3 → ℤ} (hk : k ≠ 0) {u w : Fin 3 → ℂ} (hdiv : kC k ⬝ᵥ u = 0)
    (hcurl : curlC k u = w) : u = bsC k w := by
  have hn := kSq_ne_zero hk
  rw [← hcurl]
  unfold bsC curlC
  rw [LinearMap.map_smul, cross_cross_eq_smul_sub_smul', hdiv, zero_smul, zero_sub, smul_smul,
    smul_neg, smul_smul]
  have : Complex.I / kSq k * Complex.I * (kC k ⬝ᵥ kC k) = -1 := by
    rw [show kC k ⬝ᵥ kC k = kSq k from rfl]; field_simp; simp
  rw [this]; simp

/-- **Per-mode `‖∇u‖₂ = ‖ω‖₂` (real amplitudes).** With `û = K × a / |K|²` (the real/imaginary
part of the multiplier), `|K|² |û|² = |a|²` whenever `K·a = 0`. Summing over modes with Parseval
gives `‖∇u‖₂² = Σ|k|²|û_k|² = Σ|ω̂_k|² = ‖ω‖₂²`. -/
theorem gradL2_mode {K a : Fin 3 → ℝ} (hK : K ⬝ᵥ K ≠ 0) (ha : K ⬝ᵥ a = 0) :
    (K ⬝ᵥ K) * (((K ⬝ᵥ K)⁻¹ • crossProduct K a) ⬝ᵥ ((K ⬝ᵥ K)⁻¹ • crossProduct K a))
      = a ⬝ᵥ a := by
  rw [smul_dotProduct, dotProduct_smul, cross_dot_cross, ha]
  simp only [smul_eq_mul, mul_zero, zero_mul, sub_zero]
  field_simp

end Coeff

/-! ## (B) Function level: real trigonometric modes -/

section Modes

/-- Phase `x ↦ K·x` as a continuous linear functional. -/
noncomputable def th (K : Fin 3 → ℝ) : R3 →L[ℝ] ℝ := ∑ j, K j • (EuclideanSpace.proj j : R3 →L[ℝ] ℝ)

theorem th_e (K : Fin 3 → ℝ) (i : Fin 3) : th K (e i) = K i := by
  simp [th, PiLp.single_apply]

/-- `R3` vector from coordinates. -/
noncomputable def toE (a : Fin 3 → ℝ) : R3 := (WithLp.equiv 2 (Fin 3 → ℝ)).symm a

@[simp] theorem toE_apply (a : Fin 3 → ℝ) (j : Fin 3) : toE a j = a j := rfl

/-- A real Fourier mode `cos(K·x) c + sin(K·x) d`. -/
noncomputable def mode (K c d : Fin 3 → ℝ) : R3 → R3 :=
  fun x => Real.cos (th K x) • toE c + Real.sin (th K x) • toE d

theorem comp_mode (K c d : Fin 3 → ℝ) (j : Fin 3) :
    comp j (mode K c d) = fun x => Real.cos (th K x) * c j + Real.sin (th K x) * d j := by
  funext x; simp [comp, mode]

theorem pd_trig (K : Fin 3 → ℝ) (c d : ℝ) (i : Fin 3) (x : R3) :
    pd i (fun x => Real.cos (th K x) * c + Real.sin (th K x) * d) x
      = (-Real.sin (th K x) * c + Real.cos (th K x) * d) * K i := by
  have h1 : HasFDerivAt (fun x => Real.cos (th K x)) (-Real.sin (th K x) • th K) x :=
    (th K).hasFDerivAt.cos
  have h2 : HasFDerivAt (fun x => Real.sin (th K x)) (Real.cos (th K x) • th K) x :=
    (th K).hasFDerivAt.sin
  have h := (h1.mul_const c).add (h2.mul_const d)
  unfold pd
  rw [show (fun x => Real.cos (th K x) * c + Real.sin (th K x) * d)
      = (fun y => Real.cos (th K y) * c) + (fun y => Real.sin (th K y) * d) from rfl, h.fderiv]
  simp [th_e]; ring

theorem pd_comp_mode (K c d : Fin 3 → ℝ) (i j : Fin 3) (x : R3) :
    pd i (comp j (mode K c d)) x
      = (-Real.sin (th K x) * c j + Real.cos (th K x) * d j) * K i := by
  rw [comp_mode]; exact pd_trig K (c j) (d j) i x

theorem mode_diff (K c d : Fin 3 → ℝ) (j : Fin 3) : Differentiable ℝ (comp j (mode K c d)) := by
  rw [comp_mode]
  exact (((th K).differentiable.cos).mul_const _).add (((th K).differentiable.sin).mul_const _)

theorem mode_contDiff (K c d : Fin 3 → ℝ) : ContDiff ℝ ⊤ (mode K c d) := by
  unfold mode
  exact ((th K).contDiff.cos.smul contDiff_const).add ((th K).contDiff.sin.smul contDiff_const)

/-- `|K|²`. -/
def nK (K : Fin 3 → ℝ) : ℝ := K ⬝ᵥ K

/-- **Biot–Savart potential of a mode:** for `ω = cos(K·x) a + sin(K·x) b`,
`u = cos(K·x) (K×b)/|K|² − sin(K·x) (K×a)/|K|²`. -/
noncomputable def bsMode (K a b : Fin 3 → ℝ) : R3 → R3 :=
  mode K ((nK K)⁻¹ • crossProduct K b) (-((nK K)⁻¹ • crossProduct K a))

/-- **`curl (curl⁻¹ ω) = ω` for a div-free mode.** -/
theorem curl_bsMode {K a b : Fin 3 → ℝ} (hK : nK K ≠ 0) (ha : K ⬝ᵥ a = 0) (hb : K ⬝ᵥ b = 0) :
    curl (bsMode K a b) = mode K a b := by
  have hr : (nK K)⁻¹ * nK K = 1 := inv_mul_cancel₀ hK
  unfold bsMode
  generalize (nK K)⁻¹ = r at hr ⊢
  simp only [nK, dotProduct, Fin.sum_univ_three] at hr ha hb
  funext x
  ext j
  obtain ⟨c0, c1, c2⟩ := curl_apply
    (mode K (r • crossProduct K b) (-(r • crossProduct K a))) x
  simp only [pd_comp_mode] at c0 c1 c2
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue] at c0 ⊢
    rw [c0]
    simp [mode, cross_apply]
    linear_combination (Real.cos (th K x) * (-r * K 0)) * ha
      + Real.cos (th K x) * a 0 * hr + (Real.sin (th K x) * (-r * K 0)) * hb
      + Real.sin (th K x) * b 0 * hr
  · simp only [Fin.mk_one, Fin.isValue] at c1 ⊢
    rw [c1]
    simp [mode, cross_apply]
    linear_combination (Real.cos (th K x) * (-r * K 1)) * ha
      + Real.cos (th K x) * a 1 * hr + (Real.sin (th K x) * (-r * K 1)) * hb
      + Real.sin (th K x) * b 1 * hr
  · simp only [Fin.reduceFinMk, Fin.isValue] at c2 ⊢
    rw [c2]
    simp [mode, cross_apply]
    linear_combination (Real.cos (th K x) * (-r * K 2)) * ha
      + Real.cos (th K x) * a 2 * hr + (Real.sin (th K x) * (-r * K 2)) * hb
      + Real.sin (th K x) * b 2 * hr

/-- The Biot–Savart potential of a mode is divergence-free. -/
theorem div_bsMode (K a b : Fin 3 → ℝ) : divergence (bsMode K a b) = fun _ => 0 := by
  funext x
  unfold divergence bsMode
  simp only [pd_comp_mode, Fin.sum_univ_three, cross_apply, Pi.smul_apply, Pi.neg_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
    Matrix.vecTail]
  simp
  ring

/-- A divergence-free Fourier mode with nonzero wave vector. -/
structure DFMode where
  K : Fin 3 → ℝ
  a : Fin 3 → ℝ
  b : Fin 3 → ℝ
  hK : nK K ≠ 0
  ha : K ⬝ᵥ a = 0
  hb : K ⬝ᵥ b = 0

/-- Trigonometric polynomial `Σ mode`. -/
def sumModes (L : List DFMode) : R3 → R3 := fun x => (L.map fun m => mode m.K m.a m.b x).sum

/-- Its Biot–Savart potential `Σ bsMode`. -/
def bsSum (L : List DFMode) : R3 → R3 := fun x => (L.map fun m => bsMode m.K m.a m.b x).sum

theorem bsSum_diff (L : List DFMode) (j : Fin 3) : Differentiable ℝ (comp j (bsSum L)) := by
  induction L with
  | nil =>
    have : comp j (bsSum []) = fun _ => 0 := by funext y; simp [comp, bsSum]
    rw [this]; exact differentiable_const _
  | cons m L ih =>
    have h1 := mode_diff m.K ((nK m.K)⁻¹ • crossProduct m.K m.b) (-((nK m.K)⁻¹ • crossProduct m.K m.a)) j
    have : comp j (bsSum (m :: L)) = fun y => comp j (bsMode m.K m.a m.b) y + comp j (bsSum L) y := by
      funext y; simp [comp, bsSum]
    rw [this]; exact h1.add ih

theorem curl_bsSum (L : List DFMode) : curl (bsSum L) = sumModes L := by
  induction L with
  | nil =>
    funext x
    have : bsSum [] = fun _ => 0 := by funext y; simp [bsSum]
    rw [this]
    have hc : ∀ j, comp j (fun _ : R3 => (0 : R3)) = fun _ => 0 := fun j => by
      funext y; simp [comp]
    ext j; fin_cases j <;> simp [curl, pd, hc, vec3, sumModes]
  | cons m L ih =>
    have : bsSum (m :: L) = fun y => bsMode m.K m.a m.b y + bsSum L y := by
      funext y; simp [bsSum]
    rw [this, curl_add (fun j => by unfold bsMode; exact mode_diff _ _ _ j) (bsSum_diff L), ih, curl_bsMode m.hK m.ha m.hb]
    funext x; simp [sumModes]

/-- Admissible vorticities: finite sums of divergence-free nonconstant Fourier modes. -/
def AdmTrig (g : R3 → R3) : Prop := ∃ L : List DFMode, g = sumModes L

open Classical in
/-- Concrete `curl⁻¹`: Biot–Savart on trigonometric polynomials (`0` elsewhere). -/
def curlInvTrig (g : R3 → R3) : R3 → R3 := if h : AdmTrig g then bsSum h.choose else 0

/-- **`CurlRightInverse` discharged on trigonometric polynomials.** -/
theorem curlRightInverse_trig : CurlRightInverse curlInvTrig AdmTrig := by
  intro g hg
  unfold curlInvTrig
  rw [dif_pos hg, curl_bsSum]
  exact hg.choose_spec.symm

end Modes

end

end Frohman.Tether.BiotSavart
