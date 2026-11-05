/-
Copyright (c) 2026 Benjamin Frohman. All rights reserved.
Released under Apache 2.0 license.

# Enstrophy (`‖ω‖_{L²}`) bound for the TETHERED system (quartic `𝔗_F` feedback)

Notation: `E = ½‖ω‖₂²`, `Q = ‖ω‖₄⁴`, `S = ∫ ω·Sω` (stretching), `D = ‖∇ω‖₂²`, unit torus `|T³| = 1`.
Pointwise the quartic tether is `quarticTether κ u ω = 𝔗_F[κ, ‖ω‖², u] ω ω = −κ‖ω‖⁴`
(`quarticTether_eq`, Final.lean); integrated it contributes `−κ‖ω‖₄⁴`.

Named (cited) inputs — stated, not derived here:
* `TetheredEnstrophyIdentity`: `E' = S − ν D − κ Q` (tethered vorticity equation, multiply by ω,
  integrate by parts on T³; Majda–Bertozzi 2002 §3.1 for the untethered part).
* `StrainL2Bound`: `S ≤ C‖ω‖₂‖ω‖₄²` — Hölder `|∫ω·Sω| ≤ ‖S‖₂‖ω‖₄²` plus the L² Biot–Savart
  identity `‖∇u‖₂ = ‖ω‖₂` for div-free periodic `u` (Parseval; Majda–Bertozzi Prop. 2.16). TRUE.
* `L4L2Holder`: `‖ω‖₂⁴ ≤ ‖ω‖₄⁴` on the unit torus (Hölder/Jensen).

Plain Navier–Stokes: the `−κQ` term is absent; `S ≤ C‖ω‖₂‖ω‖₄²` then cannot be absorbed by
`−νD` alone without the cubic `‖ω‖₂³`-type growth, so this argument does NOT close there.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.ODE.Gronwall

namespace Frohman.Tether.EnstrophyL2

open Set

/-- Cited: integrated tethered enstrophy identity on `[0,T)`. -/
def TetheredEnstrophyIdentity (E E' S D Q : ℝ → ℝ) (ν κ T : ℝ) : Prop :=
  ContinuousOn E (Icc 0 T) ∧
  (∀ x ∈ Ico 0 T, HasDerivWithinAt E (E' x) (Ici x) x) ∧
  (∀ x ∈ Ico 0 T, E' x = S x - ν * D x - κ * Q x)

/-- Cited: L² Calderón–Zygmund / Biot–Savart strain bound `S ≤ C‖ω‖₂‖ω‖₄²`. -/
def StrainL2Bound (E S Q : ℝ → ℝ) (C T : ℝ) : Prop :=
  ∀ x ∈ Ico 0 T, S x ≤ C * Real.sqrt (2 * E x) * Real.sqrt (Q x)

/-- Cited: Hölder on the unit torus, `‖ω‖₂⁴ ≤ ‖ω‖₄⁴`. -/
def L4L2Holder (E Q : ℝ → ℝ) (T : ℝ) : Prop := ∀ x ∈ Ico 0 T, (2 * E x) ^ 2 ≤ Q x

/-- Young: `C a b ≤ λ b² + C² a² /(4λ)`. -/
theorem young_lam {lam : ℝ} (h : 0 < lam) (C a b : ℝ) :
    C * a * b ≤ lam * b ^ 2 + C ^ 2 * a ^ 2 / (4 * lam) := by
  have e : lam * b ^ 2 + C ^ 2 * a ^ 2 / (4 * lam) - C * a * b
      = (2 * lam * b - C * a) ^ 2 / (4 * lam) := by field_simp; ring
  have : 0 ≤ (2 * lam * b - C * a) ^ 2 / (4 * lam) := by positivity
  linarith

/-- Pointwise: strain absorbed by a fraction `λ` of the tether. -/
theorem stretch_absorb {lam : ℝ} (h : 0 < lam) (C e q s : ℝ) (he : 0 ≤ e) (hq : 0 ≤ q)
    (hs : s ≤ C * Real.sqrt (2 * e) * Real.sqrt q) :
    s ≤ lam * q + C ^ 2 * (2 * e) / (4 * lam) := by
  have := young_lam h C (Real.sqrt (2 * e)) (Real.sqrt q)
  rw [Real.sq_sqrt hq, Real.sq_sqrt (by linarith)] at this
  linarith

/-- Differential inequality (Grönwall form): `E' ≤ (C²/2κ) E`. -/
theorem enstrophy_deriv_le {E S D Q : ℝ → ℝ} {ν κ C x e' : ℝ} (hκ : 0 < κ) (hν : 0 ≤ ν)
    (hD : 0 ≤ D x) (hE : 0 ≤ E x) (hQ : 0 ≤ Q x) (hid : e' = S x - ν * D x - κ * Q x)
    (hS : S x ≤ C * Real.sqrt (2 * E x) * Real.sqrt (Q x)) :
    e' ≤ C ^ 2 / (2 * κ) * E x := by
  have h := stretch_absorb hκ C (E x) (Q x) (S x) hE hQ hS
  have : C ^ 2 * (2 * E x) / (4 * κ) = C ^ 2 / (2 * κ) * E x := by field_simp; ring
  nlinarith [mul_nonneg hν hD]

/-- Logistic form: `E' ≤ (C²/κ) E − 2κ E²` (half the tether absorbs, half plus Hölder damps). -/
theorem enstrophy_deriv_logistic {E S D Q : ℝ → ℝ} {ν κ C x e' : ℝ} (hκ : 0 < κ) (hν : 0 ≤ ν)
    (hD : 0 ≤ D x) (hE : 0 ≤ E x) (hQ : 0 ≤ Q x) (hid : e' = S x - ν * D x - κ * Q x)
    (hS : S x ≤ C * Real.sqrt (2 * E x) * Real.sqrt (Q x)) (hH : (2 * E x) ^ 2 ≤ Q x) :
    e' ≤ C ^ 2 / κ * E x - 2 * κ * E x ^ 2 := by
  have h := stretch_absorb (lam := κ / 2) (by linarith) C (E x) (Q x) (S x) hE hQ hS
  have : C ^ 2 * (2 * E x) / (4 * (κ / 2)) = C ^ 2 / κ * E x := by field_simp; ring
  nlinarith [mul_nonneg hν hD, mul_le_mul_of_nonneg_left hH hκ.le]

/-- **Tethered enstrophy Grönwall bound:** `E(t) ≤ E(0) exp((C²/2κ) t)`. -/
theorem tethered_enstrophy_gronwall {E E' S D Q : ℝ → ℝ} {ν κ C T : ℝ} (hκ : 0 < κ)
    (hν : 0 ≤ ν) (hD : ∀ x ∈ Ico 0 T, 0 ≤ D x) (hE : ∀ x ∈ Ico 0 T, 0 ≤ E x)
    (hQ : ∀ x ∈ Ico 0 T, 0 ≤ Q x) (hI : TetheredEnstrophyIdentity E E' S D Q ν κ T)
    (hS : StrainL2Bound E S Q C T) :
    ∀ t ∈ Icc 0 T, E t ≤ E 0 * Real.exp (C ^ 2 / (2 * κ) * t) := by
  obtain ⟨hc, hd, hid⟩ := hI
  intro t ht
  have h := le_gronwallBound_of_liminf_deriv_right_le (f := E) (f' := E') (δ := E 0)
    (K := C ^ 2 / (2 * κ)) (ε := 0) hc
    (fun x hx r hr => by
      simpa [slope_def_field, div_eq_inv_mul] using (hd x hx).liminf_right_slope_le hr)
    le_rfl
    (fun x hx => by
      have := enstrophy_deriv_le hκ hν (hD x hx) (hE x hx) (hQ x hx) (hid x hx) (hS x hx)
      linarith) t ht
  rwa [gronwallBound_ε0, sub_zero] at h

/-- **Tethered enstrophy uniform bound:** `E(t) ≤ max(E(0), C²/(2κ²))` for all `t ∈ [0,T]`. -/
theorem tethered_enstrophy_uniform {E E' S D Q : ℝ → ℝ} {ν κ C T : ℝ} (hκ : 0 < κ)
    (hν : 0 ≤ ν) (hD : ∀ x ∈ Ico 0 T, 0 ≤ D x) (hE : ∀ x ∈ Ico 0 T, 0 ≤ E x) (hE0 : 0 ≤ E 0)
    (hQ : ∀ x ∈ Ico 0 T, 0 ≤ Q x) (hI : TetheredEnstrophyIdentity E E' S D Q ν κ T)
    (hS : StrainL2Bound E S Q C T) (hH : L4L2Holder E Q T) :
    ∀ t ∈ Icc 0 T, E t ≤ max (E 0) (C ^ 2 / (2 * κ ^ 2)) := by
  obtain ⟨hc, hd, hid⟩ := hI
  intro t ht
  refine le_of_forall_gt fun M hM => ?_
  set M' := (max (E 0) (C ^ 2 / (2 * κ ^ 2)) + M) / 2
  have hM' : max (E 0) (C ^ 2 / (2 * κ ^ 2)) < M' := by simp only [M']; linarith
  have hM0 : 0 < M' := lt_of_le_of_lt hE0 (lt_of_le_of_lt (le_max_left _ _) hM')
  have hMC : C ^ 2 / (2 * κ ^ 2) < M' := lt_of_le_of_lt (le_max_right _ _) hM'
  have key : E t ≤ M' := image_le_of_deriv_right_lt_deriv_boundary' (f := E) (f' := E')
    (a := 0) (b := T) (B := fun _ => M') (B' := fun _ => 0) hc hd
    (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hM')) continuousOn_const
    (fun x _ => hasDerivWithinAt_const _ _ _)
    (fun x hx hEx => by
      have h1 := enstrophy_deriv_logistic hκ hν (hD x hx) (hE x hx) (hQ x hx) (hid x hx)
        (hS x hx) (hH x hx)
      rw [hEx] at h1
      have : C ^ 2 < 2 * κ ^ 2 * M' := by
        rw [div_lt_iff₀ (by positivity)] at hMC; linarith
      have : C ^ 2 / κ * M' - 2 * κ * M' ^ 2 = M' / κ * (C ^ 2 - 2 * κ ^ 2 * M') := by
        field_simp
      have : M' / κ * (C ^ 2 - 2 * κ ^ 2 * M') < 0 :=
        mul_neg_of_pos_of_neg (by positivity) (by linarith)
      linarith) ht
  have : M' < M := by simp only [M']; linarith
  linarith

/-- **Z0 part of `HigherNormControl` discharged (tethered system):** the L² vorticity norm
`‖ω‖₂ = √(2E)` is bounded on `[0,T]` by `√(2·max(E(0), C²/(2κ²)))`, uniformly in `T`. -/
theorem tethered_L2_vorticity_bounded {E E' S D Q : ℝ → ℝ} {ν κ C T : ℝ} (hκ : 0 < κ)
    (hν : 0 ≤ ν) (hD : ∀ x ∈ Ico 0 T, 0 ≤ D x) (hE : ∀ x ∈ Ico 0 T, 0 ≤ E x) (hE0 : 0 ≤ E 0)
    (hQ : ∀ x ∈ Ico 0 T, 0 ≤ Q x) (hI : TetheredEnstrophyIdentity E E' S D Q ν κ T)
    (hS : StrainL2Bound E S Q C T) (hH : L4L2Holder E Q T) :
    ∀ t ∈ Icc 0 T, Real.sqrt (2 * E t) ≤ Real.sqrt (2 * max (E 0) (C ^ 2 / (2 * κ ^ 2))) :=
  fun t ht => Real.sqrt_le_sqrt (by
    linarith [tethered_enstrophy_uniform hκ hν hD hE hE0 hQ hI hS hH t ht])

end Frohman.Tether.EnstrophyL2
