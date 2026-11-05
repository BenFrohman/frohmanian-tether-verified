/-
Copyright (c) 2026 Benjamin Frohman. All rights reserved.
Released under Apache 2.0 license.

# Next rung for the TETHERED system: Lᵖ, H¹ (palinstrophy), and the Hˢ part of
# `HigherNormControl`

Model (stated precisely, see README "Model caveat"): the quartic tether enters the VORTICITY
equation as the Leray-projected field `−κ P(|ω|²ω)`:
  `ω_t + u·∇ω − ω·∇u = νΔω − κ P(|ω|²ω)`.
Since `ω` and `Δω` are divergence-free and `P` is L²-self-adjoint,
  `∫ ω·P(|ω|²ω) = ∫|ω|⁴`  (L² level, used in EnstrophyL2) and
  `∫ ∇ω:∇P(|ω|²ω) = ∫ ∇ω:∇(|ω|²ω) = ∫ |ω|²|∇ω|² + ½|∇|ω|²|² ≥ 0` (H¹ level, `tether_H1_density_nonneg`).
NOTE: this is NOT literally `curl` of the velocity forcing `quarticTether` in Torus.lean;
the two formulations must be reconciled before any public claim.

Plain Navier–Stokes: `κ = 0`. The H¹ step below then needs the L² bound as an INPUT, which
plain NS does not supply (it is the classical open enstrophy bound).
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.ODE.Gronwall
import FTVerified.May.LogLoss

namespace Frohman.Tether.PalinstrophyH1

open Set Finset

/-! ## H¹ tether density: pointwise sign-definite (pure algebra, proved) -/

/-- `∂_j(|ω|²ω_i) = |ω|² D_ij + 2 ω_i (∑_k ω_k D_kj)` with `D_ij = ∂_j ω_i`. -/
def tetherGrad (ω : Fin 3 → ℝ) (D : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  (∑ k, ω k ^ 2) * D i j + 2 * ω i * ∑ k, ω k * D k j

/-- **Tether H¹ density** `∇ω : ∇(|ω|²ω) = |ω|²|∇ω|² + ½|∇|ω|²|²`. -/
theorem tether_H1_density_eq (ω : Fin 3 → ℝ) (D : Fin 3 → Fin 3 → ℝ) :
    ∑ i, ∑ j, D i j * tetherGrad ω D i j
      = (∑ k, ω k ^ 2) * (∑ i, ∑ j, D i j ^ 2)
        + (1 / 2) * ∑ j, (2 * ∑ k, ω k * D k j) ^ 2 := by
  simp only [tetherGrad, Fin.sum_univ_three]; ring

/-- It is `≥ 0` for every orientation of `ω` relative to `∇ω` (no alignment needed). -/
theorem tether_H1_density_nonneg (ω : Fin 3 → ℝ) (D : Fin 3 → Fin 3 → ℝ) :
    0 ≤ ∑ i, ∑ j, D i j * tetherGrad ω D i j := by
  rw [tether_H1_density_eq]; positivity

/-! ## Lᵖ rung: scalar absorption (proved); constants blow up as p → ∞ -/

/-- `C X^{p+1} − κ X^{p+2} < 0` once `X > C/κ`: tether `∫|ω|^{p+2}` beats Hölder–CZ stretching
`C_p‖ω‖_{p+2}^{p+1}`. Threshold `C_p/κ` with `C_p ~ p` (CZ), so no uniform L∞ limit. -/
theorem lp_absorb {C κ X : ℝ} (n : ℕ) (hκ : 0 < κ) (hX0 : 0 < X) (hX : C / κ < X) :
    C * X ^ (n + 1) - κ * X ^ (n + 2) < 0 := by
  have hC : C < κ * X := by rwa [div_lt_iff₀ hκ, mul_comm] at hX
  have : C * X ^ (n + 1) - κ * X ^ (n + 2) = X ^ (n + 1) * (C - κ * X) := by ring
  rw [this]; exact mul_neg_of_pos_of_neg (by positivity) (by linarith)

/-! ## H¹ rung: Young (4/3, 4) and linear Grönwall (proved) -/

/-- AM–GM: `4 b w³ ≤ 3 w⁴ + b⁴` for `b, w ≥ 0`. -/
theorem amgm_four (b w : ℝ) (hb : 0 ≤ b) (hw : 0 ≤ w) : 4 * b * w ^ 3 ≤ 3 * w ^ 4 + b ^ 4 := by
  have : 3 * w ^ 4 + b ^ 4 - 4 * b * w ^ 3 = (w - b) ^ 2 * (3 * w ^ 2 + 2 * w * b + b ^ 2) := by
    ring
  nlinarith [mul_nonneg (sq_nonneg (w - b)) (by positivity : 0 ≤ 3 * w ^ 2 + 2 * w * b + b ^ 2)]

/-- Young: `A x w³ ≤ (ν/2) w⁴ + (27 A⁴ /(32 ν³)) x⁴`. -/
theorem young_43 {A ν x w : ℝ} (hA : 0 ≤ A) (hν : 0 < ν) (hx : 0 ≤ x) (hw : 0 ≤ w) :
    A * x * w ^ 3 ≤ ν / 2 * w ^ 4 + 27 * A ^ 4 / (32 * ν ^ 3) * x ^ 4 := by
  set lam := 2 * ν / 3 with hl
  have hlam : 0 < lam := by positivity
  have h := amgm_four (A * x / lam) w (by positivity) hw
  have e1 : A * x * w ^ 3 = lam / 4 * (4 * (A * x / lam) * w ^ 3) := by field_simp
  have e2 : lam / 4 * (3 * w ^ 4 + (A * x / lam) ^ 4)
      = ν / 2 * w ^ 4 + 27 * A ^ 4 / (32 * ν ^ 3) * x ^ 4 := by
    rw [hl]; field_simp; ring
  rw [e1, ← e2]; exact mul_le_mul_of_nonneg_left h (by positivity)

/-- Cited: H¹ (palinstrophy) identity for the projected tethered vorticity equation on `T³`:
`P' = 2(−ν L² − κ J + N)`, `P = G² = ‖∇ω‖₂²`, `L = ‖Δω‖₂`, `J = ∫∇ω:∇(|ω|²ω) ≥ 0`,
`N = ∫Δω·(u·∇ω − ω·∇u)` (multiply by `−Δω`, integrate by parts; Majda–Bertozzi 2002 §3.2). -/
def TetheredH1Identity (P P' L J N : ℝ → ℝ) (ν κ T : ℝ) : Prop :=
  ContinuousOn P (Icc 0 T) ∧
  (∀ x ∈ Ico 0 T, HasDerivWithinAt P (P' x) (Ici x) x) ∧
  (∀ x ∈ Ico 0 T, P' x = 2 * (-(ν * L x ^ 2) - κ * J x + N x))

/-- Cited: nonlinear H¹ bound `|N| ≤ A √G L^{3/2}`, `A = C·‖ω‖₂` (Hölder, Sobolev
`‖u‖₆+‖∇u‖₆ ≲ ‖ω‖₂+‖∇ω‖₂`, Gagliardo–Nirenberg `‖f‖₃ ≤ C‖f‖₂^{1/2}‖∇f‖₂^{1/2}`, and
`‖∇ω‖₂² ≤ ‖ω‖₂‖Δω‖₂`). With `A` from the uniform L² bound (EnstrophyL2), `A` is a constant. -/
def NonlinH1Bound (P L N : ℝ → ℝ) (A T : ℝ) : Prop :=
  ∀ x ∈ Ico 0 T, N x ≤ A * Real.sqrt (Real.sqrt (P x)) * Real.sqrt (L x) ^ 3

/-- Pointwise: `P' ≤ (27 A⁴/(16 ν³)) P`. -/
theorem palin_deriv_le {p p' l j n A ν κ : ℝ} (hA : 0 ≤ A) (hν : 0 < ν) (hκ : 0 ≤ κ)
    (hp : 0 ≤ p) (hl : 0 ≤ l) (hj : 0 ≤ j) (hid : p' = 2 * (-(ν * l ^ 2) - κ * j + n))
    (hn : n ≤ A * Real.sqrt (Real.sqrt p) * Real.sqrt l ^ 3) :
    p' ≤ 27 * A ^ 4 / (16 * ν ^ 3) * p := by
  have hy := young_43 hA hν (Real.sqrt_nonneg (Real.sqrt p)) (Real.sqrt_nonneg l)
  have h4x : Real.sqrt (Real.sqrt p) ^ 4 = p := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt hp]
  have h4w : Real.sqrt l ^ 4 = l ^ 2 := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hl]
  rw [h4x, h4w] at hy
  have : 27 * A ^ 4 / (16 * ν ^ 3) * p = 2 * (27 * A ^ 4 / (32 * ν ^ 3) * p) := by ring
  nlinarith [mul_nonneg hκ hj]

/-- **Tethered palinstrophy Grönwall bound:** `‖∇ω(t)‖₂² ≤ ‖∇ω(0)‖₂² e^{Kt}`,
`K = 27A⁴/(16ν³)` — finite on every finite interval, never blows up. -/
theorem tethered_palinstrophy_gronwall {P P' L J N : ℝ → ℝ} {A ν κ T : ℝ} (hA : 0 ≤ A)
    (hν : 0 < ν) (hκ : 0 ≤ κ) (hP : ∀ x ∈ Ico 0 T, 0 ≤ P x) (hL : ∀ x ∈ Ico 0 T, 0 ≤ L x)
    (hJ : ∀ x ∈ Ico 0 T, 0 ≤ J x) (hI : TetheredH1Identity P P' L J N ν κ T)
    (hN : NonlinH1Bound P L N A T) :
    ∀ t ∈ Icc 0 T, P t ≤ P 0 * Real.exp (27 * A ^ 4 / (16 * ν ^ 3) * t) := by
  obtain ⟨hc, hd, hid⟩ := hI
  intro t ht
  have h := le_gronwallBound_of_liminf_deriv_right_le (f := P) (f' := P') (δ := P 0)
    (K := 27 * A ^ 4 / (16 * ν ^ 3)) (ε := 0) hc
    (fun x hx r hr => by
      simpa [slope_def_field, div_eq_inv_mul] using (hd x hx).liminf_right_slope_le hr)
    le_rfl
    (fun x hx => by
      have := palin_deriv_le hA hν hκ (hP x hx) (hL x hx) (hJ x hx) (hid x hx) (hN x hx)
      linarith) t ht
  rwa [gronwallBound_ε0, sub_zero] at h

/-! ## Hˢ part of `HigherNormControl` -/

/-- Cited / standard (parabolic bootstrap): on `T³`, a bound for `‖ω‖_{H¹}` on `[0,T)` yields a
bound for `Z = ‖ω‖_{H²}` (s = 2 > 3/2) there. For plain NS this is classical (u ∈ L∞H² ⇒
smooth; Temam 1995, Constantin–Foias 1988). For the projected cubic tether the extra term obeys
`|∫∇Δω·∇P(|ω|²ω)| ≤ ‖∇Δω‖₂‖ω‖∞²‖∇ω‖₂` with `‖ω‖∞ ≤ C‖ω‖_{H¹}^{1/2}‖ω‖_{H²}^{1/2}`, which is
again linear in `‖ω‖_{H²}²` after Young — a standard estimate, NOT a literature citation for
this modified system. -/
def H1ToHsBootstrap (G Z : ℝ → ℝ) : Prop :=
  ∀ T : ℝ, 0 < T → ∀ Gb : ℝ, (∀ x ∈ Ico (0:ℝ) T, G x ≤ Gb) →
    ∃ Zb : ℝ, 0 ≤ Zb ∧ ∀ x ∈ Ico (0:ℝ) T, 0 ≤ Z x ∧ Z x ≤ Zb

/-- **`HigherNormControl` discharged for the tethered system**, given per-interval L² and H¹
bounds (EnstrophyL2 + `tethered_palinstrophy_gronwall`) and the bootstrap. -/
theorem higherNormControl_tethered {Z Z0 G : ℝ → ℝ} {SmoothOn : ℝ → Prop}
    (hL2 : ∃ Z0b, 0 ≤ Z0b ∧ ∀ x, 0 ≤ x → Z0 x ≤ Z0b)
    (hH1 : ∀ T, 0 < T → (∀ T' < T, SmoothOn T') → ∃ Gb, ∀ x ∈ Ico 0 T, G x ≤ Gb)
    (hB : H1ToHsBootstrap G Z) : HigherNormControl Z Z0 SmoothOn := by
  intro T hT hS
  obtain ⟨Z0b, hZ0b, hz⟩ := hL2
  obtain ⟨Gb, hG⟩ := hH1 T hT hS
  obtain ⟨Zb, hZb, hz2⟩ := hB T hT Gb hG
  exact ⟨Zb, Z0b, hZb, hZ0b, fun x hx => ⟨hz2 x hx, hz x hx.1⟩⟩

end Frohman.Tether.PalinstrophyH1
