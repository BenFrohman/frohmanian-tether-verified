/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman (prepared with assistance from Grok; not a co-author).

# Riccati comparison: plain blow-up vs. tethered ceiling (the author's comparison ODE)

The author's comparison ODE (Full Living Document, PASS 2, 2026-05-21, `history/2026-05-21_PASS2_C3/`)
is `y' = C y² − κ'' y³`, with bound `y ≤ max(y(0), C/κ'')` (`Layer2.comparison_bound`).
Dropping the tether (`κ'' = 0`) leaves `y' = C y²`, whose solution
`y(t) = y₀/(1 − C y₀ t)` is unbounded before `T* = 1/(C y₀)` (`riccati_blowup`).
This is ODE comparison only; it says nothing about plain Navier–Stokes solutions.
-/
import FTVerified.May.Layer2
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace Frohman.Tether.Riccati

/-- Explicit solution of the untethered comparison ODE `y' = C y²`. -/
noncomputable def ricSol (C y₀ t : ℝ) : ℝ := y₀ / (1 - C * y₀ * t)

theorem ricSol_zero (C y₀ : ℝ) : ricSol C y₀ 0 = y₀ := by simp [ricSol]

/-- `ricSol` solves `y' = C y²` wherever `1 − C y₀ t ≠ 0`. -/
theorem ricSol_hasDerivAt (C y₀ t : ℝ) (h : 1 - C * y₀ * t ≠ 0) :
    HasDerivAt (ricSol C y₀) (C * ricSol C y₀ t ^ 2) t := by
  have hd : HasDerivAt (fun s => 1 - C * y₀ * s) (-(C * y₀)) t := by
    simpa using ((hasDerivAt_id t).const_mul (C * y₀)).const_sub 1
  have := (HasDerivAt.inv hd h).const_mul y₀
  have hf : ricSol C y₀ = fun s => y₀ * (1 - C * y₀ * s)⁻¹ := by
    funext s; simp [ricSol, div_eq_mul_inv]
  rw [hf]; convert this using 1
  field_simp

/-- **Finite-time blow-up of the untethered comparison ODE.** For `C > 0`, `y₀ > 0`, the solution
exceeds every bound on `[0, 1/(C y₀))`. -/
theorem riccati_blowup {C y₀ : ℝ} (hC : 0 < C) (hy : 0 < y₀) (M : ℝ) :
    ∃ t, 0 ≤ t ∧ t < 1 / (C * y₀) ∧ M < ricSol C y₀ t := by
  set N := max M y₀ + 1
  have hN : 0 < N := by have := le_max_right M y₀; simp only [N]; linarith
  have hyN : y₀ < N := by have := le_max_right M y₀; simp only [N]; linarith
  have hMN : M < N := by have := le_max_left M y₀; simp only [N]; linarith
  have hCy : 0 < C * y₀ := mul_pos hC hy
  refine ⟨(1 - y₀ / N) / (C * y₀), ?_, ?_, ?_⟩
  · apply div_nonneg _ hCy.le
    rw [sub_nonneg, div_le_one hN]; exact hyN.le
  · rw [div_lt_div_iff_of_pos_right hCy]; have := div_pos hy hN; linarith
  · have : 1 - C * y₀ * ((1 - y₀ / N) / (C * y₀)) = y₀ / N := by field_simp; ring
    have e : y₀ / (y₀ / N) = N := by field_simp
    rw [ricSol, this, e]; exact hMN

/-- **Tethered ceiling** (the author's form): `y' ≤ C y² − κ'' y³`, `κ'' > 0` ⇒
`y ≤ max(y(0), C/κ'')`. Restatement of `Layer2.comparison_bound`. -/
theorem tethered_ceiling {y y' : ℝ → ℝ} {C κ'' T : ℝ} (hκ : 0 < κ'')
    (hy0 : 0 ≤ y 0) (hc : ContinuousOn y (Set.Icc 0 T))
    (hd : ∀ x ∈ Set.Ico 0 T, HasDerivWithinAt y (y' x) (Set.Ici x) x)
    (hineq : ∀ x ∈ Set.Ico 0 T, y' x ≤ comparisonField C κ'' (y x)) :
    ∀ t ∈ Set.Icc 0 T, y t ≤ max (y 0) (C / κ'') :=
  comparison_bound hκ hy0 hc hd hineq

end Frohman.Tether.Riccati
