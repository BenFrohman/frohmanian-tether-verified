-- SPDX-FileCopyrightText: 2026 Benjamin Stanley Frohman
-- SPDX-License-Identifier: Apache-2.0
/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman (prepared with assistance from Grok; not a co-author).

# Log-loss stretching (LOCAL) — replaces the too-strong `StretchingCZ`

`StretchingCZ` (`ω·Sω ≤ C y³`) is FALSE as an L∞ estimate (CZ operators are unbounded on L∞)
and is now deprecated. It is replaced by two TRUE statements:

* `StretchingByStrain`: `ω·Sω ≤ ‖S‖∞ |ω|²` at the maximizer (Cauchy–Schwarz / operator norm).
* `BKMLogInequality`: `‖S‖∞ ≤ ‖∇u‖∞ ≤ C (1 + ‖ω‖_{L²} + ‖ω‖_{L∞} log(e + ‖ω‖_{Hˢ}))`, s > 3/2,
  on `𝕋³`. Literature: Beale–Kato–Majda, Comm. Math. Phys. 94 (1984) 61–66, the logarithmic
  Sobolev inequality in the proof of their Thm 1 (`‖∇u‖∞ ≤ C(1+‖ω‖₂+‖ω‖∞(1+log⁺‖u‖_{H^{s+1}}))`,
  using `1+log⁺ z ≤ 2 log(e+z)`); Brezis–Gallouët, Nonlinear Anal. 4 (1980) 677–681;
  Kozono–Taniuchi, Comm. Math. Phys. 214 (2000) 191–200 (BMO refinement). Here `Z ≥ 0` is
  (a bound for) `‖ω‖_{Hˢ}` and `Z0` for `‖ω‖_{L²}`.

Result (TETHERED system, quartic 𝔗_F feedback `−κ y⁴`):
  `y' ≤ C(1+Z0) y + C log(e+Z) y² − κ'' y³`,  κ'' = κ/2 − C_abs.
Cubic damping beats `y² log` once `κ'' y > C log(e+Z)`: with `Z ≤ Zb`, `Z0 ≤ Z0b` on `[0,T]`,
`y ≤ Y* = max(y₀, B/κ'' + √(A/κ''))`, `A = C(1+Z0b)`, `B = C log(e+Zb)`.

The price: an a priori `Hˢ` bound `HigherNormControl`. Since `Hˢ ⊂ L∞` (s>3/2), that bound by
itself already controls `y`; so the hypothesis is CIRCULAR for the regularity question.
-/
import FTVerified.May.Final

namespace Frohman.Tether

/-- Pointwise data at the maximizer plus the strain sup and the two norms used by BKM. -/
structure LogLossData extends MaxPointData where
  Sinf : ℝ  -- ‖S(t)‖_∞
  Z0 : ℝ    -- ‖ω(t)‖_{L²}
  Z : ℝ     -- ‖ω(t)‖_{Hˢ}, s > 3/2

/-- TRUE: `ω·Sω ≤ ‖S‖∞ |ω|²` at the maximizer. -/
def StretchingByStrain (d : LogLossData) : Prop := d.St ≤ d.Sinf * d.y ^ 2

/-- TRUE (BKM 1984 log inequality / Brezis–Gallouët / Kozono–Taniuchi 2000), see header. -/
def BKMLogInequality (d : LogLossData) (C : ℝ) : Prop :=
  d.Sinf ≤ C * (1 + d.Z0 + d.y * Real.log (Real.exp 1 + d.Z))

/-- New comparison field `A y + B y² − κ'' y³`. -/
def logField (A B κ'' y : ℝ) : ℝ := A * y + B * y ^ 2 - κ'' * y ^ 3

/-- **Pointwise log-loss inequality (tethered system).** -/
theorem tether_pointwise_logloss {d : LogLossData} {C κ Cabs : ℝ} (hκ : 0 < κ)
    (hy : 0 < d.y) (hE : EnergyIdentity d.toMaxPointData) (hS : StretchingByStrain d)
    (hB : BKMLogInequality d C) (hV : ViscousAtMax d.toMaxPointData)
    (hT : TetherFeedback d.toMaxPointData κ) (hX : CrossControlled d.toMaxPointData κ Cabs) :
    d.y' ≤ logField (C * (1 + d.Z0)) (C * Real.log (Real.exp 1 + d.Z)) (κ / 2 - Cabs) d.y := by
  unfold EnergyIdentity StretchingByStrain BKMLogInequality ViscousAtMax TetherFeedback
    CrossControlled logField at *
  have hY := young_kappa_quarter (κ := κ) (a := d.y ^ 2) (b := d.b) hκ
  have h2 : 2 * d.y ^ 2 * d.b ≤ κ / 2 * (d.y ^ 2) ^ 2 + Cabs * d.y ^ 4 := by nlinarith
  have hSt : d.St ≤ C * (1 + d.Z0 + d.y * Real.log (Real.exp 1 + d.Z)) * d.y ^ 2 :=
    hS.trans (mul_le_mul_of_nonneg_right hB (by positivity))
  have key : d.y * d.y' ≤ d.y * (C * (1 + d.Z0) * d.y + C * Real.log (Real.exp 1 + d.Z) *
      d.y ^ 2 - (κ / 2 - Cabs) * d.y ^ 3) := by nlinarith
  exact le_of_mul_le_mul_left key hy

/-- Explicit threshold `Y = B/κ'' + √(A/κ'')`. -/
noncomputable def logThreshold (A B κ'' : ℝ) : ℝ := B / κ'' + Real.sqrt (A / κ'')

/-- **Cubic damping dominates `y² log`:** above the threshold the field is negative. -/
theorem logField_neg_above {A B κ'' y : ℝ} (hκ : 0 < κ'') (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hy : logThreshold A B κ'' < y) : logField A B κ'' y < 0 := by
  unfold logThreshold logField at *
  have hs0 := Real.sqrt_nonneg (A / κ'')
  have hss := Real.sq_sqrt (div_nonneg hA hκ.le)
  have hBk : 0 ≤ B / κ'' := div_nonneg hB hκ.le
  have hy0 : 0 < y := by linarith
  have e1 : κ'' * (B / κ'') = B := by field_simp
  have e2 : κ'' * (A / κ'') = A := by field_simp
  -- κ'' y² > B y + A
  have h1 : κ'' * y > B + κ'' * Real.sqrt (A / κ'') := by nlinarith
  have h2 : κ'' * Real.sqrt (A / κ'') * y ≥ A := by
    have : Real.sqrt (A / κ'') * y ≥ Real.sqrt (A / κ'') * Real.sqrt (A / κ'') :=
      mul_le_mul_of_nonneg_left (by linarith) hs0
    nlinarith
  have : κ'' * y * y > B * y + A := by nlinarith
  nlinarith

theorem logThreshold_nonneg {A B κ'' : ℝ} (hκ : 0 < κ'') (hB : 0 ≤ B) :
    0 ≤ logThreshold A B κ'' :=
  add_nonneg (div_nonneg hB hκ.le) (Real.sqrt_nonneg _)

/-- **New comparison theorem (log-loss).** If on `[0,T)`
`y' ≤ C(1+Z0) y + C log(e+Z) y² − κ'' y³` with `0 ≤ Z0 ≤ Z0b`, `0 ≤ Z ≤ Zb`, `C ≥ 0`, then
`y ≤ Y* = max(y₀, logThreshold (C(1+Z0b)) (C log(e+Zb)) κ'')` on `[0,T]`. -/
theorem comparison_bound_logloss {y y' Z Z0 : ℝ → ℝ} {C κ'' T Zb Z0b : ℝ} (hκ : 0 < κ'')
    (hC : 0 ≤ C) (hZb : 0 ≤ Zb) (hZ0b : 0 ≤ Z0b) (hy0 : 0 ≤ y 0)
    (hc : ContinuousOn y (Set.Icc 0 T))
    (hd : ∀ x ∈ Set.Ico 0 T, HasDerivWithinAt y (y' x) (Set.Ici x) x)
    (hZ : ∀ x ∈ Set.Ico 0 T, 0 ≤ Z x ∧ Z x ≤ Zb) (hZ0 : ∀ x ∈ Set.Ico 0 T, Z0 x ≤ Z0b)
    (hineq : ∀ x ∈ Set.Ico 0 T,
      y' x ≤ logField (C * (1 + Z0 x)) (C * Real.log (Real.exp 1 + Z x)) κ'' (y x)) :
    ∀ t ∈ Set.Icc 0 T, y t ≤
      max (y 0) (logThreshold (C * (1 + Z0b)) (C * Real.log (Real.exp 1 + Zb)) κ'') := by
  set Y := logThreshold (C * (1 + Z0b)) (C * Real.log (Real.exp 1 + Zb)) κ''
  have he : (1:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hlogb : 0 ≤ Real.log (Real.exp 1 + Zb) := Real.log_nonneg (by linarith)
  have hA : 0 ≤ C * (1 + Z0b) := mul_nonneg hC (by linarith)
  have hB : 0 ≤ C * Real.log (Real.exp 1 + Zb) := mul_nonneg hC hlogb
  intro t ht
  refine le_of_forall_gt fun M hM => ?_
  have hM' : max (y 0) Y < (max (y 0) Y + M) / 2 := by linarith
  set N := (max (y 0) Y + M) / 2
  have hN0 : 0 < N := lt_of_le_of_lt (logThreshold_nonneg hκ hB |>.trans (le_max_right _ _)) hM'
  have hNY : Y < N := lt_of_le_of_lt (le_max_right _ _) hM'
  have key := image_le_of_deriv_right_lt_deriv_boundary' (f := y) (f' := y')
    (a := 0) (b := T) (B := fun _ => N) (B' := fun _ => 0) hc hd
    (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hM')) continuousOn_const
    (fun x _ => hasDerivWithinAt_const _ _ _)
    (fun x hx hyx => by
      have h1 := hineq x hx
      rw [hyx] at h1
      have hlx : Real.log (Real.exp 1 + Z x) ≤ Real.log (Real.exp 1 + Zb) :=
        Real.log_le_log (by linarith [(hZ x hx).1]) (by linarith [(hZ x hx).2])
      have hneg := logField_neg_above hκ hA hB hNY
      unfold logField at h1 hneg
      have a1 : C * (1 + Z0 x) * N ≤ C * (1 + Z0b) * N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith [hZ0 x hx]) hC) hN0.le
      have a2 : C * Real.log (Real.exp 1 + Z x) * N ^ 2 ≤ C * Real.log (Real.exp 1 + Zb) * N ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlx hC) (by positivity)
      linarith) ht
  have key' : y t ≤ N := key
  have hNM : N < M := by simp only [N]; linarith
  linarith

/-- **Exact remaining hypothesis (higher norm).** On every smooth interval the `Hˢ` (s>3/2) and
`L²` vorticity norms are bounded. CIRCULAR for regularity: by `Hˢ ⊂ L∞` this alone bounds `y`. -/
def HigherNormControl (Z Z0 : ℝ → ℝ) (SmoothOn : ℝ → Prop) : Prop :=
  ∀ T, 0 < T → (∀ T' < T, SmoothOn T') → ∃ Zb Z0b, 0 ≤ Zb ∧ 0 ≤ Z0b ∧
    ∀ x ∈ Set.Ico 0 T, (0 ≤ Z x ∧ Z x ≤ Zb) ∧ Z0 x ≤ Z0b

/-- Solution-level log-loss tethered inequality (replaces `NSTetherEnstrophyInequality`). -/
def NSTetherLogInequality (s : NSTetherSolution) (Z Z0 : ℝ → ℝ) (C κ'' : ℝ) : Prop :=
  ∀ T, s.SmoothOn T →
    ContinuousOn s.y (Set.Icc 0 T) ∧
    (∀ x ∈ Set.Ico 0 T, HasDerivWithinAt s.y (s.y' x) (Set.Ici x) x) ∧
    (∀ x ∈ Set.Ico 0 T,
      s.y' x ≤ logField (C * (1 + Z0 x)) (C * Real.log (Real.exp 1 + Z x)) κ'' (s.y x))

/-- **global_regularity_logloss** (tethered system), conditional on the log-loss inequality,
`HigherNormControl`, BKM and local continuation. -/
theorem global_regularity_logloss {s : NSTetherSolution} {Z Z0 : ℝ → ℝ} {C κ'' : ℝ}
    (hκ : 0 < κ'') (hC : 0 ≤ C) (hI : NSTetherLogInequality s Z Z0 C κ'')
    (hH : HigherNormControl Z Z0 s.SmoothOn) (hB : BKMContinuation s)
    (hL : LocalContinuation s) : GloballySmooth s := by
  by_contra hns
  simp only [GloballySmooth, not_forall] at hns
  obtain ⟨T0, hT0⟩ := hns
  set A := {T : ℝ | s.SmoothOn T}
  have hbdd : BddAbove A := ⟨T0, fun T hT => by
    by_contra h; exact hT0 (s.smoothOn_mono (le_of_lt (not_le.1 h)) hT)⟩
  have h0 : (0 : ℝ) ∈ A := s.smoothOn_zero
  set σ := sSup A
  have hσ0 : 0 ≤ σ := le_csSup hbdd h0
  have hpre : ∀ T' < σ, s.SmoothOn T' := by
    intro T' hT'
    obtain ⟨b, hb, hlt⟩ := exists_lt_of_lt_csSup ⟨0, h0⟩ hT'
    exact s.smoothOn_mono hlt.le hb
  have hσ : s.SmoothOn σ := by
    rcases hσ0.lt_or_eq with hpos | heq
    · refine hB σ hpos hpre ?_
      obtain ⟨Zb, Z0b, hZb, hZ0b, hb⟩ := hH σ hpos hpre
      refine ⟨max (s.y 0) (logThreshold (C * (1 + Z0b)) (C * Real.log (Real.exp 1 + Zb)) κ''),
        fun t ht => ?_⟩
      obtain ⟨hc, hd, hi⟩ := hI t (hpre t ht.2)
      have sub : ∀ x ∈ Set.Ico 0 t, x ∈ Set.Ico 0 σ := fun x hx => ⟨hx.1, hx.2.trans ht.2⟩
      exact comparison_bound_logloss hκ hC hZb hZ0b s.y_zero_nonneg hc hd
        (fun x hx => (hb x (sub x hx)).1) (fun x hx => (hb x (sub x hx)).2) hi t ⟨ht.1, le_rfl⟩
    · rw [← heq]; exact s.smoothOn_zero
  obtain ⟨δ, hδ, hsδ⟩ := hL σ hσ
  have := le_csSup hbdd hsδ
  linarith

end Frohman.Tether
