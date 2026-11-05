/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman (prepared with assistance from Grok; not a co-author).

# Advancing named assumptions (LOCAL)

* `QuarticWeight` → DEFINITION. The May sources define the Layer-2 functional
  `S_ε = ∫ (½ ω_ε² − (κ/2) ω_ε⁴ ϕ_ε)`, "a quartic term weighted by |ω|²". So in the tethered
  system the scalar weight of 𝔗_F[κ,w,u] at the maximizer is *defined* as `w = ‖ω‖²`
  (`quarticTether`). No source contains a derivation that C1–C3 force this weight; it is a
  definition, not a theorem.
* `ViscousAtMax` → PROVED in line form (`inner_secondDeriv_nonpos_of_isMaxOn`): at a maximum
  of `‖v‖` along a C² line, `⟪v, v''⟫ ≤ −‖v'‖² ≤ 0`; summing over the 3 directions gives
  `ω·Δω ≤ 0` (`viscous_nonpos_at_max`).
* Vortex sup attained on the compact torus → PROVED (`periodic_exists_max`).
-/
import FTVerified.May.Enstrophy
import FTVerified.May.Torus
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Frohman.Tether

open scoped InnerProductSpace RealInnerProductSpace
open Filter Topology SignType

section Quartic
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Tethered-system contribution at the maximizer, with the quartic weight `w = ‖ω‖²`
built into the definition (user's `S_ε`, weight `|ω|²`). -/
noncomputable def quarticTether (κ : ℝ) (u ω : H) : ℝ := 𝔗_F[κ, ‖ω‖ ^ 2, u] ω ω

theorem quarticTether_eq (κ : ℝ) {u ω : H} (h : ⟪u, ω⟫ = 0) :
    quarticTether κ u ω = -κ * ‖ω‖ ^ 4 := by
  unfold quarticTether; rw [frohmanianTether_orth_self κ _ h]; ring

/-- Tether feedback in the tethered system, quartic weight by definition. -/
def TetherFeedbackQuartic (d : MaxPointData) (κ : ℝ) (u ω : H) : Prop :=
  d.tetherTerm = quarticTether κ u ω ∧ ⟪u, ω⟫ = 0 ∧ ‖ω‖ = d.y

theorem tetherFeedback_of_quartic {d : MaxPointData} {κ : ℝ} {u ω : H}
    (h : TetherFeedbackQuartic d κ u ω) : TetherFeedback d κ := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold TetherFeedback; rw [h1, quarticTether_eq κ h2, h3]

/-- `QuarticWeight` is no longer needed: the old hypothesis holds by definition. -/
theorem quarticWeight_of_def {d : MaxPointData} {κ : ℝ} {u ω : H}
    (h : TetherFeedbackQuartic d κ u ω) :
    TetherFeedbackOf d κ (‖ω‖ ^ 2) u ω ∧ QuarticWeight d (‖ω‖ ^ 2) :=
  ⟨⟨h.1, h.2.1, h.2.2⟩, by unfold QuarticWeight; rw [h.2.2]⟩

end Quartic

section MaxPrinciple

/-- Second-derivative necessary condition: at a local max of a differentiable `f : ℝ → ℝ`,
`f'' ≤ 0` (whenever `deriv f` is differentiable there). -/
theorem secondDeriv_nonpos_of_isLocalMax {f : ℝ → ℝ} {x₀ : ℝ} (hf : Differentiable ℝ f)
    (hmax : IsLocalMax f x₀) : deriv (deriv f) x₀ ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  have hd : deriv f x₀ = 0 := hmax.deriv_eq_zero
  have hs := eventually_nhdsWithin_sign_eq_of_deriv_pos (f := deriv f) hpos hd
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hs.and hmax)
  set b := x₀ + δ / 2
  have hab : x₀ < b := by simp [b]; linarith
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f hab hf.continuous.continuousOn
    (fun x _ => (hf x).differentiableWithinAt)
  have hbd : dist b x₀ < δ := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hab)]; simp only [b]; linarith
  have hcd' : dist c x₀ < δ := by
    rw [Real.dist_eq, abs_of_pos (by linarith [hc.1])]
    have := hc.2; simp only [b] at this; linarith
  have hfb := (hball hbd).2
  have hsc := (hball hcd').1
  rw [sign_pos (by linarith [hc.1] : (0:ℝ) < c - x₀)] at hsc
  have hpc : 0 < deriv f c := by
    rcases lt_trichotomy (deriv f c) 0 with h | h | h
    · rw [sign_neg h] at hsc; exact absurd hsc (by decide)
    · rw [h, sign_zero] at hsc; exact absurd hsc (by decide)
    · exact h
  rw [hcd] at hpc
  have : f b - f x₀ ≤ 0 := by linarith
  have : (f b - f x₀) / (b - x₀) ≤ 0 := div_nonpos_of_nonpos_of_nonneg this (by linarith)
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Maximum principle along a line.** If `t₀` maximizes `‖v t‖` and `v` is C² there,
`⟪v, v''⟫ ≤ −‖v'‖² ≤ 0`. -/
theorem inner_secondDeriv_le_of_isMaxOn {v : ℝ → E} {t₀ : ℝ} (hv : Differentiable ℝ v)
    (hv' : Differentiable ℝ (deriv v)) (hmax : ∀ t, ‖v t‖ ≤ ‖v t₀‖) :
    ⟪v t₀, deriv (deriv v) t₀⟫ ≤ -‖deriv v t₀‖ ^ 2 := by
  set φ : ℝ → ℝ := fun t => ⟪v t, v t⟫
  have hφd : ∀ t, HasDerivAt φ (⟪v t, deriv v t⟫ + ⟪deriv v t, v t⟫) t := fun t =>
    (hv t).hasDerivAt.inner ℝ (hv t).hasDerivAt
  have hφ : deriv φ = fun t => 2 * ⟪v t, deriv v t⟫ := by
    funext t; rw [(hφd t).deriv, real_inner_comm (deriv v t)]; ring
  have hφdiff : Differentiable ℝ φ := fun t => (hφd t).differentiableAt
  have hloc : IsLocalMax φ t₀ := Filter.Eventually.of_forall fun t => by
    simp only [φ, real_inner_self_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hmax t) 2
  have h2 := secondDeriv_nonpos_of_isLocalMax hφdiff hloc
  have hdd : HasDerivAt (fun t => 2 * ⟪v t, deriv v t⟫)
      (2 * (⟪v t₀, deriv (deriv v) t₀⟫ + ⟪deriv v t₀, deriv v t₀⟫)) t₀ :=
    ((hv t₀).hasDerivAt.inner ℝ (hv' t₀).hasDerivAt).const_mul 2
  rw [hφ, hdd.deriv, real_inner_self_eq_norm_sq] at h2
  linarith

theorem inner_secondDeriv_nonpos_of_isMaxOn {v : ℝ → E} {t₀ : ℝ} (hv : Differentiable ℝ v)
    (hv' : Differentiable ℝ (deriv v)) (hmax : ∀ t, ‖v t‖ ≤ ‖v t₀‖) :
    ⟪v t₀, deriv (deriv v) t₀⟫ ≤ 0 :=
  (inner_secondDeriv_le_of_isMaxOn hv hv' hmax).trans (by nlinarith [sq_nonneg ‖deriv v t₀‖])

/-- **`ViscousAtMax` proved.** At a global maximizer `x` of `‖ω‖`, with `ν ≥ 0` and `ω` C² along
each coordinate line, `ν Σᵢ ⟪ω, ∂ᵢ²ω⟫ ≤ 0`, so `ViscousAtMax` holds for that data. -/
theorem viscous_nonpos_at_max {ω : Torus.R3 → Torus.R3} {x : Torus.R3} {ν : ℝ} (hν : 0 ≤ ν)
    (hdiff : ∀ i, Differentiable ℝ (fun t : ℝ => ω (x + t • Torus.e i)))
    (hdiff' : ∀ i, Differentiable ℝ (deriv fun t : ℝ => ω (x + t • Torus.e i)))
    (hmax : ∀ z, ‖ω z‖ ≤ ‖ω x‖) :
    ν * ∑ i, ⟪ω x, deriv (deriv fun t : ℝ => ω (x + t • Torus.e i)) 0⟫ ≤ 0 := by
  apply mul_nonpos_of_nonneg_of_nonpos hν
  apply Finset.sum_nonpos
  intro i _
  have h := inner_secondDeriv_nonpos_of_isMaxOn (hdiff i) (hdiff' i) (t₀ := 0)
    (fun t => by simpa using hmax (x + t • Torus.e i))
  simpa using h

theorem viscousAtMax_of_max {d : MaxPointData} {ω : Torus.R3 → Torus.R3} {x : Torus.R3}
    {ν : ℝ} (hν : 0 ≤ ν)
    (hdiff : ∀ i, Differentiable ℝ (fun t : ℝ => ω (x + t • Torus.e i)))
    (hdiff' : ∀ i, Differentiable ℝ (deriv fun t : ℝ => ω (x + t • Torus.e i)))
    (hmax : ∀ z, ‖ω z‖ ≤ ‖ω x‖)
    (hV : d.V = ν * ∑ i, ⟪ω x, deriv (deriv fun t : ℝ => ω (x + t • Torus.e i)) 0⟫) :
    ViscousAtMax d := by
  unfold ViscousAtMax; rw [hV]; exact viscous_nonpos_at_max hν hdiff hdiff' hmax

end MaxPrinciple

section Compact
open Torus

theorem periodic_int_shift {β : Type*} {f : R3 → β} (hf : IsPeriodic f) (i : Fin 3) :
    ∀ (n : ℤ) z, f (z + (n : ℝ) • e i) = f z := by
  intro n
  induction n using Int.induction_on with
  | zero => intro z; simp
  | succ k ih =>
    intro z
    have : z + (((k : ℤ) + 1 : ℤ) : ℝ) • e i = (z + ((k : ℤ) : ℝ) • e i) + e i := by
      push_cast; module
    rw [this, hf, ih]
  | pred k ih =>
    intro z
    rw [← hf, show z + ((-(k:ℤ) - 1 : ℤ) : ℝ) • e i + e i = z + ((-(k:ℤ) : ℤ) : ℝ) • e i by
      push_cast; module, ih]

/-- A continuous `1`-periodic function on `ℝ³` (a function on the compact torus `𝕋³`) attains
its maximum. Applied to `‖ω(t,·)‖` this gives the maximizer `x*` and `y(t) = ‖ω(t,x*)‖`. -/
theorem periodic_exists_max {g : R3 → ℝ} (hg : Continuous g) (hp : IsPeriodic g) :
    ∃ x, ∀ z, g z ≤ g x := by
  set K : Set R3 := WithLp.toLp 2 '' Set.univ.pi fun _ => Set.Icc 0 1
  have hK : IsCompact K := (isCompact_univ_pi fun _ => isCompact_Icc).image
    (PiLp.continuous_toLp 2 _)
  have hne : K.Nonempty := ⟨_, Set.mem_image_of_mem _ (x := fun _ => 0) (by intro i _; simp)⟩
  obtain ⟨x, -, hx⟩ := hK.exists_isMaxOn hne hg.continuousOn
  refine ⟨x, fun z => ?_⟩
  set y : R3 := z - ∑ i, ((⌊z i⌋ : ℤ) : ℝ) • e i
  have hyK : y ∈ K := by
    refine ⟨WithLp.ofLp y, fun j _ => ?_, by simp⟩
    have : y j = z j - ⌊z j⌋ := by
      simp [y, Fin.sum_univ_three]
      fin_cases j <;> simp
    constructor
    · show 0 ≤ y j; rw [this]; linarith [Int.floor_le (z j)]
    · show y j ≤ 1; rw [this]; linarith [Int.lt_floor_add_one (z j)]
  have hz : z = y + ((⌊z 0⌋ : ℤ) : ℝ) • e 0 + ((⌊z 1⌋ : ℤ) : ℝ) • e 1
      + ((⌊z 2⌋ : ℤ) : ℝ) • e 2 := by
    simp only [y, Fin.sum_univ_three]; abel
  have : g z = g y := by
    rw [hz, periodic_int_shift hp, periodic_int_shift hp, periodic_int_shift hp]
  rw [this]; exact hx hyK

end Compact
end Frohman.Tether
