/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FTVerified.Sdiff.SymplecticTether

/-!
# C2/C3 obstruction audit (2026-11-04)

The metriplectic correction changes `dM/dt` by exactly `B ω M H`. C2
(`DegenerateWRTKineticEnergy`) is *by definition* `∀ F ω, B ω F H = 0`, so:

* `flow_contribution_zero_of_C2`: for ANY kernel `B` (symmetric or not, any sign, any
  projection) C2 kills the tether contribution to every functional `M`. Symmetry is not
  even needed; it is only needed to move `H` to the left slot (`tetherKernel_left_H_zero`).
* `bilin_kernel_of_nonpos_of_self_zero`: for a symmetric negative-semidefinite form (C3),
  mere energy conservation `B(H,H) = 0` already forces `B(M,H) = 0` for all `M`
  (Cauchy–Schwarz for semidefinite forms). So weakening C2 to energy conservation does
  not escape while C3 + symmetry are kept.
* `energy_conservation_not_C2`: without symmetry, `B(H,H) = 0` does not force
  `B(M,H) = 0` (antisymmetric example). But an antisymmetric part has zero diagonal
  (`antisymmetric_correction_diagonal_zero`, `nonSymmetricTetherKernel_diag`), so it
  is a reversible drift, not a signed damping, and it modifies the Euler flow of `H`
  (it is a different equation from unmodified Navier–Stokes).

No Clay claim. Open hypotheses elsewhere stay named (`FrohmanianTetherRate`,
`FrohmanianTetherClosingBound`, `KineticEnergyCurlIdentification`, ...).
-/

@[expose] public section

namespace FrohmanianTether.ObstructionAudit

open InnerProductSpace NavierStokes3D ArnoldGeometric MeasureTheory ForMathlib FrohmanianTether

/-- C2 alone (no symmetry) kills the tether's contribution `B ω M H` to `dM/dt`.
This is the definition of C2 read back (`hC2 M ω`); it is not cited as evidence for any paper claim.
The paper's energy-budget refutation is `energy_damping_iff_not_degenerate`. -/
public theorem flow_contribution_zero_of_C2
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (hC2 : DegenerateWRTKineticEnergy B) (ω : CoadjointOrbit) (M : Functional) :
    B ω M KineticEnergyHamiltonian = 0 :=
  hC2 M ω

/-- Symmetric + negative semidefinite (C3) + `B(h,h) = 0` ⇒ `B(m,h) = 0` for all `m`. -/
public theorem bilin_kernel_of_nonpos_of_self_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V)
    (hsym : ∀ x y, B x y = B y x) (hneg : ∀ x, B x x ≤ 0)
    (h : V) (hh : B h h = 0) (m : V) : B m h = 0 := by
  by_contra hb
  set b := B m h
  set a := B m m
  have key : ∀ t : ℝ, a + 2 * t * b ≤ 0 := by
    intro t
    have := hneg (m + t • h)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul] at this
    rw [hsym h m, hh] at this
    linarith
  have := key ((1 - a) / (2 * b))
  have hb2 : (2 * b) ≠ 0 := by positivity
  rw [show 2 * ((1 - a) / (2 * b)) * b = 1 - a by field_simp] at this
  linarith

/-- **Damping is exactly the failure of degeneracy (C2).** For a symmetric bilinear form `B` with
`B(x,x) ≤ 0` for every `x` (C3) and any vector `h` (standing for `δH`), the energy term `B(h,h)` is
strictly negative iff `B(m,h) ≠ 0` for some `m`. Hence a tether obeying C2 (`B(m,h) = 0` for all
`m`) cannot damp the energy, and conversely any damping tether violates C2. The nontrivial direction
is `bilin_kernel_of_nonpos_of_self_zero` (Cauchy–Schwarz for semidefinite forms); the statement is not
a restatement of C2, which appears in it only as the right-hand side. -/
public theorem energy_damping_iff_not_degenerate
    {V : Type*} [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V)
    (hsym : ∀ x y, B x y = B y x) (hneg : ∀ x, B x x ≤ 0) (h : V) :
    B h h < 0 ↔ ∃ m, B m h ≠ 0 := by
  constructor
  · intro hlt
    exact ⟨h, ne_of_lt hlt⟩
  · rintro ⟨m, hm⟩
    rcases lt_or_eq_of_le (hneg h) with hlt | heq
    · exact hlt
    · exact absurd (bilin_kernel_of_nonpos_of_self_zero B hsym hneg h heq m) hm

/-- Without symmetry, energy conservation `B(h,h)=0` does not give `B(m,h)=0`. -/
public theorem energy_conservation_not_C2 :
    ∃ (B : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ) (h m : Fin 2 → ℝ),
      B h h = 0 ∧ B m h ≠ 0 ∧ ∀ x, B x x = 0 := by
  refine ⟨fun x y => x 0 * y 1 - x 1 * y 0, ![1, 0], ![0, 1], ?_, ?_, ?_⟩
  · simp
  · simp
  · intro x; ring

end FrohmanianTether.ObstructionAudit

end

#print axioms FrohmanianTether.ObstructionAudit.flow_contribution_zero_of_C2
#print axioms FrohmanianTether.ObstructionAudit.bilin_kernel_of_nonpos_of_self_zero
#print axioms FrohmanianTether.ObstructionAudit.energy_conservation_not_C2
#print axioms FrohmanianTether.ObstructionAudit.energy_damping_iff_not_degenerate
