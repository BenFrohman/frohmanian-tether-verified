-- SPDX-FileCopyrightText: 2026 Benjamin Stanley Frohman
-- SPDX-License-Identifier: Apache-2.0
/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman (prepared with assistance from Grok; not a co-author).

# Global Regularity (rebuild of the May 28 2026 layout, LOCAL)

Mirrors `Modules/GlobalRegularity.lean`. Part 1 (degeneracy) and Part 2 (uniqueness,
Route A, κ = S) are proved. Part 3 is proved *conditional on* the named open step
`NSTetherEnstrophyInequality` with `κ'' = S/2 − C_abs`, plus the classical
`BKMContinuation` and `LocalContinuation` (not in Mathlib). No `sorry`, no axioms.
-/
import FTVerified.May.TetheredLyapunov

namespace Frohman.Tether

open scoped InnerProductSpace RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Frohmanian Symplectic Tether Theorem — May 28 three-part form.** -/
theorem frohmanian_symplectic_tether_theorem_global [FiniteDimensional ℝ H]
    (hdim : 3 ≤ Module.finrank ℝ H) {S w Cabs C : ℝ} (hS : 0 ≤ S) (hw : 0 < w) (u ω : H)
    (hu : u ≠ 0) (hω : ⟪u, ω⟫ = 0) (hn : ‖ω‖ = 1) :
    -- 1. degeneracy: the tether never touches the kinetic-energy gradient
    (∀ F : H, 𝔗_F[S, w, u] F (kineticEnergyGradient u) = 0) ∧
    -- 2. uniqueness (Route A): admissible ⇔ B = 𝔗_F[κ,w,u] with κ = S
    (∀ B : LinearMap.BilinForm ℝ H,
      IsAdmissibleCorrection u (RouteAFeedback S w u ω) B ↔ ∃ κ, κ = S ∧ B = 𝔗_F[κ, w, u]) ∧
    -- 3. global regularity, conditional on the open NS step
    (0 < kappaDD S Cabs → ∀ s : NSTetherSolution,
      NSTetherEnstrophyInequality s C (kappaDD S Cabs) →
      BKMContinuation s → LocalContinuation s → GloballySmooth s) :=
  ⟨fun F => degeneracy_verification S w u F,
   fun B => frohmanian_symplectic_tether_theorem hdim hS hw u ω hu hω hn B,
   fun hκ _ hI hB hL => global_regularity hκ hI hB hL⟩

end Frohman.Tether
