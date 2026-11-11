-- SPDX-FileCopyrightText: 2026 Benjamin Stanley Frohman
-- SPDX-License-Identifier: Apache-2.0
-- Author: Benjamin Stanley Frohman
import Mathlib

/-!
# Algebraic core of the Lie–Poisson Jacobi cancellation

This file formalizes ONLY the final algebraic step of the note: once the
functional derivative of `{G,H}` has been computed as
`δ{G,H} = [g,h] + Hess_G(k_h) - Hess_H(k_g)`, the expansion of
`{F,{G,H}} + {G,{H,F}} + {H,{F,G}}` consists of
`m [f,[g,h]] + cyclic` plus six second-derivative terms
`-Q_G(k_f,k_h) + Q_H(k_f,k_g) + ...`, which cancel pairwise because each
`Q` is symmetric; the remainder vanishes by the Jacobi identity of the Lie
algebra.  No analysis (Fréchet derivatives, the torus, sdiff) is formalized here.
-/

namespace LiePoissonCore

variable {R L V : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The six second-derivative terms cancel pairwise by symmetry of each `Q`. -/
theorem six_terms_cancel (QF QG QH : V → V → R)
    (hF : ∀ p q, QF p q = QF q p) (hG : ∀ p q, QG p q = QG q p)
    (hH : ∀ p q, QH p q = QH q p) (kf kg kh : V) :
    (-QG kf kh + QH kf kg) + (-QH kg kf + QF kg kh) + (-QF kh kg + QG kh kf) = 0 := by
  rw [hG kh kf, hH kg kf, hF kh kg]; ring

/-- Full cyclic sum, with the first-order part `m [f,[g,h]] + cyclic`, for any linear `m`. -/
theorem lie_poisson_jacobi_core (m : L →ₗ[R] R) (QF QG QH : V → V → R)
    (hF : ∀ p q, QF p q = QF q p) (hG : ∀ p q, QG p q = QG q p)
    (hH : ∀ p q, QH p q = QH q p) (f g h : L) (kf kg kh : V) :
    (m ⁅f, ⁅g, h⁆⁆ - QG kf kh + QH kf kg)
      + (m ⁅g, ⁅h, f⁆⁆ - QH kg kf + QF kg kh)
      + (m ⁅h, ⁅f, g⁆⁆ - QF kh kg + QG kh kf) = 0 := by
  have hJ : m ⁅f, ⁅g, h⁆⁆ + m ⁅g, ⁅h, f⁆⁆ + m ⁅h, ⁅f, g⁆⁆ = 0 := by
    rw [← map_add, ← map_add, lie_jacobi, map_zero]
  have h6 := six_terms_cancel QF QG QH hF hG hH kf kg kh
  linear_combination hJ + h6

end LiePoissonCore

