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

/-! ### The symmetry hypotheses are needed, and are not vacuous

`six_terms_cancel_needs_symmetry`: with `V = R = ℚ`, `QG = QH = 0` and the non-symmetric
`QF p q = p` (so `QF 1 0 = 1 ≠ 0 = QF 0 1`), the six-term sum at `kf = kh = 0`, `kg = 1`
equals `QF 1 0 - QF 0 1 = 1 ≠ 0`. So the conclusion of `six_terms_cancel` is false once the
symmetry of `QF` is dropped; the hypothesis is doing real work.

`six_terms_nonvacuous`: the hypotheses are satisfiable with a symmetric `Q` that is not
identically zero (`Q p q = p * q` on `ℚ`), and for that choice the individual terms are nonzero
(`QG kf kh = 2` at `kf = 1`, `kh = 2`), so the cancellation is not the trivial `0 = 0`.

`lie_poisson_jacobi_core_nonvacuous`: an inhabited instance of the full statement with a
non-abelian Lie algebra (`2 × 2` rational matrices with the commutator bracket), a nonzero
linear `m` (the `(0,1)` entry), and a nonzero first-order term `m ⁅f, ⁅g, h⁆⁆ = 2`
(at `f = h = E₁₂`, `g = E₂₁`).
-/

theorem six_terms_cancel_needs_symmetry :
    ¬ (∀ (QF QG QH : ℚ → ℚ → ℚ) (kf kg kh : ℚ),
        (-QG kf kh + QH kf kg) + (-QH kg kf + QF kg kh) + (-QF kh kg + QG kh kf) = 0) := by
  intro h
  have := h (fun p _ => p) (fun _ _ => 0) (fun _ _ => 0) 0 1 0
  norm_num at this

theorem six_terms_nonvacuous :
    ∃ (QF QG QH : ℚ → ℚ → ℚ) (kf kg kh : ℚ),
      (∀ p q, QF p q = QF q p) ∧ (∀ p q, QG p q = QG q p) ∧ (∀ p q, QH p q = QH q p) ∧
      QG kf kh ≠ 0 ∧
      (-QG kf kh + QH kf kg) + (-QH kg kf + QF kg kh) + (-QF kh kg + QG kh kf) = 0 := by
  refine ⟨fun p q => p * q, fun p q => p * q, fun p q => p * q, 1, 1, 2,
    fun p q => mul_comm p q, fun p q => mul_comm p q, fun p q => mul_comm p q, by norm_num, ?_⟩
  exact six_terms_cancel _ _ _ (fun p q => mul_comm p q) (fun p q => mul_comm p q)
    (fun p q => mul_comm p q) 1 1 2

/-- The `(0,1)` entry of a `2 × 2` rational matrix, as a `ℚ`-linear map. -/
def entry01 : Matrix (Fin 2) (Fin 2) ℚ →ₗ[ℚ] ℚ where
  toFun A := A 0 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem lie_poisson_jacobi_core_nonvacuous :
    ∃ (f g h : Matrix (Fin 2) (Fin 2) ℚ),
      entry01 ⁅f, ⁅g, h⁆⁆ ≠ 0 ∧
      (entry01 ⁅f, ⁅g, h⁆⁆ - (fun p q : ℚ => p * q) 1 2 + (fun p q : ℚ => p * q) 1 1)
        + (entry01 ⁅g, ⁅h, f⁆⁆ - (fun p q : ℚ => p * q) 1 1 + (fun p q : ℚ => p * q) 1 2)
        + (entry01 ⁅h, ⁅f, g⁆⁆ - (fun p q : ℚ => p * q) 2 1 + (fun p q : ℚ => p * q) 2 1) = 0 := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], !![0, 1; 0, 0], ?_, ?_⟩
  · simp [entry01, Ring.lie_def]
  · exact lie_poisson_jacobi_core entry01 (fun p q => p * q) (fun p q => p * q)
      (fun p q => p * q) (fun p q => mul_comm p q) (fun p q => mul_comm p q)
      (fun p q => mul_comm p q) _ _ _ 1 1 2

end LiePoissonCore

