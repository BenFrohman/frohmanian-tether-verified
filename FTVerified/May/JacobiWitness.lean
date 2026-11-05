/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman (prepared with assistance from Grok; not a co-author).

# An explicit witness that the mixed Jacobi terms do NOT cancel

Concrete instance of the `Jacobi.lean` framework: `H = ℝ³` (Euclidean), classical bracket
`P(a,b) = a × b` (the `so(3)` Lie–Poisson / vorticity bracket, which satisfies Jacobi), and
tether axis `u = e₁` — the amplitude direction shared by both shears `(sin y,0,0)` and
`(sin x,0,0)` of `ChevalleyEilenberg.lean`. With `a = b = e₂`, `c = e₃` the mixed cyclic sum
equals `(κ w) • e₂`, hence is nonzero whenever `κ w ≠ 0`, and the tethered Jacobiator is
nonzero.

Caveat (stated honestly): the `Jacobi.lean` framework is finite-dimensional algebra on `H`;
it has no map from a velocity field to functionals, so divergence-freeness never enters.
The same witness works for the axis of either shear, so in this framework the
divergence-free condition cannot make the mixed terms cancel.
-/
import FTVerified.May.Jacobi
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Frohman.Tether.JacobiWitness

open Frohman.Tether
open scoped InnerProductSpace RealInnerProductSpace Matrix

abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Cross-product bracket on `E3`. -/
noncomputable def crossBr (a b : E3) : E3 := WithLp.toLp 2 (a.ofLp ⨯₃ b.ofLp)

theorem crossBr_isClassical : IsClassicalBracket crossBr where
  add_left x y z := by
    simp [crossBr]
  jacobi a b c := by
    have h := jacobi_cross c.ofLp a.ofLp b.ofLp
    simp only [jacobiator, crossBr]
    have e1 : (a.ofLp ⨯₃ b.ofLp) ⨯₃ c.ofLp = -(c.ofLp ⨯₃ (a.ofLp ⨯₃ b.ofLp)) :=
      by rw [← cross_anticomm]
    have e2 : (b.ofLp ⨯₃ c.ofLp) ⨯₃ a.ofLp = -(a.ofLp ⨯₃ (b.ofLp ⨯₃ c.ofLp)) :=
      by rw [← cross_anticomm]
    have e3 : (c.ofLp ⨯₃ a.ofLp) ⨯₃ b.ofLp = -(b.ofLp ⨯₃ (c.ofLp ⨯₃ a.ofLp)) :=
      by rw [← cross_anticomm]
    ext i
    have := congrFun h i
    simp only [e1, e2, e3, PiLp.add_apply, PiLp.zero_apply] at *
    simp only [Pi.neg_apply, Pi.add_apply, Pi.zero_apply] at *
    linarith

/-- Standard basis vectors. -/
noncomputable def e1 : E3 := EuclideanSpace.single 0 1
noncomputable def e2 : E3 := EuclideanSpace.single 1 1
noncomputable def e3 : E3 := EuclideanSpace.single 2 1

/-- **Explicit non-cancellation.** The mixed cyclic sum equals `(κ w) • e₂`. -/
theorem mixed_sum_eq (κ w : ℝ) :
    mixedTerm crossBr κ w e1 e2 e2 e3 + mixedTerm crossBr κ w e1 e2 e3 e2 +
      mixedTerm crossBr κ w e1 e3 e2 e2 = (κ * w) • e2 := by
  ext i
  fin_cases i <;>
  simp [mixedTerm, tetherVec, frohmanianTether_apply, piU_apply, crossBr, e1, e2, e3,
    cross_apply, inner]

theorem mixed_sum_ne_zero {κ w : ℝ} (h : κ * w ≠ 0) :
    mixedTerm crossBr κ w e1 e2 e2 e3 + mixedTerm crossBr κ w e1 e2 e3 e2 +
      mixedTerm crossBr κ w e1 e3 e2 e2 ≠ 0 := by
  rw [mixed_sum_eq]
  intro h0
  have := congrArg (fun v : E3 => v 1) h0
  simp [e2] at this
  exact h (mul_eq_zero.2 this)

/-- **The tethered bracket fails Jacobi** at an explicit triple (so it is not Poisson). -/
theorem tethered_jacobiator_ne_zero {κ w : ℝ} (h : κ * w ≠ 0) :
    jacobiator (tetheredBracketVec crossBr κ w e1) e2 e2 e3 ≠ 0 := by
  rw [jacobiator_eq_mixed crossBr_isClassical]
  exact mixed_sum_ne_zero h

end Frohman.Tether.JacobiWitness
