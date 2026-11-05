import Mathlib.Algebra.Lie.Basic
import FTVerified.May.BiotSavart

/-!
# Chevalley–Eilenberg 2-cocycle and the T³ shear example

Formalizes the two checkable claims of the June 22, 2026 compilation slides
`05_chevalley_eilenberg_closure` / `08_shear_counterexample_t3`:

* (a) the low-degree Chevalley–Eilenberg complex with trivial coefficients,
  `d² = 0` on 1-cochains (Jacobi), and the antisymmetric correction
  `B(x,y) = β(x,y) − β(y,x)`: it is always an alternating 2-cochain; it is a
  2-cocycle **iff** `d₂ B = 0` (the cyclic condition below), and this holds
  automatically when `B` is a coboundary `B = d₁ f`. The symmetric part
  (𝔗_F) is *not* a CE cochain: a symmetric alternating form is `0` (char ≠ 2).
* (b) the T³ shear `X = (sin y, 0, 0)` is divergence-free; the variant
  `(sin x, 0, 0)` has `div = cos x ≠ 0`, so the reduced-orbit (div-free)
  cancellation fails there.
-/

namespace Frohman.Tether.CE

variable {R L : Type*} [CommRing R]

/-- 1-cochains: linear functionals. CE differential `d₁ f (x,y) = − f [x,y]`. -/
def d1 [LieRing L] [LieAlgebra R L] (f : L →ₗ[R] R) (x y : L) : R := - f ⁅x, y⁆

/-- CE differential on 2-cochains (trivial coefficients):
`d₂ c (x,y,z) = −c([x,y],z) + c([x,z],y) − c([y,z],x)`. -/
def d2 [LieRing L] (c : L → L → R) (x y z : L) : R := - c ⁅x, y⁆ z + c ⁅x, z⁆ y - c ⁅y, z⁆ x

/-- **`d ∘ d = 0`** (degree 1 → 3), equivalent to the Jacobi identity. -/
theorem d2_d1 [LieRing L] [LieAlgebra R L] (f : L →ₗ[R] R) (x y z : L) : d2 (d1 f) x y z = 0 := by
  unfold d2 d1
  have j := congrArg f (lie_jacobi x y z)
  rw [← lie_skew ⁅x, y⁆ z, ← lie_skew ⁅y, z⁆ x, ← lie_skew ⁅x, z⁆ y, ← lie_skew z x] at *
  simp only [map_add, map_neg, map_zero, lie_neg] at *
  linear_combination -j

/-- Alternating 2-cochain. -/
def IsAlt (c : L → L → R) : Prop := ∀ x y, c x y = - c y x

/-- Antisymmetric correction of a bilinear term. -/
def antiCorr (β : L → L → R) (x y : L) : R := β x y - β y x

/-- Symmetric part (the 𝔗_F-type term). -/
def symPart (β : L → L → R) (x y : L) : R := β x y + β y x

theorem antiCorr_alt (β : L → L → R) : IsAlt (antiCorr β) := by
  intro x y; unfold antiCorr; ring

/-- `B` is a CE 2-cocycle exactly when the cyclic condition `d₂ B = 0` holds (definition). -/
def IsCocycle [LieRing L] (c : L → L → R) : Prop := IsAlt c ∧ ∀ x y z, d2 c x y z = 0

theorem antiCorr_cocycle_iff [LieRing L] (β : L → L → R) :
    IsCocycle (antiCorr β) ↔ ∀ x y z, d2 (antiCorr β) x y z = 0 :=
  ⟨fun h => h.2, fun h => ⟨antiCorr_alt β, h⟩⟩

/-- Sufficient condition: if `B = d₁ f` (coboundary), `B` is a cocycle. -/
theorem cocycle_of_coboundary [LieRing L] [LieAlgebra R L] (β : L → L → R) (f : L →ₗ[R] R)
    (hB : ∀ x y, antiCorr β x y = d1 f x y) : IsCocycle (antiCorr β) := by
  refine ⟨antiCorr_alt β, fun x y z => ?_⟩
  have : antiCorr β = d1 f := funext fun x => funext fun y => hB x y
  rw [this]; exact d2_d1 f x y z

/-- The symmetric part is not a CE cochain: if it is alternating it vanishes (`2` invertible). -/
theorem symPart_not_cochain [Invertible (2 : R)] (β : L → L → R) (h : IsAlt (symPart β)) :
    symPart β = 0 := by
  funext x y
  have := h x y
  have hs : symPart β x y = symPart β y x := by unfold symPart; ring
  rw [hs] at this
  have h2 : (2 : R) * symPart β y x = 0 := by linear_combination this
  have := congrArg (⅟(2 : R) * ·) h2
  simp only [← mul_assoc, invOf_mul_self, one_mul, mul_zero] at this
  rw [hs]; simpa using this

end Frohman.Tether.CE

namespace Frohman.Tether.Shear

open Frohman.Tether.Torus Frohman.Tether.BiotSavart

/-- Divergence of a mode: `div = Σ (−sin·cᵢ + cos·dᵢ) Kᵢ`. -/
theorem div_mode (K c d : Fin 3 → ℝ) (x : R3) :
    divergence (mode K c d) x = ∑ i, (-Real.sin (th K x) * c i + Real.cos (th K x) * d i) * K i := by
  unfold divergence; simp only [pd_comp_mode]

/-- **T³ shear** `X = (sin y, 0, 0)`. -/
noncomputable def shear : R3 → R3 := mode ![0, 1, 0] 0 ![1, 0, 0]

theorem shear_divFree : ∀ x, divergence shear x = 0 := by
  intro x; unfold shear; rw [div_mode]; simp [Fin.sum_univ_three]

/-- Non-div-free variant `(sin x, 0, 0)`. -/
noncomputable def shearBad : R3 → R3 := mode ![1, 0, 0] 0 ![1, 0, 0]

theorem shearBad_div (x : R3) : divergence shearBad x = Real.cos (th ![1, 0, 0] x) := by
  unfold shearBad; rw [div_mode]; simp [Fin.sum_univ_three]

/-- The variant is genuinely not divergence-free (`div = 1` at the origin). -/
theorem shearBad_not_divFree : divergence shearBad 0 ≠ 0 := by
  rw [shearBad_div]; simp

end Frohman.Tether.Shear
