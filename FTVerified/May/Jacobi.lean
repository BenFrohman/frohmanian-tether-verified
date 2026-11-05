/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman (prepared with assistance from Grok; not a co-author).

# The 9-term Jacobi expansion (May 20 2026 Route A, "9-term Jacobi on the reduced orbit")

Algebraic model: the tethered bracket is `{a,b}_{𝔗_F} = P(a,b) + T(a,b)` on `H`, where
`P` is a vector-valued bracket satisfying the Jacobi identity (the classical part) and
`T(a,b) = -(κ w) ⟪Π_u a, Π_u b⟫ • u` is the vector-valued tether (values along `u`).
The Jacobiator `J(a,b,c) = Σ_cyc {{a,b},c}` splits into 9 cyclic groups:
3 classical–classical, 3 mixed, 3 tether–tether.

Proved: (i) the 9-term expansion; (ii) the 3 classical terms cancel (Jacobi for `P`);
(iii) each of the 3 tether–tether terms is zero because `Π_u u = 0`; hence
(iv) `J = 0` **iff** the 3 mixed terms cancel — the exact condition. In general they do
not cancel (the tether is symmetric: the bracket is metriplectic, not Poisson).
(v) Sufficient condition: `u` central for `P` and `P` maps into `span u` modulo `Π_u`,
i.e. `Π_u (P a b) = 0` — then all mixed terms vanish.
-/
import FTVerified.May.Basic

namespace Frohman.Tether

open scoped InnerProductSpace RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Vector-valued tether `T(a,b) = 𝔗_F[κ,w,u](a,b) • u`. -/
noncomputable def tetherVec (κ w : ℝ) (u a b : H) : H := 𝔗_F[κ, w, u] a b • u

/-- Tethered bracket `{a,b}_{𝔗_F} = P(a,b) + T(a,b)`. -/
noncomputable def tetheredBracketVec (P : H → H → H) (κ w : ℝ) (u a b : H) : H :=
  P a b + tetherVec κ w u a b

/-- Jacobiator of a vector-valued bracket. -/
def jacobiator (br : H → H → H) (a b c : H) : H :=
  br (br a b) c + br (br b c) a + br (br c a) b

/-- Bilinearity of `P` in the first slot is all we need of `P` (plus Jacobi). -/
structure IsClassicalBracket (P : H → H → H) : Prop where
  add_left : ∀ x y z, P (x + y) z = P x z + P y z
  jacobi : ∀ a b c, jacobiator P a b c = 0

theorem tetherVec_tetherVec (κ w : ℝ) (u a b c : H) :
    tetherVec κ w u (tetherVec κ w u a b) c = 0 := by
  simp [tetherVec, frohmanianTether_apply, projectionOrthogonalToU]

/-- Terms 7–9 (tether–tether) vanish, each by `Π_u u = 0`. -/
theorem jacobi_term7 (κ w : ℝ) (u a b c : H) : tetherVec κ w u (tetherVec κ w u a b) c = 0 :=
  tetherVec_tetherVec κ w u a b c
theorem jacobi_term8 (κ w : ℝ) (u a b c : H) : tetherVec κ w u (tetherVec κ w u b c) a = 0 :=
  tetherVec_tetherVec κ w u b c a
theorem jacobi_term9 (κ w : ℝ) (u a b c : H) : tetherVec κ w u (tetherVec κ w u c a) b = 0 :=
  tetherVec_tetherVec κ w u c a b

/-- Mixed cyclic term `M(a,b,c) = P(T(a,b),c) + T(P(a,b),c)`. -/
noncomputable def mixedTerm (P : H → H → H) (κ w : ℝ) (u a b c : H) : H :=
  P (tetherVec κ w u a b) c + tetherVec κ w u (P a b) c

/-- One cyclic group of the expansion: `{{a,b},c} = PP + mixed + TT`. -/
theorem tetheredBracket_nested {P : H → H → H} (hP : IsClassicalBracket P) (κ w : ℝ)
    (u a b c : H) :
    tetheredBracketVec P κ w u (tetheredBracketVec P κ w u a b) c =
      P (P a b) c + mixedTerm P κ w u a b c + tetherVec κ w u (tetherVec κ w u a b) c := by
  simp only [tetheredBracketVec, mixedTerm, hP.add_left, tetherVec, map_add,
    LinearMap.add_apply, add_smul]
  abel

/-- **9-term expansion** of the Jacobiator of `{·,·}_{𝔗_F}`. -/
theorem jacobiator_nine_terms {P : H → H → H} (hP : IsClassicalBracket P) (κ w : ℝ)
    (u a b c : H) :
    jacobiator (tetheredBracketVec P κ w u) a b c =
      (P (P a b) c + P (P b c) a + P (P c a) b) +
      (mixedTerm P κ w u a b c + mixedTerm P κ w u b c a + mixedTerm P κ w u c a b) +
      (tetherVec κ w u (tetherVec κ w u a b) c + tetherVec κ w u (tetherVec κ w u b c) a +
        tetherVec κ w u (tetherVec κ w u c a) b) := by
  simp only [jacobiator, tetheredBracket_nested hP]; abel

/-- Terms 1–3 (classical) cancel. -/
theorem jacobi_classical_cancel {P : H → H → H} (hP : IsClassicalBracket P) (a b c : H) :
    P (P a b) c + P (P b c) a + P (P c a) b = 0 := hP.jacobi a b c

/-- After cancellation, the Jacobiator is exactly the sum of the 3 mixed terms. -/
theorem jacobiator_eq_mixed {P : H → H → H} (hP : IsClassicalBracket P) (κ w : ℝ)
    (u a b c : H) :
    jacobiator (tetheredBracketVec P κ w u) a b c =
      mixedTerm P κ w u a b c + mixedTerm P κ w u b c a + mixedTerm P κ w u c a b := by
  rw [jacobiator_nine_terms hP, jacobi_classical_cancel hP, jacobi_term7, jacobi_term8,
    jacobi_term9]; simp

/-- **Exact Jacobi condition.** `{·,·}_{𝔗_F}` satisfies Jacobi on a set `R` (e.g. the
reduced orbit `uᗮ`) iff the mixed cyclic sum vanishes on `R`. -/
theorem jacobi_iff_mixed_cancel {P : H → H → H} (hP : IsClassicalBracket P) (κ w : ℝ)
    (u : H) (R : Set H) :
    (∀ a ∈ R, ∀ b ∈ R, ∀ c ∈ R, jacobiator (tetheredBracketVec P κ w u) a b c = 0) ↔
      ∀ a ∈ R, ∀ b ∈ R, ∀ c ∈ R,
        mixedTerm P κ w u a b c + mixedTerm P κ w u b c a + mixedTerm P κ w u c a b = 0 := by
  simp only [jacobiator_eq_mixed hP]

/-- **Sufficient condition.** If `P(u, ·) = 0` (`u` central), `P` is homogeneous in the
first slot, and `Π_u (P a b) = 0`, every mixed term vanishes, so Jacobi holds. -/
theorem mixedTerm_eq_zero {P : H → H → H} (hcen : ∀ c, P u c = 0)
    (hsmul : ∀ (r : ℝ) x z, P (r • x) z = r • P x z) (hproj : ∀ a b, piU u (P a b) = 0)
    (κ w : ℝ) (a b c : H) : mixedTerm P κ w u a b c = 0 := by
  simp only [mixedTerm, tetherVec, hsmul, hcen, smul_zero, zero_add]
  simp [frohmanianTether_apply, hproj]

theorem jacobiator_eq_zero_of_central {P : H → H → H} (hP : IsClassicalBracket P)
    (hcen : ∀ c, P u c = 0) (hsmul : ∀ (r : ℝ) x z, P (r • x) z = r • P x z)
    (hproj : ∀ a b, piU u (P a b) = 0) (κ w : ℝ) (a b c : H) :
    jacobiator (tetheredBracketVec P κ w u) a b c = 0 := by
  rw [jacobiator_eq_mixed hP, mixedTerm_eq_zero hcen hsmul hproj,
    mixedTerm_eq_zero hcen hsmul hproj, mixedTerm_eq_zero hcen hsmul hproj]; simp

end Frohman.Tether
