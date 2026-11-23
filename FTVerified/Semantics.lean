/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import FTVerified.May.Basic
import FTVerified.May.Layer2
import FTVerified.May.Main
import FTVerified.May.ChevalleyEilenberg
import FTVerified.Sdiff.ObstructionAudit
import FTVerified.Sdiff.SymplecticTether

/-!
# Truth Gate: semantics lock (see `TRUTH_GATE.md`)

PAPER_PATH: paper/frohmanian-tether-verified.tex
PAPER_SHA256: 9653476e11264bfbc49db8b9ca99615e1ac9ed004b5357de0430126bf4fd2500
PAPER_SECTION: Proved results (C1/C3, C2, and the energy-budget refutation); uniqueness and comparison bound as recorded in Conditional results

Locked paper claim (Section "Refuted claims", first item), quoted verbatim:

PAPER_QUOTE_BEGIN
\item \textbf{The tether damps the energy budget.} This is refuted. Let $B$ be a symmetric bilinear form on a real vector space $V$ with $B(x,x)\le0$ for all $x\in V$ (C3), and let $h\in V$ stand for $\delta H$. Then $B(h,h)<0$ if and only if $B(m,h)\neq0$ for some $m\in V$. Consequently, if $B(m,h)=0$ for all $m$ (C2), then $B(h,h)=0$, so the tether contributes nothing to $dH/dt$; and if $B(h,h)=0$, then $B(m,h)=0$ for all $m$
PAPER_QUOTE_END

Reading of the paper's terms (fixed here, once):
* In the abstract model, `H` is a real inner-product space; `Π_u x = x - (⟪u,x⟫/‖u‖²) • u`
  and `𝔗_F[κ,w,u](F,G) = -(κ w) ⟪Π_u F, Π_u G⟫` are written out with those formulas, not as
  library aliases.
* "a symmetric bilinear form `B` on a real vector space `V`" is a Mathlib `LinearMap.BilinForm ℝ V`
  with `B x y = B y x` for all `x, y`;
* "(C3)" on such a `B` is `B x x ≤ 0` for all `x`; "(C2)" is `B m h = 0` for all `m`;
* `h` is any vector of `V` (it stands for `δH`); "the tether contributes nothing to `dH/dt`" is
  `B h h = 0`.
* Uniqueness is the finite-dimensional, dimension-at-least-3 statement with a coefficient-fixing
  `C3`, as in Section "Conditional results".
* The comparison bound is the ODE majorant `y' ≤ C y² - κ'' y³`, not a Navier–Stokes claim.

`formal_claim` is the conjunction of the repository theorems listed in `TRUTH_GATE.lock`.
`paper_claim` transcribes the same statements from the paper's wording and formulas.

Scope: this lock covers the listed abstract-model C1/C3/C2 identities, the kernel self-pairing
and kernel degeneracy (the latter only under its three hypotheses), the energy-budget
refutation, uniqueness relative to a coefficient-fixing `C3`, the comparison bound, and the
low-degree Chevalley–Eilenberg facts. It does not certify global regularity or any Millennium
claim. `certifying` stays false until every remaining paper statement is locked.
-/

namespace TruthGate

open Frohman.Tether
open FrohmanianTether
open scoped InnerProductSpace RealInnerProductSpace

-- TRUTH-GATE LOCK BEGIN

/-- Helper used only on the paper side: the paper's formula for `Π_u`. -/
noncomputable def paperPi {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u x : H) : H :=
  x - (⟪u, x⟫ / ‖u‖ ^ 2) • u

/-- Helper used only on the paper side: the paper's formula for `𝔗_F`. -/
noncomputable def paperT {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (κ w : ℝ) (u F G : H) : ℝ :=
  -(κ * w) * ⟪paperPi u F, paperPi u G⟫

/-- The repository's locked theorems, conjoined. -/
def formal_claim : Prop :=
  -- (1) energy-budget refutation
  (∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) → (∀ x, B x x ≤ 0) → ∀ h : V,
      (B h h < 0 ↔ ∃ m, B m h ≠ 0)) ∧
  -- (2) abstract-model self-pairing, under κ w ≥ 0
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (κ w : ℝ),
    0 ≤ κ * w → ∀ u F : H, frohmanianTether κ w u F F ≤ 0) ∧
  -- (3) C1 invariance
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (κ w : ℝ) (u : H),
    InvariantUnderCoadjointAction u (frohmanianTether κ w u)) ∧
  -- (4) abstract-model C2 degeneracy, unconditional in u
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (κ w : ℝ) (u : H),
    DegenerateWRTKineticEnergy u (frohmanianTether κ w u)) ∧
  -- (5) kernel self-pairing
  (∀ F : Functional, ∀ ω : CoadjointOrbit, TetherKernel ω F F ≤ 0) ∧
  -- (6) kernel C2, under the three hypotheses of the theorem
  (∀ F : Functional, ∀ ω : CoadjointOrbit,
    FunctionalDerivative KineticEnergyHamiltonian ω = velocity_from_vorticity ω →
    (∀ x, div (velocity_from_vorticity ω) x = 0) →
    Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2) →
    TetherKernel ω F KineticEnergyHamiltonian = 0) ∧
  -- (7) uniqueness relative to a coefficient-fixing C3
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H],
    3 ≤ Module.finrank ℝ H →
    ∀ (κ w : ℝ) (u : H), u ≠ 0 →
      ∀ (C3 : LinearMap.BilinForm ℝ H → Prop),
        (∀ c : ℝ, C3 (𝔗_F[c, 1, u]) → c = κ * w) →
        ∀ B : LinearMap.BilinForm ℝ H,
          IsAdmissibleCorrection u C3 B → B = 𝔗_F[κ, w, u]) ∧
  -- (8) comparison bound
  (∀ {y y' : ℝ → ℝ} {C κ'' T : ℝ}, 0 < κ'' → 0 ≤ y 0 →
    ContinuousOn y (Set.Icc 0 T) →
    (∀ x ∈ Set.Ico 0 T, HasDerivWithinAt y (y' x) (Set.Ici x) x) →
    (∀ x ∈ Set.Ico 0 T, y' x ≤ comparisonField C κ'' (y x)) →
    ∀ t ∈ Set.Icc 0 T, y t ≤ max (y 0) (C / κ'')) ∧
  -- (9) CE: d₂ ∘ d₁ = 0
  (∀ {R L : Type} [CommRing R] [LieRing L] [LieAlgebra R L] (f : L →ₗ[R] R) (x y z : L),
    Frohman.Tether.CE.d2 (Frohman.Tether.CE.d1 f) x y z = 0) ∧
  -- (10) CE: a coboundary is a cocycle
  (∀ {R L : Type} [CommRing R] [LieRing L] [LieAlgebra R L]
      (β : L → L → R) (f : L →ₗ[R] R),
    (∀ x y, Frohman.Tether.CE.antiCorr β x y = Frohman.Tether.CE.d1 f x y) →
    Frohman.Tether.CE.IsCocycle (Frohman.Tether.CE.antiCorr β)) ∧
  -- (11) CE: a symmetric alternating part vanishes
  (∀ {R L : Type} [CommRing R] [Invertible (2 : R)] (β : L → L → R),
    Frohman.Tether.CE.IsAlt (Frohman.Tether.CE.symPart β) →
    Frohman.Tether.CE.symPart β = 0)

/-- Independent transcription of the same paper statements. -/
def paper_claim : Prop :=
  -- (1) energy-budget refutation, with both consequences
  (∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) → (∀ x, B x x ≤ 0) → ∀ h : V,
      (B h h < 0 ↔ ∃ m, B m h ≠ 0) ∧
      ((∀ m, B m h = 0) → B h h = 0) ∧
      (B h h = 0 → ∀ m, B m h = 0)) ∧
  -- (2) self-pairing written with the paper's formula
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (κ w : ℝ),
    0 ≤ κ * w → ∀ u F : H, paperT κ w u F F ≤ 0) ∧
  -- (3) C1: isometries that fix u preserve the paper formula
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (κ w : ℝ) (u : H),
    ∀ g : H ≃ₗᵢ[ℝ] H, g u = u → ∀ F G : H,
      paperT κ w u (g F) (g G) = paperT κ w u F G) ∧
  -- (4) abstract C2: the paper formula vanishes on the second slot u
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (κ w : ℝ) (u F : H),
    paperT κ w u F u = 0) ∧
  -- (5) kernel self-pairing (the paper names TetherKernel)
  (∀ ω : CoadjointOrbit, ∀ F : Functional, TetherKernel ω F F ≤ 0) ∧
  -- (6) kernel C2 with the three hypotheses written out
  (∀ ω : CoadjointOrbit, ∀ F : Functional,
    FunctionalDerivative KineticEnergyHamiltonian ω = velocity_from_vorticity ω →
    (∀ x, div (velocity_from_vorticity ω) x = 0) →
    Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2) →
    TetherKernel ω F KineticEnergyHamiltonian = 0) ∧
  -- (7) uniqueness, with admissibility written out and T written as a formula
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H],
    3 ≤ Module.finrank ℝ H →
    ∀ (κ w : ℝ) (u : H), u ≠ 0 →
      ∀ (C3 : LinearMap.BilinForm ℝ H → Prop),
        (∀ (c : ℝ) (Bc : LinearMap.BilinForm ℝ H),
          (∀ F G, Bc F G = paperT c 1 u) → C3 Bc → c = κ * w) →
        ∀ B : LinearMap.BilinForm ℝ H,
          ((∀ F G, B F G = B G F) ∧
            (∀ g : H ≃ₗᵢ[ℝ] H, g u = u → ∀ F G, B (g F) (g G) = B F G) ∧
            (∀ F, B F u = 0) ∧
            C3 B) →
          ∀ F G, B F G = paperT κ w u F G) ∧
  -- (8) comparison bound with the polynomial written out
  (∀ (y y' : ℝ → ℝ) (C κ'' T : ℝ), 0 < κ'' → 0 ≤ y 0 →
    ContinuousOn y (Set.Icc 0 T) →
    (∀ x ∈ Set.Ico 0 T, HasDerivWithinAt y (y' x) (Set.Ici x) x) →
    (∀ x ∈ Set.Ico 0 T, y' x ≤ C * (y x) ^ 2 - κ'' * (y x) ^ 3) →
    ∀ t ∈ Set.Icc 0 T, y t ≤ max (y 0) (C / κ'')) ∧
  -- (9) d₂(d₁ f) = 0, formulas written out
  (∀ {R L : Type} [CommRing R] [LieRing L] [LieAlgebra R L] (f : L →ₗ[R] R) (x y z : L),
    (- (- f ⁅⁅x, y⁆, z⁆) + (- f ⁅⁅x, z⁆, y⁆) - (- f ⁅⁅y, z⁆, x⁆) = 0)) ∧
  -- (10) coboundary ⇒ cocycle, written out
  (∀ {R L : Type} [CommRing R] [LieRing L] [LieAlgebra R L]
      (β : L → L → R) (f : L →ₗ[R] R),
    (∀ x y, β x y - β y x = - f ⁅x, y⁆) →
      (∀ x y, (β x y - β y x) = - (β y x - β x y)) ∧
      ∀ x y z,
        (let B : L → L → R := fun x y => β x y - β y x
         - B ⁅x, y⁆ z + B ⁅x, z⁆ y - B ⁅y, z⁆ x = 0)) ∧
  -- (11) symmetric part cannot be a nonzero alternating cochain
  (∀ {R L : Type} [CommRing R] [Invertible (2 : R)] (β : L → L → R),
    (∀ x y, β x y + β y x = - (β y x + β x y)) →
    ∀ x y, β x y + β y x = 0)

/-- The fixed correspondence between the formal statement and the paper's claim. -/
theorem intended_correspondence : formal_claim ↔ paper_claim := by
  have hT : ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (κ w : ℝ) (u F G : H),
      frohmanianTether κ w u F G = paperT κ w u F G := by
    intro H _ _ κ w u F G
    simp [paperT, paperPi, frohmanianTether_apply, piU_apply]
  constructor
  · rintro ⟨hEn, hSelf, hInv, hDeg, hKs, hKd, hUniq, hCmp, hD2, hCob, hSym⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro V _ _ B hsym hneg h
      have hiff := hEn V B hsym hneg h
      refine ⟨hiff, ?_, ?_⟩
      · intro hC2
        by_contra hne
        have hlt : B h h < 0 := lt_of_le_of_ne (hneg h) hne
        obtain ⟨m, hm⟩ := hiff.mp hlt
        exact hm (hC2 m)
      · intro hzero m
        by_contra hm
        have hlt := hiff.mpr ⟨m, hm⟩
        rw [hzero] at hlt
        exact lt_irrefl 0 hlt
    · intro H _ _ κ w hkw u F
      simpa [hT] using hSelf H κ w hkw u F
    · intro H _ _ κ w u g hg F G
      simpa [hT] using hInv H κ w u g hg F G
    · intro H _ _ κ w u F
      simpa [hT] using hDeg H κ w u F
    · intro ω F
      exact hKs F ω
    · intro ω F hδ hdiv hInt
      exact hKd F ω hδ hdiv hInt
    · intro H _ _ _ hdim κ w u hu C3 hfix B hB
      have hAd : IsAdmissibleCorrection u C3 B :=
        ⟨hB.1, hB.2.1, hB.2.2.1, hB.2.2.2⟩
      have hfix' : ∀ c : ℝ, C3 (𝔗_F[c, 1, u]) → c = κ * w := by
        intro c hc
        exact hfix c (𝔗_F[c, 1, u]) (fun F G => hT c 1 u F G) hc
      have hEq := hUniq H hdim κ w u hu C3 hfix' B hAd
      intro F G
      simpa [hT] using congrArg (fun B : LinearMap.BilinForm ℝ H => B F G) hEq
    · intro y y' C κ'' T hκ hy0 hc hd hineq
      exact hCmp hκ hy0 hc hd (by intro x hx; simpa [comparisonField] using hineq x hx)
    · intro R L _ _ _ f x y z
      simpa [Frohman.Tether.CE.d1, Frohman.Tether.CE.d2] using hD2 f x y z
    · intro R L _ _ _ β f hB
      have hCE := hCob β f (by intro x y; simpa [Frohman.Tether.CE.antiCorr, Frohman.Tether.CE.d1] using hB x y)
      refine ⟨?_, ?_⟩
      · intro x y
        have := hCE.1 x y
        simpa [Frohman.Tether.CE.antiCorr] using this
      · intro x y z
        have := hCE.2 x y z
        simpa [Frohman.Tether.CE.antiCorr, Frohman.Tether.CE.d2] using this
    · intro R L _ _ β hAlt
      have := hSym β (by intro x y; simpa [Frohman.Tether.CE.symPart, Frohman.Tether.CE.IsAlt] using hAlt x y)
      intro x y
      simpa [Frohman.Tether.CE.symPart] using congrFun (congrFun this x) y
  · rintro ⟨hEn, hSelf, hInv, hDeg, hKs, hKd, hUniq, hCmp, hD2, hCob, hSym⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro V _ _ B hsym hneg h
      exact (hEn V B hsym hneg h).1
    · intro H _ _ κ w hkw u F
      simpa [hT] using hSelf H κ w hkw u F
    · intro H _ _ κ w u
      intro g hg F G
      simpa [hT] using hInv H κ w u g hg F G
    · intro H _ _ κ w u
      intro F
      simpa [hT] using hDeg H κ w u F
    · intro F ω
      exact hKs ω F
    · intro F ω hδ hdiv hInt
      exact hKd ω F hδ hdiv hInt
    · intro H _ _ _ hdim κ w u hu C3 hfix B hB
      have hPack :
          (∀ F G, B F G = B G F) ∧
            (∀ g : H ≃ₗᵢ[ℝ] H, g u = u → ∀ F G, B (g F) (g G) = B F G) ∧
            (∀ F, B F u = 0) ∧
            C3 B :=
        ⟨hB.symm, hB.c1, hB.c2, hB.c3⟩
      have hfix' : ∀ (c : ℝ) (Bc : LinearMap.BilinForm ℝ H),
          (∀ F G, Bc F G = paperT c 1 u) → C3 Bc → c = κ * w := by
        intro c Bc hBc hc
        have hEq : Bc = 𝔗_F[c, 1, u] := LinearMap.ext₂ fun F G => by
          rw [hBc F G, ← hT]
        exact hfix c (hEq ▸ hc)
      have hPt := hUniq H hdim κ w u hu C3 hfix' B hPack
      refine LinearMap.ext₂ fun F G => ?_
      simpa [hT] using hPt F G
    · intro y y' C κ'' T hκ hy0 hc hd hineq
      exact hCmp y y' C κ'' T hκ hy0 hc hd (by intro x hx; simpa [comparisonField] using hineq x hx)
    · intro R L _ _ _ f x y z
      simpa [Frohman.Tether.CE.d1, Frohman.Tether.CE.d2] using hD2 f x y z
    · intro R L _ _ _ β f hB
      have h' := hCob β f (by intro x y; simpa [Frohman.Tether.CE.antiCorr, Frohman.Tether.CE.d1] using hB x y)
      refine ⟨?_, ?_⟩
      · intro x y
        simpa [Frohman.Tether.CE.antiCorr] using h'.1 x y
      · intro x y z
        simpa [Frohman.Tether.CE.antiCorr, Frohman.Tether.CE.d2] using h'.2 x y z
    · intro R L _ _ β hAlt
      have := hSym β (by intro x y; simpa [Frohman.Tether.CE.symPart] using hAlt x y)
      funext x y
      simpa [Frohman.Tether.CE.symPart] using this x y
-- TRUTH-GATE LOCK END

/-- The main theorems prove `formal_claim`. -/
theorem formal_claim_holds : formal_claim :=
  ⟨fun _ _ _ B hsym hneg h =>
      FrohmanianTether.ObstructionAudit.energy_damping_iff_not_degenerate B hsym hneg h,
    fun _ _ _ κ w hkw u F => frohmanianTether_self_nonpos_of_mul_nonneg hkw u F,
    fun _ _ _ κ w u => frohmanianTether_invariant κ w u,
    fun _ _ _ κ w u => frohmanianTether_degenerate κ w u,
    fun F ω => tetherKernel_self_nonpos F ω,
    fun F ω hδ hdiv hInt =>
      tetherKernel_degenerates_on_kinetic_energy F ω hδ hdiv hInt,
    fun _ _ _ _ hdim κ w u hu C3 hfix B hB =>
      uniqueness_of_minimal_metric_tether hdim κ w u hu C3 hfix B hB,
    fun hκ hy0 hc hd hineq => comparison_bound hκ hy0 hc hd hineq,
    fun f x y z => Frohman.Tether.CE.d2_d1 f x y z,
    fun β f hB => Frohman.Tether.CE.cocycle_of_coboundary β f hB,
    fun β hAlt => Frohman.Tether.CE.symPart_not_cochain β hAlt⟩

/-- The paper's claim, transported across the correspondence. -/
theorem paper_claim_holds : paper_claim :=
  intended_correspondence.mp formal_claim_holds

end TruthGate
