/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman (prepared with assistance from Grok; not a co-author).

# The tethered system at the VORTICITY level, reconciled with the velocity level (LOCAL)

**The tethered system (one definition, used by L² and H¹):**
  `∂ₜω + (u·∇)ω = (ω·∇)u + νΔω − κ P(|ω|²ω)`,   `u = BiotSavart(ω)`,   `P` = Leray projection.
Pointwise the tether density `−κ ω·(|ω|²ω)` is exactly the user's
`quarticTether κ u ω = 𝔗_F[κ, ‖ω‖², u] ω ω = −κ|ω|⁴` (for `ω ⟂ u`), `quarticTether_density`.

**Velocity level.** It comes from Navier–Stokes with the NONLOCAL force
  `F = curl⁻¹(−κ P(|ω|²ω))`  (`= −κ curl⁻¹ P(|ω|²ω)` for linear `curl⁻¹`),
i.e. `curl F = −κ P(|ω|²ω)`. `IsTetheredNSQuartic` is `Torus.IsTetheredNS` with exactly this
tether field, so the velocity-level system of `Torus.lean` and the vorticity-level system of
`EnstrophyL2`/`PalinstrophyH1` are now the SAME system. Two classical facts stay named Props:
* `CurlRightInverse` (Biot–Savart: `curl (curl⁻¹ g) = g` for smooth, periodic, mean-zero,
  divergence-free `g`; Majda–Bertozzi 2002 §2.4). Not in Mathlib.
* `CurlOfForcedNS` (taking curl of forced NS gives the vorticity equation with `curl F`;
  uses Schwarz symmetry and `curl((u·∇)u) = (u·∇)ω − (ω·∇)u` for div-free `u`). Standard;
  not formalized in this fderiv/periodic setting.

**Proved here (abstract Hilbert space = L²):** with `P` self-adjoint and `Pω = ω`,
`⟪ω, P g⟫ = ⟪ω, g⟫`, hence `∫ ω·P(|ω|²ω) = ∫|ω|⁴ = ‖ω‖₄⁴`; and if `P` commutes with
`A = −Δ` (true: both are Fourier multipliers), `⟪Aω, P g⟫ = ⟪Aω, g⟫`, so the H¹ tether term is
`∫∇ω:∇(|ω|²ω) ≥ 0`. These discharge the "model caveat" of PalinstrophyH1.

Plain Navier–Stokes is `κ = 0` and is kept separate (`tetheredVorticity_zero_iff`).
-/
import FTVerified.May.Final
import FTVerified.May.EnstrophyL2
import FTVerified.May.PalinstrophyH1

namespace Frohman.Tether.VorticityTether

open scoped InnerProductSpace RealInnerProductSpace
open Frohman.Tether Frohman.Tether.Torus Set

/-! ## 1. Abstract Leray projection on a real Hilbert space (`H` models `L²(𝕋³;ℝ³)`) -/

section Abstract
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A Leray-type projection: linear, L²-self-adjoint, idempotent. -/
structure LerayProj (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  P : H →ₗ[ℝ] H
  symm : ∀ a b, ⟪P a, b⟫ = ⟪a, P b⟫
  idem : ∀ a, P (P a) = P a

/-- **Key identity.** If `ω` is divergence-free (`Pω = ω`) then `⟪ω, P g⟫ = ⟪ω, g⟫`. -/
theorem inner_leray_of_divFree (L : LerayProj H) {ω : H} (hω : L.P ω = ω) (g : H) :
    ⟪ω, L.P g⟫ = ⟪ω, g⟫ := by
  rw [← L.symm, hω]

/-- L² tether term: `⟪ω, −κ P g⟫ = −κ Q` whenever `⟪ω, g⟫ = Q` (`g = |ω|²ω`, `Q = ‖ω‖₄⁴`). -/
theorem tether_L2_term (L : LerayProj H) {ω g : H} {κ Q : ℝ} (hω : L.P ω = ω)
    (hg : ⟪ω, g⟫ = Q) : ⟪ω, -κ • L.P g⟫ = -κ * Q := by
  rw [inner_smul_right, inner_leray_of_divFree L hω, hg]

/-- H¹ tether term: if `P` commutes with `A` (`A = −Δ`) and `Pω = ω`, `⟪Aω, P g⟫ = ⟪Aω, g⟫`. -/
theorem tether_H1_term (L : LerayProj H) (A : H →ₗ[ℝ] H) (hc : ∀ x, L.P (A x) = A (L.P x))
    {ω : H} (hω : L.P ω = ω) (g : H) : ⟪A ω, L.P g⟫ = ⟪A ω, g⟫ := by
  rw [← L.symm, hc, hω]

/-- Pointwise: `ω·(|ω|²ω) = |ω|⁴`. -/
theorem inner_cubic (ω : H) : ⟪ω, (‖ω‖ ^ 2) • ω⟫ = ‖ω‖ ^ 4 := by
  rw [inner_smul_right, real_inner_self_eq_norm_sq]; ring

/-- Pointwise tether density in the user's notation:
`−κ ω·(|ω|²ω) = quarticTether κ u ω = 𝔗_F[κ, ‖ω‖², u] ω ω` for `ω ⟂ u`. -/
theorem quarticTether_density (κ : ℝ) {u ω : H} (h : ⟪u, ω⟫ = 0) :
    -κ * ⟪ω, (‖ω‖ ^ 2) • ω⟫ = quarticTether κ u ω := by
  rw [inner_cubic, quarticTether_eq κ h]

/-- **Reconciliation with EnstrophyL2.** The generic forced enstrophy balance
`E' = S − νD + ⟪ω, −κ P g⟫`, with `Pω = ω` and `⟪ω,g⟫ = Q`, IS the identity
`TetheredEnstrophyIdentity` used by `tethered_enstrophy_uniform`. -/
theorem enstrophyIdentity_of_vorticityLevel (L : LerayProj H) {E E' S D Q : ℝ → ℝ}
    {w g : ℝ → H} {ν κ T : ℝ} (hcont : ContinuousOn E (Icc 0 T))
    (hder : ∀ x ∈ Ico 0 T, HasDerivWithinAt E (E' x) (Ici x) x)
    (hbal : ∀ x ∈ Ico 0 T, E' x = S x - ν * D x + ⟪w x, -κ • L.P (g x)⟫)
    (hdiv : ∀ x, L.P (w x) = w x) (hQ : ∀ x, ⟪w x, g x⟫ = Q x) :
    EnstrophyL2.TetheredEnstrophyIdentity E E' S D Q ν κ T := by
  refine ⟨hcont, hder, fun x hx => ?_⟩
  rw [hbal x hx, tether_L2_term L (hdiv x) (hQ x)]; ring

end Abstract

/-! ## 2. The concrete system on 𝕋³ -/

/-- A vector field on `ℝ³` (periodic ones are fields on `𝕋³`). -/
abbrev VField := R3 → R3

/-- `|ω|²ω`. -/
noncomputable def cubic (ω : VField) : VField := fun x => (‖ω x‖ ^ 2) • ω x

/-- Vortex stretching `(ω·∇)u`. -/
noncomputable def vortStretch (ω u : VField) (x : R3) : R3 := ∑ i, (ω x) i • pd i u x

/-- Transport `(u·∇)ω`. -/
noncomputable def vortAdvect (u ω : VField) (x : R3) : R3 := ∑ i, (u x) i • pd i ω x

/-- Vorticity equation with a vorticity-level source `G`. -/
def IsVorticityEq (ν : ℝ) (G : ℝ → VField) (u : ℝ → VField) (t : ℝ) (x : R3) : Prop :=
  deriv (fun s => vorticity u s x) t + vortAdvect (u t) (vorticity u t) x
    = vortStretch (vorticity u t) (u t) x + ν • laplacian (vorticity u t) x + G t x

/-- **The tethered system, vorticity level:**
`∂ₜω + (u·∇)ω = (ω·∇)u + νΔω − κ P(|ω|²ω)`, with `P` the (concrete) Leray projection. -/
def IsTetheredVorticityEq (ν κ : ℝ) (P : VField → VField) (u : ℝ → VField) (t : ℝ) (x : R3) :
    Prop := IsVorticityEq ν (fun s => fun y => -κ • P (cubic (vorticity u s)) y) u t x

/-- **Plain NS, vorticity level** (no tether). -/
def IsTrueVorticityEq (ν : ℝ) (u : ℝ → VField) (t : ℝ) (x : R3) : Prop :=
  IsVorticityEq ν 0 u t x

/-- `κ = 0` gives back plain NS. -/
theorem tetheredVorticity_zero_iff {ν : ℝ} {P : VField → VField} {u t x} :
    IsTetheredVorticityEq ν 0 P u t x ↔ IsTrueVorticityEq ν u t x := by
  unfold IsTetheredVorticityEq IsTrueVorticityEq IsVorticityEq
  simp

/-- Named Prop (Biot–Savart, not in Mathlib): `curlInv` right-inverts `curl` on admissible
(smooth, periodic, mean-zero, divergence-free) fields. -/
def CurlRightInverse (curlInv : VField → VField) (Adm : VField → Prop) : Prop :=
  ∀ g, Adm g → curl (curlInv g) = g

/-- **Velocity-level tether force** `F = curl⁻¹(−κ P(|ω|²ω))`. -/
noncomputable def lerayTetherForce (κ : ℝ) (P curlInv : VField → VField) : TetherField :=
  fun u t => curlInv (fun y => -κ • P (cubic (vorticity u t)) y)

/-- `curl F = −κ P(|ω|²ω)`. -/
theorem curl_lerayTetherForce {κ : ℝ} {P curlInv : VField → VField} {Adm : VField → Prop}
    (hinv : CurlRightInverse curlInv Adm) (u : ℝ → VField) (t : ℝ)
    (hadm : Adm (fun y => -κ • P (cubic (vorticity u t)) y)) :
    curl (lerayTetherForce κ P curlInv u t) = fun y => -κ • P (cubic (vorticity u t)) y :=
  hinv _ hadm

/-- **The tethered system, velocity level** — `Torus.IsTetheredNS` with the Leray tether force.
This REPLACES the unspecified `Tfb` for the L²/H¹ results. -/
def IsTetheredNSQuartic (ν κ : ℝ) (P curlInv : VField → VField) (u : ℝ → VField)
    (p : ℝ → R3 → ℝ) (T : ℝ) : Prop :=
  IsTetheredNS ν (lerayTetherForce κ P curlInv) u p T

/-- Named Prop (classical vector calculus, not formalized here): the curl of forced NS is the
vorticity equation with source `curl F`. -/
def CurlOfForcedNS (ν : ℝ) : Prop :=
  ∀ (F : ℝ → VField) u p T, ClassicalSolutionOn ν F u p T →
    ∀ t ∈ Ioo 0 T, ∀ x, IsVorticityEq ν (fun s => curl (F s)) u t x

/-- **Reconciliation theorem.** A velocity-level solution of the tethered NS with force
`F = curl⁻¹(−κP(|ω|²ω))` solves the vorticity-level tethered system — the system the
L² (EnstrophyL2) and H¹ (PalinstrophyH1) results are about. -/
theorem tetheredVorticity_of_velocity {ν κ : ℝ} {P curlInv : VField → VField}
    {Adm : VField → Prop} {u : ℝ → VField} {p : ℝ → R3 → ℝ} {T : ℝ}
    (hcurl : CurlOfForcedNS ν) (hinv : CurlRightInverse curlInv Adm)
    (hadm : ∀ t, Adm (fun y => -κ • P (cubic (vorticity u t)) y))
    (hsol : IsTetheredNSQuartic ν κ P curlInv u p T) :
    ∀ t ∈ Ioo 0 T, ∀ x, IsTetheredVorticityEq ν κ P u t x := by
  intro t ht x
  have h := hcurl _ u p T hsol t ht x
  unfold IsTetheredVorticityEq
  unfold IsVorticityEq at h ⊢
  rw [h]
  show _ + curl (lerayTetherForce κ P curlInv u t) x = _ + (-κ • P (cubic (vorticity u t)) x)
  rw [curl_lerayTetherForce hinv u t (hadm t)]

/-- Pointwise H¹ density of the SAME tether is sign-definite (from PalinstrophyH1). -/
theorem tether_H1_density_nonneg' (ω : Fin 3 → ℝ) (D : Fin 3 → Fin 3 → ℝ) :
    0 ≤ ∑ i, ∑ j, D i j * PalinstrophyH1.tetherGrad ω D i j :=
  PalinstrophyH1.tether_H1_density_nonneg ω D

end Frohman.Tether.VorticityTether
