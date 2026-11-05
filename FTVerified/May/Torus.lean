/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman (prepared with assistance from Grok; not a co-author).

# Concrete velocity fields on the 3-torus (LOCAL)

Ties the abstract record `NSTetherSolution` to an actual velocity field.

* The 3-torus `𝕋³ = ℝ³/ℤ³` is modelled by fields on `ℝ³ = EuclideanSpace ℝ (Fin 3)` that are
  `1`-periodic in each coordinate direction (`IsPeriodic`).
* `u : ℝ → ℝ³ → ℝ³` is the velocity, `p : ℝ → ℝ³ → ℝ` the pressure; derivatives are Fréchet
  derivatives (`fderiv`) along the standard basis vectors.
* `vorticity u t = curl (u t)`; `divergence`, `laplacian`, `advection`, `grad` componentwise.
* `IsNSEquation ν F u p t x`: `∂ₜu + (u·∇)u + ∇p = νΔu + F` at `(t,x)`.
* **True NS** is `F = 0` (`IsTrueNS`). **Tethered NS** (`IsTetheredNS`) is the MODIFIED system
  whose forcing is a tether feedback field `Tfb u`. How 𝔗_F[κ,w,u] (a bilinear form on the
  abstract space `H`) is realised as a vector field on `𝕋³` is NOT formalized;
  `TetherRealizesFeedback` names the property the enstrophy argument needs (contribution
  `−κ|ω|⁴` at the vorticity maximum), and `not_tetherRealizesFeedback_zero` proves true NS
  does not have it.
* `ClassicalSolutionOn`: `(t,x) ↦ u t x` and `p` are `C^∞` on `[0,T) × ℝ³`, and for `t ∈ [0,T)`
  the fields are periodic, `u` is divergence-free and solves the equation.
* `vortSup u t = ⨆ x, ‖ω(t,x)‖` (Mathlib's real `iSup`, which is `0` for an unbounded range;
  on a compact torus a continuous field is bounded, but that argument is not formalized).
* `toNSTetherSolution` builds the abstract record with `SmoothOn T := ClassicalSolutionOn … T`;
  monotonicity, `SmoothOn 0` and `y ≥ 0` are PROVED.
-/
import FTVerified.May.TetheredLyapunov
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace Frohman.Tether.Torus

/-- Euclidean 3-space. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- `i`-th standard basis vector. -/
noncomputable abbrev e (i : Fin 3) : R3 := EuclideanSpace.single i 1

/-- Build a vector of `ℝ³` from three components. -/
noncomputable def vec3 (a b c : ℝ) : R3 := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![a, b, c]

/-- `1`-periodic in every coordinate direction, i.e. a function on `𝕋³ = ℝ³/ℤ³`. -/
def IsPeriodic {β : Type*} (f : R3 → β) : Prop := ∀ x i, f (x + e i) = f x

/-- Partial derivative `∂ᵢ f (x)`. -/
noncomputable def pd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin 3) (f : R3 → F) (x : R3) : F := fderiv ℝ f x (e i)

/-- `j`-th component of a field. -/
noncomputable def comp (j : Fin 3) (v : R3 → R3) : R3 → ℝ := fun x => (v x) j

/-- Curl. -/
noncomputable def curl (v : R3 → R3) (x : R3) : R3 :=
  vec3 (pd 1 (comp 2 v) x - pd 2 (comp 1 v) x)
       (pd 2 (comp 0 v) x - pd 0 (comp 2 v) x)
       (pd 0 (comp 1 v) x - pd 1 (comp 0 v) x)

/-- Divergence. -/
noncomputable def divergence (v : R3 → R3) (x : R3) : ℝ := ∑ i, pd i (comp i v) x

/-- Vector Laplacian `Δv = Σᵢ ∂ᵢ∂ᵢ v`. -/
noncomputable def laplacian (v : R3 → R3) (x : R3) : R3 := ∑ i, pd i (pd i v) x

/-- Advection `(v·∇)v`. -/
noncomputable def advection (v : R3 → R3) (x : R3) : R3 := ∑ i, (v x) i • pd i v x

/-- Gradient of a scalar. -/
noncomputable def grad (q : R3 → ℝ) (x : R3) : R3 := vec3 (pd 0 q x) (pd 1 q x) (pd 2 q x)

/-- Vorticity `ω(t,·) = curl u(t,·)`. -/
noncomputable def vorticity (u : ℝ → R3 → R3) (t : ℝ) : R3 → R3 := curl (u t)

/-- Navier–Stokes with forcing `F` at `(t,x)`: `∂ₜu + (u·∇)u + ∇p = νΔu + F`. -/
def IsNSEquation (ν : ℝ) (F : ℝ → R3 → R3) (u : ℝ → R3 → R3) (p : ℝ → R3 → ℝ)
    (t : ℝ) (x : R3) : Prop :=
  deriv (fun s => u s x) t + advection (u t) x + grad (p t) x = ν • laplacian (u t) x + F t x

/-- A tether feedback realisation: maps a velocity history to a forcing field. -/
abbrev TetherField := (ℝ → R3 → R3) → ℝ → R3 → R3

/-- Classical (smooth, periodic, divergence-free) solution on `[0,T) × 𝕋³` with forcing `F`. -/
def ClassicalSolutionOn (ν : ℝ) (F : ℝ → R3 → R3) (u : ℝ → R3 → R3) (p : ℝ → R3 → ℝ)
    (T : ℝ) : Prop :=
  ContDiffOn ℝ ⊤ (fun q : ℝ × R3 => u q.1 q.2) (Set.Ico 0 T ×ˢ Set.univ) ∧
  ContDiffOn ℝ ⊤ (fun q : ℝ × R3 => p q.1 q.2) (Set.Ico 0 T ×ˢ Set.univ) ∧
  ∀ t ∈ Set.Ico 0 T, IsPeriodic (u t) ∧ IsPeriodic (p t) ∧
    (∀ x, divergence (u t) x = 0) ∧ (∀ x, IsNSEquation ν F u p t x)

/-- **True** Navier–Stokes: no forcing. -/
def IsTrueNS (ν : ℝ) (u : ℝ → R3 → R3) (p : ℝ → R3 → ℝ) (T : ℝ) : Prop :=
  ClassicalSolutionOn ν 0 u p T

/-- **Tethered** Navier–Stokes: forcing is the tether feedback `Tfb u` (a MODIFIED system). -/
def IsTetheredNS (ν : ℝ) (Tfb : TetherField) (u : ℝ → R3 → R3) (p : ℝ → R3 → ℝ) (T : ℝ) :
    Prop :=
  ClassicalSolutionOn ν (Tfb u) u p T

/-- With the zero tether field the tethered system IS true NS. -/
theorem tetheredNS_zero_iff {ν : ℝ} {u p T} :
    IsTetheredNS ν (fun _ => 0) u p T ↔ IsTrueNS ν u p T := Iff.rfl

/-- `y(t) = sup_x |ω(t,x)|`. -/
noncomputable def vortSup (u : ℝ → R3 → R3) (t : ℝ) : ℝ := ⨆ x, ‖vorticity u t x‖

theorem vortSup_nonneg (u : ℝ → R3 → R3) (t : ℝ) : 0 ≤ vortSup u t :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem classicalSolutionOn_mono {ν F u p} {T T' : ℝ} (h : T' ≤ T)
    (hs : ClassicalSolutionOn ν F u p T) : ClassicalSolutionOn ν F u p T' := by
  obtain ⟨hu, hp, hr⟩ := hs
  have hsub : Set.Ico 0 T' ×ˢ (Set.univ : Set R3) ⊆ Set.Ico 0 T ×ˢ Set.univ :=
    Set.prod_mono (Set.Ico_subset_Ico_right h) le_rfl
  exact ⟨hu.mono hsub, hp.mono hsub, fun t ht => hr t (Set.Ico_subset_Ico_right h ht)⟩

/-- `[0,0)` is empty, so every field is a classical solution on it. -/
theorem classicalSolutionOn_zero (ν F u p) : ClassicalSolutionOn ν F u p 0 := by
  refine ⟨?_, ?_, fun t ht => absurd ht (by simp)⟩ <;> simp

/-- Classical solution on any `[0,T)` with `T ≤ 0`; the content of local existence is
`T > 0`, which is `LocalContinuation` (Fujita–Kato / Kato). -/
theorem classicalSolutionOn_of_nonpos {ν F u p} {T : ℝ} (hT : T ≤ 0) :
    ClassicalSolutionOn ν F u p T :=
  classicalSolutionOn_mono hT (classicalSolutionOn_zero ν F u p)

/-- **Constructor**: velocity/pressure with forcing `F` ↦ `NSTetherSolution` with `y = sup|ω|`,
`y'` = right derivative of `y`, `SmoothOn T` = classical solution on `[0,T)`. -/
noncomputable def toNSTetherSolution (ν : ℝ) (F : ℝ → R3 → R3) (u : ℝ → R3 → R3)
    (p : ℝ → R3 → ℝ) : NSTetherSolution where
  y := vortSup u
  y' := fun t => derivWithin (vortSup u) (Set.Ici t) t
  SmoothOn := ClassicalSolutionOn ν F u p
  smoothOn_mono := classicalSolutionOn_mono
  smoothOn_zero := classicalSolutionOn_zero ν F u p
  y_zero_nonneg := vortSup_nonneg u 0

/-- Record for **true** NS. -/
noncomputable abbrev trueNSRecord (ν : ℝ) (u : ℝ → R3 → R3) (p : ℝ → R3 → ℝ) :=
  toNSTetherSolution ν 0 u p
/-- Record for **tethered** NS. -/
noncomputable abbrev tetheredNSRecord (ν : ℝ) (Tfb : TetherField) (u : ℝ → R3 → R3)
    (p : ℝ → R3 → ℝ) := toNSTetherSolution ν (Tfb u) u p

theorem toNSTetherSolution_smoothOn_iff {ν F u p T} :
    (toNSTetherSolution ν F u p).SmoothOn T ↔ ClassicalSolutionOn ν F u p T := Iff.rfl

theorem toNSTetherSolution_y {ν F u p} (t : ℝ) :
    (toNSTetherSolution ν F u p).y t = ⨆ x, ‖vorticity u t x‖ := rfl

theorem toNSTetherSolution_y_nonneg {ν F u p} (t : ℝ) :
    0 ≤ (toNSTetherSolution ν F u p).y t := vortSup_nonneg u t

/-- **Named Prop (not formalized).** The tether field realises 𝔗_F feedback at a vorticity
maximum: at each maximizer `x*` of `|ω(t,·)|`, `ω·curl(Tfb u) = −κ|ω|⁴`. This is
`TetherFeedback` of `Enstrophy.lean`, stated on the concrete field. -/
def TetherRealizesFeedback (Tfb : TetherField) (κ : ℝ) (u : ℝ → R3 → R3) : Prop :=
  ∀ t x, (∀ z, ‖vorticity u t z‖ ≤ ‖vorticity u t x‖) →
    inner ℝ (vorticity u t x) (curl (Tfb u t) x) = -κ * ‖vorticity u t x‖ ^ 4

/-- True NS (`Tfb = 0`) never realises the feedback at a nonzero vorticity maximum. -/
theorem not_tetherRealizesFeedback_zero {κ : ℝ} (hκ : 0 < κ) {u : ℝ → R3 → R3} {t : ℝ}
    {x : R3} (hmax : ∀ z, ‖vorticity u t z‖ ≤ ‖vorticity u t x‖)
    (hne : vorticity u t x ≠ 0) : ¬ TetherRealizesFeedback (fun _ => 0) κ u := by
  intro h
  have h1 := h t x hmax
  have hc : curl ((fun _ : ℝ → R3 → R3 => (0 : ℝ → R3 → R3)) u t) x = 0 := by
    have hz : ∀ j : Fin 3, comp j (0 : R3 → R3) = 0 := fun j => by
      funext y; simp [comp]
    simp [curl, pd, vec3, hz]
  rw [hc, inner_zero_right] at h1
  have : 0 < ‖vorticity u t x‖ := norm_pos_iff.mpr hne
  nlinarith [pow_pos this 4]

end Frohman.Tether.Torus
