-- SPDX-FileCopyrightText: 2026 Benjamin Stanley Frohman
-- SPDX-License-Identifier: Apache-2.0
import FTVerified.May.VorticityTether
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option linter.unusedSimpArgs false

namespace Frohman.Tether.CurlNS
open Frohman.Tether.Torus Frohman.Tether.VorticityTether Set

abbrev Sm (v : R3 → R3) : Prop := ContDiff ℝ ⊤ v

theorem vec3_apply (a b c : ℝ) : vec3 a b c 0 = a ∧ vec3 a b c 1 = b ∧ vec3 a b c 2 = c := by
  simp [vec3]

theorem sm_pd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {v : R3 → F}
    (hv : ContDiff ℝ ⊤ v) (i : Fin 3) : ContDiff ℝ ⊤ (pd i v) := by
  have : ContDiff ℝ ⊤ (fderiv ℝ v) := hv.fderiv_right (by simp)
  exact this.clm_apply contDiff_const

theorem pd_comm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {v : R3 → F}
    (hv : ContDiff ℝ ⊤ v) (i j : Fin 3) : pd i (pd j v) = pd j (pd i v) := by
  funext x
  have hs := ContDiffAt.isSymmSndFDerivAt_of_omega (hv.contDiffAt (x := x))
  have hd : ∀ k, pd k (pd j v) x = fderiv ℝ (fderiv ℝ v) x (e k) (e j) := by
    intro k
    unfold pd
    rw [fderiv_clm_apply ((hv.fderiv_right (m := ⊤) (by simp)).differentiable (by simp) x)
      (differentiableAt_const _)]
    simp
  have hd' : ∀ k, pd k (pd i v) x = fderiv ℝ (fderiv ℝ v) x (e k) (e i) := by
    intro k
    unfold pd
    rw [fderiv_clm_apply ((hv.fderiv_right (m := ⊤) (by simp)).differentiable (by simp) x)
      (differentiableAt_const _)]
    simp
  rw [hd, hd', hs]

theorem pd_comp {v : R3 → R3} (hv : Differentiable ℝ v) (i j : Fin 3) (x : R3) :
    pd i (comp j v) x = (pd i v x) j := by
  unfold pd comp
  have h := ((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).hasFDerivAt.comp x (hv x).hasFDerivAt)
  rw [show (fun x => v x j) = (EuclideanSpace.proj j : R3 →L[ℝ] ℝ) ∘ v from rfl, h.fderiv]
  simp

section Lin
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem pd_add {v w : R3 → F} (hv : Differentiable ℝ v) (hw : Differentiable ℝ w) (i : Fin 3) :
    pd i (fun y => v y + w y) = fun x => pd i v x + pd i w x := by
  funext x; unfold pd; rw [fderiv_fun_add (hv x) (hw x)]; rfl

theorem pd_sub {v w : R3 → F} (hv : Differentiable ℝ v) (hw : Differentiable ℝ w) (i : Fin 3) :
    pd i (fun y => v y - w y) = fun x => pd i v x - pd i w x := by
  funext x; unfold pd; rw [fderiv_fun_sub (hv x) (hw x)]; rfl

theorem pd_const_smul {v : R3 → F} (hv : Differentiable ℝ v) (c : ℝ) (i : Fin 3) :
    pd i (fun y => c • v y) = fun x => c • pd i v x := by
  funext x; unfold pd; rw [fderiv_fun_const_smul (hv x)]; rfl

theorem pd_sum {v : Fin 3 → R3 → F} (hv : ∀ k, Differentiable ℝ (v k)) (i : Fin 3) :
    pd i (fun y => ∑ k, v k y) = fun x => ∑ k, pd i (v k) x := by
  funext x; unfold pd; rw [fderiv_fun_sum (fun k _ => hv k x)]; simp

theorem pd_mul {f g : R3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin 3) : pd i (fun y => f y * g y) = fun x => f x * pd i g x + pd i f x * g x := by
  funext x; unfold pd; rw [fderiv_fun_mul (hf x) (hg x)]; simp; ring

end Lin

theorem dif {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {v : R3 → F}
    (hv : ContDiff ℝ ⊤ v) : Differentiable ℝ v := hv.differentiable (by simp)

theorem sm_comp {v : R3 → R3} (hv : ContDiff ℝ ⊤ v) (j : Fin 3) :
    ContDiff ℝ ⊤ (comp j v) :=
  (EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff.comp hv

/-- `∂ᵢ` commutes with taking a component (as functions). -/
theorem pd_comp' {v : R3 → R3} (hv : Differentiable ℝ v) (i j : Fin 3) :
    pd i (comp j v) = comp j (pd i v) := funext (pd_comp hv i j)

theorem comp_grad (q : R3 → ℝ) (j : Fin 3) : comp j (grad q) = pd j q := by
  funext y; fin_cases j <;> simp [comp, grad, vec3]

/-- `curl ∇q = 0`. -/
theorem curl_grad {q : R3 → ℝ} (hq : ContDiff ℝ ⊤ q) : curl (grad q) = 0 := by
  funext x
  simp only [curl, comp_grad, pd_comm hq 1 2, pd_comm hq 2 0, pd_comm hq 0 1, sub_self]
  simp [vec3]

theorem comp_laplacian {v : R3 → R3} (hv : ContDiff ℝ ⊤ v) (j : Fin 3) :
    comp j (laplacian v) = fun y => ∑ i, pd i (pd i (comp j v)) y := by
  funext y
  simp only [comp, laplacian]
  rw [show (∑ i, pd i (pd i v) y) j = ∑ i, (pd i (pd i v) y) j by simp]
  congr 1; funext i
  rw [pd_comp' (dif hv), pd_comp' (dif (sm_pd hv i))]
  rfl

theorem curl_apply (w : R3 → R3) (x : R3) :
    curl w x 0 = pd 1 (comp 2 w) x - pd 2 (comp 1 w) x ∧
    curl w x 1 = pd 2 (comp 0 w) x - pd 0 (comp 2 w) x ∧
    curl w x 2 = pd 0 (comp 1 w) x - pd 1 (comp 0 w) x := by
  simp [curl, vec3]

theorem comp_curl (w : R3 → R3) :
    comp 0 (curl w) = (fun y => pd 1 (comp 2 w) y - pd 2 (comp 1 w) y) ∧
    comp 1 (curl w) = (fun y => pd 2 (comp 0 w) y - pd 0 (comp 2 w) y) ∧
    comp 2 (curl w) = (fun y => pd 0 (comp 1 w) y - pd 1 (comp 0 w) y) := by
  refine ⟨?_, ?_, ?_⟩ <;> funext y <;> simp [comp, curl, vec3]

theorem sm_curl {v : R3 → R3} (hv : ContDiff ℝ ⊤ v) : ContDiff ℝ ⊤ (curl v) := by
  rw [contDiff_euclidean]
  intro j
  have h := comp_curl v
  have hs : ∀ a b, ContDiff ℝ ⊤ (pd a (comp b v)) := fun a b => sm_pd (sm_comp hv b) a
  fin_cases j
  · exact (show (fun x => curl v x 0) = comp 0 (curl v) from rfl) ▸ h.1 ▸ (hs 1 2).sub (hs 2 1)
  · exact (show (fun x => curl v x 1) = comp 1 (curl v) from rfl) ▸ h.2.1 ▸ (hs 2 0).sub (hs 0 2)
  · exact (show (fun x => curl v x 2) = comp 2 (curl v) from rfl) ▸ h.2.2 ▸ (hs 0 1).sub (hs 1 0)

theorem pd3 {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (a i : Fin 3) :
    pd a (pd i (pd i f)) = pd i (pd i (pd a f)) := by
  rw [pd_comm (sm_pd hf i) a i, pd_comm hf a i]

theorem lap_scalar_sub {f g : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) (x : R3) :
    ∑ i, pd i (pd i (fun y => f y - g y)) x = ∑ i, pd i (pd i f) x - ∑ i, pd i (pd i g) x := by
  rw [← Finset.sum_sub_distrib]
  congr 1; funext i
  rw [pd_sub (dif hf) (dif hg), pd_sub (dif (sm_pd hf i)) (dif (sm_pd hg i))]

theorem pd_lap {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (a : Fin 3) (x : R3) :
    pd a (fun y => ∑ i, pd i (pd i f) y) x = ∑ i, pd i (pd i (pd a f)) x := by
  rw [pd_sum (fun i => dif (sm_pd (sm_pd hf i) i))]
  exact Finset.sum_congr rfl fun i _ => by rw [pd3 hf]

/-- `curl Δv = Δ curl v` (smooth `v`). -/
theorem curl_laplacian {v : R3 → R3} (hv : ContDiff ℝ ⊤ v) :
    curl (laplacian v) = laplacian (curl v) := by
  have hc := sm_curl hv
  have hs : ∀ b, ContDiff ℝ ⊤ (comp b v) := fun b => sm_comp hv b
  funext x
  ext j
  have L : ∀ k, laplacian (curl v) x k = ∑ i, pd i (pd i (comp k (curl v))) x := fun k => by
    have := congrFun (comp_laplacian hc k) x
    simpa [comp] using this
  obtain ⟨c0, c1, c2⟩ := comp_curl v
  obtain ⟨a0, a1, a2⟩ := curl_apply (laplacian v) x
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [a0, L 0, c0, comp_laplacian hv, comp_laplacian hv, pd_lap (hs 2), pd_lap (hs 1),
      lap_scalar_sub (sm_pd (hs 2) 1) (sm_pd (hs 1) 2)]
  · simp only [Fin.mk_one, Fin.isValue]
    rw [a1, L 1, c1, comp_laplacian hv, comp_laplacian hv, pd_lap (hs 0), pd_lap (hs 2),
      lap_scalar_sub (sm_pd (hs 0) 2) (sm_pd (hs 2) 0)]
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [a2, L 2, c2, comp_laplacian hv, comp_laplacian hv, pd_lap (hs 1), pd_lap (hs 0),
      lap_scalar_sub (sm_pd (hs 1) 0) (sm_pd (hs 0) 1)]

theorem comp_adv {v : R3 → R3} (hv : ContDiff ℝ ⊤ v) (j : Fin 3) :
    comp j (advection v) = fun y => ∑ i, comp i v y * pd i (comp j v) y := by
  funext y
  simp only [comp, advection]
  rw [show (∑ i, (v y) i • pd i v y) j = ∑ i, (v y) i * (pd i v y) j by simp]
  congr 1; funext i
  rw [pd_comp (dif hv)]

theorem pd_comp_adv {v : R3 → R3} (hv : ContDiff ℝ ⊤ v) (k j : Fin 3) (x : R3) :
    pd k (comp j (advection v)) x = ∑ i, (comp i v x * pd k (pd i (comp j v)) x +
      pd k (comp i v) x * pd i (comp j v) x) := by
  have hs : ∀ b, ContDiff ℝ ⊤ (comp b v) := fun b => sm_comp hv b
  rw [comp_adv hv, pd_sum (fun i => (dif ((hs i).mul (sm_pd (hs j) i))))]
  exact Finset.sum_congr rfl fun i _ => by rw [pd_mul (dif (hs i)) (dif (sm_pd (hs j) i))]

/-- **Vector identity.** For smooth divergence-free `v`,
`curl((v·∇)v) = (v·∇)ω − (ω·∇)v` with `ω = curl v`. -/
theorem curl_advection {v : R3 → R3} (hv : ContDiff ℝ ⊤ v) (hdiv : ∀ x, divergence v x = 0)
    (x : R3) :
    curl (advection v) x = vortAdvect v (curl v) x - vortStretch (curl v) v x := by
  have hs : ∀ b, ContDiff ℝ ⊤ (comp b v) := fun b => sm_comp hv b
  have hd := hdiv x
  simp only [divergence, Fin.sum_univ_three] at hd
  obtain ⟨c0, c1, c2⟩ := comp_curl v
  obtain ⟨a0, a1, a2⟩ := curl_apply (advection v) x
  obtain ⟨w0, w1, w2⟩ := curl_apply v x
  have hω := dif (sm_curl hv)
  have VA : ∀ j, vortAdvect v (curl v) x j = ∑ i, comp i v x * pd i (comp j (curl v)) x :=
    fun j => by
      simp only [vortAdvect]
      rw [show (∑ i, (v x) i • pd i (curl v) x) j = ∑ i, (v x) i * (pd i (curl v) x) j by simp]
      exact Finset.sum_congr rfl fun i _ => by rw [pd_comp hω]; rfl
  have VS : ∀ j, vortStretch (curl v) v x j = ∑ i, curl v x i * pd i (comp j v) x :=
    fun j => by
      simp only [vortStretch]
      rw [show (∑ i, (curl v x) i • pd i v x) j = ∑ i, (curl v x) i * (pd i v x) j by simp]
      exact Finset.sum_congr rfl fun i _ => by rw [pd_comp (dif hv)]
  have PS : ∀ i a b c d, pd i (fun y => pd a (comp b v) y - pd c (comp d v) y) x
      = pd i (pd a (comp b v)) x - pd i (pd c (comp d v)) x := fun i a b c d => by
    rw [pd_sub (dif (sm_pd (hs b) a)) (dif (sm_pd (hs d) c))]
  ext j
  rw [PiLp.sub_apply, VA, VS]
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [a0, c0, pd_comp_adv hv, pd_comp_adv hv]
    simp only [PS, Fin.sum_univ_three, Fin.isValue, w0, w1, w2]
    simp only [pd_comm (hs 0) 1 0, pd_comm (hs 0) 2 0, pd_comm (hs 0) 2 1,
      pd_comm (hs 1) 1 0, pd_comm (hs 1) 2 0, pd_comm (hs 1) 2 1,
      pd_comm (hs 2) 1 0, pd_comm (hs 2) 2 0, pd_comm (hs 2) 2 1]
    linear_combination (pd 1 (comp 2 v) x - pd 2 (comp 1 v) x) * hd
  · simp only [Fin.mk_one, Fin.isValue]
    rw [a1, c1, pd_comp_adv hv, pd_comp_adv hv]
    simp only [PS, Fin.sum_univ_three, Fin.isValue, w0, w1, w2]
    simp only [pd_comm (hs 0) 1 0, pd_comm (hs 0) 2 0, pd_comm (hs 0) 2 1,
      pd_comm (hs 1) 1 0, pd_comm (hs 1) 2 0, pd_comm (hs 1) 2 1,
      pd_comm (hs 2) 1 0, pd_comm (hs 2) 2 0, pd_comm (hs 2) 2 1]
    linear_combination (pd 2 (comp 0 v) x - pd 0 (comp 2 v) x) * hd
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [a2, c2, pd_comp_adv hv, pd_comp_adv hv]
    simp only [PS, Fin.sum_univ_three, Fin.isValue, w0, w1, w2]
    simp only [pd_comm (hs 0) 1 0, pd_comm (hs 0) 2 0, pd_comm (hs 0) 2 1,
      pd_comm (hs 1) 1 0, pd_comm (hs 1) 2 0, pd_comm (hs 1) 2 1,
      pd_comm (hs 2) 1 0, pd_comm (hs 2) 2 0, pd_comm (hs 2) 2 1]
    linear_combination (pd 0 (comp 1 v) x - pd 1 (comp 0 v) x) * hd

/-! ## Time derivative commutes with spatial partials (Schwarz on `ℝ × ℝ³`) -/

section Time
variable {f : ℝ × R3 → ℝ}

theorem fderiv_slice {g : ℝ × R3 → ℝ} {s : ℝ} {y : R3} (hg : DifferentiableAt ℝ g (s, y))
    (w : R3) : fderiv ℝ (fun z => g (s, z)) y w = fderiv ℝ g (s, y) (0, w) := by
  have h : HasFDerivAt (fun z : R3 => ((s, z) : ℝ × R3))
      (ContinuousLinearMap.inr ℝ ℝ R3) y := by
    simpa using (hasFDerivAt_const s y).prodMk (hasFDerivAt_id y)
  have h2 := (hg.hasFDerivAt.comp y h).fderiv
  rw [show (fun z => g (s, z)) = g ∘ (fun z => ((s, z) : ℝ × R3)) from rfl, h2]; simp

theorem hasDerivAt_slice {g : ℝ × R3 → ℝ} {s : ℝ} {y : R3} (hg : DifferentiableAt ℝ g (s, y)) :
    HasDerivAt (fun r => g (r, y)) (fderiv ℝ g (s, y) (1, 0)) s := by
  have h : HasDerivAt (fun r : ℝ => ((r, y) : ℝ × R3)) (1, 0) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
  exact hg.hasFDerivAt.comp_hasDerivAt s h

/-- **Schwarz for `∂ₜ ∂ᵢ`.** If `f` is analytic near `{t} × ℝ³` then
`∂ₜ(∂ᵢ f)(t,x) = ∂ᵢ(∂ₜ f)(t,x)`. -/
theorem hasDerivAt_pd_time {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hf : ∀ s ∈ Ioo a b, ∀ y, ContDiffAt ℝ ⊤ f (s, y)) (i : Fin 3) (x : R3) :
    HasDerivAt (fun s => pd i (fun y => f (s, y)) x)
      (pd i (fun y => deriv (fun s => f (s, y)) t) x) t := by
  have hd : ∀ s ∈ Ioo a b, ∀ y, DifferentiableAt ℝ f (s, y) :=
    fun s hs y => (hf s hs y).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ (fderiv ℝ f) (t, x) :=
    ((hf t ht x).fderiv_right (m := ⊤) (by simp)).differentiableAt (by simp)
  -- LHS as `s ↦ fderiv f (s,x) (0,eᵢ)`
  have hev : (fun s => fderiv ℝ f (s, x) (0, e i)) =ᶠ[nhds t]
      (fun s => pd i (fun y => f (s, y)) x) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    unfold pd; rw [fderiv_slice (hd s hs x)]
  have hL : HasDerivAt (fun s => fderiv ℝ f (s, x) (0, e i))
      (fderiv ℝ (fderiv ℝ f) (t, x) (1, 0) (0, e i)) t := by
    have h1 := hasDerivAt_slice (g := fun q => fderiv ℝ f q (0, e i)) (s := t) (y := x)
      (hG.clm_apply (differentiableAt_const _))
    rw [fderiv_clm_apply hG (differentiableAt_const _)] at h1
    simpa using h1
  refine (hL.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  -- RHS
  have hfun : (fun y => deriv (fun s => f (s, y)) t) = fun y => fderiv ℝ f (t, y) (1, 0) := by
    funext y; exact (hasDerivAt_slice (hd t ht y)).deriv
  rw [hfun]
  unfold pd
  have hG' : DifferentiableAt ℝ (fun q => fderiv ℝ f q (1, 0)) (t, x) :=
    hG.clm_apply (differentiableAt_const _)
  rw [fderiv_slice (g := fun q => fderiv ℝ f q (1, 0)) hG',
    fderiv_clm_apply hG (differentiableAt_const _)]
  have hs := ContDiffAt.isSymmSndFDerivAt_of_omega (hf t ht x)
  simp [hs (1, 0) (0, e i)]

end Time

theorem vec3_eq (a b c : ℝ) : vec3 a b c = a • e 0 + b • e 1 + c • e 2 := by
  ext j; fin_cases j <;> simp [vec3]

theorem curl_lin {a b : R3 → R3} (ha : ∀ j, Differentiable ℝ (comp j a))
    (hb : ∀ j, Differentiable ℝ (comp j b)) (c : ℝ) :
    curl (fun y => a y + c • b y) = fun x => curl a x + c • curl b x := by
  have hc : ∀ j, comp j (fun y => a y + c • b y) = fun y => comp j a y + c • comp j b y :=
    fun j => by funext y; simp [comp]
  have hp : ∀ i j x, pd i (fun y => comp j a y + c • comp j b y) x
      = pd i (comp j a) x + c * pd i (comp j b) x := fun i j x => by
    have h1 := congrFun (pd_add (v := comp j a) (w := fun y => c • comp j b y) (ha j)
      ((hb j).const_smul c) i) x
    have h2 := congrFun (pd_const_smul (hb j) c i) x
    simp only at h1 h2
    rw [h1, h2]; rfl
  funext x
  simp only [curl, hc, hp]
  rw [vec3_eq, vec3_eq, vec3_eq]
  module

theorem curl_add {a b : R3 → R3} (ha : ∀ j, Differentiable ℝ (comp j a))
    (hb : ∀ j, Differentiable ℝ (comp j b)) :
    curl (fun y => a y + b y) = fun x => curl a x + curl b x := by
  simpa using curl_lin ha hb 1

theorem comp_add_diff {a b : R3 → R3} (ha : ∀ j, Differentiable ℝ (comp j a))
    (hb : ∀ j, Differentiable ℝ (comp j b)) (j : Fin 3) :
    Differentiable ℝ (comp j (fun y => a y + b y)) := by
  have : comp j (fun y => a y + b y) = fun y => comp j a y + comp j b y := by
    funext y; simp [comp]
  rw [this]; exact (ha j).add (hb j)

theorem hasDerivAt_vec3 {A B C : ℝ → ℝ} {a b c t : ℝ} (hA : HasDerivAt A a t)
    (hB : HasDerivAt B b t) (hC : HasDerivAt C c t) :
    HasDerivAt (fun s => vec3 (A s) (B s) (C s)) (vec3 a b c) t := by
  simp only [vec3_eq]
  exact ((hA.smul_const _).add (hB.smul_const _)).add (hC.smul_const _)

/-- **`CurlOfForcedNS`, proved** (on the open time interval `(0,T)`, where the solution is
smooth in `(t,x)` jointly; at the closed endpoint `t = 0` a one-sided time derivative would be
needed). Taking the curl of forced Navier–Stokes `∂ₜu + (u·∇)u + ∇p = νΔu + F` with smooth
divergence-free `u` gives `∂ₜω + (u·∇)ω = (ω·∇)u + νΔω + curl F`. -/
theorem curlOfForcedNS (ν : ℝ) : CurlOfForcedNS ν := by
  intro F u p T hsol t ht x
  obtain ⟨hu, hp, hr⟩ := hsol
  obtain ⟨-, -, hdiv, hns⟩ := hr t (Ioo_subset_Ico_self ht)
  set U : ℝ × R3 → R3 := fun q => u q.1 q.2 with hUdef
  have hnb : ∀ s ∈ Ioo 0 T, ∀ y : R3, Ico 0 T ×ˢ (univ : Set R3) ∈ nhds (s, y) := fun s hs y =>
    Filter.mem_of_superset (prod_mem_nhds (Ioo_mem_nhds hs.1 hs.2) Filter.univ_mem)
      (prod_mono Ioo_subset_Ico_self le_rfl)
  have hUat : ∀ s ∈ Ioo 0 T, ∀ y, ContDiffAt ℝ ⊤ U (s, y) := fun s hs y =>
    hu.contDiffAt (hnb s hs y)
  have hPat : ∀ s ∈ Ioo 0 T, ∀ y, ContDiffAt ℝ ⊤ (fun q : ℝ × R3 => p q.1 q.2) (s, y) :=
    fun s hs y => hp.contDiffAt (hnb s hs y)
  have hsl : ∀ y : R3, ContDiffAt ℝ ⊤ (fun z : R3 => ((t, z) : ℝ × R3)) y := fun y =>
    contDiffAt_const.prodMk contDiffAt_id
  have hut : ContDiff ℝ ⊤ (u t) :=
    contDiff_iff_contDiffAt.2 fun y => (hUat t ht y).comp y (hsl y)
  have hpt : ContDiff ℝ ⊤ (p t) :=
    contDiff_iff_contDiffAt.2 fun y => (hPat t ht y).comp y (hsl y)
  -- scalar components
  set fj : Fin 3 → ℝ × R3 → ℝ := fun j q => U q j with hfj
  have hfjat : ∀ j, ∀ s ∈ Ioo 0 T, ∀ y, ContDiffAt ℝ ⊤ (fj j) (s, y) := fun j s hs y =>
    (EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff.contDiffAt.comp _ (hUat s hs y)
  set D : R3 → R3 := fun y => deriv (fun s => u s y) t with hD
  have hDj : ∀ j, comp j D = fun y => deriv (fun s => fj j (s, y)) t := fun j => by
    funext y
    have hdU : DifferentiableAt ℝ U (t, y) := (hUat t ht y).differentiableAt (by simp)
    have hv : HasDerivAt (fun s => u s y) (deriv (fun s => u s y) t) t :=
      (hdU.comp (𝕜 := ℝ) (g := U) (f := fun s : ℝ => ((s, y) : ℝ × R3)) t
        (differentiableAt_id.prodMk (differentiableAt_const y))).hasDerivAt
    exact ((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hv).deriv.symm
  have hDdiff : ∀ j, Differentiable ℝ (comp j D) := fun j => by
    rw [hDj]
    have he : (fun y => deriv (fun s => fj j (s, y)) t) = fun y => fderiv ℝ (fj j) (t, y) (1, 0) :=
      by funext y; exact (hasDerivAt_slice ((hfjat j t ht y).differentiableAt (by simp))).deriv
    rw [he]
    intro y
    have hG := (((hfjat j t ht y).fderiv_right (m := ⊤) (by simp)).differentiableAt
      (by simp)).clm_apply (differentiableAt_const ((1, 0) : ℝ × R3))
    have hsd : DifferentiableAt ℝ (fun z : R3 => ((t, z) : ℝ × R3)) y :=
      (differentiableAt_const t).prodMk differentiableAt_id
    exact hG.comp y hsd
  -- time derivative of the vorticity
  have hT : ∀ a b, HasDerivAt (fun s => pd a (comp b (u s)) x) (pd a (comp b D) x) t :=
    fun a b => by
      rw [hDj]; exact hasDerivAt_pd_time ht (hfjat b) a x
  have hω : deriv (fun s => vorticity u s x) t = curl D x := by
    have := hasDerivAt_vec3 ((hT 1 2).sub (hT 2 1)) ((hT 2 0).sub (hT 0 2))
      ((hT 0 1).sub (hT 1 0))
    exact this.deriv
  -- F from the NS equation
  have hF : F t = fun y => (D y + advection (u t) y + grad (p t) y) + (-ν) • laplacian (u t) y :=
    by
      funext y
      have h := hns y
      unfold IsNSEquation at h
      rw [h]; simp [hD]
  have hs : ∀ b, ContDiff ℝ ⊤ (comp b (u t)) := fun b => sm_comp hut b
  have hAdv : ∀ j, Differentiable ℝ (comp j (advection (u t))) := fun j => by
    rw [comp_adv hut]
    exact Differentiable.fun_sum fun i _ => (dif (hs i)).mul (dif (sm_pd (hs j) i))
  have hGr : ∀ j, Differentiable ℝ (comp j (grad (p t))) := fun j => by
    rw [comp_grad]; exact dif (sm_pd hpt j)
  have hLap : ∀ j, Differentiable ℝ (comp j (laplacian (u t))) := fun j => by
    rw [comp_laplacian hut]
    exact Differentiable.fun_sum fun i _ => dif (sm_pd (sm_pd (hs j) i) i)
  have hcF : curl (F t) x = curl D x + (vortAdvect (u t) (curl (u t)) x
      - vortStretch (curl (u t)) (u t) x) + (-ν) • laplacian (curl (u t)) x := by
    rw [hF, curl_lin (comp_add_diff (comp_add_diff hDdiff hAdv) hGr) hLap,
      curl_add (comp_add_diff hDdiff hAdv) hGr, curl_add hDdiff hAdv]
    simp only
    rw [curl_grad hpt, curl_laplacian hut, curl_advection hut hdiv]
    simp
  unfold IsVorticityEq
  simp only [vorticity] at hω ⊢
  rw [hω, hcF]
  module


end Frohman.Tether.CurlNS
