/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import FTVerified.Sdiff.ObstructionAudit

/-!
# Truth Gate: semantics lock (see `TRUTH_GATE.md`)

PAPER_PATH: paper/frohmanian-tether-verified.tex
PAPER_SHA256: fb364e196d997912b4df3d0b11d59e0f6554b97e1535ce6c6cb1299c1805805e
PAPER_SECTION: Section 5 "Refuted claims", first item ("The tether damps the energy budget")

Locked paper claim (Section "Refuted claims", first item), quoted verbatim:

PAPER_QUOTE_BEGIN
\item \textbf{The tether damps the energy budget.} This is refuted. Let $B$ be a symmetric bilinear form on a real vector space $V$ with $B(x,x)\le0$ for all $x\in V$ (C3), and let $h\in V$ stand for $\delta H$. Then $B(h,h)<0$ if and only if $B(m,h)\neq0$ for some $m\in V$. Consequently, if $B(m,h)=0$ for all $m$ (C2), then $B(h,h)=0$, so the tether contributes nothing to $dH/dt$; and if $B(h,h)=0$, then $B(m,h)=0$ for all $m$
PAPER_QUOTE_END

Reading of the paper's terms (fixed here, once):
* "a symmetric bilinear form `B` on a real vector space `V`" is a Mathlib `LinearMap.BilinForm ℝ V`
  with `B x y = B y x` for all `x, y`;
* "(C3)" is `B x x ≤ 0` for all `x`; "(C2)" is `B m h = 0` for all `m`;
* `h` is any vector of `V` (it stands for `δH`); "the tether contributes nothing to `dH/dt`" is
  `B h h = 0`.

History: the previous lock (2026-11-16) locked `flow_contribution_zero_of_C2`, which is C2 read back
(`hC2 M ω`), a tautology. That theorem is no longer cited. The paper item is rewritten to the
nontrivial statement proved by `energy_damping_iff_not_degenerate` (Cauchy–Schwarz for semidefinite
forms), and C2 appears in it only as a consequence or as one side of an equivalence, never as the
hypothesis that gives the conclusion.

`formal_claim` is the statement of
`FrohmanianTether.ObstructionAudit.energy_damping_iff_not_degenerate`. `paper_claim` transcribes the
paper item with Mathlib only: the equivalence and both consequences.

Scope: this certifies only the locked item. It says nothing about global regularity, which stays
open.
-/

namespace TruthGate

-- TRUTH-GATE LOCK BEGIN
/-- The repository's main statement (`energy_damping_iff_not_degenerate`). -/
def formal_claim : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) → (∀ x, B x x ≤ 0) → ∀ h : V,
      (B h h < 0 ↔ ∃ m, B m h ≠ 0)

/-- The paper's item: the equivalence, and its two consequences (C2 gives no `dH/dt` term;
`B(h,h) = 0` gives C2). -/
def paper_claim : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) → (∀ x, B x x ≤ 0) → ∀ h : V,
      (B h h < 0 ↔ ∃ m, B m h ≠ 0) ∧
      ((∀ m, B m h = 0) → B h h = 0) ∧
      (B h h = 0 → ∀ m, B m h = 0)

/-- The fixed correspondence between the formal statement and the paper's claim. -/
theorem intended_correspondence : formal_claim ↔ paper_claim := by
  constructor
  · intro hf V _ _ B hsym hneg h
    have hiff := hf V B hsym hneg h
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
  · intro hp V _ _ B hsym hneg h
    exact (hp V B hsym hneg h).1
-- TRUTH-GATE LOCK END

/-- The main theorem proves `formal_claim`. -/
theorem formal_claim_holds : formal_claim :=
  fun _ _ _ B hsym hneg h =>
    FrohmanianTether.ObstructionAudit.energy_damping_iff_not_degenerate B hsym hneg h

/-- The paper's claim, transported across the correspondence. -/
theorem paper_claim_holds : paper_claim :=
  intended_correspondence.mp formal_claim_holds

end TruthGate
